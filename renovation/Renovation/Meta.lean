import Lean
import Renovation.TestCaseEnv
import Renovation.AddConstInfo

open Lean Elab Term Command Meta
open Lean.Parser.Command

/-- Checks that the kernel indeed rejects `decl`. -/
def assertKernelRejects (decl : Declaration) : CoreM Unit := do
  -- Synchronously, unlike `addDecl`, which may check definitions in a separate task
  let accepted := ((← getEnv).toKernelEnv.addDecl (← getOptions) decl).toBool
  if accepted then
    -- The toolchain pinned here (lean4#16595 at 53e1623) lacks some checks of the final version
    if Lean.githash.startsWith "53e1623" then
      logWarning "the kernel of this toolchain accepts this bad declaration"
    else
      throwError "the kernel accepts this bad declaration"

/-! Definitions and theorems, as in the tutorial -/

def addTestCaseDeclCore (descr? : Option String) (decl : Lean.Declaration) (outcome : Outcome) :
    CoreM Unit := do
  match outcome with
  | .good => addDecl decl
  | .bad =>
    assertKernelRejects decl
    withOptions (fun o => debug.skipKernelTC.set o true) do
      addDecl decl
  registerTestCase {
    decls := decl.getNames.toArray
    outcome := outcome
    description := descr?
  }

open TSyntax.Compat in
def getDescr (descr? : Option (TSyntax ``plainDocComment)) : CoreM (Option String) := do
  let descrStr? ← descr?.mapM (getDocStringText ·)
  return descrStr?.map (·.trimAscii.copy)

open TSyntax.Compat in -- due to plainDocComments vs. docComment
def elabAndAddTestCaseDecl (descr? : Option (TSyntax ``plainDocComment)) (name : TSyntax ``declId)
    (type : Term) (value : Term) (outcome : Outcome) (declKind : ConstantKind) :
    CommandElabM Unit := liftTermElabM do
  let descrStr? ← getDescr descr?
  let (declName, lparams) ← match name with
    | `(declId| $n:ident) => pure (n.getId, [])
    | `(declId| $n:ident.{ $[$ls:ident],* }) => pure (n.getId, ls.toList.map (·.getId))
    | _ => throwUnsupportedSyntax
  withLevelNames lparams do
    let typeExpr ← elabTermAndSynthesize type none
    let valueExpr ← elabTermAndSynthesize value (some typeExpr)
    Term.synthesizeSyntheticMVarsNoPostponing
    let typeExpr ← instantiateMVars typeExpr
    if typeExpr.hasMVar then
      throwError "Failed to elaborate type, has remaining metavariables:{indentD typeExpr}"
    let valueExpr ← instantiateMVars valueExpr
    if valueExpr.hasMVar then
      throwError "Failed to elaborate value, has remaining metavariables:{indentD valueExpr}"
    let decl ← match declKind with
      | .defn => pure <| .defnDecl {
          name := declName, levelParams := lparams, type := typeExpr, value := valueExpr
          hints := .opaque, safety := .safe }
      | .thm => pure <| .thmDecl {
          name := declName, levelParams := lparams, type := typeExpr, value := valueExpr }
      | _ => throwError "Unsupported declaration kind in test case: {repr declKind}"
    addTestCaseDeclCore descrStr? decl outcome

elab descr?:(plainDocComment)? "good_def " name:declId ":" type:term ":=" value:term : command => do
  elabAndAddTestCaseDecl descr? name type value Outcome.good ConstantKind.defn

elab descr?:(plainDocComment)? "bad_def " name:declId ":" type:term ":=" value:term : command => do
  elabAndAddTestCaseDecl descr? name type value Outcome.bad ConstantKind.defn

elab descr?:(plainDocComment)? "good_thm " name:declId ":" type:term ":=" value:term : command => do
  elabAndAddTestCaseDecl descr? name type value Outcome.good ConstantKind.thm

elab descr?:(plainDocComment)? "bad_thm " name:declId ":" type:term ":=" value:term : command => do
  elabAndAddTestCaseDecl descr? name type value Outcome.bad ConstantKind.thm

section Unchecked

/-- An elaborator that just inserts the term, without regard for the actual type needed here -/
syntax (name := unchecked) "unchecked " term : term

@[term_elab «unchecked»]
def elabUnchecked : TermElab := fun stx expectedType? => do
  match stx with
  | `(unchecked $t) =>
    let some expectedType := expectedType? |
      tryPostpone
      throwError "invalid 'unchecked', expected type required"
    let e ← elabTerm t none
    let mvar ← mkFreshExprMVar expectedType MetavarKind.syntheticOpaque
    mvar.mvarId!.assign e
    return mvar
  | _ => throwUnsupportedSyntax

end Unchecked

/--
`proj% S i e` is the primitive projection `Expr.proj S i e`, the `i`th field (counting from 0) of
`e : S ...`. The inductive types here are declared without structure information, so the usual
`e.1` notation does not apply to them.
-/
syntax (name := projPrim) "proj% " ident num term:max : term

@[term_elab projPrim]
def elabProjPrim : TermElab := fun stx _ => do
  match stx with
  | `(proj% $s:ident $i:num $e) =>
    let some (.inductInfo _) := (← getEnv).find? s.getId |
      throwError "proj%: {s.getId} is not an inductive type"
    return .proj s.getId i.getNat (← elabTerm e none)
  | _ => throwUnsupportedSyntax

/-! Inductive types with explicit flags -/

/-- The feature flags of an inductive type (lean4#16595). They are all off by default. -/
structure Flags where
  isImpredicative : Bool := false
  isK : Bool := false
  hasProjections : Bool := false
  hasEta : Bool := false
  hasLargeElim : Bool := false
  deriving Inhabited, Repr

/--
The recursor of a type without large elimination has no reduction rules. The toolchain pinned here
(lean4#16595 at 53e1623) still generates them; the final version of the PR does not, so they are
dropped here, after the kernel has checked the declaration. This is a no-op on a toolchain built
from the final version of the PR.
-/
def dropSmallRecRules (env : Environment) (ci : ConstantInfo) : ConstantInfo :=
  match ci with
  | .recInfo v =>
    -- Not `getMajorInduct`, which for the recursor of an auxiliary type of a nested inductive is
    -- the container
    match env.find? v.all.head! with
    | some (.inductInfo iv) => if iv.hasLargeElim then ci else .recInfo { v with rules := [] }
    | _ => ci
  | ci => ci

/-- Applies `dropSmallRecRules` to the recursors of the inductive types `types`. -/
def fixupRecRules (types : List Name) : CoreM Unit := do
  let env ← getEnv
  -- The recursors, including those of the auxiliary types of nested inductives
  let mut recs := #[]
  for t in types do
    if let some ci := env.toKernelEnv.find? (t ++ `rec) then recs := recs.push ci
    let mut i := 1
    while true do
      let some ci := env.toKernelEnv.find? (t ++ Name.mkSimple s!"rec_{i}") | break
      recs := recs.push ci
      i := i + 1
  for ci in recs do
    modifyEnv (insertConstInfo · (dropSmallRecRules env ci))

/-- An inductive block as elaborated, with the flags that the elaborator chose. -/
structure Block where
  levelParams : List Name
  numParams : Nat
  types : List InductiveType

/--
Elaborates an `inductive` command (or a `mutual` block of them) with the usual elaborator, and
returns the declaration that it sent to the kernel, without keeping anything in the environment.
-/
def scratchElabInductive (cmd : Syntax) : CommandElabM Block := do
  -- The names of the types, in the order of the source
  let names : Array Name := Id.run do
    let mut names := #[]
    for s in cmd.topDown do
      if s.isOfKind ``Lean.Parser.Command.inductive then
        names := names.push s[1][0].getId
    return names
  if names.isEmpty then throwError "no inductive type in{indentD cmd}"
  let env ← getEnv
  -- Skip the auxiliary constructions, some of which do not cope with all flags
  let opts := (← getOptions)
    |>.set `genInjectivity false |>.set `genSizeOfSpec false
    |>.set `bootstrap.inductiveCheckResultingUniverse false
  withScope (fun sc => { sc with opts }) do
    elabCommand cmd
  let env' ← getEnv
  setEnv env
  -- The elaborator may have split a mutual block; it is sent to the kernel as one block here
  let types ← names.toList.mapM fun n => do
    let some (.inductInfo w) := env'.find? n | throwError "missing inductive {n}"
    let ctors ← w.ctors.mapM fun c => do
      let some (.ctorInfo cv) := env'.find? c | throwError "missing constructor {c}"
      pure ({ name := c, type := cv.type } : Constructor)
    pure ({ name := n, type := w.type, ctors, isImpredicative := w.isImpredicative,
            isK := w.isK, hasProjections := w.hasProjections, hasEta := w.hasEta,
            hasLargeElim := w.hasLargeElim } : InductiveType)
  let some (.inductInfo v) := env'.find? names[0]! | unreachable!
  for n in names do
    let some (.inductInfo w) := env'.find? n | unreachable!
    unless w.levelParams == v.levelParams && w.numParams == v.numParams do
      throwError "the types of the block differ in their universe parameters or parameters"
  return { levelParams := v.levelParams, numParams := v.numParams, types }

def Lean.InductiveType.setFlags (t : InductiveType) (f : Flags) : InductiveType :=
  { t with isImpredicative := f.isImpredicative, isK := f.isK, hasProjections := f.hasProjections,
           hasEta := f.hasEta, hasLargeElim := f.hasLargeElim }

def Block.toDecl (b : Block) (flags : Name → Flags) : Declaration :=
  .inductDecl b.levelParams b.numParams (b.types.map fun t => t.setFlags (flags t.name)) false

/-- Replaces the result sort `Sort l` of `∀ ..., Sort l` by `Sort (max 1 l)`. -/
partial def liftResultSort : Expr → Expr
  | .forallE n d b bi => .forallE n d (liftResultSort b) bi
  | .sort l => .sort (mkLevelMax' (mkLevelSucc .zero) l).normalize
  | e => e

/--
Elaborates the flags of a test: either `{ ... } : Flags`, used for all types of the block, or a
list `[(`A, { ... }), ...]` for each type (types not listed get all flags off).
-/
def elabFlags (stx : Term) : TermElabM (Name → Flags) := do
  if stx.raw.isOfKind `«term[_]» then
    let ty := mkApp (mkConst ``List [0]) <|
      mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Name) (mkConst ``Flags)
    let e ← elabTermEnsuringType stx ty
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let l ← unsafe Meta.evalExpr (List (Name × Flags)) ty e
    return fun n => (l.lookup n).getD {}
  else
    let e ← elabTermEnsuringType stx (mkConst ``Flags)
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let f ← unsafe Meta.evalExpr Flags (mkConst ``Flags) e
    return fun _ => f

def flagsOf (d : Declaration) (n : Name) : Option InductiveType :=
  match d with
  | .inductDecl _ _ ts _ => ts.find? (·.name == n)
  | _ => none

/--
The constants that a kernel lacking the check that rejects `bad` would produce: those the kernel
produces for `wellFormed` (which has the same names and constructors), with the types and flags of
the inductive types taken from `bad`, and the recursors' `k` from the flags of `bad`.
-/
def badInductiveConsts (bad wellFormed : Declaration) : CoreM (Array ConstantInfo) := do
  let env ← getEnv
  try
    addDecl wellFormed
    let env' ← getEnv
    let added := env'.constants.map₂.toArray.filter (!env.contains ·.1)
    let added := added.map fun (n, ci) => (n, dropSmallRecRules env' ci)
    let firstIsK := match bad with
      | .inductDecl _ _ (t :: _) _ => t.isK
      | _ => false
    return added.map fun (_, ci) => match ci with
      | .inductInfo v =>
        match flagsOf bad v.name with
        | some t => .inductInfo { v with
            type := t.type, isImpredicative := t.isImpredicative, isK := t.isK,
            hasProjections := t.hasProjections, hasEta := t.hasEta, hasLargeElim := t.hasLargeElim }
        | none => ci
      | .recInfo v => .recInfo { v with k := firstIsK }
      | ci => ci
  finally
    setEnv env

syntax (name := goodInductive) (plainDocComment)? "good_inductive " term " in " command : command

syntax (name := badInductive) (plainDocComment)? "bad_inductive " term
  (" via " term)? (" lifted")? (" patch " term)? " in " command : command

@[command_elab goodInductive]
def elabGoodInductive : CommandElab := fun stx => do
  let descr? : Option (TSyntax ``plainDocComment) :=
    if stx[0].isNone then none else some ⟨stx[0][0]⟩
  let block ← scratchElabInductive stx[4]
  liftTermElabM do
    let flags ← elabFlags ⟨stx[2]⟩
    let decl := block.toDecl flags
    addDecl decl
    fixupRecRules (block.types.map (·.name))
    registerTestCase {
      decls := (block.types.map (·.name)).toArray
      outcome := .good
      description := ← getDescr descr?
    }

/--
`bad_inductive flags via wfFlags lifted patch f in cmd`: the inductive block `cmd`, with the given
flags, which the kernel rejects. The constants of the test are produced from the block with
`wfFlags` instead (which the kernel accepts), see `badInductiveConsts`; with `lifted`, the result
sort of the latter is raised to `Sort (max 1 l)`, so that it may have large elimination. Finally,
`patch : ConstantInfo → ConstantInfo` is applied to all constants, if given; the declaration itself
is then not required to be rejected by the kernel.
-/
@[command_elab badInductive]
def elabBadInductive : CommandElab := fun stx => do
  let descr? : Option (TSyntax ``plainDocComment) :=
    if stx[0].isNone then none else some ⟨stx[0][0]⟩
  let block ← scratchElabInductive stx[7]
  liftTermElabM do
    let flags ← elabFlags ⟨stx[2]⟩
    let wfFlags ← if stx[3].isNone then pure flags else elabFlags ⟨stx[3][1]⟩
    let doLift := !stx[4].isNone
    let decl := block.toDecl flags
    let wfBlock := if doLift then
        { block with types := block.types.map fun t => { t with type := liftResultSort t.type } }
      else block
    let wellFormed := wfBlock.toDecl wfFlags
    let mut cis ← badInductiveConsts decl wellFormed
    if stx[5].isNone then
      assertKernelRejects decl
    else
      let ty := Expr.forallE `ci (mkConst ``ConstantInfo) (mkConst ``ConstantInfo) .default
      let e ← elabTermEnsuringType (⟨stx[5][1]⟩ : Term) ty
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let f ← unsafe Meta.evalExpr (ConstantInfo → ConstantInfo) ty e
      cis := cis.map f
    addConstInfos cis
    registerTestCase {
      decls := (block.types.map (·.name)).toArray
      outcome := .bad
      description := ← getDescr descr?
    }

/-! Helpers for patches -/

def ConstantInfo.mapInduct (f : InductiveVal → InductiveVal) : ConstantInfo → ConstantInfo
  | .inductInfo v => .inductInfo (f v)
  | ci => ci

def ConstantInfo.mapRec (f : RecursorVal → RecursorVal) : ConstantInfo → ConstantInfo
  | .recInfo v => .recInfo (f v)
  | ci => ci

/--
Turns a recursor with large elimination into one that eliminates only into `Prop`, by setting its
motive's universe parameter (the first one) to zero. It keeps its reduction rules.
-/
def RecursorVal.motiveToProp (v : RecursorVal) : RecursorVal :=
  match v.levelParams with
  | u :: us =>
    let inst (e : Expr) := e.instantiateLevelParams [u] [.zero]
    { v with levelParams := us, type := inst v.type,
             rules := v.rules.map fun r => { r with rhs := inst r.rhs } }
  | [] => v
