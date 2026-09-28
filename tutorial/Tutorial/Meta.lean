import Lean
import Tutorial.TestCaseEnv
import Tutorial.AddConstInfo

open Lean Elab Term Command
open Lean.Parser.Command

def addTestCaseDeclCore (descr? : Option String) (decl : Lean.Declaration) (outcome : Outcome) (unchecked := false) : CoreM Unit := do
  match unchecked, outcome with
  | false, .good => addDecl decl
  | _, _ =>
    withOptions (fun o => debug.skipKernelTC.set o true) do
      addDecl decl
  registerTestCase {
    decls := decl.getNames.toArray
    outcome := outcome
    description := descr?
  }

def addTestCaseDecl (descr? : Option String) (declName : Name) (levelParams : List Name) (typeExpr : Expr) (valueExpr : Expr) (outcome : Outcome) (declKind : ConstantKind) (unchecked := false) : CoreM Unit := do
  let decl ← match declKind with
    | .defn => pure <| .defnDecl {
        name := declName
        levelParams := levelParams
        type := typeExpr
        value := valueExpr
        hints := .opaque
        safety := .safe
      }
    | .thm => pure <| .thmDecl {
        name := declName
        levelParams := levelParams
        type := typeExpr
        value := valueExpr
      }
    | _ => throwError "Unsupported declaration kind in test case: {repr declKind}"
  addTestCaseDeclCore descr? decl outcome (unchecked := unchecked)

open TSyntax.Compat in -- due to plainDocComments vs. docComment
def elabAndAddTestCaseDecl (descr? : Option (TSyntax ``plainDocComment)) (name : TSyntax ``declId) (type : Term) (value : Term) (outcome : Outcome) (declKind : ConstantKind) (unchecked := false) : CommandElabM Unit := liftTermElabM do
  let descrStr? ← descr?.mapM (getDocStringText ·)
  let descrStr? := descrStr?.map (·.trimAscii.copy)
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
    addTestCaseDecl descrStr? declName lparams typeExpr valueExpr outcome declKind (unchecked := unchecked)

elab descr?:(plainDocComment)? "good_def " name:declId ":" type:term ":=" value:term : command => do
  elabAndAddTestCaseDecl descr? name type value Outcome.good ConstantKind.defn

elab descr?:(plainDocComment)? "good_unchecked_def " name:declId ":" type:term ":=" value:term : command => do
  elabAndAddTestCaseDecl descr? name type value Outcome.good ConstantKind.defn (unchecked := true)

elab descr?:(plainDocComment)? "bad_def " name:declId ":" type:term ":=" value:term : command => do
  elabAndAddTestCaseDecl descr? name type value Outcome.bad ConstantKind.defn

elab descr?:(plainDocComment)? "good_thm " name:declId ":" type:term ":=" value:term : command => do
  elabAndAddTestCaseDecl descr? name type value Outcome.good ConstantKind.thm

elab descr?:(plainDocComment)? "bad_thm " name:declId ":" type:term ":=" value:term : command => do
  elabAndAddTestCaseDecl descr? name type value Outcome.bad ConstantKind.thm

open TSyntax.Compat in -- due to plainDocComments vs. docComment
def elabRawTestDecl (descr? : Option (TSyntax `Lean.Parser.Command.plainDocComment)) (decl : Term) (outcome : Outcome) : CommandElabM Unit := liftTermElabM do
  let descrStr? ← descr?.mapM (getDocStringText ·)
  let descrStr? := descrStr?.map (·.trimAscii.copy)
  let expectedType := Lean.mkConst ``Lean.Declaration
  let declExpr ← elabTerm decl (some expectedType)
  Term.synthesizeSyntheticMVarsNoPostponing
  let declExpr ← instantiateMVars declExpr
  let decl ← Lean.Meta.MetaM.run' <| unsafe Meta.evalExpr (α := Lean.Declaration) expectedType declExpr
  addTestCaseDeclCore descrStr? decl outcome

elab descr?:(plainDocComment)? "good_decl " decl:term : command => do
  elabRawTestDecl descr? decl .good

elab descr?:(plainDocComment)? "bad_decl " decl:term : command => do
  elabRawTestDecl descr? decl .bad

def addTestCaseCIsCore (descr? : Option String) (cis : Array Lean.ConstantInfo) (outcome : Outcome)
    (renamings : NameMap Name := {}) : CoreM Unit := do
  addConstInfos cis
  registerTestCase {
    decls := cis.map (·.name)
    outcome := outcome
    description := descr?
    renamings
  }


open TSyntax.Compat in -- due to plainDocComments vs. docComment
def elabRawTestCIs (descr? : Option (TSyntax `Lean.Parser.Command.plainDocComment)) (cis : Term) (outcome : Outcome) : CommandElabM Unit := liftTermElabM do
  let descrStr? ← descr?.mapM (getDocStringText ·)
  let descrStr? := descrStr?.map (·.trimAscii.copy)
  let expectedType := mkApp (Lean.mkConst ``Array [0]) (Lean.mkConst ``Lean.ConstantInfo)
  let cisExpr ← elabTerm cis (some expectedType)
  let cisExpr ← instantiateMVars cisExpr
  synthesizeSyntheticMVarsNoPostponing
  let cis ← Lean.Meta.MetaM.run' <| unsafe Meta.evalExpr (α := Array Lean.ConstantInfo) expectedType cisExpr
  addTestCaseCIsCore descrStr? cis outcome

elab descr?:(plainDocComment)? "good_raw_consts " ci:term : command => do
  elabRawTestCIs descr? ci .good

elab descr?:(plainDocComment)? "bad_raw_consts " ci:term : command => do
  elabRawTestCIs descr? ci .bad

open TSyntax.Compat in -- due to plainDocComments vs. docComment
def elabRawTestConsts (descr? : Option (TSyntax `Lean.Parser.Command.plainDocComment)) (cis : Term)
    (outcome : Outcome) (renamingsTerm? : Option Term := none) : CommandElabM Unit := liftTermElabM do
  let descrStr? ← descr?.mapM (getDocStringText ·)
  let descrStr? := descrStr?.map (·.trimAscii.copy)
  let expectedType := mkApp (Lean.mkConst ``Array [0]) (Lean.mkConst ``Lean.Name)
  let namesExpr ← elabTerm cis (some expectedType)
  let namesExpr ← instantiateMVars namesExpr
  let names ← Lean.Meta.MetaM.run' <| unsafe Meta.evalExpr (α := Array Lean.Name) expectedType namesExpr
  let cis ← names.mapM Lean.getConstInfo
  let renamingsMap : NameMap Name ← match renamingsTerm? with
    | some renamingsTerm =>
      let nameType := Lean.mkConst ``Name
      let pairType := mkApp2 (Lean.mkConst ``Prod [0, 0]) nameType nameType
      let renamingsType := mkApp (Lean.mkConst ``Array [0]) pairType
      let renamingsExpr ← elabTerm renamingsTerm (some renamingsType)
      let renamingsExpr ← instantiateMVars renamingsExpr
      synthesizeSyntheticMVarsNoPostponing
      let renamingPairs ← Lean.Meta.MetaM.run' <|
        unsafe Meta.evalExpr (α := Array (Lean.Name × Lean.Name)) renamingsType renamingsExpr
      pure <| renamingPairs.foldl (fun m (k, v) => m.insert k v) ({} : NameMap Name)
    | none => pure {}
  addTestCaseCIsCore descrStr? cis outcome renamingsMap

syntax (name := goodConsts) (plainDocComment)? "good_consts " term (" renaming " term)? : command
syntax (name := badConsts) (plainDocComment)? "bad_consts " term (" renaming " term)? : command

private def elabConstsCmd (outcome : Outcome) : CommandElab := fun stx => do
  let descr? : Option (TSyntax `Lean.Parser.Command.plainDocComment) :=
    if stx[0].isNone then none else some ⟨stx[0][0]⟩
  let names : Term := ⟨stx[2]⟩
  let renamingsTerm? : Option Term :=
    if stx[3].isNone then none else some ⟨stx[3][1]⟩
  elabRawTestConsts descr? names outcome renamingsTerm?

@[command_elab goodConsts] def elabGoodConsts : CommandElab := elabConstsCmd .good
@[command_elab badConsts] def elabBadConsts : CommandElab := elabConstsCmd .bad

section Unchecked

/-- An elaborator that just inserts the term, without regard for the acutal type needed here -/
syntax (name := unchecked) "unchecked" term : term

section
open Lean Meta Elab Term


@[term_elab «unchecked»]
def elabUnchecked : TermElab := fun stx expectedType? => do
  match stx with
  | `(unchecked $t) =>
    let some expectedType := expectedType? |
      tryPostpone
      throwError "invalid 'unchecked', expected type required"
    let e ←  elabTerm t none
    let mvar ← mkFreshExprMVar expectedType MetavarKind.syntheticOpaque
    mvar.mvarId!.assign e
    return mvar
  | _ => throwUnsupportedSyntax

end

end Unchecked

/-! Some expression builder helpers -/

def arrow  (dom : Expr) (codom : Expr) (n := `x) : Expr :=
  Lean.mkForall n BinderInfo.default dom codom

def dummyRecInfo (indName : Lean.Name) : Lean.ConstantInfo :=
  .recInfo {
      name := indName ++ `rec
      levelParams := []
      type := .sort 0
      all := [indName]
      numParams := 0
      numIndices := 0
      numMotives := 0
      numMinors := 0
      rules := []
      k := false
      isUnsafe := false
  }

/-! Inductive types that the kernel rejects -/

/--
Computes the constants of an inductive declaration that the kernel rejects.

The kernel does all the work of generating the types, constructors and recursors (including the
auxiliary recursors of nested inductives), but it is handed `wellFormed`, a variant of the
declaration that it accepts, in a scratch environment. `patch` then turns each of the resulting
constants into its counterpart for the rejected declaration.

This produces what a kernel lacking the check that rejects the declaration would have produced.
-/
def patchedInductive (wellFormed : Declaration) (patch : ConstantInfo → ConstantInfo) :
    CoreM (Array ConstantInfo) := do
  let env ← getEnv
  try
    addDecl wellFormed
    -- Everything the kernel added: whatever the names of the auxiliary recursors are
    let added := (← getEnv).constants.map₂.toArray.filter (!env.contains ·.1)
    return added.map (patch ·.2)
  finally
    setEnv env

/-- Adds the constants of an inductive declaration that the kernel rejects; see `patchedInductive`. -/
def addPatchedInductive (wellFormed : Declaration) (patch : ConstantInfo → ConstantInfo) :
    CoreM Unit := do
  addConstInfos (← patchedInductive wellFormed patch)
