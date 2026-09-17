import Export
import Tutorial.AddConstInfo
open Lean
open Std (HashMap)

initialize importedRecursorMap : IO.Ref (NameMap NameSet) ← do
  IO.mkRef {}

def addRecInfo (constInfo : ConstantInfo) (recursorMap : NameMap NameSet) : NameMap NameSet :=
  if let .recInfo recVal := constInfo then
    recVal.all.foldl (init := recursorMap) fun recursorMap indName =>
      recursorMap.alter indName <|
        fun
        | none => some <| NameSet.empty.insert recVal.name
        | some recNames => some <| recNames.insert recVal.name
  else
    recursorMap

/--
Like initstate, but assumes that the imported entries in `env` are
always the same and cache them
-/
def initStateCached (env : Environment) (cliOptions : List String := []) : M Unit := do
  let mut recursorMap : NameMap NameSet := (← importedRecursorMap.get)
  if recursorMap.isEmpty then
    for (_, constInfo) in env.constants.map₁ do
      recursorMap := addRecInfo constInfo recursorMap
    importedRecursorMap.set recursorMap
  for (_, constInfo) in env.constants.map₂ do
    recursorMap := addRecInfo constInfo recursorMap
  modify fun st => { st with
    exportMData  := cliOptions.any  (· == "--export-mdata")
    exportUnsafe := cliOptions.any (· == "--export-unsafe")
    recursorMap
  }

/-- Like `M.run`, but with smaller HashMap capacities suitable for small exports.
The defaults in `State` are tuned for full Mathlib export (10M expressions etc.)
and are wasteful when called repeatedly for small test cases. -/
def M.runSmall (env : Environment) (act : M α) : IO α :=
  StateT.run' (s := {
    visitedExprs := HashMap.emptyWithCapacity 1024
    visitedNames := HashMap.emptyWithCapacity 256 |>.insert .anonymous 0
    visitedLevels := HashMap.emptyWithCapacity 64 |>.insert .zero 0
    noMDataExprs := HashMap.emptyWithCapacity 256
  }) do
    ReaderT.run (r := { env }) do
      act

/--
Renames a name according to `renamings`, also renaming prefixes, so that renaming `Foo` to `Bar`
also renames `Foo.rec` to `Bar.rec`. Not applied recursively to its own result.
-/
partial def renameName (renamings : NameMap Name) (n : Name) : Name :=
  if let some target := renamings.find? n then
    target
  else
    match n with
    | .anonymous => .anonymous
    | .str pre s => .str (renameName renamings pre) s
    | .num pre i => .num (renameName renamings pre) i

/-- Applies `renameName` to all constants (and projected structures) occurring in `e`. -/
partial def renameConsts (renamings : NameMap Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us =>
      let n' := renameName renamings n
      if n' == n then none else some (.const n' us)
    | .proj s i b =>
      let s' := renameName renamings s
      if s' == s then none else some (.proj s' i (renameConsts renamings b))
    | _ => none

/-- Renames a constant info: its own name, and everything it refers to. -/
def renameConstInfo (renamings : NameMap Name) (ci : ConstantInfo) : ConstantInfo :=
  let rn := renameName renamings
  let re := renameConsts renamings
  match ci with
  | .axiomInfo v => .axiomInfo { v with name := rn v.name, type := re v.type }
  | .quotInfo v => .quotInfo { v with name := rn v.name, type := re v.type }
  | .defnInfo v => .defnInfo
      { v with name := rn v.name, type := re v.type, value := re v.value, all := v.all.map rn }
  | .thmInfo v => .thmInfo
      { v with name := rn v.name, type := re v.type, value := re v.value, all := v.all.map rn }
  | .opaqueInfo v => .opaqueInfo
      { v with name := rn v.name, type := re v.type, value := re v.value, all := v.all.map rn }
  | .inductInfo v => .inductInfo
      { v with name := rn v.name, type := re v.type, all := v.all.map rn, ctors := v.ctors.map rn }
  | .ctorInfo v => .ctorInfo
      { v with name := rn v.name, type := re v.type, induct := rn v.induct }
  | .recInfo v =>
    let rules := v.rules.map (fun r => { r with ctor := rn r.ctor, rhs := re r.rhs })
    .recInfo { v with name := rn v.name, type := re v.type, all := v.all.map rn, rules }

/-- The constants that `dumpConstant n` visits, following the same traversal as the exporter. -/
partial def collectDumped (env : Environment) (recursorMap : NameMap NameSet) (n : Name)
    (acc : NameSet) : NameSet :=
  if acc.contains n then acc else
  match env.find? n with
  | none => acc
  | some ci =>
    let go (acc : NameSet) (ns : List Name) : NameSet :=
      ns.foldl (fun acc n => collectDumped env recursorMap n acc) acc
    let exprs := #[ci.type] ++ ci.value?.toArray ++
      (match ci with | .recInfo v => v.rules.toArray.map (·.rhs) | _ => #[])
    let acc := exprs.foldl (fun acc e => go acc e.getUsedConstants.toList) (acc.insert n)
    match ci with
    | .inductInfo v =>
      go (go acc (v.all ++ v.ctors)) ((recursorMap.find? v.name).getD {}).toList
    | .ctorInfo v => go acc [v.induct]
    | .recInfo v => go acc v.all
    | _ => acc

/--
Exports `constants`, renamed according to `renamings`.

The renaming is applied to the declarations themselves, so that the exporter never sees the old
names and the export stays canonical: every name and expression is printed exactly once, with
consecutive indices, even where two declarations end up sharing a name.

Since an environment maps a name to a single constant, such a pair of namesakes is put in the
environment under two different keys: the exporter prints the name of the constant it finds, but
looks constants up by the key we give it (`recursorMap` and the `dumpConstant` calls below).
Inductive types and constructors are the exception, as the exporter both looks up and prints the
names in the `all` and `ctors` fields, so they have to keep their new name as their key.
-/
def exportDeclsFromEnv (env : Lean.Environment) (constants : Array Name)
    (renamings : NameMap Name := {}) : IO Unit := do
  M.runSmall env do
    initStateCached env ["--export-unsafe"]
    dumpMetadata
    if renamings.isEmpty then
      for c in constants do
        modify (fun st => { st with noMDataExprs := {} })
        let _ ← dumpConstant c
    else
      let recursorMap := (← get).recursorMap
      let dumped := constants.foldl (init := ({} : NameSet)) fun acc c =>
        collectDumped env recursorMap c acc
      -- Rename the constants that are going to be dumped, inductive types and constructors first,
      -- as those have to keep their new name as their key
      let mut renamed := #[]
      for n in dumped do
        if let some ci := env.find? n then
          renamed := renamed.push (n, renameConstInfo renamings ci)
      let isType : ConstantInfo → Bool
        | .inductInfo _ | .ctorInfo _ => true
        | _ => false
      let ordered := renamed.filter (isType ·.2) ++ renamed.filter (!isType ·.2)
      -- Put them into the environment, under their new name if that is still free
      let mut renamedEnv := env
      let mut keys : NameMap Name := {}
      let mut taken : NameSet := {}
      for (n, ci) in ordered do
        let mut key := ci.name
        while taken.contains key do
          key := `_namesake ++ key
        taken := taken.insert key
        keys := keys.insert n key
        renamedEnv := insertConstInfo renamedEnv ci key
      -- The exporter looks up the recursors of an inductive type by its new name
      for n in dumped do
        if let some recs := recursorMap.find? n then
          let recs := recs.foldl (init := ({} : NameSet)) fun recs r =>
            recs.insert (keys.getD r r)
          modify fun st => { st with
            recursorMap := st.recursorMap.insert (renameName renamings n) recs }
      withReader (fun ctx => { ctx with env := renamedEnv }) do
        for c in constants do
          modify (fun st => { st with noMDataExprs := {} })
          dumpConstant (keys.getD c c)
      -- Had a constant that the exporter visits been missed above, the export would still refer to
      -- the old name
      for (key, _) in renamings do
        if (← get).visitedNames.contains key then
          panic! s!"the export refers to {key}, which should have been renamed"
