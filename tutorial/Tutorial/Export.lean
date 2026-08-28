import Export
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

def exportDeclsFromEnv (env : Lean.Environment) (constants : Array Name)
    (renamings : NameMap Name := {}) : IO Unit := do
  M.runSmall env do
    initStateCached env ["--export-unsafe"]
    dumpMetadata
    -- First dump all names in the range of the renamings map
    for (_, target) in renamings.toList do
      let _ ← dumpName target
    -- Then extend visitedNames so that the keys point to the same index as their values
    for (key, target) in renamings.toList do
      let some idx := (← get).visitedNames[target]? | panic! s!"Name {target} not found in visitedNames"
      modify fun st => { st with visitedNames := st.visitedNames.insert key idx }
    for c in constants do
      modify (fun st => { st with noMDataExprs := {} })
      let _ ← dumpConstant c
