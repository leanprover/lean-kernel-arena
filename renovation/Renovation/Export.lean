import LeanExport.Basic
open Lean LeanExport
open Std (HashMap)

/-!
Exports test cases with the exporter that ships with the Lean toolchain of lean4#16595, which
writes the per-inductive feature flags.
-/

/--
The metadata line. The toolchain still writes format version `3.1.0`, but the new flags on
inductive types make this format `3.2.0`, as proposed for lean4#16595.
-/
def renovationMetadata : Json :=
  Json.mkObj [
    ("meta", Json.mkObj [
      ("exporter", Json.mkObj [("name", "lean4export"), ("version", "3.2.0")]),
      ("lean", Json.mkObj [("version", versionString), ("githash", githash)]),
      ("format", Json.mkObj [("version", "3.2.0")])
    ])
  ]

/-- Like `M.run`, but with HashMap capacities suitable for small exports. -/
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
Exports `constants` from `env`. It exports them from its kernel environment, which also has the
constants that were put into the environment bypassing the kernel (see `insertConstInfo`), and
there they replace the constants of the same name that the kernel added.
-/
def exportDeclsFromEnv (env : Lean.Environment) (constants : Array Name) : IO Unit := do
  let env := Environment.ofKernelEnv env.toKernelEnv
  M.runSmall env do
    initState env ["--export-unsafe"]
    IO.println renovationMetadata.compress
    for c in constants do
      modify (fun st => { st with noMDataExprs := {} })
      dumpConstant c
