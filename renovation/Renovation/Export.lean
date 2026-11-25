import LeanExport.Basic
import Renovation.AddConstInfo
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
The constants that exporting `roots` from `env` writes out: their dependencies, and with an
inductive type its whole block, constructors and recursors, and with a quotient the whole `Quot`
package.
-/
partial def exportClosure (env : Kernel.Environment) (roots : Array Name) :
    PersistentHashMap Name ConstantInfo := Id.run do
  let mut todo := roots.toList
  let mut acc : PersistentHashMap Name ConstantInfo := {}
  while true do
    let n :: rest := todo | break
    todo := rest
    if acc.contains n then continue
    let some ci := env.find? n | continue
    acc := acc.insert n ci
    let exprs := #[ci.type] ++ (ci.value? (allowOpaque := true)).toArray ++
      (match ci with | .recInfo v => v.rules.toArray.map (·.rhs) | _ => #[])
    for e in exprs do
      todo := e.getUsedConstants.toList ++ todo
    match ci with
    | .inductInfo v =>
      todo := v.all ++ v.ctors ++ todo
      -- The recursors, including those of the auxiliary types of nested inductives
      for t in v.all do
        todo := (t ++ `rec) :: todo
        let mut i := 1
        while (env.find? (t ++ Name.mkSimple s!"rec_{i}")).isSome do
          todo := (t ++ Name.mkSimple s!"rec_{i}") :: todo
          i := i + 1
    | .ctorInfo v => todo := v.induct :: todo
    | .recInfo v => todo := v.all ++ todo
    | .quotInfo _ => todo := [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind, ``Eq] ++ todo
    | _ => pure ()
  return acc

/--
Exports `constants` from `env`. It exports them from its kernel environment, which also has the
constants that were put into the environment bypassing the kernel (see `insertConstInfo`), and
there they replace the constants of the same name that the kernel added, even imported ones like
`Quot`. As the exporter would look up imported constants among the imported ones, it is given an
environment with just the constants it writes out.
-/
def exportDeclsFromEnv (env : Lean.Environment) (constants : Array Name) : IO Unit := do
  let kenv := env.toKernelEnv
  let env := Environment.ofKernelEnv (kenv.withConsts (exportClosure kenv constants))
  M.runSmall env do
    initState env ["--export-unsafe"]
    IO.println renovationMetadata.compress
    for c in constants do
      modify (fun st => { st with noMDataExprs := {} })
      dumpConstant c
