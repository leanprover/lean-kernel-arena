import Lean
import Tutorial.Export

open Lean

inductive Outcome where | good | bad

structure TestCase where
  decls : Array Name
  outcome : Outcome
  description : Option String
  renamings : NameMap Name := {}

initialize testCaseCounter : EnvExtension Nat ←
  registerEnvExtension (pure 1) (asyncMode := .sync)

def bumpTestCaseCounter [Monad m] [MonadEnv m] : m Nat := do
  let n := testCaseCounter.getState (← getEnv)
  setEnv <| testCaseCounter.setState (← getEnv) (n + 1)
  pure n

section CopiedFromLean4Export

end CopiedFromLean4Export

def registerTestCase (testCase : TestCase) : CoreM Unit := do
  let n ← bumpTestCaseCounter
  let some outdir ← IO.getEnv "OUT" | return ()
  let outdir := System.FilePath.mk outdir
  let nStr :=
    let s := toString n
    let zeros : String := String.ofList (List.replicate (3 - s.length) '0')
    zeros ++ s
  let lastName := testCase.decls.back!
  let displayName := match testCase.renamings.find? lastName with
    | some target => target
    | none => lastName
  let testname := s!"{nStr}_{displayName.toString}"
  let subdir := match testCase.outcome with
    | Outcome.good => "good"
    | Outcome.bad  => "bad"
  IO.FS.createDirAll (outdir / subdir)
  let filename := (outdir / subdir / testname).addExtension "ndjson"
  let infofilename := (outdir / subdir / testname).addExtension "info.json"
  IO.println s!"Writing {filename}"
  let h ← IO.FS.Handle.mk filename .write
  let stream := IO.FS.Stream.ofHandle h
  IO.withStdout stream do
    exportDeclsFromEnv (← getEnv) testCase.decls testCase.renamings
  if let some descr := testCase.description then
    IO.FS.writeFile infofilename <| Json.pretty <| .mkObj [ ("description", .str descr) ]
