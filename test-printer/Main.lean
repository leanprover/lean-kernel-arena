import TestPrinter.Merge
import TestPrinter.PrettyPrint
import TestPrinter.AddConstInfo
import TestPrinter.Render

open Lean in
open TestPrinter in
private def isRecursor (env : ExportedEnv) (name : Lean.Name) : Bool :=
  match env.constMap[name]? with
  | some (.recInfo _) => true
  | _ => false

open TestPrinter in
def main (args : List String) : IO Unit := do
  let (ppAll, testDir, outputPath) ← match args with
    | ["--pp-all", dir, out] => pure (true, dir, out)
    | [dir, out] => pure (false, dir, out)
    | _ => throw (IO.userError "Usage: test-printer [--pp-all] <test-dir> <output-path>")

  IO.eprintln s!"Discovering test files in {testDir}..."
  let testFiles ← discoverTestFiles testDir
  IO.eprintln s!"Found {testFiles.size} test files."

  IO.eprintln "Parsing test files..."
  let mut parsedTests : Array ParsedTest := #[]
  for tf in testFiles do
    let parsed ← parseTestFile tf
    parsedTests := parsedTests.push parsed
    IO.eprintln s!"  Parsed {tf.baseName} ({parsed.env.constOrder.size} declarations)"

  IO.eprintln "Resolving shared declarations..."
  let resolvedTests := resolveTests parsedTests

  IO.eprintln "Building environment..."
  -- Collect all constants from all tests
  let mut allConstants : Array Lean.ConstantInfo := #[]
  for test in parsedTests do
    for (_, ci) in test.env.constMap do
      allConstants := allConstants.push ci
  -- Build a Lean Environment with all constants injected
  let env ← Lean.importModules #[] {}
  let coreCtx : Lean.Core.Context :=
    { fileName := "<kernel-export>", fileMap := default }
  let coreState : Lean.Core.State := { env }
  let (env, _) ← (do
    addConstInfos allConstants
    Lean.getEnv : Lean.CoreM _).toIO coreCtx coreState
  IO.eprintln s!"  {allConstants.size} constants loaded"

  IO.eprintln "Pretty-printing declarations..."
  let mut results : Array (ResolvedTest × Array PrettyDecl) := #[]
  for test in resolvedTests do
    let declsToPrint := if ppAll then test.parsed.env.constOrder else test.newDecls
    let mut decls : Array PrettyDecl := #[]
    for name in declsToPrint do
      match test.parsed.env.constMap[name]? with
      | some ci =>
        if let .recInfo _ := ci then pure ()
        else
          let (decl, _, _) ← (ppConstantInfo ci).toIO
            { fileName := "<kernel-export>", fileMap := default }
            { env }
          decls := decls.push decl
      | none => pure ()
    -- Also filter recursors from sharedDecls
    let filteredShared := test.sharedDecls.filter (fun n => !isRecursor test.parsed.env n)
    let filteredTest := { test with sharedDecls := filteredShared }
    results := results.push (filteredTest, decls)
    IO.eprintln s!"  {test.parsed.file.baseName}: {decls.size} declarations pretty-printed"

  IO.eprintln "Generating HTML..."
  let html := generatePage results
  if let some parent := (outputPath : System.FilePath).parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputPath html
  IO.eprintln s!"Written to {outputPath} ({html.length} bytes)"
