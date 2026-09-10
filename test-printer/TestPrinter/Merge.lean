import Lean.Data.Json.Parser
import TestPrinter.Types
import Std.Data.HashMap

namespace TestPrinter

def discoverTestFiles (dir : System.FilePath) : IO (Array TestFile) := do
  let mut files : Array TestFile := #[]
  for (subdirName, isGood) in #[("good", true), ("bad", false)] do
    let subdirPath := dir / subdirName
    let dirExists ← subdirPath.pathExists
    unless dirExists do continue
    let entries ← subdirPath.readDir
    let mut ndjsonPaths : Array System.FilePath := #[]
    for entry in entries do
      if entry.fileName.endsWith ".ndjson" then
        ndjsonPaths := ndjsonPaths.push entry.path
    let sortedPaths := ndjsonPaths.qsort (fun a b => a.toString < b.toString)
    for ndjsonPath in sortedPaths do
      let fname := ndjsonPath.fileName.getD ""
      let baseName := if fname.endsWith ".ndjson" then (fname.dropEnd 7).toString else fname
      let parentDir := ndjsonPath.parent.getD dir
      let infoPath := parentDir / (baseName ++ ".info.json")
      let statsPath := parentDir / (baseName ++ ".stats.json")
      files := files.push { ndjsonPath, infoPath, statsPath, baseName, isGood }
  let sortedFiles := files.qsort (fun a b => a.baseName < b.baseName)
  return sortedFiles

def parseJsonFile (path : System.FilePath) : IO Lean.Json := do
  let content ← IO.FS.readFile path
  match Lean.Json.parse content with
  | .ok json => return json
  | .error msg => throw (IO.userError s!"Failed to parse JSON file {path}: {msg}")

def parseTestFile (tf : TestFile) : IO ParsedTest := do
  let infoJson ← parseJsonFile tf.infoPath
  let info ←
    match (Lean.FromJson.fromJson? infoJson : Except String TestInfo) with
    | .ok v => pure v
    | .error msg => throw (IO.userError s!"Failed to parse {tf.infoPath}: {msg}")
  let statsJson ← parseJsonFile tf.statsPath
  let stats ←
    match (Lean.FromJson.fromJson? statsJson : Except String TestStats) with
    | .ok v => pure v
    | .error msg => throw (IO.userError s!"Failed to parse {tf.statsPath}: {msg}")
  let handle ← IO.FS.Handle.mk tf.ndjsonPath .read
  let env ← TestPrinter.parseStream (.ofHandle handle)
  return { file := tf, info, stats, env }

def resolveTests (tests : Array ParsedTest) : Array ResolvedTest := Id.run do
  let mut globalSeen : Std.HashMap Lean.Name Unit := {}
  let mut result : Array ResolvedTest := #[]
  for test in tests do
    let mut newDecls : Array Lean.Name := #[]
    let mut sharedDecls : Array Lean.Name := #[]
    for name in test.env.constOrder do
      if globalSeen.contains name then
        sharedDecls := sharedDecls.push name
      else
        newDecls := newDecls.push name
        globalSeen := globalSeen.insert name ()
    result := result.push { parsed := test, newDecls, sharedDecls }
  return result

end TestPrinter
