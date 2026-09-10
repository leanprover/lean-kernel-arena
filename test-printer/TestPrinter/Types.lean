import Lean.Data.Json
import SubVerso.Highlighting.Highlighted
import TestPrinter.NdjsonParser

namespace TestPrinter

open Lean

structure TestInfo where
  description : String
  deriving Inhabited

instance : FromJson TestInfo where
  fromJson? json := do
    let description ← json.getObjValAs? String "description"
    return { description }

structure TestStats where
  name : String
  outcome : String
  description : String
  sourceUrl : String
  deriving Inhabited

instance : FromJson TestStats where
  fromJson? json := do
    let name ← json.getObjValAs? String "name"
    let outcome ← json.getObjValAs? String "outcome"
    let description ← json.getObjValAs? String "description"
    let sourceUrl := (json.getObjValAs? String "source_url").toOption.getD ""
    return { name, outcome, description, sourceUrl }

structure TestFile where
  ndjsonPath : System.FilePath
  infoPath : System.FilePath
  statsPath : System.FilePath
  baseName : String
  isGood : Bool
  deriving Inhabited

structure ParsedTest where
  file : TestFile
  info : TestInfo
  stats : TestStats
  env : ExportedEnv
  deriving Inhabited

structure ResolvedTest where
  parsed : ParsedTest
  newDecls : Array Lean.Name
  sharedDecls : Array Lean.Name
  deriving Inhabited

structure PrettyDecl where
  kind : String
  name : Lean.Name
  levelParams : List Lean.Name
  paramsPP : Option SubVerso.Highlighting.Highlighted := none
  /-- Highlighted " : type" with a soft line break after the colon;
      the pretty printer decides whether to break based on the layout. -/
  colonTypePP : SubVerso.Highlighting.Highlighted
  valuePP : Option SubVerso.Highlighting.Highlighted
  deriving Inhabited

end TestPrinter
