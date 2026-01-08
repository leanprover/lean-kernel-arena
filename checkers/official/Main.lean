import Export.Parse
import Lean4Checker.Replay
import Lean

def runKernel (solution : Export.ExportedEnv) : IO Unit := do
  let mut env ← Lean.mkEmptyEnvironment
  let mut constMap := solution.constMap
  -- Lean's kernel interprets just the addition of `Quot as adding all of these so adding them
  -- multiple times leads to errors.
  constMap := constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| env.replay' constMap
  IO.println s!"Accepted {constMap.size} declarations."


def main (args : List String) : IO Unit := do
  let (inputPath, parseOnly) ← match args with
    | ["--parse-only", inputPath] => pure (inputPath, true)
    | [inputPath] => pure (inputPath, false)
    | _ => throw <| .userError "Expected input file path as first argument, optionally followed by --parse-only."
  let content ← IO.FS.readFile inputPath
  let env ← .ofExcept (Export.parse content)
  if parseOnly then
    IO.println "Parse successful."
  else
    runKernel env
