import Export.Parse
import Lean

def sameKind : Lean.QuotKind → Lean.QuotKind → Bool
  | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
  | _, _ => false

def runKernel (solution : Export.ExportedEnv) : IO Unit := do
  let env ← Lean.mkEmptyEnvironment
  let mut constMap := solution.constMap
  -- Lean's kernel interprets just the addition of `Quot as adding all of these so adding them
  -- multiple times leads to errors.
  constMap := constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  let kenv ← env.toKernelEnv.replay constMap
  -- The names erased above must still be the quotient constants the kernel installed;
  -- otherwise an ordinary declaration wearing one of these names would go unchecked.
  for n in [`Quot, `Quot.mk, `Quot.lift, `Quot.ind] do
    if let some exported := solution.constMap[n]? then
      let ok := match exported, kenv.find? n with
        | .quotInfo e, some (.quotInfo k) =>
          sameKind e.kind k.kind && e.levelParams == k.levelParams && e.type == k.type
        | _, _ => false
      unless ok do
        throw <| IO.userError s!"Quotient constant mismatch on: {n}"
  IO.println s!"Accepted {constMap.size} declarations."


def main (args : List String) : IO Unit := do
  let (inputPath, parseOnly) ← match args with
    | ["--parse-only", inputPath] => pure (inputPath, true)
    | [inputPath] => pure (inputPath, false)
    | _ => throw <| .userError "Expected input file path as first argument, optionally followed by --parse-only."
  let handle ← IO.FS.Handle.mk inputPath .read
  let env ← Export.parseStream (.ofHandle handle)
  if parseOnly then
    IO.println "Parse successful."
  else
    runKernel env
