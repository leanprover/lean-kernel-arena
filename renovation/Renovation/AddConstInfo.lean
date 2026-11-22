module
public import Lean.Environment
import all Lean.Environment

open Lean

/--
This is a hack to insert ConstInfos directly, bypassing the kernel completely.

NB: The option `set_option debug.skipKernelTC true` does not apply when adding inductives, so if we
want to get bad inductives into the environment, we have to use this.
-/
public def insertConstInfo (env : Environment) (ci : Lean.ConstantInfo) : Environment :=
  { env with
    base.public.constants := env.base.public.constants.insert ci.name ci
    base.private.constants := env.base.private.constants.insert ci.name ci
    checked := env.checked.map (fun e => { e with constants := e.constants.insert ci.name ci })
  }

public def addConstInfos [Monad m] [MonadEnv m] (cis : Array Lean.ConstantInfo) : m Unit := do
  for ci in cis do
    modifyEnv (insertConstInfo · ci)
