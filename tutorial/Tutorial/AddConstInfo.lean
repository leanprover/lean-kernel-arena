module
public import Lean.Environment
import all Lean.Environment

open Lean

/--
This is a hack to insert ConstInfos directly, bypassing the kernel completely.

NB: The option `set_option debug.skipKernelTC true` does not apply when adding inductives, so if we
want to get bad inductives into the environment, we have to use this.
-/
public def addConstInfos [Monad m] [MonadEnv m]  (cis : Array Lean.ConstantInfo) : m Unit := do
  for ci in cis do
    modifyEnv (fun env => { env with
      base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
      base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
      checked := env.checked.map (fun e => { e with constants := e.constants.insert ci.name ci })
    })
