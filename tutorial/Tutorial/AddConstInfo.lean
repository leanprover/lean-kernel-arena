module
public import Lean.Environment
import all Lean.Environment

open Lean

/--
This is a hack to insert ConstInfos directly, bypassing the kernel completely.

The `key` can differ from `ci.name`, which is how the exporter can be made to export two
declarations that share a name: it prints the name of the constant, but looks it up by the key.

NB: The option `set_option debug.skipKernelTC true` does not apply when adding inductives, so if we
want to get bad inductives into the environment, we have to use this.
-/
public def insertConstInfo (env : Environment) (ci : Lean.ConstantInfo) (key : Name := ci.name) :
    Environment :=
  { env with
    base.public.constants.map₁ := env.base.public.constants.map₁.insert key ci
    base.private.constants.map₁ := env.base.private.constants.map₁.insert key ci
    checked := env.checked.map (fun e => { e with constants := e.constants.insert key ci })
  }

public def addConstInfos [Monad m] [MonadEnv m] (cis : Array Lean.ConstantInfo) : m Unit := do
  for ci in cis do
    modifyEnv (insertConstInfo · ci)
