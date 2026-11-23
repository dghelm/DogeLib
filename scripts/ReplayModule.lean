import LeanChecker

/-!
Replay the declarations of one module into Lean's kernel, for `scripts/replay.sh`.

The module is the value of the environment variable `REPLAY_MODULE`.
leanchecker replays every module whose name starts with its argument, in one process.
This script calls the replay function of leanchecker, `replayFromImports` of Lean v4.35.0, on the named module alone.
It fails with the error of the kernel when a declaration does not replay.

Adapted from EthLib, `scripts/ReplayModule.lean` at commit `b4070a856`, dedicated to the public domain under CC0 1.0.
The changes are the toolchain version in this comment and the attribution.
-/

#eval show IO Unit from do
  let some name ← IO.getEnv "REPLAY_MODULE" | throw <| IO.userError "REPLAY_MODULE is not set"
  unsafe replayFromImports name.toName
