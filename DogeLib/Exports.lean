module

public import DogeLib.Exports.Main
public import DogeLib.Serialization.Exports
public import DogeLib.Transaction.Exports

/-!
# `DogeLib.Exports`

Root of the `Exports` Lake library: the oracle, `dogelib-oracle`, and the operations of each layer.
Its imports include the entry point, so that `lake exe check-decls` checks every module of the library.
-/
