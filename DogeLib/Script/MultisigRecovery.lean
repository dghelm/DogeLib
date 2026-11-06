module

public import DogeLib.Script.Verify

/-!
# `Script.MultisigRecovery`

The worked property target of design record 0003, section 7: a multisig redeem script with a time-locked recovery key.

```text
OP_IF
  OP_k <P1> ... <Pn> OP_n OP_CHECKMULTISIG
OP_ELSE
  <1000000> OP_CHECKLOCKTIMEVERIFY OP_DROP <R> OP_CHECKSIG
OP_ENDIF
```

`multisigRecoveryScript k keys R` builds these bytes for `1 ≤ k ≤ n ≤ 16`, where `n` is the number of keys.
Each key push is `CScript() << vch` (`pushEncoding`), so a 33-byte key is the byte `0x21` and the key.
The lock-time operand 1,000,000 is the push `03 40 42 0f`: three bytes of the positive sign-magnitude integer `0x0f4240`, as `CScriptNum::serialize` writes it (D24).
Section 7 uses 2-of-3. The locktime 1,000,000 is illustrative, not a deployment height or an activation claim.

`DogeLib.Script.Proofs.MultisigRecovery` defines the two branch predicates of section 7 and proves the equivalence.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/-- `OP_1` to `OP_16` for `1 ≤ k ≤ 16`: the byte `0x50 + k` (D24). -/
def smallIntOpcode (k : Nat) : UInt8 := (0x50 + k).toUInt8

/-- The push `03 40 42 0f` of the lock-time operand 1,000,000: a positive three-byte script number. -/
def recoveryLockTimePush : List UInt8 := [0x03, 0x40, 0x42, 0x0f]

/-- The lock-time operand of the template. -/
def recoveryLockTime : Nat := 1000000

/--
The redeem script of section 7 for `k` of the keys `keys` and the recovery key `recovery`:
`OP_IF OP_k <keys> OP_n OP_CHECKMULTISIG OP_ELSE <1000000> OP_CHECKLOCKTIMEVERIFY OP_DROP <recovery> OP_CHECKSIG OP_ENDIF`.
It is meaningful for `1 ≤ k ≤ n ≤ 16`, where `n` is the number of keys.
-/
def multisigRecoveryScript (k : Nat) (keys : List (List UInt8)) (recovery : List UInt8) : List UInt8 :=
  [0x63, smallIntOpcode k] ++ (keys.map pushEncoding).flatten ++ [smallIntOpcode keys.length, 0xae, 0x67] ++
    recoveryLockTimePush ++ [0xb1, 0x75] ++ pushEncoding recovery ++ [0xac, 0x68]

/-- The P2SH output script that commits to `redeem`: `OP_HASH160 <HASH160 redeem> OP_EQUAL`. -/
def p2shScriptPubKey (redeem : List UInt8) : List UInt8 :=
  [0xa9, 0x14] ++ (Cryptography.Hash.hash160 ⟨redeem.toArray⟩).toList ++ [0x87]

end DogeLib.Script
