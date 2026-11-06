module

public import DogeLib.Script.SignatureEncoding
public import DogeLib.Transaction.LegacySighash

/-!
# `Script.Signature`

The signature checker that the signature opcodes call, and the matching loop of `OP_CHECKMULTISIG`.

| DogeLib | Core | Source |
| --- | --- | --- |
| `SignatureChecker` | `BaseSignatureChecker::CheckSig`, the virtual call | D25, lines 128 to 147 |
| `baseChecker` | `BaseSignatureChecker` | D25, lines 128 to 147 |
| `transactionChecker` | `TransactionSignatureChecker::CheckSig` with `SIGVERSION_BASE`, `CheckLockTime` and `CheckSequence` | D3, lines 1253 to 1353 |
| `lockTimeSatisfied` | The body of `TransactionSignatureChecker::CheckLockTime` | D3, lines 1274 to 1308 |
| `sequenceSatisfied` | The body of `TransactionSignatureChecker::CheckSequence` | D3, lines 1310 to 1353 |
| `multisigLoop` | The matching loop of `OP_CHECKMULTISIG` | D3, lines 963 to 992 |

## The verifier

`transactionChecker` takes the elliptic-curve check as a parameter `verify`, Core's `VerifySignature` (D3, lines 1248 to 1251).
`verify sig pubKey digest` receives the signature without its hash-type byte, the public-key bytes and the digest.
It returns `some true` or `some false` when it decides the signature, and `none` when it is unavailable.
DogeLib does not specify ECDSA.
A result about a spend that uses `transactionChecker` holds for Core only if `verify` agrees with Core's `CPubKey::Verify` on the requests it decides.
SOUNDNESS.md records this hypothesis.

A checker result of `none` gives an unsupported result in the evaluator, never a rejection.

## Lock-time checks

`checkLockTime` and `checkSequence` are Core's `CheckLockTime` and `CheckSequence`.
`OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY` call them with a decoded operand `n`, `0 ≤ n < 2^39` (D3, lines 377 and 408).
`transactionChecker` reads the transaction's lock time and version and the sequence of input `nIn`.
For an index outside the inputs, both fields return `none`.
Core reads `vin[nIn]` there, which is undefined behavior, so the result makes no claim about Core.
`InputContext` in `DogeLib.Script.Verify` excludes that index.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/--
The signature check that `EvalScript` calls: `BaseSignatureChecker::CheckSig` (D25, lines 128 to 147) with `SIGVERSION_BASE`.
`checkSig sig pubKey scriptCode` receives the signature with its hash-type byte, the public-key bytes and the effective script code.
It returns `some b` for Core's result `b`, or `none` when the check is unavailable.
-/
structure SignatureChecker where
  /-- `CheckSig(vchSig, vchPubKey, scriptCode, SIGVERSION_BASE)`, or `none` when unavailable. -/
  checkSig : (sig pubKey scriptCode : List UInt8) → Option Bool
  /-- `CheckLockTime(nLockTime)`, or `none` when unavailable. The opcode passes only `0 ≤ n < 2^39`. -/
  checkLockTime : Int → Option Bool
  /-- `CheckSequence(nSequence)`, or `none` when unavailable. The opcode passes only `0 ≤ n < 2^39` with bit 31 clear. -/
  checkSequence : Int → Option Bool

/-- Core's `BaseSignatureChecker` (D25, lines 128 to 147): every signature, lock-time and sequence check fails. -/
def baseChecker : SignatureChecker where
  checkSig _ _ _ := some false
  checkLockTime _ := some false
  checkSequence _ := some false

/-- `LOCKTIME_THRESHOLD` (D24, `src/script/script.h` line 35): a lock time below it is a block height, and otherwise a time. -/
def lockTimeThreshold : Nat := 500000000

/-- `CTxIn::SEQUENCE_FINAL` (D4, line 76). -/
def sequenceFinal : UInt32 := 0xffffffff

/-- `CTxIn::SEQUENCE_LOCKTIME_DISABLE_FLAG` (D4, line 81): bit 31, `1 << 31`. -/
def sequenceLockTimeDisableFlag : Nat := 0x80000000

/-- `CTxIn::SEQUENCE_LOCKTIME_TYPE_FLAG` (D4, line 86): bit 22, `1 << 22`. -/
def sequenceLockTimeTypeFlag : Nat := 0x400000

/-- `CTxIn::SEQUENCE_LOCKTIME_MASK` (D4, line 90). -/
def sequenceLockTimeMask : Nat := 0xffff

/--
The body of `TransactionSignatureChecker::CheckLockTime` (D3, lines 1274 to 1308), for the transaction's lock time `lockTime` and the input's sequence `sequence`.
It holds when the operand `n` and `lockTime` lie on the same side of `LOCKTIME_THRESHOLD`, `n` is at most `lockTime`, and `sequence` is not `SEQUENCE_FINAL`.
-/
def lockTimeSatisfied (lockTime sequence : UInt32) (n : Int) : Bool :=
  ((decide (lockTime.toNat < lockTimeThreshold) && decide (n < lockTimeThreshold)) ||
      (decide (lockTimeThreshold ≤ lockTime.toNat) && decide ((lockTimeThreshold : Int) ≤ n))) &&
    decide (n ≤ lockTime.toNat) && sequence != sequenceFinal

/--
The body of `TransactionSignatureChecker::CheckSequence` (D3, lines 1310 to 1353), for the version bits `version` and the input's sequence `sequence`.
Core reads the version as `uint32_t` (line 1318), which is `version.toNat`.
It holds when the version is at least 2 and the disable bit of `sequence` is clear.
The masked operand and the masked sequence must also have the same type bit, and the masked operand must be at most the masked sequence.
The mask is `SEQUENCE_LOCKTIME_TYPE_FLAG | SEQUENCE_LOCKTIME_MASK`.
Core masks the operand as an `int64_t`. Here it is masked as `n.toNat`, which agrees for `n ≥ 0`, the only operands that the opcode passes.
-/
def sequenceSatisfied (version sequence : UInt32) (n : Int) : Bool :=
  let mask := sequenceLockTimeTypeFlag ||| sequenceLockTimeMask
  let txMasked := sequence.toNat &&& mask
  let nMasked := n.toNat &&& mask
  decide (2 ≤ version.toNat) && sequence.toNat &&& sequenceLockTimeDisableFlag == 0 &&
    ((decide (txMasked < sequenceLockTimeTypeFlag) && decide (nMasked < sequenceLockTimeTypeFlag)) ||
      (decide (sequenceLockTimeTypeFlag ≤ txMasked) && decide (sequenceLockTimeTypeFlag ≤ nMasked))) &&
    decide (nMasked ≤ txMasked)

/--
The elliptic-curve check: Core's `VerifySignature` (D3, lines 1248 to 1251), which calls `CPubKey::Verify`.
It receives the signature without its hash-type byte, the public-key bytes and the digest.
`none` means that the verifier is unavailable.
-/
abbrev SignatureVerifier := List UInt8 → List UInt8 → Hash256 → Option Bool

/--
`TransactionSignatureChecker::CheckSig` (D3, lines 1253 to 1272) with `SIGVERSION_BASE`, for input `nIn` of `tx`.
It checks in Core's order:

1. A public key that fails `isValidPubKey` gives `false` (lines 1255 to 1257).
2. An empty signature gives `false` (lines 1261 and 1262).
3. The last byte is the hash type, zero-extended as Core's `int nHashType = vchSig.back()` does, and it is removed (lines 1263 and 1264).
4. The digest is `legacySignatureHash` of the script code (line 1266).
5. The result is `verify` on the remaining signature bytes, the public-key bytes and the digest (line 1268).

Steps 1 and 2 never call `verify`.
A script code of 2^64 bytes or more lies outside `Transaction.Script` and gives `none`.
The evaluator never passes such a script code, because its script has at most 10,000 bytes, and the result makes no claim about Core.

`checkLockTime` is `lockTimeSatisfied` and `checkSequence` is `sequenceSatisfied` on the sequence of input `nIn` (lines 1274 to 1353).
An index outside the inputs gives `none` for both: Core's `vin[nIn]` is undefined behavior there.
-/
def transactionChecker (tx : Transaction) (nIn : UInt32) (verify : SignatureVerifier) : SignatureChecker where
  checkSig sig pubKey code :=
    if !isValidPubKey pubKey then some false
    else match sig.getLast? with
      | none => some false
      | some hashType =>
        if h : code.length < 2 ^ 64 then
          verify sig.dropLast pubKey (legacySignatureHash ⟨⟨code, h⟩⟩ tx nIn hashType.toUInt32)
        else none
  checkLockTime n := tx.inputs.val[nIn.toNat]?.map fun i => lockTimeSatisfied tx.lockTime i.sequence n
  checkSequence n := tx.inputs.val[nIn.toNat]?.map fun i => sequenceSatisfied tx.version i.sequence n

/--
The matching loop of `OP_CHECKMULTISIG` (D3, lines 963 to 992), over any signature and key types.
`sigs` and `keys` list the items in the order that Core visits them: `stacktop(-isig)` and `stacktop(-ikey)` for increasing `isig` and `ikey`, nearest the stack top first.
`check sig key` gives Core's `fOk` for one pair, or an error that stops the loop.
A successful check consumes the signature, and every check consumes the key.
The loop stops with `false` when more signatures than keys remain (lines 990 and 991), and with `true` when no signature remains.
The case of a signature without a key is unreachable from `OP_CHECKMULTISIG`, whose count check gives at most as many signatures as keys.
-/
def multisigLoop {α β ε : Type} (check : α → β → Except ε Bool) : List α → List β → Except ε Bool
  | [], _ => .ok true
  | _ :: _, [] => .ok false
  | sig :: sigs, key :: keys =>
    match check sig key with
    | .error e => .error e
    | .ok ok =>
      let rest := if ok then sigs else sig :: sigs
      if keys.length < rest.length then .ok false else multisigLoop check rest keys

end DogeLib.Script
