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
| `transactionChecker` | `TransactionSignatureChecker::CheckSig` with `SIGVERSION_BASE` | D3, lines 1253 to 1272 |
| `multisigLoop` | The matching loop of `OP_CHECKMULTISIG` | D3, lines 963 to 992 |

## The verifier

`transactionChecker` takes the elliptic-curve check as a parameter `verify`, Core's `VerifySignature` (D3, lines 1248 to 1251).
`verify sig pubKey digest` receives the signature without its hash-type byte, the public-key bytes and the digest.
It returns `some true` or `some false` when it decides the signature, and `none` when it is unavailable.
DogeLib does not specify ECDSA.
A result about a spend that uses `transactionChecker` holds for Core only if `verify` agrees with Core's `CPubKey::Verify` on the requests it decides.
SOUNDNESS.md records this hypothesis.

A checker result of `none` gives an unsupported result in the evaluator, never a rejection.

## Stage 4

Core's checker also has `CheckLockTime` and `CheckSequence`.
Stage 4 adds them to `SignatureChecker` as fields.
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

/-- Core's `BaseSignatureChecker` (D25, lines 128 to 147): every signature check fails. -/
def baseChecker : SignatureChecker where
  checkSig _ _ _ := some false

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
