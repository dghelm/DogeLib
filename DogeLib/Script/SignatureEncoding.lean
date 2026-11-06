module

public import DogeLib.Script.Error
public import DogeLib.Script.Flags

/-!
# `Script.SignatureEncoding`

The encoding checks of signatures and public keys that the signature opcodes run before they verify a signature.
They are byte predicates. No definition here does elliptic-curve arithmetic.

| DogeLib | Core | Source |
| --- | --- | --- |
| `isCompressedOrUncompressedPubKey` | `IsCompressedOrUncompressedPubKey` | D3, lines 66 to 86 |
| `isValidSignatureEncoding` | `IsValidSignatureEncoding` | D3, lines 110 to 173 |
| `isLowDerSignature` | `IsLowDERSignature` | D3, lines 175 to 184 |
| `isDefinedHashtypeSignature` | `IsDefinedHashtypeSignature` | D3, lines 186 to 195 |
| `checkSignatureEncoding` | `CheckSignatureEncoding` | D3, lines 197 to 212 |
| `checkPubKeyEncoding` | `CheckPubKeyEncoding` for `SIGVERSION_BASE` | D3, lines 214 to 223 |
| `parseDerLax` | `ecdsa_signature_parse_der_lax` | D50, lines 27 to 166 |
| `checkLowS` | `CPubKey::CheckLowS` | D50, lines 289 to 295 |
| `pubKeyLength`, `isValidPubKey` | `CPubKey::GetLen`, `Set` and `IsValid` | D51, lines 59 to 66, 143 to 146 and 189 to 196 |

The opcodes `OP_CHECKSIG` and `OP_CHECKMULTISIG` call `CheckSignatureEncoding` and then `CheckPubKeyEncoding` (D3, lines 898 and 972).
This module specifies no opcode. `DogeLib.Script.Eval` runs these checks in the signature opcodes.

## The lax parser and LOW_S

`CheckLowS` does not test the S bytes of the signature.
It parses the signature with the lax DER parser of D50 and tests the S scalar that the parser stores.
The parser stores zero for both R and S when either value overflows.
A value overflows when it has more than 32 bytes after its leading zeros, or when it is at least the group order `n` (D52, lines 335 to 354, and D53, lines 119 to 129).
The parser still reports success.

`CheckLowS` therefore accepts such a signature whatever its S, and the LOW_S filter can accept a signature with a high S (design record 0003, section 5).
`parseDerLax` keeps this case.

The parser's result also depends on `sizeof(size_t)`, through one test of a long-form length field (D50, lines 76 and 114).
`parseDerLaxWith` takes that size as a parameter, and `parseDerLax` uses 8, the size on a 64-bit build.

## Byte reads

Core reads bytes by index. Here `List.getD sig i 0` reads byte `i`, and gives `0` past the end.
Each of Core's reads is in bounds after the checks that precede it, so the default never decides a result that Core computes.
-/

@[expose] public section

namespace DogeLib.Script

/-- The order `n` of the secp256k1 group: `SECP256K1_N_0` to `SECP256K1_N_3` (D53, lines 13 to 16), and SEC 2 v2 §2.4.1 (S2). -/
def secp256k1Order : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- Half the group order, rounded down: `SECP256K1_N_H_0` to `SECP256K1_N_H_3` (D53, lines 24 to 27). -/
def secp256k1HalfOrder : Nat :=
  0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0

/-- The big-endian value of a byte string: the first byte is the most significant. The empty string is zero. -/
def beNat (bytes : List UInt8) : Nat := bytes.foldl (fun acc b => 256 * acc + b.toNat) 0

/-! ## Strict DER -/

/--
`IsValidSignatureEncoding` (D3, lines 110 to 173): the strict DER form of BIP66, followed by one hash-type byte.
The checks run in Core's order:

1. The size is from 9 to 73 bytes.
2. Byte 0 is `0x30`, and byte 1 is the size minus 3.
3. With `lenR` byte 3, `5 + lenR` is below the size. With `lenS` byte `5 + lenR`, `lenR + lenS + 7` is the size.
4. Byte 2 is `0x02`. R is not empty, its first byte is below `0x80`, and it has no excess leading zero.
5. Byte `lenR + 4` is `0x02`. S is not empty, its first byte is below `0x80`, and it has no excess leading zero.

A leading zero is excess unless more bytes follow and the next byte has its top bit set.
-/
def isValidSignatureEncoding (sig : List UInt8) : Bool :=
  let at_ (i : Nat) : UInt8 := sig.getD i 0
  if sig.length < 9 then false
  else if 73 < sig.length then false
  else if at_ 0 != 0x30 then false
  else if (at_ 1).toNat != sig.length - 3 then false
  else
    let lenR := (at_ 3).toNat
    if sig.length ≤ 5 + lenR then false
    else
      let lenS := (at_ (5 + lenR)).toNat
      if lenR + lenS + 7 != sig.length then false
      else if at_ 2 != 0x02 then false
      else if lenR == 0 then false
      else if at_ 4 &&& 0x80 != 0 then false
      else if 1 < lenR && at_ 4 == 0x00 && at_ 5 &&& 0x80 == 0 then false
      else if at_ (lenR + 4) != 0x02 then false
      else if lenS == 0 then false
      else if at_ (lenR + 6) &&& 0x80 != 0 then false
      else if 1 < lenS && at_ (lenR + 6) == 0x00 && at_ (lenR + 7) &&& 0x80 == 0 then false
      else true

/-! ## The lax parser -/

/--
The sequence length of the lax parser (D50, lines 43 to 54), read at position `pos`.
Its value is ignored. A long form, with the top bit set, is skipped together with the bytes it counts.
Returns the position after it.
-/
def laxSequenceLength (input : List UInt8) (pos : Nat) : Option Nat :=
  if pos = input.length then none
  else
    let lenbyte := input.getD pos 0
    let pos := pos + 1
    if lenbyte &&& 0x80 != 0 then
      let n := lenbyte.toNat - 0x80
      if input.length < pos + n then none else some (pos + n)
    else some pos

/--
The length of R or S in the lax parser (D50, lines 62 to 87 and 100 to 125), read at position `pos`.
A short form is the byte itself.
A long form counts the bytes that follow. Its leading zero bytes are skipped, and the rest must be fewer than `sizeTBytes`, which is `sizeof(size_t)`.
Its value is then big-endian.
Returns the length and the position after the field.
-/
def laxIntegerLength (sizeTBytes : Nat) (input : List UInt8) (pos : Nat) : Option (Nat × Nat) :=
  if pos = input.length then none
  else
    let lenbyte := input.getD pos 0
    let pos := pos + 1
    if lenbyte &&& 0x80 != 0 then
      let n := lenbyte.toNat - 0x80
      if input.length < pos + n then none
      else
        let field := (input.drop pos).take n
        let digits := field.dropWhile (· == 0)
        if sizeTBytes ≤ digits.length then none
        else some (beNat digits, pos + n)
    else some (lenbyte.toNat, pos)

/--
One integer of the lax parser, R or S (D50, lines 56 to 92 and 94 to 130), whose tag is at position `pos`.
The tag must be `0x02`, and the bytes that its length counts must lie within the input.
Returns the start and the length of the integer's bytes.
-/
def laxInteger (sizeTBytes : Nat) (input : List UInt8) (pos : Nat) : Option (Nat × Nat) :=
  if pos = input.length || input.getD pos 0 != 0x02 then none
  else
    match laxIntegerLength sizeTBytes input (pos + 1) with
    | none => none
    | some (len, pos) => if input.length - pos < len then none else some (pos, len)

/--
The scalars that the lax parser stores for the bytes of R and S (D50, lines 132 to 164).
Leading zeros are ignored.
A value of more than 32 bytes overflows (lines 138 and 150).
Otherwise `secp256k1_ecdsa_signature_parse_compact` overflows when a value is at least `secp256k1Order` (D52, lines 344 to 347, and D53, lines 119 to 129).
After an overflow both scalars are zero.
-/
def laxStore (rBytes sBytes : List UInt8) : Nat × Nat :=
  let r := rBytes.dropWhile (· == 0)
  let s := sBytes.dropWhile (· == 0)
  let overflow := 32 < r.length || 32 < s.length
  let overflow := overflow || !(decide (beNat r < secp256k1Order) && decide (beNat s < secp256k1Order))
  if overflow then (0, 0) else (beNat r, beNat s)

/--
`ecdsa_signature_parse_der_lax` (D50, lines 27 to 166), with `sizeof(size_t)` as `sizeTBytes`.
`none` is Core's return value 0. `some (r, s)` is the return value 1, with the scalars that the parser stores.

The parser needs the sequence tag `0x30`, a sequence length, and the integers R and S in that order.
It ignores the value of the sequence length and every byte after S.
It accepts negative integers and excess padding.
-/
def parseDerLaxWith (sizeTBytes : Nat) (input : List UInt8) : Option (Nat × Nat) :=
  if 0 = input.length || input.getD 0 0 != 0x30 then none
  else
    match laxSequenceLength input 1 with
    | none => none
    | some pos =>
      match laxInteger sizeTBytes input pos with
      | none => none
      | some (rpos, rlen) =>
        match laxInteger sizeTBytes input (rpos + rlen) with
        | none => none
        | some (spos, slen) => some (laxStore ((input.drop rpos).take rlen) ((input.drop spos).take slen))

/-- `ecdsa_signature_parse_der_lax` on a 64-bit build, where `sizeof(size_t)` is 8. -/
def parseDerLax (input : List UInt8) : Option (Nat × Nat) := parseDerLaxWith 8 input

/--
`CPubKey::CheckLowS` (D50, lines 289 to 295): the lax parser succeeds, and the S that it stores is at most `secp256k1HalfOrder`.
`secp256k1_ecdsa_signature_normalize` reports a high S when S is above that bound (D52, lines 381 to 398, and D53, lines 158 to 168).
-/
def checkLowS (sig : List UInt8) : Bool :=
  match parseDerLax sig with
  | none => false
  | some (_, s) => decide (s ≤ secp256k1HalfOrder)

/-! ## The signature checks -/

/--
`IsLowDERSignature` (D3, lines 175 to 184).
A signature that fails `isValidSignatureEncoding` gives `SIG_DER`.
Otherwise `CheckLowS` runs on the signature without its last byte, the hash type, and its failure gives `SIG_HIGH_S`.
-/
def isLowDerSignature (sig : List UInt8) : Except ScriptError Unit :=
  if !isValidSignatureEncoding sig then .error .sigDer
  else if !checkLowS sig.dropLast then .error .sigHighS
  else .ok ()

/--
`IsDefinedHashtypeSignature` (D3, lines 186 to 195).
The last byte, with the `SIGHASH_ANYONECANPAY` bit `0x80` cleared, must be from `SIGHASH_ALL` to `SIGHASH_SINGLE`, 1 to 3 (D25).
The empty signature fails.
-/
def isDefinedHashtypeSignature (sig : List UInt8) : Bool :=
  match sig.getLast? with
  | none => false
  | some b =>
    let hashType := b &&& ~~~0x80
    !(hashType < 1 || 3 < hashType)

/--
`CheckSignatureEncoding` (D3, lines 197 to 212), with Core's `else if` chain:

- The empty signature passes, whatever the flags.
- With `DERSIG`, `LOW_S` or `STRICTENC`, a signature that fails `isValidSignatureEncoding` gives `SIG_DER`.
- Otherwise, with `LOW_S`, a failure of `isLowDerSignature` gives its error.
- Otherwise, with `STRICTENC`, a signature that fails `isDefinedHashtypeSignature` gives `SIG_HASHTYPE`.
-/
def checkSignatureEncoding (sig : List UInt8) (flags : UInt32) : Except ScriptError Unit :=
  if sig.isEmpty then .ok ()
  else if (hasFlag flags ScriptFlags.derSig || hasFlag flags ScriptFlags.lowS ||
      hasFlag flags ScriptFlags.strictEnc) && !isValidSignatureEncoding sig then .error .sigDer
  else if hasFlag flags ScriptFlags.lowS && (isLowDerSignature sig).isOk == false then
    isLowDerSignature sig
  else if hasFlag flags ScriptFlags.strictEnc && !isDefinedHashtypeSignature sig then .error .sigHashtype
  else .ok ()

/-! ## Public keys -/

/--
`IsCompressedOrUncompressedPubKey` (D3, lines 66 to 86).
A key that starts with `0x04` passes with 65 bytes.
A key that starts with `0x02` or `0x03` passes with 33 bytes.
No other key passes.
-/
def isCompressedOrUncompressedPubKey (pubKey : List UInt8) : Bool :=
  if pubKey.length < 33 then false
  else
    let header := pubKey.getD 0 0
    if header == 0x04 then pubKey.length == 65
    else if header == 0x02 || header == 0x03 then pubKey.length == 33
    else false

/--
`CheckPubKeyEncoding` (D3, lines 214 to 223) in `SIGVERSION_BASE`.
With `STRICTENC`, a key that fails `isCompressedOrUncompressedPubKey` gives `PUBKEYTYPE`.

Core's second test needs `SIGVERSION_WITNESS_V0` and the `WITNESS_PUBKEYTYPE` flag (lines 219 to 221).
Design record 0003 runs only `SIGVERSION_BASE`, and `WITNESS_PUBKEYTYPE` is outside `supportedFlags`, so this definition omits that test.
-/
def checkPubKeyEncoding (pubKey : List UInt8) (flags : UInt32) : Except ScriptError Unit :=
  if hasFlag flags ScriptFlags.strictEnc && !isCompressedOrUncompressedPubKey pubKey then .error .pubkeyType
  else .ok ()

/--
`CPubKey::GetLen` (D51, lines 189 to 196): the length of a public key with this first byte.
It is 33 for `0x02` and `0x03`, 65 for `0x04`, `0x06` and `0x07`, and 0 for any other byte.
-/
def pubKeyLength (header : UInt8) : Nat :=
  if header == 2 || header == 3 then 33
  else if header == 4 || header == 6 || header == 7 then 65
  else 0

/--
Whether `CPubKey(begin, end)` holds a valid key: `Set` (D51, lines 59 to 66) and then `IsValid` (lines 143 to 146).
`Set` keeps the bytes when they are not empty and `pubKeyLength` of the first byte is nonzero and equals their number.
Otherwise it invalidates the key, and `IsValid` fails.
The hybrid headers `0x06` and `0x07` give valid keys of 65 bytes.
This test is not a check that the bytes encode a point on the curve.
-/
def isValidPubKey (pubKey : List UInt8) : Bool :=
  match pubKey with
  | [] => false
  | header :: _ => pubKeyLength header != 0 && pubKeyLength header == pubKey.length

end DogeLib.Script
