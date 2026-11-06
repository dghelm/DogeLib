module

public import DogeLib.Script.Instruction
public import DogeLib.Transaction.LegacySighashReference

/-!
# `Script.SignatureCode`

Legacy signature-code preparation, before the signature serializer removes code separators.
`CScript::operator<<(const std::vector<unsigned char>&)` constructs each signature push (D24, lines 437 to 464).
The vector constructor delegates to this overload (D24, line 418).
`EvalScript` removes these pushes with `FindAndDelete` (D3, lines 891 to 896 and 952 to 961).
The deletion implementation is `Transaction.findAndDelete` (D24, lines 570 to 596).

Lengths in a PUSHDATA4 header wrap modulo 2^32, as Core's `WriteLE32` does.
The reader round trip requires a payload shorter than 2^32 bytes.
Script's 520-byte element limit lies within that domain.
-/

@[expose] public section

namespace DogeLib.Script

/-- The low `width` bytes of `n`, in little-endian order, for Core's push length fields (D24). -/
def pushLengthBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, n => n.toUInt8 :: pushLengthBytes width (n / 256)

/-- The header of `CScript() << vch` for a vector of `n` bytes (D24, lines 437 to 464). -/
def pushHeader (n : Nat) : List UInt8 :=
  if n < 76 then [n.toUInt8]
  else if n ≤ 255 then 0x4c :: pushLengthBytes 1 n
  else if n ≤ 65535 then 0x4d :: pushLengthBytes 2 n
  else 0x4e :: pushLengthBytes 4 n

/--
The bytes of `CScript() << data`, using Core's vector overload (D24).
Empty data gives `00`, and a one-byte number uses a direct push rather than a numeric opcode.
-/
def pushEncoding (data : List UInt8) : List UInt8 := pushHeader data.length ++ data

/--
Legacy script code from `beginCodeHash`, with every supplied signature push removed (D3).
`signatures` follows `stacktop(-isig-k)` for increasing `k`: nearest the stack top first.
Each signature includes its hash-type byte.
CHECKSIG supplies one signature, and CHECKMULTISIG supplies all signatures before its matching loop.
The caller establishes that `beginCodeHash` is the cursor after the last executed separator.
The signature serializer removes the remaining code separators later.
-/
def effectiveScriptCode (script : List UInt8) (beginCodeHash : Nat)
    (signatures : List (List UInt8)) : List UInt8 :=
  signatures.foldl (fun code sig => (Transaction.findAndDelete code (pushEncoding sig)).1)
    (script.drop beginCodeHash)

end DogeLib.Script
