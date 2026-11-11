module

public import DogeLib.Serialization.PackedCodec
public import DogeLib.Serialization.Codec
public import DogeLib.Serialization.CompactSize

/-!
# `Serialization.Reader`

Readers in the style of Dogecoin Core's stream classes: prefix decoders with a typed error.

A *reader* of `α` is a function `List UInt8 → Except ReadError (α × List UInt8)`.
On success it returns a value and the remainder.
On failure it returns the first error that Core's stream would throw, as a `CompactSize.ReadError`.
`CompactSize.decodeBounded` and `CountedList.decodeBounded` are readers.

This module defines three ways to build readers:

- `readFixed`: the reader of a fixed-length value, from its codec. Every failure is `truncated`.
- `readPair`: the reader of a pair. It reads the first component, then the second from the remainder.
- `readMap`: the reader of `α`, from a reader of `β` and a conversion `β → α`.

Core reads the fields of a structure in order, and stops at the first failure.
`readPair` reads in the same order, so the error of a composite reader is the error of the first field that fails.

`DogeLib.Serialization.Proofs.Reader` relates a reader to a codec with the predicate `ReaderAgrees`, and proves that the three constructions preserve it.
-/

@[expose] public section

namespace DogeLib.Serialization

open CompactSize (ReadError)

/--
The reader of a value of fixed length, from its codec: the value and the remainder, or `truncated` when the codec rejects the input.

Use it only for a codec that rejects exactly the inputs that are too short, such as the integer codecs and the codec of `Bytes n`.
Core reads these values with `CDataStream::read`, which fails only at the end of the data (SOURCES.md, D21).

`CDataStream` holds its read position in an `unsigned int`, and computes the next position in that type (D21, lines 151 and 346).
This reader keeps the exact remainder.
With a 32-bit `unsigned int`, the two agree while the read position plus the size of the read is below 2^32.
Above that bound Core's position wraps, and this reader makes no claim about the stream.
-/
def readFixed {α : Type} [Codec α] (bs : List UInt8) : Except ReadError (α × List UInt8) :=
  match Codec.decode (α := α) bs with
  | some p => .ok p
  | none => .error .truncated

/--
The reader of a pair: `r1` reads the first component, and `r2` reads the second from the remainder.
The result is the first error, if there is one.
-/
def readPair {α β : Type} (r1 : List UInt8 → Except ReadError (α × List UInt8))
    (r2 : List UInt8 → Except ReadError (β × List UInt8)) (bs : List UInt8) :
    Except ReadError ((α × β) × List UInt8) :=
  match r1 bs with
  | .error e => .error e
  | .ok (a, rest) =>
    match r2 rest with
    | .error e => .error e
    | .ok (b, rest') => .ok ((a, b), rest')

/-- The reader of `α` that reads a `β` with `r` and converts it with `f`. Errors are the errors of `r`. -/
def readMap {α β : Type} (f : β → α) (r : List UInt8 → Except ReadError (β × List UInt8))
    (bs : List UInt8) : Except ReadError (α × List UInt8) :=
  match r bs with
  | .error e => .error e
  | .ok (b, rest) => .ok (f b, rest)

/-- The packed form of `readFixed`, with `truncated` for a rejected input. -/
def readFixedSlice {α : Type} [PackedCodec α] (s : ByteSlice) :
    Except ReadError (α × ByteSlice) :=
  match PackedCodec.decodeSlice s with
  | some p => .ok p
  | none => .error .truncated

/-- Read two fields from a slice in order, with the first error as the result. -/
def readPairSlice {α β : Type} (r1 : ByteSlice → Except ReadError (α × ByteSlice))
    (r2 : ByteSlice → Except ReadError (β × ByteSlice)) (s : ByteSlice) :
    Except ReadError ((α × β) × ByteSlice) :=
  match r1 s with
  | .error e => .error e
  | .ok (a, rest) =>
    match r2 rest with
    | .error e => .error e
    | .ok (b, rest') => .ok ((a, b), rest')

/-- Convert the value of a slice reader with `f`, and keep its error and remainder. -/
def readMapSlice {α β : Type} (f : β → α) (r : ByteSlice → Except ReadError (β × ByteSlice))
    (s : ByteSlice) : Except ReadError (α × ByteSlice) :=
  match r s with
  | .error e => .error e
  | .ok (b, rest) => .ok (f b, rest)

end DogeLib.Serialization
