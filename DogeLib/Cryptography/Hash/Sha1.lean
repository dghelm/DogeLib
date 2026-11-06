module

public import DogeLib.Cryptography.Hash.Sha256

/-!
# `Sha1`

SHA-1 for messages of whole bytes, following FIPS 180-4 §6.1.2.
The FIPS input domain contains messages shorter than 2^61 bytes.
The total definition also accepts longer messages, whose encoded bit length wraps modulo 2^64.
The digest contains twenty bytes in SHA-1 output order.

SHA-1 reuses SHA-256's padding, big-endian reader, Ch and Maj.
The schedule and round structure adapt DogeLib's SHA-256 from EthLib at commit `6a93711e7cc062e787fff6747e4101a141d38b7a` (CC0 1.0).
The current EthLib pin `bb6dfe5` restructures SHA-256 in `d59f0e3a`, which DogeLib has not ported.
The adaptation changes the recurrence, constants, working variables and digest length to SHA-1.
SOURCES.md maps these definitions to FIPS 180-4 and pinned Core's `CSHA1`.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Sha1

/-- Rotation left by `n` bits for `0 < n < 32`, FIPS 180-4 §3.2. -/
@[inline] def rotl (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- The round function for `t < 80`, FIPS 180-4 §4.1.1. -/
@[inline] def f (t : Nat) (x y z : UInt32) : UInt32 :=
  if t < 20 then Sha256.ch x y z
  else if t < 40 then x ^^^ y ^^^ z
  else if t < 60 then Sha256.maj x y z
  else x ^^^ y ^^^ z

/-- The round constant for `t < 80`, FIPS 180-4 §4.2.1. -/
def K (t : Nat) : UInt32 :=
  if t < 20 then 0x5a827999
  else if t < 40 then 0x6ed9eba1
  else if t < 60 then 0x8f1bbcdc
  else 0xca62c1d6

/-- The five initial hash words, FIPS 180-4 §5.3.1. -/
def IV : Vector UInt32 5 := #v[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

/-- The first `count` words of the message schedule, each computed from the ones before it. -/
def schedulePrefix (block : ByteArray) (start : Nat) : (count : Nat) → Vector UInt32 count
  | 0 => .emptyWithCapacity 80
  | t + 1 =>
    let W := schedulePrefix block start t
    let next := if early : t < 16 then Sha256.big32 block (start + 4 * t)
      else rotl (W[t - 3]'(by omega) ^^^ W[t - 8]'(by omega) ^^^
        W[t - 14]'(by omega) ^^^ W[t - 16]'(by omega)) 1
    W.push next

/--
The message schedule W₀ to W₇₉ of the block starting at byte `start`, FIPS 180-4 §6.1.2, step 1.

The first sixteen words are the block's, and each later word mixes four earlier ones.
-/
def schedule (block : ByteArray) (start : Nat) : Vector UInt32 80 := schedulePrefix block start 80

/-- One round on the five working variables, FIPS 180-4 §6.1.2, step 3. -/
@[inline] def round (state : Vector UInt32 5) (t : Nat) (word : UInt32) : Vector UInt32 5 :=
  let a := state[0]
  let b := state[1]
  let c := state[2]
  let d := state[3]
  let e := state[4]
  #v[rotl a 5 + f t b c d + e + K t + word, a, rotl b 30, c, d]

/-- Eighty rounds followed by addition of the initial state, FIPS 180-4 §6.1.2, steps 2 to 4. -/
def compress (state : Vector UInt32 5) (block : ByteArray) (start : Nat) : Vector UInt32 5 :=
  let W := schedule block start
  let working := (List.finRange 80).foldl (fun current t => round current t.val W[t]) state
  state.zipWith (· + ·) working

/-- The five hash words as twenty bytes, each word big-endian, FIPS 180-4 §6.1.2. -/
def digest (state : Vector UInt32 5) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 20 => (state[i.val / 4]'(by omega) >>> (24 - 8 * UInt32.ofNat (i.val % 4))).toUInt8⟩

/--
SHA-1 of whole bytes, FIPS 180-4 §6.1.
FIPS defines it for messages shorter than 2^61 bytes.
Longer messages have their encoded bit length taken modulo 2^64.
-/
def hash (message : ByteArray) : ByteArray :=
  let padded := Sha256.pad message
  digest ((List.range (padded.size / 64)).foldl (fun state i => compress state padded (64 * i)) IV)

end DogeLib.Cryptography.Hash.Sha1

namespace DogeLib.Cryptography.Hash

/-- SHA-1 in digest order, with FIPS 180-4 agreement for whole-byte messages shorter than 2^61 bytes. -/
@[inline] def sha1 (data : ByteArray) : ByteArray := Sha1.hash data

end DogeLib.Cryptography.Hash
