module

public import DogeLib.Cryptography.Hash.Sha1
public import DogeLib.Cryptography.Proofs.Hash.Sha256

/-!
# Proofs: `Hash.Sha1`

SHA-1 agrees with a separate FIPS 180-4 §6.1.2 model on every message shorter than 2^61 bytes.
The model uses bit vectors and a named state, with its own round functions and constants.
Only the identical padding and input-word model reuse SHA-256's model.

The proof structure adapts EthLib's SHA-256 proof at commit `6a93711e7cc062e787fff6747e4101a141d38b7a`, under CC0 1.0.
The current EthLib pin `bb6dfe5` restructures SHA-256 in `d59f0e3a`, which DogeLib has not ported.
The adaptation replaces SHA-256's recurrence, rounds, constants, state and digest with SHA-1's.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Sha1

namespace Spec

/-- A word with arithmetic modulo 2^32, FIPS 180-4 §3.2. -/
abbrev Word := BitVec 32

/-- The five working variables, FIPS 180-4 §6.1.2. -/
structure State where
  /-- The working variable `a`. -/
  a : Word
  /-- The working variable `b`. -/
  b : Word
  /-- The working variable `c`. -/
  c : Word
  /-- The working variable `d`. -/
  d : Word
  /-- The working variable `e`. -/
  e : Word
  deriving DecidableEq

/-- The round function for `t < 80`, FIPS 180-4 §4.1.1. -/
def function (t : Nat) (x y z : Word) : Word :=
  if t < 20 then (x &&& y) ^^^ ((~~~x) &&& z)
  else if t < 40 then x ^^^ y ^^^ z
  else if t < 60 then (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
  else x ^^^ y ^^^ z

/-- The round constant for `t < 80`, FIPS 180-4 §4.2.1. -/
def constant (t : Nat) : Word :=
  if t < 20 then 0x5a827999
  else if t < 40 then 0x6ed9eba1
  else if t < 60 then 0x8f1bbcdc
  else 0xca62c1d6

/-- One round of FIPS 180-4 §6.1.2, step 3. -/
def step (s : State) (t : Nat) (word : Word) : State :=
  ⟨s.a.rotateLeft 5 + function t s.b s.c s.d + s.e + constant t + word,
    s.a, s.b.rotateLeft 30, s.c, s.d⟩

/-- The SHA-1 schedule as a recurrence, FIPS 180-4 §6.1.2, step 1. -/
def messageWord (input : Vector Word 16) (t : Nat) : Word :=
  if early : t < 16 then input[t]
  else (messageWord input (t - 3) ^^^ messageWord input (t - 8) ^^^
    messageWord input (t - 14) ^^^ messageWord input (t - 16)).rotateLeft 1
termination_by t

/-- The sixteen big-endian input words, shared with SHA-256 under FIPS 180-4 §5.2.1. -/
def inputWords := Sha256.Spec.inputWords

/-- The first `n` rounds of a block, FIPS 180-4 §6.1.2, steps 2 and 3. -/
def rounds (input : Vector Word 16) (initial : State) : Nat → State
  | 0 => initial
  | n + 1 => step (rounds input initial n) n (messageWord input n)

/-- Eighty rounds, followed by addition of the initial state, FIPS 180-4 §6.1.2, step 4. -/
def compression (input : Vector Word 16) (initial : State) : State :=
  let w := rounds input initial 80
  ⟨initial.a + w.a, initial.b + w.b, initial.c + w.c, initial.d + w.d, initial.e + w.e⟩

/-- The initial hash value, FIPS 180-4 §5.3.1. -/
def initial : State :=
  ⟨0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0⟩

/-- The padding model shared with SHA-256, as FIPS 180-4 §5.1.1 prescribes. -/
def padded := Sha256.Spec.padded

/-- The hash state after the first `n` blocks, FIPS 180-4 §6.1.2. -/
def blocks (message : ByteArray) (initial : State) : Nat → State
  | 0 => initial
  | n + 1 => compression (inputWords message (64 * n)) (blocks message initial n)

/-- The five words in digest order. -/
def State.words (s : State) : Vector Word 5 := #v[s.a, s.b, s.c, s.d, s.e]

/-- Each hash word as four big-endian bytes, FIPS 180-4 §6.1.2. -/
def digest (s : State) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 20 =>
    UInt8.ofNat ((s.words[i.val / 4]'(by omega)).toNat / 2 ^ (24 - 8 * (i.val % 4)) % 256)⟩

/-- SHA-1, FIPS 180-4 §6.1. -/
def hash (message : ByteArray) : ByteArray :=
  let input := padded message
  digest (blocks input initial (input.size / 64))

end Spec

/-- Five machine words interpreted as the model's working variables. -/
def interpret (state : Vector UInt32 5) : Spec.State :=
  ⟨state[0].toBitVec, state[1].toBitVec, state[2].toBitVec, state[3].toBitVec, state[4].toBitVec⟩

/-- A machine rotation by 1, 5 or 30 equals the bit-vector rotation. -/
private theorem rotl_toBitVec (x : UInt32) (n : Nat) (allowed : n = 1 ∨ n = 5 ∨ n = 30) :
    (rotl x (UInt32.ofNat n)).toBitVec = x.toBitVec.rotateLeft n := by
  rcases allowed with rfl | rfl | rfl
  all_goals simp [rotl, BitVec.rotateLeft_def]

/-- The executable round function equals the independent bit-vector expression for every round index. -/
theorem f_toBitVec (t : Nat) (x y z : UInt32) :
    (f t x y z).toBitVec = Spec.function t x.toBitVec y.toBitVec z.toBitVec := by
  unfold f Spec.function
  by_cases h20 : t < 20
  · simp [h20, Sha256.ch]
  · by_cases h40 : t < 40
    · simp [h20, h40]
    · by_cases h60 : t < 60
      · simp [h20, h40, h60, Sha256.maj]
      · simp [h20, h40, h60]

/-- The executable constants equal the independent model constants for every round index. -/
theorem K_toBitVec (t : Nat) : (K t).toBitVec = Spec.constant t := by
  unfold K Spec.constant
  split <;> simp_all
  all_goals split <;> simp_all
  all_goals split <;> rfl

/-- Extending the schedule keeps every word already computed. -/
theorem schedulePrefix_get (block : ByteArray) (start count upper i : Nat) (within : i < count)
    (bound : count ≤ upper) :
    (schedulePrefix block start upper)[i]'(by omega) = (schedulePrefix block start count)[i] := by
  -- Each step only appends, so no earlier position ever changes.
  induction upper generalizing count with
  | zero => omega
  | succ upper ih =>
    by_cases same : count = upper + 1
    · subst count; rfl
    · rw [schedulePrefix, Vector.getElem_push_lt (by omega)]
      exact ih count within (by omega)

/-- The first sixteen schedule words are the block's big-endian words. -/
theorem schedule_input (block : ByteArray) (start i : Nat) (input : i < 16) :
    (schedule block start)[i]'(by omega) = Sha256.big32 block (start + 4 * i) := by
  rw [schedule, schedulePrefix_get block start (i + 1) 80 i (by omega) (by omega)]
  simp [schedulePrefix, input]

/-- Every later word follows the SHA-1 recurrence, FIPS 180-4 §6.1.2, step 1. -/
theorem schedule_recurrence (block : ByteArray) (start i : Nat) (later : 16 ≤ i) (within : i < 80) :
    (schedule block start)[i] = rotl
      ((schedule block start)[i - 3]'(by omega) ^^^ (schedule block start)[i - 8]'(by omega) ^^^
       (schedule block start)[i - 14]'(by omega) ^^^ (schedule block start)[i - 16]'(by omega)) 1 := by
  unfold schedule
  rw [schedulePrefix_get block start (i + 1) 80 i (by omega) (by omega),
    schedulePrefix_get block start i 80 (i - 3) (by omega) (by omega),
    schedulePrefix_get block start i 80 (i - 8) (by omega) (by omega),
    schedulePrefix_get block start i 80 (i - 14) (by omega) (by omega),
    schedulePrefix_get block start i 80 (i - 16) (by omega) (by omega)]
  simp [schedulePrefix, show ¬ i < 16 by omega]

/-- Every schedule word equals the model's recurrence, for indices below eighty. -/
theorem schedule_toBitVec (block : ByteArray) (start : Nat) :
    ∀ t, (within : t < 80) →
      ((schedule block start)[t]).toBitVec = Spec.messageWord (Spec.inputWords block start) t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro within
    by_cases early : t < 16
    · rw [schedule_input block start t early, Sha256.big32_toBitVec, Spec.messageWord]
      simp [early, Spec.inputWords, Sha256.Spec.inputWords]
    · rw [schedule_recurrence block start t (by omega) within]
      rw [show (1 : UInt32) = UInt32.ofNat 1 from rfl, rotl_toBitVec _ 1 (by omega)]
      simp only [UInt32.toBitVec_xor]
      rw [ih (t - 3) (by omega) (by omega), ih (t - 8) (by omega) (by omega),
        ih (t - 14) (by omega) (by omega), ih (t - 16) (by omega) (by omega)]
      conv => rhs; rw [Spec.messageWord]
      simp [early]

/-- One executable round equals one model round, for every round index and input state. -/
theorem round_toState (state : Vector UInt32 5) (t : Nat) (word : UInt32) :
    interpret (round state t word) = Spec.step (interpret state) t word.toBitVec := by
  have rot5 (x : UInt32) : (rotl x 5).toBitVec = x.toBitVec.rotateLeft 5 :=
    rotl_toBitVec x 5 (by omega)
  have rot30 (x : UInt32) : (rotl x 30).toBitVec = x.toBitVec.rotateLeft 30 :=
    rotl_toBitVec x 30 (by omega)
  simp [interpret, round, Spec.step, f_toBitVec, K_toBitVec, rot5, rot30]

/-- The first rounds of a block are the model's first rounds. -/
private theorem rounds_toState (block : ByteArray) (start : Nat) (state : Vector UInt32 5) :
    ∀ n, (bounded : n ≤ 80) →
      interpret (((List.finRange 80).take n).foldl
        (fun current t => round current t.val (schedule block start)[t]) state) =
      Spec.rounds (Spec.inputWords block start) (interpret state) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro bounded
    -- One more index is one more round.
    rw [List.take_succ_eq_append_getElem (by simp; omega), List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.getElem_finRange, Fin.cast_mk]
    rw [round_toState, ih (by omega)]
    simp only [Fin.getElem_fin]
    rw [schedule_toBitVec block start n (by omega)]
    simp only [Spec.rounds]

/-- `compress` is the compression of FIPS 180-4 §6.1.2, steps 2 to 4. -/
theorem compress_toState (state : Vector UInt32 5) (block : ByteArray) (start : Nat) :
    interpret (compress state block start) =
      Spec.compression (Spec.inputWords block start) (interpret state) := by
  have rounds := rounds_toState block start state 80 (by omega)
  rw [List.take_of_length_le (by simp)] at rounds
  simp only [compress, Spec.compression, ← rounds]
  simp [interpret]

/-- Shared executable padding equals the shared FIPS padding model below 2^61 bytes. -/
theorem pad_eq_spec (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    Sha256.pad message = Spec.padded message := Sha256.pad_eq_spec message admitted

/-- Every digest is 20 bytes long, whatever the message. -/
@[simp] theorem hash_size (message : ByteArray) : (hash message).size = 20 := by
  simp only [hash, digest, ByteArray.size, Array.size_ofFn]

/-- Compressing the first `n` blocks is the model's chain of blocks. -/
theorem blocks_toState (message : ByteArray) (state : Vector UInt32 5) (n : Nat) :
    interpret ((List.range n).foldl (fun current i => compress current message (64 * i)) state) =
      Spec.blocks message (interpret state) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, compress_toState, ih, Spec.blocks]

/-- The state words, read in digest order. -/
private theorem interpret_words (state : Vector UInt32 5) (i : Nat) (within : i < 5) :
    (interpret state).words[i] = state[i].toBitVec := by
  rcases i with _ | _ | _ | _ | _ | i
  all_goals first | omega | simp [interpret, Spec.State.words]

/-- One output byte is one base-256 digit of its word. -/
private theorem digit (word : UInt32) (k : Nat) (within : k < 4) :
    (word >>> (24 - 8 * UInt32.ofNat k)).toUInt8 = UInt8.ofNat ((word.toNat / 2 ^ (24 - 8 * k)) % 256) := by
  rcases k with _ | _ | _ | _ | k
  all_goals first | omega | (apply UInt8.toNat_inj.mp; simp [Nat.shiftRight_eq_div_pow])

/-- `digest` writes the model's digest. -/
theorem digest_eq_spec (state : Vector UInt32 5) : digest state = Spec.digest (interpret state) := by
  apply ByteArray.ext
  apply Array.ext
  · simp [digest, Spec.digest]
  · intro p left right
    have within : p < 20 := by simpa [digest] using left
    simp only [digest, Spec.digest, Array.getElem_ofFn]
    rw [digit _ _ (Nat.mod_lt _ (by decide)), interpret_words state (p / 4) (by omega), UInt32.toNat_toBitVec]

/--
SHA-1 is the hash of FIPS 180-4 §6.1, on every message shorter than 2⁶¹ bytes.

FIPS 180-4 §5.1.1 bounds a message at 2⁶⁴ bits, which is 2⁶¹ bytes.
-/
theorem hash_eq_spec (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    hash message = Spec.hash message := by
  have start : interpret IV = Spec.initial := by decide
  simp only [hash, Spec.hash, digest_eq_spec, blocks_toState, start, pad_eq_spec message admitted]

end DogeLib.Cryptography.Hash.Sha1
