module

public import DogeLib.Block.HeaderSequence
public import DogeLib.Block.Proofs.ContextualCheck

/-!
# Properties of the block-index model

The theorems are the stage-1 targets of design record 0008, section 11, and the lemmas that they need.

- `HeaderIndex.lookup_insert_self` and `HeaderIndex.lookup_insert_of_ne`: the interface of lookup and insertion.
- `ancestorWalk_take`, `ancestorWalk_length_le` and `ancestorWalk_eq_ancestorChain`: the walk with less fuel is a prefix, and fuel beyond the height does not change it in a well-formed index.
- `ancestorWalk_valid`: in a well-formed index, every walk from an entry passes `validateWorkView`.
- `ancestorView_congr_chain` and the target `ancestorView_congr`: `contextualCheckBlockHeader` gives the same result on `ancestorView` as on the whole chain of predecessors.
- The target `lastCheckpointInIndex_eq`: suppose that each checkpoint hash in the index belongs to an entry at its table height.
  Then the search over the index equals `lastCheckpoint` of design record 0006 on the table heights whose hashes the index has.

The stage-2 theorems describe one step, `acceptBlockHeader`:

- `checkWellFormed_iff`: the executable check equals `WellFormed`.
- `accept_known`, `accept_genesis_known`, `accept_genesis_insert` and `accept_genesis_parent`: a known hash, and the genesis hash.
- The target `accept_eq_ok_iff`: the conditions under which the step accepts an unknown hash other than genesis.
- The target `accept_eq_error_iff`, from one theorem for each rejection, and its companion `accept_eq_heightOutOfRange_iff`.
- The targets `accept_ok_insert` and `accept_link`: the entry that an acceptance adds.
- The target `accept_error_index`: an error leaves the index unchanged, except for the marks of step 6.
- The target `wellFormed_preserved`: each step keeps `WellFormed`.
- The target `failedAncestor_verdict_perm`: the verdict does not depend on the order of the failed list.

The stage-3 theorems describe the sequence, `processNewBlockHeaders`:

- The targets `process_append`, `process_error_suffix` and `process_prefix_ok`: a sequence over `xs ++ ys` is the composition of its two parts.
- The target `process_linear`: take a list that extends one entry in order, without failure state.
  It is accepted exactly when each header passes step 2 and the contextual check on the view that its predecessors extend.
  `process_height` gives the heights of the added entries.
- The target `process_no_failure`: without failure flags and failed blocks, no step returns `duplicate`, `prevBlockInvalid` or `failedAncestor`, and no step sets a flag.
- The target `process_adjustedTime_mono`: a later adjusted time keeps an acceptance and its result.
- The target `process_complete`: without anchors, within the height budget and with an adjusted time in the domain, the sequence returns no adapter error.

Section 13.1 of the record replaces the target `accept_genesis` with `accept_genesis_known`, `accept_genesis_insert` and `accept_genesis_parent`.
`addToBlockIndex` follows Core and searches the index for `hashPrevBlock`.
So a genesis entry gets no predecessor and height 0 only when the index lacks the genesis header's `hashPrevBlock`.

The theorems establish the behaviour of DogeLib's definitions.
They say nothing about whether an index is the state that a node holds: the anchors, the failure flags and the failed list are inputs.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Work

/-! ## Lookup and insertion -/

/-- For every index, hash and entry, the lookup of a hash after its insertion gives the inserted entry. -/
theorem HeaderIndex.lookup_insert_self (index : HeaderIndex) (hash : Hash256) (entry : IndexEntry) :
    (index.insert hash entry).lookup hash = some entry := by
  simp [HeaderIndex.lookup, HeaderIndex.insert]

/-- For every index and entry, the insertion under one hash does not change the lookup of another hash. -/
theorem HeaderIndex.lookup_insert_of_ne (index : HeaderIndex) (hash other : Hash256) (entry : IndexEntry)
    (ne : other ≠ hash) :
    (index.insert hash entry).lookup other = index.lookup other := by
  have differ : (other.val == hash.val) = false := beq_false_of_ne fun same => ne (Subtype.ext same)
  simp [HeaderIndex.lookup, HeaderIndex.insert, List.lookup_cons, differ]

/-- For every index, hash and entry, an insertion does not change the failed list. -/
theorem HeaderIndex.insert_failedBlocks (index : HeaderIndex) (hash : Hash256) (entry : IndexEntry) :
    (index.insert hash entry).failedBlocks = index.failedBlocks := rfl

/-! ## The walk -/

/-- For every index, fuel and entry, the walk has at most `fuel` entries. -/
theorem ancestorWalk_length_le (index : HeaderIndex) (fuel : Nat) (entry : IndexEntry) :
    (ancestorWalk index fuel entry).length ≤ fuel := by
  induction fuel generalizing entry with
  | zero => simp [ancestorWalk]
  | succ n ih =>
    simp only [ancestorWalk, List.length_cons]
    split
    · have := ih ‹_›; omega
    · simp

/-- For every index and entry, the walk with `n` entries of fuel is the first `n` entries of the walk with `m ≥ n` entries of fuel. -/
theorem ancestorWalk_take (index : HeaderIndex) (entry : IndexEntry) (n m : Nat) (le : n ≤ m) :
    (ancestorWalk index m entry).take n = ancestorWalk index n entry := by
  induction n generalizing m entry with
  | zero => simp [ancestorWalk]
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [ancestorWalk, List.take_succ_cons]
    split
    · rw [ih _ _ (by omega)]
    · simp

/-- A walk with positive fuel starts with the entry itself. -/
private theorem ancestorWalk_head? (index : HeaderIndex) (fuel : Nat) (entry : IndexEntry) (b : BlockIndex)
    (head : (ancestorWalk index fuel entry).head? = some b) : b = entry.toBlockIndex := by
  cases fuel with
  | zero => simp [ancestorWalk] at head
  | succ n => simp only [ancestorWalk, List.head?_cons, Option.some.injEq] at head; exact head.symm

/-- A list passes `validateWorkView` when its first entry is below 2147483647, links to the next entry, and the rest passes. -/
private theorem validateWorkView_cons_of (a : BlockIndex) (rest : List BlockIndex)
    (bound : a.nHeight < 2147483647) (valid : validateWorkView rest = .ok ())
    (link : ∀ b, rest.head? = some b → a.nHeight = b.nHeight + 1) :
    validateWorkView (a :: rest) = .ok () := by
  cases rest with
  | nil =>
    have out : ¬ a.nHeight ≥ 2147483647 := by omega
    simp [validateWorkView, out]
    rfl
  | cons b rest => exact (validateWorkView_cons_cons a b rest).mpr ⟨bound, link b rfl, valid⟩

/-- In a well-formed index, an entry's resolved predecessor is an entry of the index at one height lower. -/
private theorem parent_of_link {network : WorkNetwork} {index : HeaderIndex} (wf : WellFormed network index)
    {hash : Hash256} {entry parent : IndexEntry} (found : index.lookup hash = some entry)
    (link : entry.prev.bind index.lookup = some parent) :
    ∃ prev, index.lookup prev = some parent ∧ entry.height = parent.height + 1 := by
  obtain ⟨prev, hprev, hlook⟩ := Option.bind_eq_some_iff.mp link
  obtain ⟨-, parent', found', height⟩ := wf.prevLink hash entry prev found hprev
  rw [found'] at hlook
  cases hlook
  exact ⟨prev, found', height⟩

/--
For every network, fuel and entry of a well-formed index, the walk from the entry passes `validateWorkView`.
Its heights are below 2147483647, and each entry is one above the next.
-/
theorem ancestorWalk_valid (network : WorkNetwork) (index : HeaderIndex) (wf : WellFormed network index)
    (fuel : Nat) (hash : Hash256) (entry : IndexEntry) (found : index.lookup hash = some entry) :
    validateWorkView (ancestorWalk index fuel entry) = .ok () := by
  induction fuel generalizing hash entry with
  | zero => rfl
  | succ n ih =>
    have bound := wf.heightBound hash entry found
    simp only [ancestorWalk]
    split
    · rename_i parent link
      obtain ⟨prev, found', height⟩ := parent_of_link wf found link
      refine validateWorkView_cons_of _ _ bound (ih prev parent found') ?_
      intro b head
      rw [ancestorWalk_head? index n parent b head]
      exact height
    · exact validateWorkView_cons_of _ _ bound rfl (by simp)

/--
For every network and entry of a well-formed index, fuel of at least `entry.height + 1` gives the whole chain: the walk equals `ancestorChain`.
Each step of the walk lowers the height by one, so the walk ends before the fuel runs out.
-/
theorem ancestorWalk_eq_ancestorChain (network : WorkNetwork) (index : HeaderIndex)
    (wf : WellFormed network index) (fuel : Nat) (hash : Hash256) (entry : IndexEntry)
    (found : index.lookup hash = some entry) (enough : entry.height + 1 ≤ fuel) :
    ancestorWalk index fuel entry = ancestorChain index entry := by
  induction fuel generalizing hash entry with
  | zero => omega
  | succ n ih =>
    unfold ancestorChain
    simp only [ancestorWalk]
    congr 1
    cases link : entry.prev.bind index.lookup with
    | none => rfl
    | some parent =>
      obtain ⟨prev, found', height⟩ := parent_of_link wf found link
      simp only
      rw [height, ih prev parent found' (by omega), ancestorChain]

/-! ## The view -/

/--
Let `prev` be an entry of a well-formed index.
For every network, header, adjusted time and last checkpoint, `contextualCheckBlockHeader` gives the same result on `ancestorView network index prev` as on `ancestorChain index prev`.
`ancestorChain index prev` is the whole chain of predecessors in the index.
The result is the same acceptance, the same rejection or the same adapter error.
-/
theorem ancestorView_congr_chain (network : WorkNetwork) (index : HeaderIndex)
    (wf : WellFormed network index) (hash : Hash256) (prev : IndexEntry)
    (found : index.lookup hash = some prev) (header : PureBlockHeader) (adjustedTime : Int64)
    (lastCheckpointHeight : Option Nat) :
    contextualCheckBlockHeader network header (ancestorView network index prev) adjustedTime
        lastCheckpointHeight =
      contextualCheckBlockHeader network header (ancestorChain index prev) adjustedTime
        lastCheckpointHeight := by
  have positive : 0 < contextualViewDepth network prev.toBlockIndex := by
    simp only [contextualViewDepth, nMedianTimeSpan]; omega
  have agree : (ancestorView network index prev).take (contextualViewDepth network prev.toBlockIndex) =
      (ancestorChain index prev).take (contextualViewDepth network prev.toBlockIndex) := by
    have viewShort := ancestorWalk_length_le index (contextualViewDepth network prev.toBlockIndex) prev
    unfold ancestorView
    rw [List.take_of_length_le viewShort]
    by_cases deep : contextualViewDepth network prev.toBlockIndex ≤ prev.height + 1
    · exact (ancestorWalk_take index prev _ _ deep).symm
    · rw [ancestorWalk_eq_ancestorChain network index wf _ hash prev found (by omega)]
      have chainShort := ancestorWalk_length_le index (prev.height + 1) prev
      unfold ancestorChain
      rw [List.take_of_length_le (by omega)]
  obtain ⟨d, hd⟩ : ∃ d, contextualViewDepth network prev.toBlockIndex = d + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos positive).symm⟩
  have viewValid := ancestorWalk_valid network index wf (contextualViewDepth network prev.toBlockIndex)
    hash prev found
  have chainValid := ancestorWalk_valid network index wf (prev.height + 1) hash prev found
  unfold ancestorView ancestorChain at *
  revert agree viewValid chainValid
  rw [hd]
  simp only [ancestorWalk]
  rw [← hd]
  intro agree viewValid chainValid
  exact contextualCheck_congr_prefix network header prev.toBlockIndex _ _ adjustedTime
    lastCheckpointHeight viewValid chainValid agree

/--
The target `ancestorView_congr` of design record 0008, section 11.
Let `prev` be an entry of a well-formed index whose chain of predecessors reaches height 0: the last entry of `ancestorChain index prev` has height 0.
Then for every network, header, adjusted time and last checkpoint, `contextualCheckBlockHeader` gives the same result on `ancestorView network index prev` as on that whole chain.
The chain then has no anchor, so it is the chain of `pprev` links that Core walks.
`ancestorView_congr_chain` proves the equality without the height-0 hypothesis, for a chain that ends at an anchor.
-/
theorem ancestorView_congr (network : WorkNetwork) (index : HeaderIndex)
    (wf : WellFormed network index) (hash : Hash256) (prev : IndexEntry)
    (found : index.lookup hash = some prev)
    (_reaches : (ancestorChain index prev).getLast?.map BlockIndex.nHeight = some 0)
    (header : PureBlockHeader) (adjustedTime : Int64) (lastCheckpointHeight : Option Nat) :
    contextualCheckBlockHeader network header (ancestorView network index prev) adjustedTime
        lastCheckpointHeight =
      contextualCheckBlockHeader network header (ancestorChain index prev) adjustedTime
        lastCheckpointHeight :=
  ancestorView_congr_chain network index wf hash prev found header adjustedTime lastCheckpointHeight

/-! ## The checkpoint search -/

/-- Let `f c` be `some c.height` for each element `c` that satisfies `q`, and `none` otherwise.
Then the search with `f` gives the height of the first element that satisfies `q`. -/
private theorem findSome?_eq_find?_map (l : List Checkpoint) (f : Checkpoint → Option Nat)
    (q : Checkpoint → Bool) (hf : ∀ c ∈ l, f c = if q c then some c.height else none) :
    l.findSome? f = (l.find? q).map Checkpoint.height := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := hf a (by simp)
    have ht := ih (fun c hc => hf c (by simp [hc]))
    rw [List.findSome?_cons, List.find?_cons, ha]
    cases q a <;> simp [ht]

/-- Two predicates that agree on every element of a list find the same element. -/
private theorem find?_congr_mem (l : List Checkpoint) (p q : Checkpoint → Bool)
    (h : ∀ c ∈ l, p c = q c) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.find?_cons, List.find?_cons, h a (by simp), ih (fun c hc => h c (by simp [hc]))]

/-- In a list whose heights increase strictly, two elements with the same height are the same element. -/
private theorem eq_of_height_eq (l : List Checkpoint) (sorted : l.Pairwise (fun a b => a.height < b.height))
    (a b : Checkpoint) (ha : a ∈ l) (hb : b ∈ l) (height : a.height = b.height) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    rw [List.pairwise_cons] at sorted
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · have := sorted.1 b hb; omega
    · have := sorted.1 a ha; omega
    · exact ih sorted.2 ha hb

/-- Two entries of a network's checkpoint table with the same height are the same entry. -/
private theorem checkpoint_eq_of_height_eq (network : WorkNetwork) (a b : Checkpoint)
    (ha : a ∈ checkpoints network) (hb : b ∈ checkpoints network) (height : a.height = b.height) :
    a = b := by
  have sorted := checkpointHeights_sorted network
  unfold checkpointHeights at sorted
  rw [List.pairwise_map] at sorted
  exact eq_of_height_eq _ sorted a b ha hb height

/--
The target `lastCheckpointInIndex_eq` of design record 0008, section 11.
Let the index be well formed, and suppose that each table hash in the index belongs to an entry at its table height.
Then for every network and enabled flag, `lastCheckpointInIndex` equals `lastCheckpoint` of design record 0006.
That function takes the table heights whose hashes the index has, `checkpointHeightsInIndex`.
The hypothesis on heights is the hash commitment assumption of design record 0006, stated for this index.
The proof does not use `WellFormed`.
-/
theorem lastCheckpointInIndex_eq (network : WorkNetwork) (enabled : Bool) (index : HeaderIndex)
    (_wf : WellFormed network index)
    (heights : ∀ checkpoint ∈ checkpoints network, ∀ hash entry, checkpoint.blockHash? = some hash →
      index.lookup hash = some entry → entry.height = checkpoint.height) :
    lastCheckpointInIndex network enabled index =
      lastCheckpoint network enabled (checkpointHeightsInIndex network index) := by
  unfold lastCheckpointInIndex lastCheckpoint
  cases enabled
  · rfl
  · simp only [ite_true]
    rw [findSome?_eq_find?_map _ _ fun c => (c.blockHash?.bind index.lookup).isSome]
    · congr 1
      apply find?_congr_mem
      intro c hc
      rw [List.mem_reverse] at hc
      apply Bool.eq_iff_iff.mpr
      rw [List.contains_iff_mem]
      simp only [checkpointHeightsInIndex, List.mem_map, List.mem_filter]
      constructor
      · intro found
        exact ⟨c, ⟨hc, found⟩, rfl⟩
      · rintro ⟨c', ⟨hc', found⟩, height⟩
        rwa [checkpoint_eq_of_height_eq network c' c hc' hc height] at found
    · intro c hc
      rw [List.mem_reverse] at hc
      cases hh : c.blockHash? with
      | none => simp
      | some hash =>
        cases hl : index.lookup hash with
        | none => simp [hl]
        | some entry => simp [hl, heights c hc hash entry hh hl]

/-! ## The executable check of `WellFormed` -/

/-- An entry that the lookup finds is a pair of the list. -/
private theorem mem_of_lookup {index : HeaderIndex} {hash : Hash256} {entry : IndexEntry}
    (found : index.lookup hash = some entry) : (hash, entry) ∈ index.entries := by
  obtain ⟨l₁, l₂, eq, -⟩ := List.lookup_eq_some_iff.mp found
  rw [eq]; simp

/--
For every network and index, `checkWellFormed` returns true exactly when the index satisfies `WellFormed`.
-/
theorem checkWellFormed_iff (network : WorkNetwork) (index : HeaderIndex) :
    checkWellFormed network index = true ↔ WellFormed network index := by
  simp only [checkWellFormed, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨entries, failed⟩
    have entryOk : ∀ hash entry, index.lookup hash = some entry → wellFormedEntry network index hash entry = true := by
      intro hash entry found
      have := entries (hash, entry) (mem_of_lookup found)
      simpa [found] using this
    constructor
    · intro hash entry found
      have := entryOk hash entry found
      simp only [wellFormedEntry, Bool.and_eq_true, beq_iff_eq] at this
      exact this.1.1
    · intro hash entry prev found link
      have := entryOk hash entry found
      simp only [wellFormedEntry, link, Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] at this
      obtain ⟨⟨-, hp, parent, hparent, height⟩, -⟩ := this
      exact ⟨hp, parent, hparent, by simpa using height⟩
    · intro hash entry found none zero
      have := entryOk hash entry found
      simp only [wellFormedEntry, none, zero, Bool.and_eq_true, beq_iff_eq] at this
      simpa using this.1.2
    · intro hash entry found
      have := entryOk hash entry found
      simp only [wellFormedEntry, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    · intro hash mem
      have := failed hash mem
      simp only [Option.any_eq_true] at this
      obtain ⟨entry, found, valid⟩ := this
      exact ⟨entry, found, valid⟩
  · intro wf
    refine ⟨?_, ?_⟩
    · intro pair _
      by_cases found : index.lookup pair.1 = some pair.2
      · simp only [found, bne_self_eq_false, Bool.false_or]
        simp only [wellFormedEntry, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        refine ⟨⟨wf.keyHash _ _ found, ?_⟩, wf.heightBound _ _ found⟩
        cases link : pair.2.prev with
        | some prev =>
          obtain ⟨hp, parent, hparent, height⟩ := wf.prevLink _ _ prev found link
          simp [hp, hparent, height]
        | none =>
          by_cases zero : pair.2.height = 0
          · simp [wf.genesis _ _ found link zero]
          · simp [zero]
      · simp [found]
    · intro hash mem
      obtain ⟨entry, found, valid⟩ := wf.failedListed hash mem
      simp [found, valid]

/-! ## One step: errors of the contextual check -/

/-- Let `error` be an error of the contextual check, and `r` a rejection.
The step error of step 5 is the rejection `r` exactly when `r` is `contextual error` and `error` is a Core rejection. -/
theorem HeaderStepError.ofContextual_eq_rejection_iff (error : ContextualHeaderError) (r : HeaderRejection) :
    HeaderStepError.ofContextual error = .rejection r ↔ r = .contextual error ∧ error.isRejection = true := by
  cases error <;> simp [HeaderStepError.ofContextual, ContextualHeaderError.isRejection, eq_comm]

/-- For every error of the contextual check, the step error of step 5 is not `heightOutOfRange`. -/
theorem HeaderStepError.ofContextual_ne_heightOutOfRange (error : ContextualHeaderError) :
    HeaderStepError.ofContextual error ≠ .adapter .heightOutOfRange := by
  cases error <;> simp [HeaderStepError.ofContextual, ContextualHeaderError.isRejection]

/-- Splits every branch of `acceptBlockHeader` and closes the branches whose hypotheses decide the goal. -/
local macro "accept_cases" : tactic => `(tactic| (
  repeat' split
  all_goals (try simp_all [HeaderStepError.ofContextual_eq_rejection_iff])
  all_goals first
    | done
    | (intros; omega)
    | (constructor <;> intro h <;> obtain ⟨h₁, h₂⟩ := h <;> subst h₁ <;> exact ⟨rfl, h₂⟩)))

section Step

variable (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader)

/-! ## One step: known hashes and genesis -/

/--
The target `accept_known` of design record 0008, section 11.
Let the index be well formed, and let it have an entry under the hash of the header, which is not the network's genesis hash.
If the entry has no failure flag, the step accepts the hash and returns the input index.
If the entry has a failure flag, the step returns `duplicate` and the input index.
The step does not check the proof of work or the AuxPoW payload of a known header (item 6).
-/
theorem accept_known (_wf : WellFormed ctx.network index) (entry : IndexEntry)
    (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash)
    (known : index.lookup header.pure.getHash = some entry) :
    (entry.isFailed = false → acceptBlockHeader ctx index header = (index, .ok header.pure.getHash)) ∧
    (entry.isFailed = true →
      acceptBlockHeader ctx index header = (index, .error (.rejection .duplicate))) := by
  constructor <;> intro failed <;> simp [acceptBlockHeader, notGenesis, known, failed]

/--
Let the hash of the header be the network's genesis hash, and let the index have an entry under it.
Then the step accepts the hash and returns the input index, even when the entry has a failure flag (item 1).
-/
theorem accept_genesis_known (_wf : WellFormed ctx.network index) (entry : IndexEntry)
    (genesis : genesisHash? ctx.network = some header.pure.getHash)
    (known : index.lookup header.pure.getHash = some entry) :
    acceptBlockHeader ctx index header = (index, .ok header.pure.getHash) := by
  simp [acceptBlockHeader, genesis, known]

/--
Let the hash of the header be the network's genesis hash, and let the index have neither that hash nor the header's `hashPrevBlock`.
Then the step accepts the hash and inserts an entry with no predecessor, height 0 and no flags.
Design record 0008, section 13.1, names this theorem as one of the three that replace the target `accept_genesis`.
The real genesis header has the null `hashPrevBlock` (item 2).

The theorem also covers a genesis header whose `hashPrevBlock` is its own hash, for example with an empty index.
Core links that entry to itself at height 1, and the model inserts a root at height 0, a difference that section 13.1 accepts.
-/
theorem accept_genesis_insert (_wf : WellFormed ctx.network index)
    (genesis : genesisHash? ctx.network = some header.pure.getHash)
    (unknown : index.lookup header.pure.getHash = none)
    (noParent : index.lookup header.pure.hashPrevBlock = none) :
    acceptBlockHeader ctx index header =
      (index.insert header.pure.getHash ⟨header.pure, 0, none, false, false, false⟩, .ok header.pure.getHash) := by
  simp [acceptBlockHeader, addToBlockIndex, genesis, unknown, noParent]

/--
Let the hash of the header be the network's genesis hash, and let the index lack that hash.
Let the index have an entry `parent` under the header's `hashPrevBlock`.
Then `addToBlockIndex` links the new entry to `parent`, as Core's `AddToBlockIndex` does (D33, lines 2772 to 2778).
If `parent` is at `maxPrevHeight` or above, the step returns `heightOutOfRange` and the input index (decision 17).
The hypotheses exclude a header whose `hashPrevBlock` is its own hash: `accept_genesis_insert` covers that header.
-/
theorem accept_genesis_parent (_wf : WellFormed ctx.network index)
    (genesis : genesisHash? ctx.network = some header.pure.getHash)
    (unknown : index.lookup header.pure.getHash = none) (parent : IndexEntry)
    (found : index.lookup header.pure.hashPrevBlock = some parent) :
    acceptBlockHeader ctx index header =
      if maxPrevHeight ≤ parent.height then (index, .error (.adapter .heightOutOfRange))
      else (index.insert header.pure.getHash
          ⟨header.pure, parent.height + 1, some header.pure.hashPrevBlock, false, false, false⟩,
        .ok header.pure.getHash) := by
  simp [acceptBlockHeader, addToBlockIndex, genesis, unknown, found]

/-- For every context, index and header, a hash that the step accepts is the hash of the header. -/
theorem accept_ok_hash (result : Hash256) (ok : (acceptBlockHeader ctx index header).2 = .ok result) :
    result = header.pure.getHash := by
  simp only [acceptBlockHeader] at ok
  revert ok
  repeat' split
  all_goals (intro ok; simp_all)

/-! ## One step: acceptance -/

/--
The target `accept_eq_ok_iff` of design record 0008, section 11.
Let the index be well formed, and let the hash of the header be unknown and not the network's genesis hash.
The step accepts exactly when five conditions hold:

1. Step 2 passes: `checkBlockHeader` accepts the full header.
2. The index has a predecessor under `hashPrevBlock`, and it has no failure flag.
3. The predecessor's height is below `maxPrevHeight`, 2147483646.
4. The contextual check accepts on the view and the last checkpoint of section 5.4.
5. The predecessor has `scriptsValid`, or no member of the failed list is its ancestor.
-/
theorem accept_eq_ok_iff (_wf : WellFormed ctx.network index)
    (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash)
    (unknown : index.lookup header.pure.getHash = none) :
    (acceptBlockHeader ctx index header).2 = .ok header.pure.getHash ↔
      checkBlockHeader ctx.network header = .ok () ∧
      ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧ prev.isFailed = false ∧
        prev.height < maxPrevHeight ∧ contextualCheckInIndex ctx index header.pure prev = .ok () ∧
        (prev.scriptsValid = true ∨
          ∀ member ∈ index.failedBlocks, isAncestorInIndex index header.pure.hashPrevBlock prev member = false) := by
  simp only [acceptBlockHeader, notGenesis, unknown, ite_false]
  cases hc : checkBlockHeader ctx.network header with
  | error e => simp
  | ok u =>
    cases hp : index.lookup header.pure.hashPrevBlock with
    | none => simp
    | some prev =>
      cases hf : prev.isFailed
      · by_cases hh : maxPrevHeight ≤ prev.height
        · simp [hf, hh, Nat.not_lt.mpr hh]
        · cases hcc : contextualCheckInIndex ctx index header.pure prev with
          | error e => simp [hf, hh, hcc]
          | ok u' =>
            have lt : prev.height < maxPrevHeight := Nat.lt_of_not_le hh
            cases hs : prev.scriptsValid
            · cases ha : failedAncestor? index header.pure.hashPrevBlock prev with
              | some f =>
                simp only [hf, hh, hcc, hs, ha, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff,
                  Option.some.injEq, exists_eq_left', true_and, false_or, lt]
                intro all
                have := all f (List.mem_of_find?_eq_some ha)
                have := List.find?_some ha
                simp_all
              | none =>
                simp only [hf, hh, hcc, hs, ha, Bool.false_eq_true, ite_false, true_iff,
                  Option.some.injEq, exists_eq_left', true_and, false_or, lt]
                intro member mem
                have := List.find?_eq_none.mp ha member mem
                simpa using this
            · simp [hf, hh, hcc, hs, lt]
      · simp [hf]

/-- For a hash other than genesis, an acceptance returns the hash of the header.
If the hash was unknown, the index has the predecessor below `maxPrevHeight`, and the result index is `addToBlockIndex` of the input index. -/
theorem accept_unknown_ok (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash)
    (result : Hash256) (ok : (acceptBlockHeader ctx index header).2 = .ok result) :
    result = header.pure.getHash ∧
    (index.lookup header.pure.getHash = none →
      ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧ prev.height < maxPrevHeight ∧
        (acceptBlockHeader ctx index header).1 = addToBlockIndex index header.pure) := by
  simp only [acceptBlockHeader, notGenesis, ite_false] at ok ⊢
  revert ok
  repeat' split
  all_goals (try simp_all)
  all_goals (intro h₁ h₂; subst h₁; simp_all)

/-- For an unknown hash with an entry `prev` under `hashPrevBlock`, `addToBlockIndex` inserts an entry linked to `prev`, at `prev`'s height plus one, without flags. -/
theorem addToBlockIndex_of_unknown (header : PureBlockHeader) (prev : IndexEntry)
    (unknown : index.lookup header.getHash = none)
    (found : index.lookup header.hashPrevBlock = some prev) :
    addToBlockIndex index header =
      index.insert header.getHash ⟨header, prev.height + 1, some header.hashPrevBlock, false, false, false⟩ := by
  simp [addToBlockIndex, unknown, found]

/--
The target `accept_ok_insert` of design record 0008, section 11.
Let the index be well formed, and let the step accept an unknown hash other than genesis.
Then the result index is the input index with one inserted entry under the hash.
The entry has the predecessor hash `hashPrevBlock`, the predecessor's height plus one and no flags.
The failed list does not change.
-/
theorem accept_ok_insert (_wf : WellFormed ctx.network index)
    (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash)
    (unknown : index.lookup header.pure.getHash = none)
    (result : Hash256) (ok : (acceptBlockHeader ctx index header).2 = .ok result) :
    ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧
      (acceptBlockHeader ctx index header).1 = index.insert header.pure.getHash
        ⟨header.pure, prev.height + 1, some header.pure.hashPrevBlock, false, false, false⟩ ∧
      (acceptBlockHeader ctx index header).1.failedBlocks = index.failedBlocks := by
  obtain ⟨-, step⟩ := accept_unknown_ok ctx index header notGenesis result ok
  obtain ⟨prev, found, -, eq⟩ := step unknown
  rw [eq, addToBlockIndex_of_unknown index header.pure prev unknown found]
  exact ⟨prev, found, rfl, rfl⟩

/--
The target `accept_link` of design record 0008, section 11.
Let the index be well formed, and let the step accept an unknown hash other than genesis.
Then the result index has an entry under the hash.
Its predecessor hash is the header's `hashPrevBlock`, and its height is the height of the predecessor's entry plus one.
-/
theorem accept_link (wf : WellFormed ctx.network index)
    (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash)
    (unknown : index.lookup header.pure.getHash = none)
    (result : Hash256) (ok : (acceptBlockHeader ctx index header).2 = .ok result) :
    ∃ entry prev, (acceptBlockHeader ctx index header).1.lookup header.pure.getHash = some entry ∧
      index.lookup header.pure.hashPrevBlock = some prev ∧
      entry.prev = some header.pure.hashPrevBlock ∧ entry.height = prev.height + 1 := by
  obtain ⟨prev, found, eq, -⟩ := accept_ok_insert ctx index header wf notGenesis unknown result ok
  exact ⟨_, prev, by rw [eq, HeaderIndex.lookup_insert_self], found, rfl, rfl⟩

/-! ## One step: rejections -/

/-- Step 1, for a hash other than genesis.
The step returns `duplicate` exactly when the index has an entry under the hash with a failure flag. -/
theorem accept_eq_duplicate_iff (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash) :
    (acceptBlockHeader ctx index header).2 = .error (.rejection .duplicate) ↔
      ∃ entry, index.lookup header.pure.getHash = some entry ∧ entry.isFailed = true := by
  simp only [acceptBlockHeader, notGenesis, ite_false]
  accept_cases

/-- Step 2, for a hash other than genesis.
The step returns `highHash error` exactly when the hash is unknown and `checkBlockHeader` returns `error`. -/
theorem accept_eq_highHash_iff (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash)
    (error : CheckPowError) :
    (acceptBlockHeader ctx index header).2 = .error (.rejection (.highHash error)) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .error error := by
  simp only [acceptBlockHeader, notGenesis, ite_false]
  accept_cases

/-- Step 3, for a hash other than genesis.
The step returns `prevBlockNotFound` exactly when the hash is unknown, step 2 passes and the index lacks `hashPrevBlock`. -/
theorem accept_eq_prevBlockNotFound_iff (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash) :
    (acceptBlockHeader ctx index header).2 = .error (.rejection .prevBlockNotFound) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .ok () ∧
      index.lookup header.pure.hashPrevBlock = none := by
  simp only [acceptBlockHeader, notGenesis, ite_false]
  accept_cases

/-- Step 4, for a hash other than genesis.
The step returns `prevBlockInvalid` exactly when the hash is unknown and step 2 passes, and the predecessor has a failure flag. -/
theorem accept_eq_prevBlockInvalid_iff (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash) :
    (acceptBlockHeader ctx index header).2 = .error (.rejection .prevBlockInvalid) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .ok () ∧
      ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧ prev.isFailed = true := by
  simp only [acceptBlockHeader, notGenesis, ite_false]
  accept_cases

/--
The companion of the target `accept_eq_error_iff` of design record 0008, section 11.
Let the index be well formed, and let the hash of the header not be the genesis hash.
The step returns `heightOutOfRange` exactly when steps 1 to 4 pass and the predecessor is at height `maxPrevHeight`, 2147483646.
-/
theorem accept_eq_heightOutOfRange_iff (wf : WellFormed ctx.network index)
    (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash) :
    (acceptBlockHeader ctx index header).2 = .error (.adapter .heightOutOfRange) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .ok () ∧
      ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧ prev.isFailed = false ∧
        prev.height = maxPrevHeight := by
  have bound := wf.heightBound header.pure.hashPrevBlock
  simp only [acceptBlockHeader, notGenesis, ite_false]
  repeat' split
  all_goals (try simp_all [HeaderStepError.ofContextual_ne_heightOutOfRange, maxPrevHeight])
  all_goals omega

/-- Step 5, for a hash other than genesis.
The step returns the rejection `contextual error` exactly when four conditions hold.
Steps 1 to 4 pass, and the predecessor is below `maxPrevHeight`.
The contextual check returns `error`, and `error` is a Core rejection. -/
theorem accept_eq_contextual_iff (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash)
    (error : ContextualHeaderError) :
    (acceptBlockHeader ctx index header).2 = .error (.rejection (.contextual error)) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .ok () ∧
      ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧ prev.isFailed = false ∧
        prev.height < maxPrevHeight ∧ contextualCheckInIndex ctx index header.pure prev = .error error ∧
        error.isRejection = true := by
  simp only [acceptBlockHeader, notGenesis, ite_false]
  accept_cases

/-- Step 6, for a hash other than genesis.
The step returns `failedAncestor failed` exactly when steps 1 to 5 pass and the predecessor is below `maxPrevHeight`.
The predecessor must also lack `scriptsValid`.
`failed` is then the first member of the failed list that is an ancestor of the predecessor. -/
theorem accept_eq_failedAncestor_iff (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash)
    (failed : Hash256) :
    (acceptBlockHeader ctx index header).2 = .error (.rejection (.failedAncestor failed)) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .ok () ∧
      ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧ prev.isFailed = false ∧
        prev.height < maxPrevHeight ∧ contextualCheckInIndex ctx index header.pure prev = .ok () ∧
        prev.scriptsValid = false ∧ failedAncestor? index header.pure.hashPrevBlock prev = some failed := by
  simp only [acceptBlockHeader, notGenesis, ite_false]
  accept_cases

/--
The target `accept_eq_error_iff` of design record 0008, section 11.
Let the index be well formed, and let the hash of the header not be the genesis hash.
For each rejection of section 3.1, the step returns it exactly when its condition fails and the conditions of all earlier steps hold.
For steps 5 and 6, the earlier conditions include the height bound of `heightOutOfRange`.
`accept_eq_heightOutOfRange_iff` is the companion statement for `heightOutOfRange`.
-/
theorem accept_eq_error_iff (_wf : WellFormed ctx.network index)
    (notGenesis : genesisHash? ctx.network ≠ some header.pure.getHash) :
    ((acceptBlockHeader ctx index header).2 = .error (.rejection .duplicate) ↔
      ∃ entry, index.lookup header.pure.getHash = some entry ∧ entry.isFailed = true) ∧
    (∀ error, (acceptBlockHeader ctx index header).2 = .error (.rejection (.highHash error)) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .error error) ∧
    ((acceptBlockHeader ctx index header).2 = .error (.rejection .prevBlockNotFound) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .ok () ∧
      index.lookup header.pure.hashPrevBlock = none) ∧
    ((acceptBlockHeader ctx index header).2 = .error (.rejection .prevBlockInvalid) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .ok () ∧
      ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧ prev.isFailed = true) ∧
    (∀ error, (acceptBlockHeader ctx index header).2 = .error (.rejection (.contextual error)) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .ok () ∧
      ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧ prev.isFailed = false ∧
        prev.height < maxPrevHeight ∧ contextualCheckInIndex ctx index header.pure prev = .error error ∧
        error.isRejection = true) ∧
    (∀ failed, (acceptBlockHeader ctx index header).2 = .error (.rejection (.failedAncestor failed)) ↔
      index.lookup header.pure.getHash = none ∧ checkBlockHeader ctx.network header = .ok () ∧
      ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧ prev.isFailed = false ∧
        prev.height < maxPrevHeight ∧ contextualCheckInIndex ctx index header.pure prev = .ok () ∧
        prev.scriptsValid = false ∧ failedAncestor? index header.pure.hashPrevBlock prev = some failed) :=
  ⟨accept_eq_duplicate_iff ctx index header notGenesis,
    accept_eq_highHash_iff ctx index header notGenesis,
    accept_eq_prevBlockNotFound_iff ctx index header notGenesis,
    accept_eq_prevBlockInvalid_iff ctx index header notGenesis,
    accept_eq_contextual_iff ctx index header notGenesis,
    accept_eq_failedAncestor_iff ctx index header notGenesis⟩

end Step

/-! ## The marks of step 6 -/

/-- For every index, list of hashes and key, `markFailedChild` keeps the lookup of the key.
It sets `failedChild` on the entry when the key is in the list. -/
theorem lookup_markFailedChild (index : HeaderIndex) (hashes : List Hash256) (key : Hash256) :
    (markFailedChild index hashes).lookup key =
      (index.lookup key).map fun entry =>
        if key ∈ hashes then { entry with failedChild := true } else entry := by
  induction hashes generalizing index with
  | nil => simp [markFailedChild]
  | cons hash rest ih =>
    simp only [markFailedChild, List.foldl_cons] at ih ⊢
    rw [ih]
    cases found : index.lookup hash with
    | none =>
      by_cases same : key = hash
      · subst same; simp [found]
      · simp [same]
    | some entry =>
      by_cases same : key = hash
      · subst same; simp [found, HeaderIndex.lookup_insert_self]
      · simp only
        rw [HeaderIndex.lookup_insert_of_ne _ _ _ _ same]
        simp [same]

/-- For every index and list of hashes, `markFailedChild` does not change the failed list. -/
theorem markFailedChild_failedBlocks (index : HeaderIndex) (hashes : List Hash256) :
    (markFailedChild index hashes).failedBlocks = index.failedBlocks := by
  induction hashes generalizing index with
  | nil => rfl
  | cons hash rest ih =>
    simp only [markFailedChild, List.foldl_cons] at ih ⊢
    rw [ih]
    split <;> rfl

/-- For every context, index and header, an error other than `failedAncestor` returns the input index. -/
theorem accept_error_index_other (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader)
    (error : HeaderStepError) (err : (acceptBlockHeader ctx index header).2 = .error error)
    (notFailed : ∀ failed, error ≠ .rejection (.failedAncestor failed)) :
    (acceptBlockHeader ctx index header).1 = index := by
  simp only [acceptBlockHeader] at err ⊢
  revert err
  repeat' split
  all_goals intro h
  all_goals first
    | rfl
    | (simp at h; done)
    | (simp only at h; injection h with h; exact absurd h.symm (notFailed _))

/-- For every context, index and header, the rejection `failedAncestor failed` returns `markFailedChild` of the input index.
The marked keys are `failedChildPath` from the predecessor down to `failed`. -/
theorem accept_error_failedAncestor (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader)
    (failed : Hash256)
    (err : (acceptBlockHeader ctx index header).2 = .error (.rejection (.failedAncestor failed))) :
    ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧
      (acceptBlockHeader ctx index header).1 =
        markFailedChild index (failedChildPath index (prev.height + 1) header.pure.hashPrevBlock prev failed) := by
  simp only [acceptBlockHeader] at err ⊢
  revert err
  repeat' split
  all_goals (try simp_all [HeaderStepError.ofContextual_eq_rejection_iff])

/--
The target `accept_error_index` of design record 0008, section 11.
Let the index be well formed, and let the step return an error.
On an adapter error, and on a rejection other than `failedAncestor`, the result index is the input index.
On `failedAncestor failed`, the failed list does not change, and only `failedChild` changes.
It becomes true on the keys of `failedChildPath`: the entries from the predecessor down the predecessor links to `failed`, without `failed`.
-/
theorem accept_error_index (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader)
    (_wf : WellFormed ctx.network index) (error : HeaderStepError)
    (err : (acceptBlockHeader ctx index header).2 = .error error) :
    ((∀ failed, error ≠ .rejection (.failedAncestor failed)) →
      (acceptBlockHeader ctx index header).1 = index) ∧
    (∀ failed, error = .rejection (.failedAncestor failed) →
      ∃ prev, index.lookup header.pure.hashPrevBlock = some prev ∧
        (acceptBlockHeader ctx index header).1.failedBlocks = index.failedBlocks ∧
        ∀ key, (acceptBlockHeader ctx index header).1.lookup key =
          (index.lookup key).map fun entry =>
            if key ∈ failedChildPath index (prev.height + 1) header.pure.hashPrevBlock prev failed then
              { entry with failedChild := true }
            else entry) := by
  refine ⟨accept_error_index_other ctx index header error err, ?_⟩
  intro failed same
  subst same
  obtain ⟨prev, found, eq⟩ := accept_error_failedAncestor ctx index header failed err
  refine ⟨prev, found, ?_, fun key => ?_⟩
  · rw [eq, markFailedChild_failedBlocks]
  · rw [eq, lookup_markFailedChild]

/-! ## Well-formed indexes after a step -/

/-- For every index, hash, key and entry, the lookup after an insertion is the inserted entry for the inserted hash and the earlier lookup otherwise. -/
theorem HeaderIndex.lookup_insert (index : HeaderIndex) (hash key : Hash256) (entry : IndexEntry) :
    (index.insert hash entry).lookup key = if key = hash then some entry else index.lookup key := by
  by_cases same : key = hash
  · subst same; simp [HeaderIndex.lookup_insert_self]
  · simp [same, HeaderIndex.lookup_insert_of_ne _ _ _ _ same]

/--
Let the index be well formed, and let it lack `hash`.
Suppose that the entry meets the conditions of `WellFormed`.
Its header hashes to `hash`, and its predecessor link meets the condition on links.
Without a predecessor at height 0, `hash` is the genesis hash, and its height is below 2147483647.
Then the index with the entry inserted under `hash` is well formed.
-/
theorem wellFormed_insert {network : WorkNetwork} (index : HeaderIndex) (wf : WellFormed network index)
    (hash : Hash256) (entry : IndexEntry) (unknown : index.lookup hash = none)
    (hkey : entry.header.getHash = hash)
    (hlink : ∀ prev, entry.prev = some prev → entry.header.hashPrevBlock = prev ∧
      ∃ parent, index.lookup prev = some parent ∧ entry.height = parent.height + 1)
    (hgen : entry.prev = none → entry.height = 0 → genesisHash? network = some hash)
    (hbound : entry.height < 2147483647) :
    WellFormed network (index.insert hash entry) := by
  have ne : ∀ key e, index.lookup key = some e → key ≠ hash := by
    intro key e found same; subst same; simp [unknown] at found
  constructor
  · intro key e found
    rw [HeaderIndex.lookup_insert] at found
    split at found
    · next same => cases found; subst same; exact hkey
    · exact wf.keyHash key e found
  · intro key e prev found link
    rw [HeaderIndex.lookup_insert] at found
    split at found
    · cases found
      obtain ⟨hp, parent, hparent, height⟩ := hlink prev link
      refine ⟨hp, parent, ?_, height⟩
      rw [HeaderIndex.lookup_insert_of_ne _ _ _ _ (ne prev parent hparent)]; exact hparent
    · obtain ⟨hp, parent, hparent, height⟩ := wf.prevLink key e prev found link
      refine ⟨hp, parent, ?_, height⟩
      rw [HeaderIndex.lookup_insert_of_ne _ _ _ _ (ne prev parent hparent)]; exact hparent
  · intro key e found none zero
    rw [HeaderIndex.lookup_insert] at found
    split at found
    · next same => cases found; subst same; exact hgen none zero
    · exact wf.genesis key e found none zero
  · intro key e found
    rw [HeaderIndex.lookup_insert] at found
    split at found
    · cases found; exact hbound
    · exact wf.heightBound key e found
  · intro key mem
    obtain ⟨e, found, valid⟩ := wf.failedListed key mem
    refine ⟨e, ?_, valid⟩
    rw [HeaderIndex.lookup_insert_of_ne _ _ _ _ (ne key e found)]; exact found

/--
Let the index be well formed.
Suppose that an entry under the header's `hashPrevBlock` is below `maxPrevHeight`.
Suppose also that, when the index lacks both `hashPrevBlock` and the header's hash, that hash is the genesis hash.
Then `addToBlockIndex` gives a well-formed index.
-/
theorem wellFormed_addToBlockIndex {network : WorkNetwork} (index : HeaderIndex)
    (wf : WellFormed network index) (header : PureBlockHeader)
    (bound : ∀ parent, index.lookup header.hashPrevBlock = some parent → parent.height < maxPrevHeight)
    (genesis : index.lookup header.hashPrevBlock = none → index.lookup header.getHash = none →
      genesisHash? network = some header.getHash) :
    WellFormed network (addToBlockIndex index header) := by
  simp only [addToBlockIndex]
  split
  · exact wf
  · next hk =>
    split
    · next parent hp =>
      have := bound parent hp
      refine wellFormed_insert index wf _ _ hk rfl ?_ (by simp) (by simp only [maxPrevHeight] at this ⊢; omega)
      intro prev link
      simp only [Option.some.injEq] at link
      subst link
      exact ⟨rfl, parent, hp, rfl⟩
    · next hp =>
      exact wellFormed_insert index wf _ _ hk rfl (by simp) (fun _ _ => genesis hp hk) (by simp)

/--
Let `index` be well formed, and let `index'` have the same failed list.
Suppose that each lookup in `index'` gives an entry exactly when the lookup in `index` does, with the same header, height, predecessor and `failedValid`.
Then `index'` is well formed: `WellFormed` reads no other field.
-/
theorem wellFormed_of_shape {network : WorkNetwork} {index index' : HeaderIndex}
    (wf : WellFormed network index) (failed : index'.failedBlocks = index.failedBlocks)
    (same : ∀ key, (index'.lookup key).map (fun e => (e.header, e.height, e.prev, e.failedValid)) =
      (index.lookup key).map (fun e => (e.header, e.height, e.prev, e.failedValid))) :
    WellFormed network index' := by
  have back : ∀ key e', index'.lookup key = some e' → ∃ e, index.lookup key = some e ∧
      e'.header = e.header ∧ e'.height = e.height ∧ e'.prev = e.prev ∧ e'.failedValid = e.failedValid := by
    intro key e' found
    have := same key
    rw [found] at this
    cases hk : index.lookup key with
    | none => simp [hk] at this
    | some e =>
      simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨e, rfl, this⟩
  have fwd : ∀ key e, index.lookup key = some e → ∃ e', index'.lookup key = some e' ∧
      e'.height = e.height ∧ e'.failedValid = e.failedValid := by
    intro key e found
    have := same key
    rw [found] at this
    cases hk : index'.lookup key with
    | none => simp [hk] at this
    | some e' =>
      simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨e', rfl, this.2.1, this.2.2.2⟩
  constructor
  · intro key e' found
    obtain ⟨e, he, header, -⟩ := back key e' found
    rw [header]; exact wf.keyHash key e he
  · intro key e' prev found link
    obtain ⟨e, he, header, height, hprev, -⟩ := back key e' found
    rw [hprev] at link
    obtain ⟨hp, parent, hparent, hheight⟩ := wf.prevLink key e prev he link
    obtain ⟨parent', hp', hph, -⟩ := fwd prev parent hparent
    exact ⟨header ▸ hp, parent', hp', by omega⟩
  · intro key e' found none zero
    obtain ⟨e, he, -, height, hprev, -⟩ := back key e' found
    exact wf.genesis key e he (hprev ▸ none) (height ▸ zero)
  · intro key e' found
    obtain ⟨e, he, -, height, -⟩ := back key e' found
    rw [height]; exact wf.heightBound key e he
  · intro key mem
    rw [failed] at mem
    obtain ⟨e, he, valid⟩ := wf.failedListed key mem
    obtain ⟨e', he', -, valid'⟩ := fwd key e he
    exact ⟨e', he', valid' ▸ valid⟩

/-- For every well-formed index and list of hashes, `markFailedChild` gives a well-formed index. -/
theorem wellFormed_markFailedChild {network : WorkNetwork} (index : HeaderIndex)
    (wf : WellFormed network index) (hashes : List Hash256) :
    WellFormed network (markFailedChild index hashes) := by
  refine wellFormed_of_shape wf (markFailedChild_failedBlocks index hashes) fun key => ?_
  rw [lookup_markFailedChild, Option.map_map]
  congr 1
  funext e
  simp only [Function.comp_def]
  split <;> rfl

/--
The target `wellFormed_preserved` of design record 0008, section 11.
For every context and header, the step maps a well-formed index to a well-formed index.
-/
theorem wellFormed_preserved (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader)
    (wf : WellFormed ctx.network index) :
    WellFormed ctx.network (acceptBlockHeader ctx index header).1 := by
  simp only [acceptBlockHeader]
  repeat' split
  all_goals try dsimp only
  all_goals first
    | exact wf
    | exact wellFormed_markFailedChild index wf _
    | (apply wellFormed_addToBlockIndex index wf <;> intros <;> simp_all <;> omega)

/-! ## The order of the failed list -/

/-- For every index and list, the index with another failed list has the same lookups. -/
theorem HeaderIndex.lookup_withFailed (index : HeaderIndex) (l : List Hash256) :
    ({ index with failedBlocks := l } : HeaderIndex).lookup = index.lookup := rfl

/-- For every index, list, fuel and entry, the walk does not read the failed list. -/
theorem ancestorWalk_withFailed (index : HeaderIndex) (l : List Hash256) (n : Nat) (e : IndexEntry) :
    ancestorWalk { index with failedBlocks := l } n e = ancestorWalk index n e := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih => simp only [ancestorWalk, HeaderIndex.lookup_withFailed, ih]

/-- For every context, index, list, header and entry, the contextual check of step 5 does not read the failed list. -/
theorem contextualCheckInIndex_withFailed (ctx : HeaderContext) (index : HeaderIndex) (l : List Hash256)
    (h : PureBlockHeader) (e : IndexEntry) :
    contextualCheckInIndex ctx { index with failedBlocks := l } h e = contextualCheckInIndex ctx index h e := by
  simp only [contextualCheckInIndex, ancestorView, ancestorWalk_withFailed, lastCheckpointInIndex,
    HeaderIndex.lookup_withFailed]

/-- For every index, list, fuel, hash, entry and height, the ancestor walk does not read the failed list. -/
theorem ancestorHashAt_withFailed (index : HeaderIndex) (l : List Hash256) (n : Nat) (h : Hash256)
    (e : IndexEntry) (height : Nat) :
    ancestorHashAt { index with failedBlocks := l } n h e height = ancestorHashAt index n h e height := by
  induction n generalizing h e with
  | zero => rfl
  | succ n ih => simp only [ancestorHashAt, HeaderIndex.lookup_withFailed, ih]

/-- For every index, list, hash and entry, the ancestor test of step 6 does not read the failed list. -/
theorem isAncestorInIndex_withFailed (index : HeaderIndex) (l : List Hash256) (h : Hash256) (e : IndexEntry) :
    isAncestorInIndex { index with failedBlocks := l } h e = isAncestorInIndex index h e := by
  funext member
  simp only [isAncestorInIndex, HeaderIndex.lookup_withFailed, ancestorHashAt_withFailed]

/--
The target `failedAncestor_verdict_perm` of design record 0008, section 11.
Let the index be well formed, and let `failed'` be a permutation of its failed list.
Then the step gives the same verdict and reason with either list.
Either the two results are equal, or both are `failedAncestor`, possibly with different members.
The marks of step 6 can differ (design record 0008, item 16).
-/
theorem failedAncestor_verdict_perm (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader)
    (_wf : WellFormed ctx.network index) (failed' : List Hash256) (perm : index.failedBlocks.Perm failed') :
    (acceptBlockHeader ctx index header).2 =
        (acceptBlockHeader ctx { index with failedBlocks := failed' } header).2 ∨
      ∃ failed failed₂,
        (acceptBlockHeader ctx index header).2 = .error (.rejection (.failedAncestor failed)) ∧
        (acceptBlockHeader ctx { index with failedBlocks := failed' } header).2 =
          .error (.rejection (.failedAncestor failed₂)) := by
  have noneIff : ∀ p : Hash256 → Bool,
      index.failedBlocks.find? p = none ↔ failed'.find? p = none := by
    intro p
    simp only [List.find?_eq_none]
    exact ⟨fun h x mem => h x (perm.mem_iff.mpr mem), fun h x mem => h x (perm.mem_iff.mp mem)⟩
  simp only [acceptBlockHeader, HeaderIndex.lookup_withFailed, contextualCheckInIndex_withFailed,
    failedAncestor?, isAncestorInIndex_withFailed]
  by_cases g : genesisHash? ctx.network = some header.pure.getHash
  · left; simp only [g, ite_true]; repeat' split <;> try rfl
  simp only [g, ite_false]
  cases hk : index.lookup header.pure.getHash with
  | some entry => left; simp only; split <;> rfl
  | none =>
  cases hc : checkBlockHeader ctx.network header with
  | error e => left; simp only
  | ok u =>
  cases hp : index.lookup header.pure.hashPrevBlock with
  | none => left; simp only
  | some prev =>
  cases hf : prev.isFailed
  case true => left; simp [hf]
  by_cases hh : maxPrevHeight ≤ prev.height
  · left; simp [hf, hh]
  cases hcc : contextualCheckInIndex ctx index header.pure prev with
  | error e => left; simp [hf, hh, hcc]
  | ok u' =>
  cases hs : prev.scriptsValid
  case true => left; simp [hf, hh, hcc, hs]
  have rel := noneIff (isAncestorInIndex index header.pure.hashPrevBlock prev)
  cases ha : index.failedBlocks.find? (isAncestorInIndex index header.pure.hashPrevBlock prev) <;>
    cases hb : failed'.find? (isAncestorInIndex index header.pure.hashPrevBlock prev)
  · left; simp [hf, hh, hcc, hs, ha, hb]
  · rw [rel.mp ha] at hb; cases hb
  · rw [rel.mpr hb] at ha; cases ha
  · rename_i first second
    right; exact ⟨first, second, by simp [hf, hh, hcc, hs, ha], by simp [hf, hh, hcc, hs, hb]⟩


/-! ## The sequence: composition -/

/-- For every length and pair of results, the composition with a first result that is an error is the first result. -/
theorem composeSequence_of_error (n : Nat) (first second : HeaderSequenceResult) (error : HeaderSequenceError)
    (err : first.2 = .error error) : composeSequence n first second = first := by
  simp [composeSequence, err]

section Sequence

variable (ctx : HeaderContext)

/--
Take every start position `n`, index, result so far `last` and list.
The loop from position `n` with `last` is the composition of the success `last` with the loop from position 0 and `none`.
-/
theorem processSteps_eq_compose (n : Nat) (index : HeaderIndex) (last : Option Hash256)
    (headers : List BlockHeader) :
    processSteps ctx n index last headers =
      composeSequence n (index, .ok last) (processSteps ctx 0 index none headers) := by
  induction headers generalizing n index last with
  | nil => rfl
  | cons header rest ih =>
    cases hstep : acceptBlockHeader ctx index header with
    | mk index' result =>
      cases result with
      | error e => simp [processSteps, hstep, composeSequence]
      | ok hash =>
        simp only [processSteps, hstep]
        rw [ih (n + 1), ih 1]
        obtain ⟨final, outcome⟩ := processSteps ctx 0 index' none rest
        rcases outcome with e | _ | h
        · simp only [composeSequence]
          rw [Nat.add_assoc, Nat.add_comm 1 n]
        · rfl
        · rfl

/--
For every start position, index, result so far and pair of lists, the loop over `xs ++ ys` runs the loop over `xs`.
If that loop fails, the result is its result.
Otherwise the loop continues over `ys` from its index, at position `p + xs.length`.
-/
theorem processSteps_append (p : Nat) (index : HeaderIndex) (last : Option Hash256)
    (xs ys : List BlockHeader) :
    processSteps ctx p index last (xs ++ ys) =
      match (processSteps ctx p index last xs).2 with
      | .error _ => processSteps ctx p index last xs
      | .ok last' => processSteps ctx (p + xs.length) (processSteps ctx p index last xs).1 last' ys := by
  induction xs generalizing p index last with
  | nil => simp [processSteps]
  | cons header rest ih =>
    cases hstep : acceptBlockHeader ctx index header with
    | mk index' result =>
      cases result with
      | error e => simp [processSteps, hstep]
      | ok hash =>
        simp only [List.cons_append, processSteps, hstep, List.length_cons]
        rw [ih, show p + 1 + rest.length = p + (rest.length + 1) by omega]

/-- For every start position, result so far and list, the loop keeps a well-formed index well formed, also when a step fails. -/
theorem wellFormed_processSteps (p : Nat) (index : HeaderIndex) (last : Option Hash256)
    (headers : List BlockHeader) (wf : WellFormed ctx.network index) :
    WellFormed ctx.network (processSteps ctx p index last headers).1 := by
  induction headers generalizing p index last with
  | nil => exact wf
  | cons header rest ih =>
    have step := wellFormed_preserved ctx index header wf
    cases hstep : acceptBlockHeader ctx index header with
    | mk index' result =>
      rw [hstep] at step
      cases result with
      | error e => simp only [processSteps, hstep]; exact step
      | ok hash => simp only [processSteps, hstep]; exact ih _ _ _ step

/-- For every well-formed index and list, the sequence is the loop from position 0 with `none`: the test of `checkWellFormed` passes. -/
theorem processNewBlockHeaders_of_wellFormed (index : HeaderIndex) (wf : WellFormed ctx.network index)
    (headers : List BlockHeader) :
    processNewBlockHeaders ctx index headers = processSteps ctx 0 index none headers := by
  simp [processNewBlockHeaders, (checkWellFormed_iff ctx.network index).mpr wf]

/-- For every index that fails `WellFormed`, and every list, the sequence returns `notWellFormed` at position 0 with the input index. -/
theorem processNewBlockHeaders_of_not_wellFormed (index : HeaderIndex) (bad : ¬ WellFormed ctx.network index)
    (headers : List BlockHeader) :
    processNewBlockHeaders ctx index headers = (index, .error ⟨0, .adapter .notWellFormed⟩) := by
  have : checkWellFormed ctx.network index = false := by
    cases h : checkWellFormed ctx.network index
    · rfl
    · exact absurd ((checkWellFormed_iff ctx.network index).mp h) bad
  simp [processNewBlockHeaders, this]

/--
The target `process_append` of design record 0008, section 11.
Let the index be well formed.
For every pair of lists, processing `xs ++ ys` gives `composeSequence xs.length` of two results.
The first is the result of `xs`, and the second is the result of `ys` from the index after `xs`.
The theorem needs no height budget.
-/
theorem process_append (index : HeaderIndex) (_wf : WellFormed ctx.network index) (xs ys : List BlockHeader) :
    processNewBlockHeaders ctx index (xs ++ ys) =
      composeSequence xs.length (processNewBlockHeaders ctx index xs)
        (processNewBlockHeaders ctx (processNewBlockHeaders ctx index xs).1 ys) := by
  by_cases wf : WellFormed ctx.network index
  · have after := wellFormed_processSteps ctx 0 index none xs wf
    rw [processNewBlockHeaders_of_wellFormed ctx index wf, processNewBlockHeaders_of_wellFormed ctx index wf,
      processNewBlockHeaders_of_wellFormed ctx _ after, processSteps_append]
    cases h : (processSteps ctx 0 index none xs).2 with
    | error e => simp [composeSequence, h]
    | ok last' =>
      simp only [Nat.zero_add]
      rw [processSteps_eq_compose]
      simp [composeSequence, h]
  · rw [processNewBlockHeaders_of_not_wellFormed ctx index wf, processNewBlockHeaders_of_not_wellFormed ctx index wf]
    rfl

/--
The target `process_error_suffix` of design record 0008, section 11.
Let the index be well formed, and let processing `xs` fail with `error`, at the position that `error` holds.
Then for every list `ys`, processing `xs ++ ys` fails with the same error at the same position.
It also returns the same index.
-/
theorem process_error_suffix (index : HeaderIndex) (wf : WellFormed ctx.network index) (xs ys : List BlockHeader)
    (error : HeaderSequenceError) (fail : (processNewBlockHeaders ctx index xs).2 = .error error) :
    processNewBlockHeaders ctx index (xs ++ ys) = ((processNewBlockHeaders ctx index xs).1, .error error) := by
  rw [process_append ctx index wf, composeSequence_of_error _ _ _ _ fail]
  exact Prod.ext rfl fail

/--
The target `process_prefix_ok` of design record 0008, section 11.
Let the index be well formed.
For every pair of lists, if processing `xs ++ ys` succeeds, processing `xs` succeeds.
-/
theorem process_prefix_ok (index : HeaderIndex) (wf : WellFormed ctx.network index) (xs ys : List BlockHeader)
    (last : Option Hash256) (ok : (processNewBlockHeaders ctx index (xs ++ ys)).2 = .ok last) :
    ∃ last', (processNewBlockHeaders ctx index xs).2 = .ok last' := by
  cases h : (processNewBlockHeaders ctx index xs).2 with
  | ok last' => exact ⟨last', rfl⟩
  | error e =>
    rw [process_error_suffix ctx index wf xs ys e h] at ok
    cases ok

end Sequence

/-! ## The sequence: the index after accepted steps -/

/-- The index after `addToBlockIndex` of each header of a list in order: the index after a sequence of acceptances (`processSteps_ok_index`). -/
def addHeaders (index : HeaderIndex) (headers : List BlockHeader) : HeaderIndex :=
  headers.foldl (fun acc header => addToBlockIndex acc header.pure) index

/-- For every context, index and header, an acceptance returns `addToBlockIndex` of the input index. For a known hash, that is the input index. -/
theorem accept_ok_index (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader) (result : Hash256)
    (ok : (acceptBlockHeader ctx index header).2 = .ok result) :
    (acceptBlockHeader ctx index header).1 = addToBlockIndex index header.pure := by
  simp only [acceptBlockHeader] at ok ⊢
  revert ok
  repeat' split
  all_goals (intro ok; simp_all [addToBlockIndex])

/-- For every context, start position, index, result so far and list, a successful loop returns `addHeaders` of the input index. -/
theorem processSteps_ok_index (ctx : HeaderContext) (p : Nat) (index : HeaderIndex) (last : Option Hash256)
    (headers : List BlockHeader) (result : Option Hash256)
    (ok : (processSteps ctx p index last headers).2 = .ok result) :
    (processSteps ctx p index last headers).1 = addHeaders index headers := by
  induction headers generalizing p index last with
  | nil => rfl
  | cons header rest ih =>
    cases hstep : acceptBlockHeader ctx index header with
    | mk index' r =>
      cases r with
      | error e => simp [processSteps, hstep] at ok
      | ok hash =>
        have eq := accept_ok_index ctx index header hash (by rw [hstep])
        rw [hstep] at eq
        simp only [processSteps, hstep] at ok ⊢
        rw [ih _ _ _ ok]
        simp only [addHeaders, List.foldl_cons]
        rw [← eq]

/-- For every index, header, key and entry, `addToBlockIndex` keeps the entry under a key that the index has. -/
theorem lookup_addToBlockIndex_of_some (index : HeaderIndex) (header : PureBlockHeader) (key : Hash256)
    (entry : IndexEntry) (found : index.lookup key = some entry) :
    (addToBlockIndex index header).lookup key = some entry := by
  have ne : index.lookup header.getHash = none → key ≠ header.getHash := by
    intro unknown same; subst same; rw [found] at unknown; cases unknown
  simp only [addToBlockIndex]
  cases hk : index.lookup header.getHash with
  | some _ => exact found
  | none =>
    cases hp : index.lookup header.hashPrevBlock <;>
      (simp only []; rw [HeaderIndex.lookup_insert_of_ne _ _ _ _ (ne hk)]; exact found)

/-- For every index, list, key and entry, `addHeaders` keeps the entry under a key that the index has. -/
theorem lookup_addHeaders_of_some (index : HeaderIndex) (headers : List BlockHeader) (key : Hash256)
    (entry : IndexEntry) (found : index.lookup key = some entry) :
    (addHeaders index headers).lookup key = some entry := by
  induction headers generalizing index with
  | nil => exact found
  | cons header rest ih => exact ih _ (lookup_addToBlockIndex_of_some index header.pure key entry found)


/-! ## The sequence: a linear extension -/

/--
The headers link from `prev` in order.
The first header's `hashPrevBlock` is `prev`, and each later header's `hashPrevBlock` is the hash of the header before it.
-/
def LinksFrom : Hash256 → List BlockHeader → Prop
  | _, [] => True
  | prev, header :: rest => header.pure.hashPrevBlock = prev ∧ LinksFrom header.pure.getHash rest

/--
The view entries of headers that extend an entry at height `base`, newest first.
The header at position `j` of the list becomes `⟨base + j + 1, nTime, nBits⟩`.
-/
def linearView (base : Nat) (headers : List BlockHeader) : List BlockIndex :=
  (headers.mapIdx fun j header => ⟨base + j + 1, header.pure.nTime, header.pure.nBits⟩).reverse

/-- For every height, header and list, the view of `header :: rest` is the view of `rest` above `base + 1`.
The entry of `header` at `base + 1` follows it. -/
theorem linearView_cons (base : Nat) (header : BlockHeader) (rest : List BlockHeader) :
    linearView base (header :: rest) =
      linearView (base + 1) rest ++ [⟨base + 1, header.pure.nTime, header.pure.nBits⟩] := by
  simp only [linearView, List.mapIdx_cons, List.reverse_cons, Nat.add_zero]
  congr 3
  funext j h
  rw [show base + (j + 1) + 1 = base + 1 + j + 1 by omega]

/--
Take every network and pair of entries below 2147483647.
The view depth of the higher entry is at most the view depth of the lower entry.
The depth is 241 or 14401 below the first DigiShield height and 11 from it (`contextualViewDepth_eq`).
-/
theorem contextualViewDepth_antitone (network : WorkNetwork) (a b : BlockIndex) (le : a.nHeight ≤ b.nHeight)
    (range : b.nHeight < 2147483647) :
    contextualViewDepth network b ≤ contextualViewDepth network a := by
  rw [contextualViewDepth_eq network a (by omega), contextualViewDepth_eq network b range]
  cases network <;> simp only <;> (repeat' split) <;> omega

/--
Let `prev` be an entry of a well-formed index, and let `fuel` be at least the view depth of `prev`.
Then `contextualCheckBlockHeader` gives the same result on `ancestorView` as on the walk from `prev` with `fuel` entries.
This holds for every network, header, adjusted time and last checkpoint.
-/
theorem ancestorView_congr_walk (network : WorkNetwork) (index : HeaderIndex) (wf : WellFormed network index)
    (hash : Hash256) (prev : IndexEntry) (found : index.lookup hash = some prev) (fuel : Nat)
    (deep : contextualViewDepth network prev.toBlockIndex ≤ fuel) (header : PureBlockHeader)
    (adjustedTime : Int64) (lastCheckpointHeight : Option Nat) :
    contextualCheckBlockHeader network header (ancestorView network index prev) adjustedTime
        lastCheckpointHeight =
      contextualCheckBlockHeader network header (ancestorWalk index fuel prev) adjustedTime
        lastCheckpointHeight := by
  have positive : 0 < contextualViewDepth network prev.toBlockIndex := by
    simp only [contextualViewDepth, nMedianTimeSpan]; omega
  have agree : (ancestorView network index prev).take (contextualViewDepth network prev.toBlockIndex) =
      (ancestorWalk index fuel prev).take (contextualViewDepth network prev.toBlockIndex) := by
    unfold ancestorView
    rw [List.take_of_length_le (ancestorWalk_length_le _ _ _), ancestorWalk_take index prev _ _ deep]
  have viewValid := ancestorWalk_valid network index wf (contextualViewDepth network prev.toBlockIndex)
    hash prev found
  have walkValid := ancestorWalk_valid network index wf fuel hash prev found
  have cons : ∀ n, 0 < n → ∃ rest, ancestorWalk index n prev = prev.toBlockIndex :: rest := by
    intro n pos
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨_, rfl⟩
  obtain ⟨r₁, h₁⟩ := cons _ positive
  obtain ⟨r₂, h₂⟩ := cons fuel (by omega)
  unfold ancestorView at agree ⊢
  rw [h₁] at agree viewValid ⊢
  rw [h₂] at agree walkValid ⊢
  exact contextualCheck_congr_prefix network header prev.toBlockIndex r₁ r₂ adjustedTime
    lastCheckpointHeight viewValid walkValid agree

/-- An insertion under a key that the index lacks does not change the walk from an entry of a well-formed index. -/
theorem ancestorWalk_insert_fresh {network : WorkNetwork} (index : HeaderIndex) (wf : WellFormed network index)
    (fresh : Hash256) (new : IndexEntry) (unknown : index.lookup fresh = none) (fuel : Nat) (key : Hash256)
    (entry : IndexEntry) (found : index.lookup key = some entry) :
    ancestorWalk (index.insert fresh new) fuel entry = ancestorWalk index fuel entry := by
  induction fuel generalizing key entry with
  | zero => rfl
  | succ n ih =>
    cases hp : entry.prev with
    | none => simp [ancestorWalk, hp]
    | some p =>
      obtain ⟨-, parent, hparent, -⟩ := wf.prevLink key entry p found hp
      have ne : p ≠ fresh := by rintro rfl; rw [hparent] at unknown; cases unknown
      simp only [ancestorWalk, hp, Option.bind_some, HeaderIndex.lookup_insert_of_ne _ _ _ _ ne, hparent,
        ih p parent hparent]

/-- An insertion under a key that the index lacks does not change the ancestor walk of step 6 from an entry of a well-formed index. -/
theorem ancestorHashAt_insert_fresh {network : WorkNetwork} (index : HeaderIndex) (wf : WellFormed network index)
    (fresh : Hash256) (new : IndexEntry) (unknown : index.lookup fresh = none) (fuel : Nat) (key : Hash256)
    (entry : IndexEntry) (found : index.lookup key = some entry) (height : Nat) :
    ancestorHashAt (index.insert fresh new) fuel key entry height = ancestorHashAt index fuel key entry height := by
  induction fuel generalizing key entry with
  | zero => rfl
  | succ n ih =>
    cases hp : entry.prev with
    | none => simp [ancestorHashAt, hp]
    | some p =>
      obtain ⟨-, parent, hparent, -⟩ := wf.prevLink key entry p found hp
      have ne : p ≠ fresh := by rintro rfl; rw [hparent] at unknown; cases unknown
      simp only [ancestorHashAt, hp, HeaderIndex.lookup_insert_of_ne _ _ _ _ ne, hparent, ih p parent hparent]

/-- One unfolding of `ancestorHashAt` with positive fuel. -/
private theorem ancestorHashAt_succ (index : HeaderIndex) (fuel : Nat) (hash : Hash256) (entry : IndexEntry)
    (height : Nat) :
    ancestorHashAt index (fuel + 1) hash entry height =
      if entry.height = height then some hash
      else if entry.height < height then none
      else
        match entry.prev with
        | some prev =>
          match index.lookup prev with
          | some parent => ancestorHashAt index fuel prev parent height
          | none => none
        | none => none := rfl

/-- The entry that an acceptance adds above the entry `tip`: the header, the height of `tip` plus one, the predecessor `hashPrevBlock` and no flags. -/
def linkedEntry (tip : IndexEntry) (header : BlockHeader) : IndexEntry :=
  ⟨header.pure, tip.height + 1, some header.pure.hashPrevBlock, false, false, false⟩

/--
Let `tip` be an entry of a well-formed index under `tipHash`, and let a header with an unknown hash link to it.
Insert the header's `linkedEntry`.
Then a member of the index is an ancestor of the new entry exactly when it is an ancestor of `tip`.
-/
theorem isAncestorInIndex_linked {network : WorkNetwork} (index : HeaderIndex) (wf : WellFormed network index)
    (tipHash : Hash256) (tip : IndexEntry) (found : index.lookup tipHash = some tip) (header : BlockHeader)
    (unknown : index.lookup header.pure.getHash = none) (link : header.pure.hashPrevBlock = tipHash)
    (member : Hash256) (memberEntry : IndexEntry) (inIndex : index.lookup member = some memberEntry) :
    isAncestorInIndex (index.insert header.pure.getHash (linkedEntry tip header)) header.pure.getHash
        (linkedEntry tip header) member =
      isAncestorInIndex index tipHash tip member := by
  have ne : member ≠ header.pure.getHash := by rintro rfl; rw [inIndex] at unknown; cases unknown
  have tipNe : tipHash ≠ header.pure.getHash := by rintro rfl; rw [found] at unknown; cases unknown
  have fresh := ancestorHashAt_insert_fresh index wf header.pure.getHash (linkedEntry tip header) unknown
    (tip.height + 1) tipHash tip found memberEntry.height
  simp only [isAncestorInIndex, HeaderIndex.lookup_insert_of_ne _ _ _ _ ne, inIndex]
  rw [ancestorHashAt_succ _ (linkedEntry tip header).height]
  simp only [linkedEntry]
  by_cases same : tip.height + 1 = memberEntry.height
  · have differ : (header.pure.getHash.val == member.val) = false :=
      beq_false_of_ne fun eq => ne (Subtype.ext eq).symm
    have notEq : ¬ tip.height = memberEntry.height := by omega
    have below : tip.height < memberEntry.height := by omega
    rw [ancestorHashAt_succ]
    simp only [same, notEq, below, ite_true, ite_false]
    simpa using differ
  · by_cases above : tip.height + 1 < memberEntry.height
    · have notEq : ¬ tip.height = memberEntry.height := by omega
      have below : tip.height < memberEntry.height := by omega
      rw [ancestorHashAt_succ]
      simp only [same, above, notEq, below, ite_true, ite_false]
    · simp only [same, above, ite_false, link, HeaderIndex.lookup_insert_of_ne _ _ _ _ tipNe, found]
      simp only [linkedEntry, link] at fresh
      rw [fresh]


/--
The setting of `process_linear`: a list of headers that extends the entry `tip` of a well-formed index in order.
The heights stay below 2147483647, and the hashes are new, distinct and not the genesis hash.
`tip` has no failure flag, and no member of the failed list is `tip` or an ancestor of it.
-/
structure LinearSetting (ctx : HeaderContext) (index : HeaderIndex) (tipHash : Hash256) (tip : IndexEntry)
    (headers : List BlockHeader) : Prop where
  /-- The index is well formed. -/
  wf : WellFormed ctx.network index
  /-- `tip` is the entry under `tipHash`. -/
  found : index.lookup tipHash = some tip
  /-- The height budget: the last header's height `tip.height + headers.length` is below 2147483647. -/
  budget : tip.height + headers.length < 2147483647
  /-- The headers link from `tipHash` in order. -/
  links : LinksFrom tipHash headers
  /-- The index has no header of the list. -/
  unknown : ∀ header ∈ headers, index.lookup header.pure.getHash = none
  /-- The hashes of the headers are distinct. -/
  distinct : (headers.map (·.pure.getHash)).Nodup
  /-- No header has the genesis hash of the network. -/
  notGenesis : ∀ header ∈ headers, genesisHash? ctx.network ≠ some header.pure.getHash
  /-- `tip` has no failure flag. -/
  notFailed : tip.isFailed = false
  /-- No member of the failed list is `tip` or an ancestor of it. -/
  noFailedAncestor : ∀ member ∈ index.failedBlocks, isAncestorInIndex index tipHash tip member = false

namespace LinearSetting

variable {ctx : HeaderContext} {index : HeaderIndex} {tipHash : Hash256} {tip : IndexEntry}
  {header : BlockHeader} {rest : List BlockHeader}

/-- The first header of the setting links to `tip`. -/
theorem foundPrev (s : LinearSetting ctx index tipHash tip (header :: rest)) :
    index.lookup header.pure.hashPrevBlock = some tip := by
  rw [s.links.1]; exact s.found

/-- The index lacks the hash of the first header. -/
theorem unknownHead (s : LinearSetting ctx index tipHash tip (header :: rest)) :
    index.lookup header.pure.getHash = none :=
  s.unknown header (List.mem_cons_self ..)

/-- The acceptance of the first header inserts its `linkedEntry`. -/
theorem addToBlockIndex_eq (s : LinearSetting ctx index tipHash tip (header :: rest)) :
    addToBlockIndex index header.pure = index.insert header.pure.getHash (linkedEntry tip header) :=
  addToBlockIndex_of_unknown index header.pure tip s.unknownHead s.foundPrev

/-- After the first header, the rest of the list extends the entry of the first header in the same setting. -/
theorem next (s : LinearSetting ctx index tipHash tip (header :: rest)) :
    LinearSetting ctx (addToBlockIndex index header.pure) header.pure.getHash (linkedEntry tip header) rest := by
  have distinct := s.distinct
  rw [List.map_cons, List.nodup_cons] at distinct
  have budget := s.budget
  simp only [List.length_cons] at budget
  have wf' : WellFormed ctx.network (addToBlockIndex index header.pure) := by
    apply wellFormed_addToBlockIndex index s.wf header.pure
    · intro parent hp
      rw [s.foundPrev] at hp; cases hp
      simp only [maxPrevHeight]; omega
    · intro hp; rw [s.foundPrev] at hp; cases hp
  rw [s.addToBlockIndex_eq] at wf' ⊢
  refine ⟨wf', HeaderIndex.lookup_insert_self .., by simp only [linkedEntry]; omega, s.links.2, ?_,
    distinct.2, fun h mem => s.notGenesis h (List.mem_cons_of_mem _ mem), rfl, ?_⟩
  · intro h mem
    have ne : h.pure.getHash ≠ header.pure.getHash := fun same =>
      distinct.1 (List.mem_map.mpr ⟨h, mem, same⟩)
    rw [HeaderIndex.lookup_insert_of_ne _ _ _ _ ne]
    exact s.unknown h (List.mem_cons_of_mem _ mem)
  · intro member mem
    rw [HeaderIndex.insert_failedBlocks] at mem
    obtain ⟨me, hm, -⟩ := s.wf.failedListed member mem
    rw [isAncestorInIndex_linked index s.wf tipHash tip s.found header s.unknownHead s.links.1 member me hm]
    exact s.noFailedAncestor member mem

/-- The step accepts the first header exactly when step 2 and the contextual check on `tip` pass. -/
theorem accept_ok_iff (s : LinearSetting ctx index tipHash tip (header :: rest)) :
    (∃ r, (acceptBlockHeader ctx index header).2 = .ok r) ↔
      checkBlockHeader ctx.network header = .ok () ∧ contextualCheckInIndex ctx index header.pure tip = .ok () := by
  have notGenesis := s.notGenesis header (List.mem_cons_self ..)
  have iff := accept_eq_ok_iff ctx index header s.wf notGenesis s.unknownHead
  have budget := s.budget
  simp only [List.length_cons] at budget
  constructor
  · rintro ⟨r, ok⟩
    have := accept_ok_hash ctx index header r ok
    subst this
    obtain ⟨c, prev, hp, -, -, cc, -⟩ := iff.mp ok
    rw [s.foundPrev] at hp; cases hp
    exact ⟨c, cc⟩
  · rintro ⟨c, cc⟩
    refine ⟨_, iff.mpr ⟨c, tip, s.foundPrev, s.notFailed, by simp only [maxPrevHeight]; omega, cc, Or.inr ?_⟩⟩
    intro member mem
    rw [s.links.1]
    exact s.noFailedAncestor member mem

/-- The walk from the entry of the first header is that entry followed by the walk from `tip` in the input index. -/
theorem ancestorWalk_linked (s : LinearSetting ctx index tipHash tip (header :: rest)) (fuel : Nat) :
    ancestorWalk (addToBlockIndex index header.pure) (fuel + 1) (linkedEntry tip header) =
      (linkedEntry tip header).toBlockIndex :: ancestorWalk index fuel tip := by
  have tipNe : header.pure.hashPrevBlock ≠ header.pure.getHash := by
    intro same; have := s.foundPrev; rw [same, s.unknownHead] at this; cases this
  rw [s.addToBlockIndex_eq]
  simp only [ancestorWalk]
  simp only [linkedEntry, Option.bind_some, HeaderIndex.lookup_insert_of_ne _ _ _ _ tipNe, s.foundPrev]
  rw [ancestorWalk_insert_fresh index s.wf _ _ s.unknownHead fuel tipHash tip s.found]

end LinearSetting

/-- A statement about each position of a list with a first element splits into the first element and the positions of the rest. -/
private theorem forall_lt_cons {α : Type} (head : α) (rest : List α) (P : Nat → α → Prop) :
    (∀ i (lt : i < (head :: rest).length), P i (head :: rest)[i]) ↔
      P 0 head ∧ ∀ i (lt : i < rest.length), P (i + 1) rest[i] := by
  constructor
  · intro h
    exact ⟨h 0 (by simp), fun i lt => h (i + 1) (by simp; omega)⟩
  · rintro ⟨h0, h⟩ i lt
    cases i with
    | zero => exact h0
    | succ i => exact h i (by simp at lt; omega)

/--
In the linear setting, the loop succeeds exactly when each header passes step 2 and the contextual check of step 5.
The check of the header at position `i` runs on the index after the headers before it, with the entry of its predecessor.
-/
theorem LinearSetting.steps_ok_iff {ctx : HeaderContext} {index : HeaderIndex} {tipHash : Hash256}
    {tip : IndexEntry} {headers : List BlockHeader} (s : LinearSetting ctx index tipHash tip headers)
    (p : Nat) (last : Option Hash256) :
    (∃ r, (processSteps ctx p index last headers).2 = .ok r) ↔
      ∀ i (lt : i < headers.length), checkBlockHeader ctx.network headers[i] = .ok () ∧
        ∃ e, (addHeaders index (headers.take i)).lookup headers[i].pure.hashPrevBlock = some e ∧
          contextualCheckInIndex ctx (addHeaders index (headers.take i)) headers[i].pure e = .ok () := by
  induction headers generalizing index tipHash tip p last with
  | nil => simp [processSteps]
  | cons header rest ih =>
    rw [forall_lt_cons header rest (fun i x => checkBlockHeader ctx.network x = .ok () ∧
      ∃ e, (addHeaders index ((header :: rest).take i)).lookup x.pure.hashPrevBlock = some e ∧
        contextualCheckInIndex ctx (addHeaders index ((header :: rest).take i)) x.pure e = .ok ())]
    have zero : (checkBlockHeader ctx.network header = .ok () ∧
        ∃ e, (addHeaders index ((header :: rest).take 0)).lookup header.pure.hashPrevBlock = some e ∧
          contextualCheckInIndex ctx (addHeaders index ((header :: rest).take 0)) header.pure e = .ok ()) ↔
        (∃ r, (acceptBlockHeader ctx index header).2 = .ok r) := by
      rw [s.accept_ok_iff]
      simp [addHeaders, s.foundPrev]
    rw [zero]
    cases hstep : acceptBlockHeader ctx index header with
    | mk index' r =>
      cases r with
      | error e => simp [processSteps, hstep]
      | ok hash =>
        have eq := accept_ok_index ctx index header hash (by rw [hstep])
        rw [hstep] at eq
        simp only at eq
        subst eq
        simp only [processSteps, hstep]
        rw [ih s.next (p + 1) (some hash)]
        simp only [Except.ok.injEq, exists_eq', true_and, List.take_succ_cons]
        rfl

/--
In the linear setting, the index after the headers before position `i` holds the predecessor's entry of the header at `i`.
The entry is at height `tip.height + i`, and the index is well formed.
The walk from that entry with `i + fuel` entries is the view of those headers, followed by the walk from `tip` in the input index.
-/
theorem LinearSetting.walk {ctx : HeaderContext} {index : HeaderIndex} {tipHash : Hash256}
    {tip : IndexEntry} {headers : List BlockHeader} (s : LinearSetting ctx index tipHash tip headers) :
    ∀ i (lt : i < headers.length), ∃ e,
      (addHeaders index (headers.take i)).lookup headers[i].pure.hashPrevBlock = some e ∧
      e.height = tip.height + i ∧ WellFormed ctx.network (addHeaders index (headers.take i)) ∧
      ∀ fuel, ancestorWalk (addHeaders index (headers.take i)) (i + fuel) e =
        linearView tip.height (headers.take i) ++ ancestorWalk index fuel tip := by
  induction headers generalizing index tipHash tip with
  | nil => intro i lt; simp at lt
  | cons header rest ih =>
    rw [forall_lt_cons header rest (fun i x => ∃ e,
      (addHeaders index ((header :: rest).take i)).lookup x.pure.hashPrevBlock = some e ∧
      e.height = tip.height + i ∧ WellFormed ctx.network (addHeaders index ((header :: rest).take i)) ∧
      ∀ fuel, ancestorWalk (addHeaders index ((header :: rest).take i)) (i + fuel) e =
        linearView tip.height ((header :: rest).take i) ++ ancestorWalk index fuel tip)]
    constructor
    · refine ⟨tip, by simp [addHeaders, s.foundPrev], rfl, s.wf, fun fuel => ?_⟩
      simp [addHeaders, linearView]
    · intro i lt
      obtain ⟨e, he, height, wfi, walk⟩ := ih s.next i lt
      refine ⟨e, he, by simp only [linkedEntry] at height; omega, wfi, fun fuel => ?_⟩
      simp only [List.take_succ_cons]
      show ancestorWalk (addHeaders (addToBlockIndex index header.pure) (rest.take i)) (i + 1 + fuel) e = _
      rw [show i + 1 + fuel = i + (fuel + 1) by omega, walk (fuel + 1), s.ancestorWalk_linked fuel,
        linearView_cons]
      simp [linkedEntry, IndexEntry.toBlockIndex]

/-- In the linear setting, the index after all the headers holds the entry of each header.
The entry of the header at position `i` has height `tip.height + i + 1` and the predecessor `hashPrevBlock`. -/
theorem LinearSetting.lookup_addHeaders {ctx : HeaderContext} {index : HeaderIndex} {tipHash : Hash256}
    {tip : IndexEntry} {headers : List BlockHeader} (s : LinearSetting ctx index tipHash tip headers) :
    ∀ i (lt : i < headers.length), ∃ entry,
      (addHeaders index headers).lookup headers[i].pure.getHash = some entry ∧
      entry.height = tip.height + i + 1 ∧ entry.prev = some headers[i].pure.hashPrevBlock := by
  induction headers generalizing index tipHash tip with
  | nil => intro i lt; simp at lt
  | cons header rest ih =>
    rw [forall_lt_cons header rest (fun i x => ∃ entry,
      (addHeaders index (header :: rest)).lookup x.pure.getHash = some entry ∧
      entry.height = tip.height + i + 1 ∧ entry.prev = some x.pure.hashPrevBlock)]
    constructor
    · refine ⟨linkedEntry tip header, ?_, rfl, rfl⟩
      exact lookup_addHeaders_of_some (addToBlockIndex index header.pure) rest _ _
        (by rw [s.addToBlockIndex_eq]; exact HeaderIndex.lookup_insert_self ..)
    · intro i lt
      obtain ⟨entry, he, height, prev⟩ := ih s.next i lt
      exact ⟨entry, he, by simp only [linkedEntry] at height; omega, prev⟩


/--
The target `process_linear` of design record 0008, section 11, the linear case of option S3.

Let the index be well formed, with the entry `tip` under `tipHash`.
Let `headers` be `h₁ … hₙ`, and let them link from `tipHash` in order (`LinksFrom`), with `tip.height + n < 2147483647`.
The hashes of the headers are unknown: the index has none of them, and they are distinct.
So no hash is known when its step runs.
No hash is the genesis hash.
The path has no failure state: `tip` has no failure flag, and no member of the failed list is `tip` or an ancestor of it.

Then the sequence succeeds exactly when each header passes step 2 and the contextual check.
For the header at position `i`, the check uses two inputs:

- The view `linearView tip.height (headers.take i)` of the headers before it, newest first, followed by `ancestorView` of `tip` in the input index.
- The last checkpoint of the index after those headers, `addHeaders index (headers.take i)`.
-/
theorem process_linear (ctx : HeaderContext) (index : HeaderIndex) (wf : WellFormed ctx.network index)
    (tipHash : Hash256) (tip : IndexEntry) (found : index.lookup tipHash = some tip)
    (headers : List BlockHeader) (budget : tip.height + headers.length < 2147483647)
    (links : LinksFrom tipHash headers)
    (unknown : ∀ header ∈ headers, index.lookup header.pure.getHash = none)
    (distinct : (headers.map (·.pure.getHash)).Nodup)
    (notGenesis : ∀ header ∈ headers, genesisHash? ctx.network ≠ some header.pure.getHash)
    (notFailed : tip.isFailed = false)
    (noFailedAncestor : ∀ member ∈ index.failedBlocks, isAncestorInIndex index tipHash tip member = false) :
    (∃ last, (processNewBlockHeaders ctx index headers).2 = .ok last) ↔
      ∀ i (lt : i < headers.length),
        checkBlockHeader ctx.network headers[i] = .ok () ∧
        contextualCheckBlockHeader ctx.network headers[i].pure
            (linearView tip.height (headers.take i) ++ ancestorView ctx.network index tip) ctx.adjustedTime
            (lastCheckpointInIndex ctx.network ctx.checkpointsEnabled (addHeaders index (headers.take i))) =
          .ok () := by
  have s : LinearSetting ctx index tipHash tip headers :=
    ⟨wf, found, budget, links, unknown, distinct, notGenesis, notFailed, noFailedAncestor⟩
  rw [processNewBlockHeaders_of_wellFormed ctx index wf, s.steps_ok_iff 0 none]
  refine forall_congr' fun i => forall_congr' fun lt => and_congr_right' ?_
  obtain ⟨e, he, height, wfi, walk⟩ := s.walk i lt
  have depth : contextualViewDepth ctx.network e.toBlockIndex ≤
      i + contextualViewDepth ctx.network tip.toBlockIndex := by
    have := contextualViewDepth_antitone ctx.network tip.toBlockIndex e.toBlockIndex
      (by simp only [IndexEntry.toBlockIndex]; omega) (by simp only [IndexEntry.toBlockIndex]; omega)
    omega
  have check : contextualCheckInIndex ctx (addHeaders index (headers.take i)) headers[i].pure e =
      contextualCheckBlockHeader ctx.network headers[i].pure
        (linearView tip.height (headers.take i) ++ ancestorView ctx.network index tip) ctx.adjustedTime
        (lastCheckpointInIndex ctx.network ctx.checkpointsEnabled (addHeaders index (headers.take i))) := by
    unfold contextualCheckInIndex
    rw [ancestorView_congr_walk ctx.network _ wfi _ e he _ depth, walk]
    rfl
  simp only [he, Option.some.injEq, exists_eq_left', check]

/--
The target `process_height` of design record 0008, section 11.
In the setting of `process_linear`, let the sequence succeed.
Then the result index holds the entry of the header at position `i` at height `tip.height + i + 1`, with the predecessor `hashPrevBlock`.
With positions from 1, as the record writes `hᵢ`, the entry of `hᵢ` has height `tip.height + i`.
-/
theorem process_height (ctx : HeaderContext) (index : HeaderIndex) (wf : WellFormed ctx.network index)
    (tipHash : Hash256) (tip : IndexEntry) (found : index.lookup tipHash = some tip)
    (headers : List BlockHeader) (budget : tip.height + headers.length < 2147483647)
    (links : LinksFrom tipHash headers)
    (unknown : ∀ header ∈ headers, index.lookup header.pure.getHash = none)
    (distinct : (headers.map (·.pure.getHash)).Nodup)
    (notGenesis : ∀ header ∈ headers, genesisHash? ctx.network ≠ some header.pure.getHash)
    (notFailed : tip.isFailed = false)
    (noFailedAncestor : ∀ member ∈ index.failedBlocks, isAncestorInIndex index tipHash tip member = false)
    (last : Option Hash256) (ok : (processNewBlockHeaders ctx index headers).2 = .ok last) :
    ∀ i (lt : i < headers.length), ∃ entry,
      (processNewBlockHeaders ctx index headers).1.lookup headers[i].pure.getHash = some entry ∧
      entry.height = tip.height + i + 1 ∧ entry.prev = some headers[i].pure.hashPrevBlock := by
  have s : LinearSetting ctx index tipHash tip headers :=
    ⟨wf, found, budget, links, unknown, distinct, notGenesis, notFailed, noFailedAncestor⟩
  rw [processNewBlockHeaders_of_wellFormed ctx index wf] at ok ⊢
  rw [processSteps_ok_index ctx 0 index none headers last ok]
  exact s.lookup_addHeaders


/-! ## The sequence: failure state, adjusted time and completeness -/

/--
Take every index, header, key and entry.
An entry of `addToBlockIndex` is an entry of the input index, or the new entry under the header's hash.
The new entry has the header, no flags and no `scriptsValid`.
With a predecessor under `hashPrevBlock`, it is linked to it at its height plus one, and otherwise it has no predecessor and height 0.
-/
theorem lookup_addToBlockIndex (index : HeaderIndex) (header : PureBlockHeader) (key : Hash256)
    (entry : IndexEntry) (found : (addToBlockIndex index header).lookup key = some entry) :
    index.lookup key = some entry ∨
      (key = header.getHash ∧ entry.failedValid = false ∧ entry.failedChild = false ∧
        entry.scriptsValid = false ∧ entry.header = header ∧
        (∀ parent, index.lookup header.hashPrevBlock = some parent →
          entry.height = parent.height + 1 ∧ entry.prev = some header.hashPrevBlock) ∧
        (index.lookup header.hashPrevBlock = none → entry.height = 0 ∧ entry.prev = none)) := by
  simp only [addToBlockIndex] at found
  cases hk : index.lookup header.getHash with
  | some _ => simp only [hk] at found; exact Or.inl found
  | none =>
    simp only [hk] at found
    cases hp : index.lookup header.hashPrevBlock with
    | some parent =>
      simp only [hp, HeaderIndex.lookup_insert] at found
      split at found
      · next same => cases found; exact Or.inr ⟨same, rfl, rfl, rfl, rfl, by simp, by simp⟩
      · exact Or.inl found
    | none =>
      simp only [hp, HeaderIndex.lookup_insert] at found
      split at found
      · next same => cases found; exact Or.inr ⟨same, rfl, rfl, rfl, rfl, by simp, by simp⟩
      · exact Or.inl found

/--
Let the index have no failure flag and an empty failed list.
Then for every context and header, the step returns neither `duplicate`, `prevBlockInvalid` nor `failedAncestor`.
The index after the step also has no failure flag and an empty failed list.
-/
theorem accept_no_failure (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader)
    (noFlags : ∀ key entry, index.lookup key = some entry → entry.failedValid = false ∧ entry.failedChild = false)
    (noFailed : index.failedBlocks = []) :
    (∀ error, (acceptBlockHeader ctx index header).2 = .error error →
      error ≠ .rejection .duplicate ∧ error ≠ .rejection .prevBlockInvalid ∧
      ∀ failed, error ≠ .rejection (.failedAncestor failed)) ∧
    (∀ key entry, (acceptBlockHeader ctx index header).1.lookup key = some entry →
      entry.failedValid = false ∧ entry.failedChild = false) ∧
    (acceptBlockHeader ctx index header).1.failedBlocks = [] := by
  have notFailed : ∀ key entry, index.lookup key = some entry → entry.isFailed = false := by
    intro key entry found
    obtain ⟨a, b⟩ := noFlags key entry found
    simp [IndexEntry.isFailed, a, b]
  have noAncestor : ∀ prevHash prev, failedAncestor? index prevHash prev = none := by
    intro prevHash prev; simp [failedAncestor?, noFailed]
  have errors : ∀ error, (acceptBlockHeader ctx index header).2 = .error error →
      error ≠ .rejection .duplicate ∧ error ≠ .rejection .prevBlockInvalid ∧
      ∀ failed, error ≠ .rejection (.failedAncestor failed) := by
    intro error err
    by_cases g : genesisHash? ctx.network = some header.pure.getHash
    · have : error = .adapter .heightOutOfRange := by
        simp only [acceptBlockHeader, g, ite_true] at err
        revert err
        repeat' split
        all_goals (intro err; simp at err; try exact err.symm)
      subst this
      simp
    · refine ⟨?_, ?_, ?_⟩
      · rintro rfl
        obtain ⟨entry, found, failed⟩ := (accept_eq_duplicate_iff ctx index header g).mp err
        rw [notFailed _ _ found] at failed; cases failed
      · rintro rfl
        obtain ⟨-, -, prev, found, failed⟩ := (accept_eq_prevBlockInvalid_iff ctx index header g).mp err
        rw [notFailed _ _ found] at failed; cases failed
      · rintro failed rfl
        obtain ⟨-, -, prev, -, -, -, -, -, found⟩ :=
          (accept_eq_failedAncestor_iff ctx index header g failed).mp err
        rw [noAncestor] at found; cases found
  refine ⟨errors, ?_⟩
  cases hr : (acceptBlockHeader ctx index header).2 with
  | ok r =>
    rw [accept_ok_index ctx index header r hr]
    refine ⟨fun key entry found => ?_, ?_⟩
    · rcases lookup_addToBlockIndex index header.pure key entry found with old | ⟨-, a, b, -⟩
      · exact noFlags key entry old
      · exact ⟨a, b⟩
    · simp only [addToBlockIndex]
      split
      · exact noFailed
      · split <;> exact noFailed
  | error e =>
    rw [accept_error_index_other ctx index header e hr (errors e hr).2.2]
    exact ⟨noFlags, noFailed⟩

/--
The target `process_no_failure` of design record 0008, section 11 (item 19).
Let the index be well formed, without failure flags and with an empty failed list.
Then for every context and list, no step returns `duplicate`, `prevBlockInvalid` or `failedAncestor`.
The result index has no failure flag and an empty failed list, so no step sets a flag.
Only the last step that runs can fail, so the theorem states this of the result.
-/
theorem process_no_failure (ctx : HeaderContext) (index : HeaderIndex) (wf : WellFormed ctx.network index)
    (headers : List BlockHeader)
    (noFlags : ∀ key entry, index.lookup key = some entry → entry.failedValid = false ∧ entry.failedChild = false)
    (noFailed : index.failedBlocks = []) :
    (∀ error, (processNewBlockHeaders ctx index headers).2 = .error error →
      error.error ≠ .rejection .duplicate ∧ error.error ≠ .rejection .prevBlockInvalid ∧
      ∀ failed, error.error ≠ .rejection (.failedAncestor failed)) ∧
    (∀ key entry, (processNewBlockHeaders ctx index headers).1.lookup key = some entry →
      entry.failedValid = false ∧ entry.failedChild = false) ∧
    (processNewBlockHeaders ctx index headers).1.failedBlocks = [] := by
  rw [processNewBlockHeaders_of_wellFormed ctx index wf]
  generalize 0 = p
  generalize (none : Option Hash256) = last
  induction headers generalizing p index last with
  | nil => exact ⟨fun _ err => by simp [processSteps] at err, noFlags, noFailed⟩
  | cons header rest ih =>
    obtain ⟨errors, flags, failed⟩ := accept_no_failure ctx index header noFlags noFailed
    have wf' := wellFormed_preserved ctx index header wf
    cases hstep : acceptBlockHeader ctx index header with
    | mk index' r =>
      rw [hstep] at errors flags failed wf'
      cases r with
      | error e =>
        simp only [processSteps, hstep]
        refine ⟨fun error err => ?_, flags, failed⟩
        simp only [Except.error.injEq] at err
        subst err
        exact errors e rfl
      | ok hash =>
        simp only [processSteps, hstep]
        exact ih index' wf' flags failed (p + 1) (some hash)

/--
Let the step accept with the adjusted time of `ctx`, and let `t` be a greater adjusted time up to `maxAdjustedTime`.
Then the step with `t` gives the same result.
-/
theorem accept_adjustedTime_mono (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader) (t : Int64)
    (later : ctx.adjustedTime.toInt ≤ t.toInt) (bounded : t.toInt ≤ maxAdjustedTime) (result : Hash256)
    (ok : (acceptBlockHeader ctx index header).2 = .ok result) :
    acceptBlockHeader { ctx with adjustedTime := t } index header = acceptBlockHeader ctx index header := by
  have mono : ∀ prev, contextualCheckInIndex ctx index header.pure prev = .ok () →
      contextualCheckInIndex { ctx with adjustedTime := t } index header.pure prev = .ok () := by
    intro prev accepted
    exact contextualCheck_adjustedTime_mono ctx.network header.pure _ ctx.adjustedTime t _ accepted later bounded
  simp only [acceptBlockHeader] at ok ⊢
  revert ok
  repeat' split
  all_goals (intro ok; simp_all)

/-- Let a loop succeed with the adjusted time of `ctx`, for any start position, index, result so far and list.
Then it gives the same result with a greater adjusted time up to `maxAdjustedTime`. -/
theorem processSteps_adjustedTime_mono (ctx : HeaderContext) (t : Int64)
    (later : ctx.adjustedTime.toInt ≤ t.toInt) (bounded : t.toInt ≤ maxAdjustedTime) (p : Nat)
    (index : HeaderIndex) (last : Option Hash256) (headers : List BlockHeader) (result : Option Hash256)
    (ok : (processSteps ctx p index last headers).2 = .ok result) :
    processSteps { ctx with adjustedTime := t } p index last headers = processSteps ctx p index last headers := by
  induction headers generalizing p index last with
  | nil => rfl
  | cons header rest ih =>
    cases hstep : acceptBlockHeader ctx index header with
    | mk index' r =>
      cases r with
      | error e => simp [processSteps, hstep] at ok
      | ok hash =>
        have same := accept_adjustedTime_mono ctx index header t later bounded hash (by rw [hstep])
        rw [hstep] at same
        simp only [processSteps, hstep] at ok ⊢
        rw [same]
        exact ih _ _ _ ok

/--
The target `process_adjustedTime_mono` of design record 0008, section 11.
Let the index be well formed, and let the sequence accept with the adjusted time of `ctx`.
Then for every greater adjusted time `t` up to `maxAdjustedTime`, `INT64_MAX − 7200`, the sequence gives the same result.
It accepts with the same last hash, and it returns the same index.
-/
theorem process_adjustedTime_mono (ctx : HeaderContext) (index : HeaderIndex) (_wf : WellFormed ctx.network index)
    (headers : List BlockHeader) (t : Int64) (later : ctx.adjustedTime.toInt ≤ t.toInt)
    (bounded : t.toInt ≤ maxAdjustedTime) (last : Option Hash256)
    (ok : (processNewBlockHeaders ctx index headers).2 = .ok last) :
    processNewBlockHeaders { ctx with adjustedTime := t } index headers = processNewBlockHeaders ctx index headers := by
  unfold processNewBlockHeaders at ok ⊢
  by_cases check : checkWellFormed ctx.network index
  · simp only [check, ite_true] at ok ⊢
    exact processSteps_adjustedTime_mono ctx t later bounded 0 index none headers last ok
  · simp [check] at ok

/--
Let the index be well formed and without anchors: every entry without a predecessor is at height 0.
Then for every entry and fuel of at least its height plus one, the walk from the entry ends at height 0.
-/
theorem ancestorWalk_last_zero {network : WorkNetwork} {index : HeaderIndex} (wf : WellFormed network index)
    (noAnchor : ∀ key entry, index.lookup key = some entry → entry.prev = none → entry.height = 0)
    (fuel : Nat) (key : Hash256) (entry : IndexEntry) (found : index.lookup key = some entry)
    (enough : entry.height + 1 ≤ fuel) :
    (ancestorWalk index fuel entry).getLast?.map BlockIndex.nHeight = some 0 := by
  induction fuel generalizing key entry with
  | zero => omega
  | succ n ih =>
    cases hp : entry.prev with
    | none => simp [ancestorWalk, hp, noAnchor key entry found hp, IndexEntry.toBlockIndex]
    | some p =>
      obtain ⟨-, parent, hparent, height⟩ := wf.prevLink key entry p found hp
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have := ih p parent hparent (by omega)
      simp only [ancestorWalk, hp, Option.bind_some, hparent] at this ⊢
      rw [List.getLast?_cons_cons]
      exact this

/--
Let the index be well formed and without anchors, every height in it below `maxPrevHeight`, and the adjusted time at most `maxAdjustedTime`.
Then for every header, the step returns no adapter error.
-/
theorem accept_complete (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader)
    (wf : WellFormed ctx.network index)
    (noAnchor : ∀ key entry, index.lookup key = some entry → entry.prev = none → entry.height = 0)
    (bounded : ctx.adjustedTime.toInt ≤ maxAdjustedTime)
    (budget : ∀ key entry, index.lookup key = some entry → entry.height < maxPrevHeight) :
    ∀ error, (acceptBlockHeader ctx index header).2 = .error error → ∀ adapter, error ≠ .adapter adapter := by
  have contextual : ∀ key prev e, index.lookup key = some prev →
      contextualCheckInIndex ctx index header.pure prev = .error e →
      ∀ adapter, HeaderStepError.ofContextual e ≠ .adapter adapter := by
    intro key prev e found fail adapter
    unfold contextualCheckInIndex at fail
    rw [ancestorView_congr_chain ctx.network index wf key prev found] at fail
    have valid := ancestorWalk_valid ctx.network index wf (prev.height + 1) key prev found
    have last := ancestorWalk_last_zero wf noAnchor (prev.height + 1) key prev found (Nat.le_refl _)
    obtain ⟨rest, hrest⟩ : ∃ rest, ancestorWalk index (prev.height + 1) prev = prev.toBlockIndex :: rest :=
      ⟨_, rfl⟩
    unfold ancestorChain at fail
    rw [hrest] at fail valid last
    have rejection := contextualCheck_complete ctx.network header.pure _ rest ctx.adjustedTime _ valid last
      bounded e fail
    rw [(HeaderStepError.ofContextual_eq_rejection_iff e (.contextual e)).mpr ⟨rfl, rejection⟩]
    simp
  intro error err adapter same
  subst same
  simp only [acceptBlockHeader] at err
  revert err
  repeat' split
  all_goals intro err
  all_goals first
    | (simp at err; done)
    | (simp only [Except.error.injEq] at err
       first
         | (have := budget _ _ ‹_›; omega)
         | exact contextual _ _ _ ‹_› ‹_› _ err)

/-- The loop form of `process_complete`, by induction on the list with its height budget. -/
theorem processSteps_complete (ctx : HeaderContext) (bounded : ctx.adjustedTime.toInt ≤ maxAdjustedTime)
    (headers : List BlockHeader) (p : Nat) (index : HeaderIndex) (last : Option Hash256)
    (wf : WellFormed ctx.network index)
    (noAnchor : ∀ key entry, index.lookup key = some entry → entry.prev = none → entry.height = 0)
    (budget : ∀ key entry, index.lookup key = some entry → entry.height + headers.length < 2147483647)
    (short : headers.length ≤ 2147483647) :
    ∀ error, (processSteps ctx p index last headers).2 = .error error → ∀ adapter, error.error ≠ .adapter adapter := by
  induction headers generalizing p index last with
  | nil => intro error err; simp [processSteps] at err
  | cons header rest ih =>
    simp only [List.length_cons] at budget short
    have step := accept_complete ctx index header wf noAnchor bounded
      (fun key entry found => by have := budget key entry found; simp only [maxPrevHeight]; omega)
    have wf' := wellFormed_preserved ctx index header wf
    cases hstep : acceptBlockHeader ctx index header with
    | mk index' r =>
      rw [hstep] at step wf'
      cases r with
      | error e =>
        intro error err
        simp only [processSteps, hstep, Except.error.injEq] at err
        subst err
        exact step e rfl
      | ok hash =>
        have eq := accept_ok_index ctx index header hash (by rw [hstep])
        rw [hstep] at eq
        simp only at eq
        subst eq
        simp only [processSteps, hstep]
        refine ih (p + 1) _ (some hash) wf' ?_ ?_ (by omega)
        · intro key entry found none
          rcases lookup_addToBlockIndex index header.pure key entry found with old | ⟨-, -, -, -, -, linked, root⟩
          · exact noAnchor key entry old none
          · cases hp : index.lookup header.pure.hashPrevBlock with
            | some parent => have := (linked parent hp).2; rw [none] at this; cases this
            | none => exact (root hp).1
        · intro key entry found
          rcases lookup_addToBlockIndex index header.pure key entry found with old | ⟨-, -, -, -, -, linked, root⟩
          · have := budget key entry old; omega
          · cases hp : index.lookup header.pure.hashPrevBlock with
            | some parent =>
              have := budget _ parent hp
              have := (linked parent hp).1
              omega
            | none => have := (root hp).1; omega

/--
The target `process_complete` of design record 0008, section 11.
Let the index be well formed and without anchors: every entry without a predecessor is at height 0, the genesis entry.
Let the adjusted time be in the domain, at most `maxAdjustedTime`.
Let `headers` have `n` headers, with the height budget of section 11: the greatest height in the index plus `n` is below 2147483647.
The theorem states the budget for each entry, and also takes `n ≤ 2147483647` for an index without entries (design record 0008, section 13.2).
From an empty index, the genesis header and the headers after it reach `heightOutOfRange` only at position 2147483647, so only a list of 2147483648 or more headers can reach it.
Then the sequence returns no adapter error.
-/
theorem process_complete (ctx : HeaderContext) (index : HeaderIndex) (wf : WellFormed ctx.network index)
    (headers : List BlockHeader)
    (noAnchor : ∀ key entry, index.lookup key = some entry → entry.prev = none → entry.height = 0)
    (bounded : ctx.adjustedTime.toInt ≤ maxAdjustedTime)
    (budget : ∀ key entry, index.lookup key = some entry → entry.height + headers.length < 2147483647)
    (short : headers.length ≤ 2147483647) :
    ∀ error, (processNewBlockHeaders ctx index headers).2 = .error error →
      ∀ adapter, error.error ≠ .adapter adapter := by
  rw [processNewBlockHeaders_of_wellFormed ctx index wf]
  exact processSteps_complete ctx bounded headers 0 index none wf noAnchor budget short

end DogeLib.Block
