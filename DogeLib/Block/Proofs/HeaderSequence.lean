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

The target `accept_genesis` of section 11 is not proved.
Its statement says that the genesis entry gets no predecessor and height 0.
`addToBlockIndex` follows Core and searches the index for `hashPrevBlock`, so that holds only when the index lacks the genesis header's `hashPrevBlock`.
`accept_genesis_insert` proves the statement with that hypothesis, and `accept_genesis_parent` gives the other case.

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
The theorem states the target `accept_genesis` of design record 0008, section 11, without chain work, under the hypothesis on `hashPrevBlock`.
The real genesis header has the null `hashPrevBlock` (item 2).
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

end DogeLib.Block
