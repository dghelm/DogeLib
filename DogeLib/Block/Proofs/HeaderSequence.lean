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

end DogeLib.Block
