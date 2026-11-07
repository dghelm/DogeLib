module

public import DogeLib.Work.NextWork

/-!
# Median time past

`CBlockIndex::GetMedianTimePast` in `src/chain.h` lines 284-298 at Core `e0a1c15` (D18).
Core collects the time of the entry and the times of up to ten predecessors, and stops early at genesis.
It sorts those times and returns the element at index `count / 2`.
For an even count, that element is the upper median.

The view is the checked finite view of `DogeLib.Work.NextWork`: block-index entries from newest to oldest, with consecutive heights.
Core's walk has every predecessor, so it collects `min 11 (h + 1)` times for an entry at height `h`.
A finite view can stop above genesis.
On such a view, Core's function would give a different median, not an error.
So this adapter rejects a view with fewer than `min 11 (h + 1)` entries, and never takes the median of fewer times.
The adapter errors describe the finite view, not Core consensus rejection codes.

The times are UInt32 values widened to Int, as `GetBlockTime` widens them to int64_t (D18, lines 274-277).
The widening is exact, so the order of the widened values is the order of the UInt32 values.
-/

@[expose] public section

namespace DogeLib.Work

/-- `nMedianTimeSpan` (`src/chain.h`, D18, line 284 at `e0a1c15`): the greatest number of times in a median. -/
def nMedianTimeSpan : Nat := 11

/-- `CBlockIndex::GetBlockTime` (`src/chain.h`, D18, lines 274-277 at `e0a1c15`).
The UInt32 time widens exactly to Int, as Core widens it to int64_t. -/
def BlockIndex.getBlockTime (entry : BlockIndex) : Int := entry.nTime.toNat

/-- Errors of the finite-view adapter to `GetMedianTimePast` (D18, lines 284-298 at `e0a1c15`).
These errors describe the adapter, not Core consensus rejection codes. -/
inductive MedianTimeError where
  /-- `validateWorkView` rejects the view, with its error. -/
  | invalidView (error : NextWorkError)
  /-- The view has no entry. Core's function needs an entry, and its callers never pass a null index. -/
  | emptyView
  /-- The view has fewer entries than Core's walk would read, so it lacks required history. -/
  | shortView
  deriving DecidableEq, Repr

/-- The number of times that Core's walk collects from an entry at the height of `last`: `min 11 (nHeight + 1)`.
The walk reads at most `nMedianTimeSpan` entries and stops after genesis (D18, lines 293-294 at `e0a1c15`). -/
def medianTimeSpan (last : BlockIndex) : Nat := min nMedianTimeSpan (last.nHeight + 1)

/-- The widened times of the first `count` entries of a view, in ascending order.
`List.mergeSort` from Lean core sorts them, as `std::sort` does in D18 line 296 at `e0a1c15`. -/
def sortedTimes (view : List BlockIndex) (count : Nat) : List Int :=
  ((view.take count).map BlockIndex.getBlockTime).mergeSort

/-- `CBlockIndex::GetMedianTimePast` on a checked finite view (`src/chain.h`, D18, lines 284-298 at `e0a1c15`).
The first entry of the view represents the index whose median Core computes.
The function checks the view with `validateWorkView`, and requires at least `count` entries, where `count` is `medianTimeSpan` of the first entry.
The result is the element at index `count / 2` of the sorted times of the first `count` entries.
An invalid, empty or short view returns an adapter error. -/
def medianTimePast (view : List BlockIndex) : Except MedianTimeError Int := do
  match validateWorkView view with
  | .error error => throw (.invalidView error)
  | .ok () => pure ()
  match view with
  | [] => throw .emptyView
  | last :: rest =>
    if deep : medianTimeSpan last ≤ rest.length + 1 then
      have index : medianTimeSpan last / 2 < (sortedTimes (last :: rest) (medianTimeSpan last)).length := by
        have positive : 0 < medianTimeSpan last := by
          simp only [medianTimeSpan, nMedianTimeSpan]
          omega
        simp only [sortedTimes, List.length_mergeSort, List.length_map, List.length_take,
          List.length_cons]
        omega
      return (sortedTimes (last :: rest) (medianTimeSpan last))[medianTimeSpan last / 2]
    else throw .shortView

end DogeLib.Work
