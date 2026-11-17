module

public import DogeLib.Block.Connect
public import DogeLib.Block.ContextualBody

/-!
# Block validation

The checks that Core runs on a new mainnet block, in Core's order, on a supplied chain view and coin set.

Core has no one function with these steps.
`AcceptBlock` runs the header and block checks when a block arrives, and `ConnectBlock` runs later, when the block joins the active chain (SOURCES.md, D33, D110 and D112):

1. `CheckBlockHeader` (`AcceptBlockHeader`, line 3224).
2. `ContextualCheckBlockHeader` (line 3238).
3. `CheckBlock` (`AcceptBlock`, line 3329).
4. `ContextualCheckBlock` (line 3330).
5. `ConnectBlock`.

`validateBlock` runs the five in this order, and returns the first failure (design record 0010, section 5).
For the genesis hash, `AcceptBlockHeader` skips steps 1 and 2 (line 3212), and `ConnectBlock` adds no coin.

## What the composition leaves out

`validateBlock` is the composition of the five checks. It is not `AcceptBlock`, `ProcessNewBlock` or `ActivateBestChain`:

- It has no block index. The caller supplies the view of the predecessor, and establishes that `hashPrevBlock` is the hash of that predecessor. `AcceptBlockHeader` finds the predecessor under that hash, and its other steps (`duplicate` and the three `bad-prevblk` cases) are in `acceptBlockHeader` of `DogeLib.Block.HeaderSequence`.
- It writes nothing, and it chooses no chain.
- `ConnectBlock` runs with `fJustCheck` true, so its own `CheckBlock` call has both flags false (D112, line 1804). Step 3 has already run with the caller's flags. When a node connects a block that step 3 accepted with both flags true, `CheckBlock` returns at once, because step 3 set `fChecked` (D106, lines 2943 and 2997).

Core's callers pass both flags of step 3 as true.
The flags are parameters here for the comparison.
A changed block has no valid proof of work, so its requests clear `fCheckPOW`, which also skips step 1.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction
open DogeLib.Script
open DogeLib.Work

/-- What the five checks read apart from the block and the coin set. -/
structure ValidateContext where
  /-- The predecessor and its ancestors, newest first, as `contextualCheckBlockHeader` takes them. Empty for a block at the genesis position. -/
  view : List BlockIndex
  /-- The adjusted time of `ContextualCheckBlockHeader`. -/
  adjustedTime : Int64
  /-- The height of the last checkpoint, as `contextualCheckBlockHeader` takes it. -/
  lastCheckpointHeight : Option Nat
  /-- Whether `VersionBitsState` gives `ACTIVE` for CSV. -/
  csvActive : Bool
  /-- Whether `VersionBitsState` gives `ACTIVE` for SegWit. -/
  segwitActive : Bool
  /-- The median time past of the predecessor, which `contextualCheckBlockBody` reads only with an active CSV state. -/
  prevMedianTimePast : Int
  /-- The hash of the ancestor of the predecessor at `BIP34Height`, as `ConnectContext.bip34Ancestor`. -/
  bip34Ancestor : Option Hash256

/-- The height of the block: the height of the predecessor plus one, or 0 without a predecessor. -/
def ValidateContext.height (ctx : ValidateContext) : Nat :=
  match ctx.view with
  | [] => 0
  | prev :: _ => prev.nHeight + 1

/-- The failure of the first check that fails. -/
inductive ValidateError where
  /-- Step 1: `CheckBlockHeader` fails: `high-hash`. -/
  | header (e : CheckPowError)
  /-- Step 2: `ContextualCheckBlockHeader` fails or returns an adapter error. -/
  | contextualHeader (e : ContextualHeaderError)
  /-- Step 3: `CheckBlock` fails. -/
  | checkBlock (e : CheckBlockError)
  /-- Step 4: `ContextualCheckBlock` fails or returns an adapter error. -/
  | contextualBody (e : ContextualBodyError)
  /-- Step 5: `ConnectBlock` fails or returns a result outside its model. -/
  | connect (e : ConnectBlockError)
  deriving DecidableEq, Repr

/-- Core's reject reason, or `none` for an adapter error or a result outside the model. -/
def ValidateError.rejectReason : ValidateError → Option String
  | .header e => some e.rejectReason
  | .contextualHeader e => e.rejectReason
  | .checkBlock e => some e.rejectReason
  | .contextualBody e => e.rejectReason
  | .connect e => e.rejectReason

/-- The denial-of-service score of the failing check. -/
def ValidateError.dosScore : ValidateError → Nat
  | .header _ => 50
  | .contextualHeader e => e.dosScore
  | .checkBlock e => e.dosScore
  | .contextualBody e => e.dosScore
  | .connect e => e.dosScore

/-- The reject code of the failing check. -/
def ValidateError.rejectCode : ValidateError → Nat
  | .header _ => 0x10
  | .contextualHeader e => e.rejectCode
  | .checkBlock e => e.rejectCode
  | .contextualBody e => e.rejectCode
  | .connect e => e.rejectCode

/-- The name of the failing step, for diagnostics. -/
def ValidateError.step : ValidateError → String
  | .header _ => "CheckBlockHeader"
  | .contextualHeader _ => "ContextualCheckBlockHeader"
  | .checkBlock _ => "CheckBlock"
  | .contextualBody _ => "ContextualCheckBlock"
  | .connect _ => "ConnectBlock"

/--
The five checks of a new mainnet block in Core's order, with the failure of the first check that fails.
The module documentation gives the steps, the genesis case and what the composition leaves out.

`fCheckPOW` and `fCheckMerkleRoot` are the flags of step 3. Step 1 runs only with `fCheckPOW`.
`s` is the coin set after the predecessor.
On success the result has the coin set after the block and the changes of the block.
-/
def validateBlock (verify : SignatureVerifier) (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext)
    (s : CoinSet) (b : Block) : Except ValidateError ConnectResult :=
  let genesis := some b.header.pure.getHash == genesisHash? .mainnet
  match (if genesis || !fCheckPOW then .ok () else checkBlockHeader .mainnet b.header) with
  | .error e => .error (.header e)
  | .ok () =>
    match (if genesis then .ok () else
        contextualCheckBlockHeader .mainnet b.header.pure ctx.view ctx.adjustedTime ctx.lastCheckpointHeight) with
    | .error e => .error (.contextualHeader e)
    | .ok () =>
      match checkBlock .mainnet fCheckPOW fCheckMerkleRoot b with
      | .error e => .error (.checkBlock e)
      | .ok () =>
        match contextualCheckBlockBody ctx.height ctx.prevMedianTimePast ctx.csvActive ctx.segwitActive b with
        | .error e => .error (.contextualBody e)
        | .ok () =>
          match connectBlock verify true
              ⟨ctx.height, b.header.pure.hashPrevBlock, ctx.bip34Ancestor, ctx.csvActive⟩ s b with
          | .error e => .error (.connect e)
          | .ok result => .ok result

end DogeLib.Block
