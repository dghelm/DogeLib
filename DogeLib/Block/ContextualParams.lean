module

public import DogeLib.Block.ProofOfWork

/-!
# Contextual parameters and checkpoints

The parameters by height that Core's `ContextualCheckBlockHeader` reads, design record 0006, stage 2.
The sources are at the Core pin (SOURCES.md):

- `fAllowLegacyBlocks`, `BIP65Height` and `BIP66Height` of `Consensus::Params`, `src/consensus/params.h` lines 50 to 53 and 82 (D15).
- Their values in each network record, and the record trees, in `src/chainparams.cpp` (D14).
- The checkpoint tables of `src/chainparams.cpp` (D9), with the type `MapCheckpoints` of `src/chainparams.h` lines 28 to 32 (D68).
- `Checkpoints::GetLastCheckpoint`, `src/checkpoints.cpp` lines 18 to 30 (D67).
- The flag `fCheckpointsEnabled`: its default in `src/validation.h` line 144 (D69), and the option `-checkpoints` in `src/init.cpp` line 951 (D70).

`getContextualParams` selects a record with the search of `ParamsTree.getConsensus`, at the height that the caller gives.
`ContextualCheckBlockHeader` gives the candidate height (D33, lines 3068 to 3070).
`lastCheckpoint` takes the enabled flag and the set of known checkpoint heights as inputs.
In Core, the set comes from the block index `mapBlockIndex`, which this module does not model.

The module does not compose the checks of `ContextualCheckBlockHeader`.
The theorems are in `DogeLib.Block.Proofs.ContextualParams`.

## Source

The records and tables are transcribed from Core's source, which is MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/chainparams.cpp`:

Copyright (c) 2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Copyright (c) 2022-2024 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.

Original notice from `src/checkpoints.cpp`:

Copyright (c) 2009-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block

/--
The fields of Core's `Consensus::Params` (D15) that `ContextualCheckBlockHeader` reads, apart from the work fields.
`toVersionGateParams` is the record that `checkVersion` takes.
Core stores both heights as `int`. Every value in D14 is positive, so the fields are natural numbers.
-/
structure ContextualParams extends VersionGateParams where
  /-- `BIP65Height`: from this height on, the base version must be at least 4 (D15, line 51). -/
  bip65Height : Nat
  /-- `BIP66Height`: from this height on, the base version must be at least 3 (D15, line 53). -/
  bip66Height : Nat
  deriving DecidableEq, Repr

/-- Mainnet before height 145000, `consensus`: `BIP65Height` and `BIP66Height` at D14 lines 86 and 87, `fAllowLegacyBlocks` at line 122. -/
def mainnetContextualParams : ContextualParams := ⟨⟨true⟩, 3464751, 1034383⟩

/-- Mainnet from height 145000, `digishieldConsensus`: a copy of `consensus` (D14, line 126) that changes none of these fields. -/
def mainnetDigishieldContextualParams : ContextualParams := ⟨⟨true⟩, 3464751, 1034383⟩

/-- Mainnet from height 371337, `auxpowConsensus`: a copy of `digishieldConsensus` (D14, line 134) with `fAllowLegacyBlocks` false (line 136). -/
def mainnetAuxpowContextualParams : ContextualParams := ⟨⟨false⟩, 3464751, 1034383⟩

/-- Testnet before height 145000, `consensus`: `BIP65Height` and `BIP66Height` at D14 lines 246 and 247, `fAllowLegacyBlocks` at line 279. -/
def testnetContextualParams : ContextualParams := ⟨⟨true⟩, 1854705, 708658⟩

/-- Testnet from height 145000, `digishieldConsensus`: a copy of `consensus` (D14, line 282) that changes none of these fields. -/
def testnetDigishieldContextualParams : ContextualParams := ⟨⟨true⟩, 1854705, 708658⟩

/-- Testnet from height 157500, `minDifficultyConsensus`: a copy of `digishieldConsensus` (D14, line 291) that changes none of these fields. -/
def testnetMinDifficultyContextualParams : ContextualParams := ⟨⟨true⟩, 1854705, 708658⟩

/-- Testnet from height 158100, `auxpowConsensus`: a copy of `minDifficultyConsensus` (D14, line 297) with `fAllowLegacyBlocks` false (line 300). -/
def testnetAuxpowContextualParams : ContextualParams := ⟨⟨false⟩, 1854705, 708658⟩

/-- Regtest before height 10, `consensus`: `BIP65Height` and `BIP66Height` at D14 lines 390 and 391, `fAllowLegacyBlocks` at line 419. -/
def regtestContextualParams : ContextualParams := ⟨⟨true⟩, 1351, 1251⟩

/-- Regtest from height 10, `digishieldConsensus`: a copy of `consensus` (D14, line 425) that changes none of these fields. -/
def regtestDigishieldContextualParams : ContextualParams := ⟨⟨true⟩, 1351, 1251⟩

/-- Regtest from height 20, `auxpowConsensus`: a copy of `digishieldConsensus` (D14, line 430) with `fAllowLegacyBlocks` false (line 431). -/
def regtestAuxpowContextualParams : ContextualParams := ⟨⟨false⟩, 1351, 1251⟩

/--
The contextual projection of each network's tree, with Core's effective heights and links.
The links are at D14 lines 138 to 141, 302 to 306 and 434 to 437.
The effective heights are at lines 123, 127 and 135 on mainnet.
On testnet they are at lines 278, 283, 292 and 298, and on regtest at lines 426 and 432.
The regtest `consensus` record does not set `nHeightEffective`, so the zero initialization of the static object gives it height 0.
-/
def contextualTree : Work.WorkNetwork → ParamsTree ContextualParams
  | .mainnet => .node 145000 mainnetDigishieldContextualParams
      (some (.node 0 mainnetContextualParams none none))
      (some (.node 371337 mainnetAuxpowContextualParams none none))
  | .testnet => .node 145000 testnetDigishieldContextualParams
      (some (.node 0 testnetContextualParams none none))
      (some (.node 157500 testnetMinDifficultyContextualParams none
        (some (.node 158100 testnetAuxpowContextualParams none none))))
  | .regtest => .node 10 regtestDigishieldContextualParams
      (some (.node 0 regtestContextualParams none none))
      (some (.node 20 regtestAuxpowContextualParams none none))

/-- The contextual fields of the record that `GetConsensus` selects for a height (D14, lines 494 to 506). -/
def getContextualParams (network : Work.WorkNetwork) (height : UInt32) : ContextualParams :=
  ((contextualTree network).getConsensus height).2

/-- Every record of a tree with its effective height, in preorder: the node, then the left subtree, then the right subtree. -/
def ParamsTree.records {α : Type} : ParamsTree α → List (UInt32 × α)
  | .node effective params left right =>
    (effective, params) ::
      ((match left with | some tree => tree.records | none => []) ++
        (match right with | some tree => tree.records | none => []))

/--
One entry of Core's `MapCheckpoints` (D68, line 28): a block height and the hash of the block at that height.
`hash` is the argument of `uint256S` in D9, in display order with the prefix `0x`.
`Work.ArithUint256.targetBytesOfHex` reads it into the internal byte order of `uint256`.
-/
structure Checkpoint where
  /-- The key of the map, an `int` in Core. -/
  height : Nat
  /-- The hash literal, as Core's source writes it. -/
  hash : String
  deriving DecidableEq, Repr

/--
The `checkpointData` table of each network, in source order.
Mainnet has 23 entries (D9, lines 180 to 205), testnet has 19 (lines 340 to 361), and regtest has only the genesis block (lines 461 to 464).
`checkpoints_heights_sorted` proves that the heights increase strictly, so the list order is the key order of the `std::map`.
-/
def checkpoints : Work.WorkNetwork → List Checkpoint
  | .mainnet => [
      ⟨0, "0x1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691"⟩,
      ⟨104679, "0x35eb87ae90d44b98898fec8c39577b76cb1eb08e1261cfc10706c8ce9a1d01cf"⟩,
      ⟨145000, "0xcc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72"⟩,
      ⟨371337, "0x60323982f9c5ff1b5a954eac9dc1269352835f47c2c5222691d80f0d50dcf053"⟩,
      ⟨450000, "0xd279277f8f846a224d776450aa04da3cf978991a182c6f3075db4c48b173bbd7"⟩,
      ⟨771275, "0x1b7d789ed82cbdc640952e7e7a54966c6488a32eaad54fc39dff83f310dbaaed"⟩,
      ⟨1000000, "0x6aae55bea74235f0c80bd066349d4440c31f2d0f27d54265ecd484d8c1d11b47"⟩,
      ⟨1250000, "0x00c7a442055c1a990e11eea5371ca5c1c02a0677b33cc88ec728c45edc4ec060"⟩,
      ⟨1500000, "0xf1d32d6920de7b617d51e74bdf4e58adccaa582ffdc8657464454f16a952fca6"⟩,
      ⟨1750000, "0x5c8e7327984f0d6f59447d89d143e5f6eafc524c82ad95d176c5cec082ae2001"⟩,
      ⟨2000000, "0x9914f0e82e39bbf21950792e8816620d71b9965bdbbc14e72a95e3ab9618fea8"⟩,
      ⟨2031142, "0x893297d89afb7599a3c571ca31a3b80e8353f4cf39872400ad0f57d26c4c5d42"⟩,
      ⟨2250000, "0x0a87a8d4e40dca52763f93812a288741806380cd569537039ee927045c6bc338"⟩,
      ⟨2510150, "0x77e3f4a4bcb4a2c15e8015525e3d15b466f6c022f6ca82698f329edef7d9777e"⟩,
      ⟨2750000, "0xd4f8abb835930d3c4f92ca718aaa09bef545076bd872354e0b2b85deefacf2e3"⟩,
      ⟨3000000, "0x195a83b091fb3ee7ecb56f2e63d01709293f57f971ccf373d93890c8dc1033db"⟩,
      ⟨3250000, "0x7f3e28bf9e309c4b57a4b70aa64d3b2ea5250ae797af84976ddc420d49684034"⟩,
      ⟨3500000, "0xeaa303b93c1c64d2b3a2cdcf6ccf21b10cc36626965cc2619661e8e1879abdfb"⟩,
      ⟨3606083, "0x954c7c66dee51f0a3fb1edb26200b735f5275fe54d9505c76ebd2bcabac36f1e"⟩,
      ⟨3854173, "0xe4b4ecda4c022406c502a247c0525480268ce7abbbef632796e8ca1646425e75"⟩,
      ⟨3963597, "0x2b6927cfaa5e82353d45f02be8aadd3bfd165ece5ce24b9bfa4db20432befb5d"⟩,
      ⟨4303965, "0xed7d266dcbd8bb8af80f9ccb8deb3e18f9cc3f6972912680feeb37b090f8cee0"⟩,
      ⟨5050000, "0xe7d4577405223918491477db725a393bcfc349d8ee63b0a4fde23cbfbfd81dea"⟩]
  | .testnet => [
      ⟨0, "0xbb0a78264637406b6360aad926284d544d7049f45189db5664f3c4d07350559e"⟩,
      ⟨483173, "0xa804201ca0aceb7e937ef7a3c613a9b7589245b10cc095148c4ce4965b0b73b5"⟩,
      ⟨591117, "0x5f6b93b2c28cedf32467d900369b8be6700f0649388a7dbfd3ebd4a01b1ffad8"⟩,
      ⟨658924, "0xed6c8324d9a77195ee080f225a0fca6346495e08ded99bcda47a8eea5a8a620b"⟩,
      ⟨703635, "0x839fa54617adcd582d53030a37455c14a87a806f6615aa8213f13e196230ff7f"⟩,
      ⟨1000000, "0x1fe4d44ea4d1edb031f52f0d7c635db8190dc871a190654c41d2450086b8ef0e"⟩,
      ⟨1202214, "0xa2179767a87ee4e95944703976fee63578ec04fa3ac2fc1c9c2c83587d096977"⟩,
      ⟨1250000, "0xb46affb421872ca8efa30366b09694e2f9bf077f7258213be14adb05a9f41883"⟩,
      ⟨1500000, "0x0caa041b47b4d18a4f44bdc05cef1a96d5196ce7b2e32ad3e4eb9ba505144917"⟩,
      ⟨1750000, "0x8042462366d854ad39b8b95ed2ca12e89a526ceee5a90042d55ebb24d5aab7e9"⟩,
      ⟨2000000, "0xd6acde73e1b42fc17f29dcc76f63946d378ae1bd4eafab44d801a25be784103c"⟩,
      ⟨2250000, "0xc4342ae6d9a522a02e5607411df1b00e9329563ef844a758d762d601d42c86dc"⟩,
      ⟨2500000, "0x3a66ec4933fbb348c9b1889aaf2f732fe429fd9a8f74fee6895eae061ac897e2"⟩,
      ⟨2750000, "0x473ea9f625d59f534ffcc9738ffc58f7b7b1e0e993078614f5484a9505885563"⟩,
      ⟨3062910, "0x113c41c00934f940a41f99d18b2ad9aefd183a4b7fe80527e1e6c12779bd0246"⟩,
      ⟨3286675, "0x07fef07a255d510297c9189dc96da5f4e41a8184bc979df8294487f07fee1cf3"⟩,
      ⟨3445426, "0x70574db7856bd685abe7b0a8a3e79b29882620645bd763b01459176bceb58cd1"⟩,
      ⟨3976284, "0xaf23c3e750bb4f2ce091235f006e7e4e2af453d4c866282e7870471dcfeb4382"⟩,
      ⟨5900000, "0x199bea6a442310589cbb50a193a30b097c228bd5a0f21af21e4e53dd57c382d3"⟩]
  | .regtest => [
      ⟨0, "0x3d2160a3b5dc4a9d62e7e66a295f70313ac808440ef7400d6c0772171ce973a5"⟩]

/-- The heights of the checkpoint table of a network, in ascending order. -/
def checkpointHeights (network : Work.WorkNetwork) : List Nat :=
  (checkpoints network).map Checkpoint.height

/--
The height of the block that check 4 of `ContextualCheckBlockHeader` compares with the candidate height (D33, lines 3093 to 3100).
`enabled` is `fCheckpointsEnabled`, which is true by default (D69, line 144) and set by `-checkpoints` (D70, line 951).
`known` holds the table heights whose hashes the block index contains.
A height in `known` that is not in the table has no effect.

With `enabled` false, the result is `none`, and check 4 does not run.
Otherwise the search follows `GetLastCheckpoint` (D67, lines 18 to 30): it walks the table from the greatest height down, and returns the first height in `known`.
The result is `none` when no table height is in `known`, as Core's `NULL`.

The result is the table key, not the `nHeight` of a block-index entry.
The two agree when the checkpoint hash identifies the block at that height.
-/
def lastCheckpoint (network : Work.WorkNetwork) (enabled : Bool) (known : List Nat) : Option Nat :=
  if enabled then
    ((checkpoints network).reverse.find? (fun c => known.contains c.height)).map Checkpoint.height
  else none

end DogeLib.Block
