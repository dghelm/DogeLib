# The conformance corpus

The conformance corpus is a set of mainnet block ranges with the verdicts and coin changes of Dogecoin Core on each block.
A program that validates Dogecoin blocks can run the ranges and compare its results with Core's.
It needs no DogeLib code, no Core build and no node.
The blocks and the requests are release assets, and the expected results and the checker are in this repository.

This document defines the four formats of the corpus, the rules that give a verdict, and the steps of a run.
[Design record 0011](design/0011-mainnet-ranges.md), section 9, gives the design.

## What a run shows

The expected results of each range are the response of the Core harness: Dogecoin Core at commit `e0a1c157791544e818c901bd9341896965afbf9d` (1.14.9), built with `scripts/build_core_harness.sh`.
In the same run, DogeLib's oracle gave the same results ([provenance](#provenance)).

When the checker passes on the results of a program, the program and Core agree on these values for each block of the range:

- the verdict, with the reject reason of a rejected block,
- the coin changes, through their digest and the numbers of spent and created coins.

The two programs also agree on the digest of the coins of the request, before the first block and after the last.

The coins of a request are not the coin set of mainnet.
They are the *restricted coins* (see [the coins](#the-coins)).
The restricted coins are the coins of Core's coin set at the start of the range whose transaction ID a block of the range names.
So the end digest is the digest of the restricted coins and their changes, and not the digest of the mainnet coin set.

A run does not test the rules that no block of a range reaches.
Every block of every range is a mainnet block that Core accepts.
So a pass shows no agreement on a rejected block.

## The ranges

Each range runs from a start height `a + 1` to an end height `b`.
The *predecessor* is the block at height `a`.
Each range holds a rule change of Dogecoin, or tests the block forms of one period ([design record 0011](design/0011-mainnet-ranges.md), section 4).

| Range | Heights | Blocks | Reason | Hash of the predecessor |
| --- | --- | ---: | --- | --- |
| `short` | 9,001 to 10,000 | 1,000 | Blocks of the random subsidy era. CI runs it | `fabb78a928ea1c3de0e1ad6280cdf4e913beaeb3ca260b8db26689c0d01ec563` |
| `A` | 145,001 to 155,000 | 10,000 | The first blocks with the fixed subsidy and with coinbase maturity 240 | `cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72` |
| `B` | 370,337 to 372,336 | 2,000 | The first block with an auxiliary proof of work (AuxPoW), at 371,337 | `379aa7b051f6c0d5c53070866f47060e3d99b5abd188049202e04388b787cc34` |
| `C` | 599,000 to 600,999 | 2,000 | The last subsidy change, at 600,000 | `d764ad57b7afef54eb2c1d194ff94f99d77fc7d3c04240f84af041dd0ddf0e25` |
| `D` | 1,033,383 to 1,035,382 | 2,000 | BIP34, BIP66 and the DERSIG flag, from 1,034,383. CI runs it | `0039e940b0a569464d4941fea016a988936cac79e39d342e75601d6a7712ecce` |
| `E1` | 1,198,520 to 1,200,519 | 2,000 | The version-bits state of CSV changes from `DEFINED` to `STARTED` at 1,199,520 | `ecf7c5c524986851feac0765c5ce62fd295bf3679de6105bea7490c9bd4e5a83` |
| `E2` | 1,702,520 to 1,704,519 | 2,000 | The version-bits state of CSV changes from `STARTED` to `FAILED` at 1,703,520 | `75300cf6f7cb6efc8b38f6d5abebf6a99b34f85dec62629b9c0d78d10da83064` |
| `F` | 3,463,751 to 3,465,750 | 2,000 | BIP65 and the CLTV flag, from 3,464,751 | `90a80e14416c82c832f5fc466f8708efe664ea0871c2e23c679126d2cb15cbde` |
| `H` | 5,049,001 to 5,050,000 | 1,000 | A period with a high transaction rate. The range ends at Core's last checkpoint | `31173b903e276bb360c800aee1ded4a7b7735a3a93a3b8bc816eb419250c3fcd` |

The hashes are in display order, as Core's RPC prints them.
The first block of each range names the hash of its predecessor as its previous hash.

## Run a range

You need Python 3.10 or later for the scripts, and `xz` or Python's `lzma` module to decompress the assets.
[`tests/conformance/release.json`](../tests/conformance/release.json) names the GitHub release, and gives the size and the SHA-256 of each asset and of each decompressed file.

Each range has three assets, each compressed with xz:

| Asset | File | Format |
| --- | --- | --- |
| `conformance-<range>-<a+1>-<b>.blocks.bin.xz` | `blocks.bin` | The blocks, in [`dogelib-blocks/1`](#the-blocks-dogelib-blocks1) |
| `conformance-<range>-<a+1>-<b>.manifest.json.xz` | `manifest.json` | The manifest of the blocks. A program under test does not need it |
| `conformance-<range>-<a+1>-<b>.request.json.xz` | `request.json` | The [range request](#the-range-request) |

`release.json` is a JSON object in the format `dogelib-corpus-assets/1`, with these keys:

| Key | Value |
| --- | --- |
| `format` | `"dogelib-corpus-assets/1"` |
| `repository`, `tag` | The GitHub repository and the tag of the release |
| `ranges` | A list with one object for each range: `name`, `first`, `last`, `blocks` and `files` |

`files` maps each of `blocks.bin`, `manifest.json` and `request.json` to an object.
Its keys are `asset`, `asset_bytes` and `asset_sha256` for the compressed asset, and `bytes` and `sha256` for the decompressed file.
The address of an asset is `https://github.com/<repository>/releases/download/<tag>/<asset>`.

To run one range with your own program:

1. Download the `blocks.bin` and `request.json` assets of the range from the release.
2. Check the size and the SHA-256 of each asset against `release.json`.
3. Decompress each asset, and check the size and the SHA-256 of each file against `release.json`.
4. Run your program on the request and the blocks, as [the range request](#the-range-request) defines.
5. Write the results of your program as a [results file](#the-results-dogelib-range-results1).
6. Compare the results file with the expected results:

   ```bash
   python3 -I scripts/check_range_results.py results.jsonl tests/conformance/ranges/<range>/expected.jsonl
   ```

The checker prints `PASS` and exits with status 0 when the results agree.
It prints the first difference and exits with status 1 when they disagree.
A file that is not a results file gives status 2.
The checker uses only the Python standard library, so a copy of the file alone runs it.

Outside a DogeLib clone, copy the checker and the expected results of the range, and give their paths:

```bash
python3 -I check_range_results.py results.jsonl expected.jsonl
```

The expected results of a range are the file `tests/conformance/ranges/<range>/expected.jsonl` of the repository `dghelm/DogeLib`.
`tests/conformance/SHA256SUMS` pins each of these files.
The links of this document and the paths of its commands are relative to a clone of that repository.

Steps 1 to 3 for every range, with the checks of the blocks of `scripts/fetch_blocks.py --check`, are one command of a DogeLib clone:

```bash
python3 -I scripts/conformance.py fetch
```

It writes `build/conformance/<range>/request.json` and `build/conformance/<range>/fixture/blocks.bin`.
Name ranges after the command to fetch only those ranges.

### With a dogelib-oracle/1 program

`scripts/range_results.py` writes the results file of a program that answers `block.validate` requests of the `dogelib-oracle/1` protocol ([docs/oracle.md](oracle.md#block-validation)).
The Core harness and DogeLib's oracle are two such programs.
The script uses only the Python standard library, so it also runs from a copy of the file alone.

To run a range in the Core harness:

1. Build the harness from a clone of Dogecoin Core. The build needs libevent, and it downloads Boost 1.70.0 ([BUILDING.md](../BUILDING.md)):

   ```bash
   scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness
   ```

2. Write the results file:

   ```bash
   python3 -I scripts/range_results.py --range D --request build/conformance/D/request.json --blocks build/conformance/D/fixture/blocks.bin --output build/conformance/D/results.jsonl build/core-harness/core-oracle
   ```

3. Run the checker on `build/conformance/D/results.jsonl`, as in step 6 above.

The script sends the program two requests, each to a new process.
The first is the range request with an empty blocks file. Its result has no block record, and its digest and number of coins are those of the coins of the request.
The second is the range request with the blocks file.
Each request is one line of JSON on standard input, and the response is one line on standard output.

#### An example: the short range

Each request is the object of `request.json` with two more keys, `id` and `blocks_file`.
`blocks_file` is the path of the blocks file, and a relative path starts at the working directory of the program ([docs/oracle.md](oracle.md#blocks-from-a-file)).
In the lines below, `...` marks the entries and digits that this example leaves out, so the lines are not complete JSON.
The second request of the short range is this line:

```json
{"op":"block.validate","mode":"allow_witness","check_pow":true,"check_merkle_root":true,"adjusted_time":4102444800,"chain":[{"height":9000,"time":1386921194,"bits":471492351},{"height":8999,"time":1386921171,"bits":471492351},...],"bip34_ancestor_hex":null,"coins":[{"txid_hex":"00046b16fcb77ab2...","coinbase":false,"height":5951,"outputs":[{"n":1,"value":"401139213418","script_hex":"76a9140e17c572...88ac"}]},...],"id":"range","blocks_file":"/data/short/blocks.bin"}
```

The response repeats the `id`, and the result is the object `ok`, with one record in `blocks` for each block ([docs/oracle.md](oracle.md#block-validation)):

```json
{"id":"range","ok":{"blocks":[{"height":9001,"hash_hex":"ef4043ef...","hash_display":"a94f4890d483ef62d2e59dd342187dbc41601f398045c9df0009cd8eef4340ef","valid":true,"reject_reason":null,"dos":null,"reject_code":null,"changes_digest_hex":"e4fa25152176e26ef472df4a1baf214fd251bc7f765bc6b7598b2493523d20b8","spent":47,"created":93,"set_digest_hex":null,"set_value":null},...],"out_of_domain_at":null,"set_digest_hex":"df2822c32b94e18245581f49a345faabe590f648c320112d64f92ebbe798f30d","set_coins":64545,"set_value":"137312791477033652"}}
```

The first request has the `id` `"start"` and an empty blocks file.
Its result has an empty list `blocks`, the `set_digest_hex` `d772bc6274db17c2fbcbcbedb5cfa736ed860707d6d4fbbd63bd6f1d958c6942` and the `set_coins` 35,224.

The lines of the [results file](#the-results-dogelib-range-results1) take their values from these sources:

| Line | Keys | Source |
| --- | --- | --- |
| Start | `request_sha256`, `blocks_sha256` | The SHA-256 of the files `request.json` and `blocks.bin`, not of a request line |
| Start | `start_set_digest_hex`, `start_set_coins` | `set_digest_hex` and `set_coins` of the first result |
| Block | `height`, `hash_display`, `valid`, `reject_reason`, `changes_digest_hex`, `spent`, `created` | The keys with the same names of each record of `blocks` of the second result. The other keys of the record do not go into the results |
| End | `end_set_digest_hex`, `end_set_coins` | `set_digest_hex` and `set_coins` of the second result |

So the results file of the short range starts and ends with these lines:

```json
{"format":"dogelib-range-results/1","range":"short","first":9001,"last":10000,"request_sha256":"159cf6bc689012fe4bf428eb99de9352352230c74d339283c76a6c2c26b5aa63","blocks_sha256":"ad5553cf0b0b4c68553124497cddaa4310359025c69204116c84a8c664da4c5b","start_set_digest_hex":"d772bc6274db17c2fbcbcbedb5cfa736ed860707d6d4fbbd63bd6f1d958c6942","start_set_coins":35224}
{"height":9001,"hash_display":"a94f4890d483ef62d2e59dd342187dbc41601f398045c9df0009cd8eef4340ef","valid":true,"reject_reason":null,"changes_digest_hex":"e4fa25152176e26ef472df4a1baf214fd251bc7f765bc6b7598b2493523d20b8","spent":47,"created":93}
...
{"end_set_digest_hex":"df2822c32b94e18245581f49a345faabe590f648c320112d64f92ebbe798f30d","end_set_coins":64545}
```

A response with `error` in the place of `ok` refuses the request.
When `out_of_domain_at` is not null, `blocks` has fewer records than the file has blocks.
In both cases the script writes no results file.

## The blocks: `dogelib-blocks/1`

`blocks.bin` holds the blocks of the range in height order, one record for each height of the range:

1. The height, as a 4-byte little-endian integer.
2. The length of the block in bytes, as a 4-byte little-endian integer. The length is at most 33,554,432, Core's `MAX_SIZE`.
3. The block, exactly as Core serializes it on the network. That is the 80-byte header, then the AuxPoW payload when bit 8 of the version is set. The CompactSize count and the transactions follow.

The file has no header and no other framing.
The block hash is the double SHA-256 of the 80-byte header.

`manifest.json` is a JSON object that describes the blocks.
It has the format name `dogelib-blocks/1`, the heights and the number of blocks and of bytes.
For each block it has the hash, the size and the number of transactions.

`scripts/fetch_blocks.py --check` checks a directory of both files and their `SHA256SUMS`.
It checks the headers, the Merkle roots, the links between the blocks and the hashes that the repository pins.
The committed list `tests/block/mainnet-blocks/ranges/<range>/hashes.txt` pins the hash of each block of the ranges A to H.
The hashes of the short range are pinned by `tests/block/mainnet-subsidy-prev-hashes`.

## The range request

The range request is one JSON object with exactly these keys:

| Key | Value in the corpus | Meaning |
| --- | --- | --- |
| `op` | `"block.validate"` | The operation |
| `mode` | `"allow_witness"` | The read mode of every transaction. It is the mode of Core's network and disk paths. |
| `check_pow` | `true` | Core's `fCheckPOW`: `CheckBlockHeader` checks the proof of work, with the AuxPoW rules of mainnet |
| `check_merkle_root` | `true` | Core's `fCheckMerkleRoot`: `CheckBlock` checks the Merkle root and the duplicate transactions of CVE-2012-2459 |
| `adjusted_time` | `4102444800` | Core's adjusted network time, in seconds since 1970. The value is 2100-01-01, so that no block of the corpus is too far in the future |
| `chain` | A list | The headers below the first block (see [the chain](#the-chain)) |
| `bip34_ancestor_hex` | A hash or `null` | The hash of the block at height 1,034,383 below the predecessor, in serialization order, or `null` when the predecessor is below that height |
| `coins` | A list | The coins before the first block (see [the coins](#the-coins)) |

Hexadecimal strings hold bytes in the order in which Core serializes them.
For a hash, that order is the reverse of the display order.

### The verdict of a block

A program runs Core's checks of a new block on each block of the file in order, and stops at the first check that fails.
The checks are these functions of Dogecoin Core at the pinned commit, with these arguments:

1. `CheckBlockHeader`, with `fCheckPOW` from `check_pow`.
2. `ContextualCheckBlockHeader` on the predecessor, with checkpoints disabled and with the adjusted time of the request.
3. `CheckBlock`, with `fCheckPOW` and `fCheckMerkleRoot` from the request.
4. `ContextualCheckBlock` on the predecessor.
5. `ConnectBlock` on the coins, with `fJustCheck` true, with every script checked and with no assumed-valid block.

For the genesis block, steps 1 and 2 do not run, and step 5 adds no coin.
No range of the corpus holds the genesis block.

A block that passes all five checks is *accepted*.
It becomes the predecessor of the next block, and its changes enter the coins.
A *rejected* block changes nothing, and the next block of the file must also extend the same predecessor.
Each block must name the hash of the current predecessor as its previous hash.
The first block names the predecessor of the request, whose hash the table of [the ranges](#the-ranges) gives.

The checks read the consensus parameters of mainnet.
These include the subsidy, the difficulty rules, the AuxPoW chain ID, the heights of BIP34, BIP65 and BIP66, and the deployments of CSV and SegWit.
Core reads the script verification flags of a block from its height and its predecessor.

#### Where Core defines the rules

This document names Core's checks, but it does not restate the rules inside them.
A program of your own needs the source of Dogecoin Core at the pinned commit for those rules.
The table names, for each rule that a verdict depends on, the files of Core and the functions or constants that define it.
The paths are relative to the root of the Core repository, and [SOURCES.md](../SOURCES.md) links each file at the pin:

| Rule | Files | Functions and constants |
| --- | --- | --- |
| Serialization of blocks and transactions, the transaction ID and CompactSize | `src/primitives/block.h`, `src/primitives/pureheader.h`, `src/primitives/transaction.h`, `src/primitives/transaction.cpp`, `src/serialize.h` | `CBlock::SerializationOp`, `CPureBlockHeader`, `SerializeTransaction`, `UnserializeTransaction`, `CTransaction::ComputeHash`, `ReadCompactSize`, `MAX_SIZE` |
| Proof of work and the target | `src/dogecoin.cpp`, `src/pow.cpp`, `src/primitives/pureheader.cpp`, `src/crypto/scrypt.cpp`, `src/arith_uint256.cpp`, `src/auxpow.cpp`, `src/chainparams.cpp` | `CheckAuxPowProofOfWork`, `CheckProofOfWork`, `CPureBlockHeader::GetPoWHash`, `scrypt_1024_1_1_256_sp_generic`, `arith_uint256::SetCompact`, `UintToArith256`, `CAuxPow::check`, `powLimit` |
| Difficulty retarget | `src/pow.cpp`, `src/dogecoin.cpp`, `src/chainparams.cpp` | `GetNextWorkRequired`, `CalculateDogecoinNextWorkRequired`, `AllowDigishieldMinDifficultyForBlock`, `nPowTargetTimespan`, `nPowTargetSpacing`, `CChainParams::GetConsensus` |
| Median time, the future limit and transaction finality | `src/chain.h`, `src/validation.cpp`, `src/script/script.h` | `CBlockIndex::GetMedianTimePast`, `nMedianTimeSpan`, `ContextualCheckBlockHeader`, `ContextualCheckBlock`, `IsFinalTx`, `LOCKTIME_THRESHOLD` |
| Random subsidy | `src/dogecoin.cpp`, and `boost/random/mersenne_twister.hpp` and `boost/random/uniform_int.hpp` of Boost 1.70.0 | `generateMTRandom`, `GetDogecoinBlockSubsidy`, `boost::mt19937`, `boost::uniform_int` |
| Coinbase maturity and BIP30 | `src/validation.cpp`, `src/chainparams.cpp`, `src/chainparams.h` | `Consensus::CheckTxInputs`, `GetSpendHeight`, `ConnectBlock`, `nCoinbaseMaturity`, `CChainParams::GetConsensus` |
| Script verification and signatures | `src/validation.cpp`, `src/script/interpreter.cpp`, `src/script/script.h`, `src/script/script_error.cpp`, `src/pubkey.cpp`, `src/secp256k1/` | `ConnectBlock`, `CheckInputs`, `VerifyScript`, `EvalScript`, `SignatureHash`, `CheckSignatureEncoding`, `ScriptErrorString`, `CPubKey::Verify`, `ecdsa_signature_parse_der_lax`, `MAX_SCRIPT_SIZE`, `MAX_OPS_PER_SCRIPT` |
| Bounds of blocks and transactions, signature operations, amounts and the order of the checks | `src/validation.cpp`, `src/consensus/consensus.h`, `src/consensus/merkle.cpp`, `src/amount.h`, `src/script/script.cpp` | `CheckBlock`, `CheckTransaction`, `ContextualCheckBlock`, `ConnectBlock`, `GetLegacySigOpCount`, `GetP2SHSigOpCount`, `GetTransactionSigOpCost`, `BlockMerkleRoot`, `MAX_BLOCK_BASE_SIZE`, `MAX_BLOCK_WEIGHT`, `MAX_BLOCK_SIGOPS_COST`, `MAX_MONEY`, `MoneyRange`, `CScript::GetSigOpCount` |

### The chain

`chain` lists headers below the first block, newest first.
The first entry is the predecessor, and each later entry is the block below the one before it.
Each entry is an object with these keys:

- `height`: the height of the block.
- `time`: `nTime` of its header.
- `bits`: `nBits` of its header, as a number.
- `version`: `nVersion` of its header, as an unsigned 32-bit number. Only the entries of the ranges E1 and E2 have it.

The chain gives no hash. The hash of the predecessor is the previous hash of the first block.
The chain is long enough for every read of Core below the first block:

- The median time of the last 11 blocks.
- The difficulty retarget.
- The version-bits states of CSV and SegWit, which need the median time of the aligned period boundary and its ten predecessors.

In the ranges E1 and E2 the aligned period boundary has a median time between the start and the timeout of the CSV deployment.
Core's `VersionBitsState` then walks back one period at a time, to the last boundary whose median time is below the CSV start.
It counts the versions of the blocks above that boundary.
So the chain of E1 and E2 reaches that boundary, at height 1,189,439, and its ten predecessors, and each entry has a version.
The chain of E2 has 513,092 entries.
On mainnet, CSV never reaches `LOCKED_IN`, and SegWit is never active.

### The coins

`coins` is a list of objects, one for each transaction ID that has a coin:

| Key | Value |
| --- | --- |
| `txid_hex` | The transaction ID, 32 bytes in serialization order |
| `coinbase` | `true` when the transaction is a coinbase |
| `height` | The height of the block of the transaction |
| `outputs` | The unspent outputs of the transaction, in index order. Each is `{n, value, script_hex}`: the output index, the amount in koinu as a string of decimal digits, and the script |

A transaction ID occurs once, and each entry has at least one output.
The coins obey the bounds of the snapshot format ([the snapshot](#the-snapshot-dogelib-coins1)):

- The height is from 0 to 2,147,483,646.
- The output index `n` is from 0 to 1,048,575, and one entry has each index at most once.
- The amount is from 0 to `MAX_MONEY`, 1,000,000,000,000,000,000 koinu.
- No script starts with `OP_RETURN` or has more than 10,000 bytes, because Core's coin set never holds such an output.

The oracle and the Core harness both refuse a request whose coins break one of these rules.
The order of the entries does not matter.

The coins of a range request are its *restricted coins*.
Core's harness replayed mainnet from the genesis block and wrote its coin set at the predecessor's height as a [snapshot](#the-snapshot-dogelib-coins1).
Let `T` be the set of transaction IDs that the blocks of the range name.
The restricted coins are the coins of that snapshot whose transaction ID is in `T`.
`T` holds the ID of each transaction of the range, and the ID in the outpoint of each input.

Core's checks of a block read coins only by those IDs.
So each block gets the same verdict and the same changes on the restricted coins as on the whole coin set.
DogeLib proves this property of its own model as `validateBlock_restrict` ([docs/soundness/blocks.md](soundness/blocks.md#validateblock_restrict-a-block-on-the-coins-that-it-names)).
For Core, the evidence is a test on the short range and the ranges A to D, F and H ([provenance](#provenance)).
There Core's block records on the restricted coins equal those of recorded runs on the whole coin set.

## Digests

A digest covers a list of coin records.
A *coin record* is these bytes:

1. One tag byte: 0 for a spent coin, 1 for a created coin, 2 for a member of a set.
2. The outpoint: the 32 bytes of the transaction ID in serialization order, then the output index in 4 little-endian bytes.
3. The height of the coin's transaction, as a 4-byte little-endian integer.
4. One byte: 1 for a coin of a coinbase, and 0 otherwise.
5. The output as Core serializes a `CTxOut`: the amount in 8 little-endian bytes, the CompactSize length of the script, and the script.

A digest starts as 32 zero bytes.
For each record in order, the digest `d` becomes the double SHA-256 of `d` followed by the record.
The digest is written as 64 lowercase hexadecimal digits of its 32 bytes, in the order of the hash output.

The *digest of the changes* of an accepted block visits its changes in the order of Core's `UpdateCoins`.
It takes the transactions in block order.
For each transaction, it takes the coin of each input in input order with the tag 0.
Then it takes each output that enters the set, in output order, with the tag 1.
The coinbase has no input record.
An output whose script starts with `OP_RETURN` or has more than 10,000 bytes enters no set and has no record.

The *digest of a set* visits every coin of the set with the tag 2.
The transaction IDs are in the order of their 32 bytes in serialization order, compared as byte strings.
The outputs of one ID are in index order.

A spent coin has the height and the coinbase byte of its transaction.
A created coin has the height of its block, and the coinbase byte 1 exactly when it is an output of the coinbase.

## The results: `dogelib-range-results/1`

A results file holds one line of JSON for the start, one for each block record, and one for the end.
Each line is a JSON object, and the file ends with a newline.
The order of the keys and the white space in a line do not matter.

The start line has these keys:

| Key | Value |
| --- | --- |
| `format` | `"dogelib-range-results/1"` |
| `range` | The name of the range, such as `"D"` |
| `first`, `last` | The heights of the first and the last record of `blocks.bin` |
| `request_sha256` | The SHA-256 of the file `request.json`, as 64 lowercase hexadecimal digits |
| `blocks_sha256` | The SHA-256 of the file `blocks.bin` |
| `start_set_digest_hex` | The digest of the set of the coins of the request |
| `start_set_coins` | The number of coins of the request: the sum of the numbers of outputs of its entries |

Each block line has these keys, for the blocks of `blocks.bin` in order.
A results file has exactly one block line for each block, so the heights run from `first` to `last` without a gap.

So the format covers a range of consecutive heights in which every block is accepted.
A rejected block can stand only at the last height, because the next candidate after it has the same height ([docs/oracle.md](oracle.md#blocks-from-a-file)).
Every block of the corpus is accepted.

| Key | Value |
| --- | --- |
| `height` | The height of the block |
| `hash_display` | The hash of the block in display order |
| `valid` | `true` for an accepted block, `false` for a rejected block |
| `reject_reason` | `null` for an accepted block. For a rejected block, the reject reason of Core's `CValidationState`, such as `"bad-txns-inputs-missingorspent"` |
| `changes_digest_hex` | The digest of the changes of an accepted block, or `null` |
| `spent`, `created` | The numbers of spent and created coins of an accepted block, or `null` |

The end line has these keys:

| Key | Value |
| --- | --- |
| `end_set_digest_hex` | The digest of the set of the coins after the last accepted block |
| `end_set_coins` | The number of those coins |

The checker compares the values of each line with the expected results, in order.
It reports a missing block, an added block, and each field that differs.
It also refuses a file whose block lines do not cover the heights from `first` to `last` once each, in order.
A script reason of `ConnectBlock` has the form `mandatory-script-verify-flag-failed (<text>)`, with the text of Core's `ScriptErrorString` ([docs/oracle.md](oracle.md#block-validation) lists the reasons).

## The snapshot: `dogelib-coins/1`

A *snapshot* is a coin set as a file.
The corpus does not publish snapshots, because they are large: the snapshot at height 5,049,000 holds 87,775,851 coins.
The format defines the start of each range, and the restricted coins come from it.
The manifest of each snapshot is committed in [`tests/block/mainnet-blocks/snapshots`](../tests/block/mainnet-blocks/snapshots).

A snapshot is the coin records of the whole set under the tag 2, in the order of the [digest of a set](#digests).
The file has no header, no count and no other framing.
So one coin set has exactly one byte sequence as its snapshot.
The digest of the set is the digest over the records of the file in order.

A reader rejects a file with any of these faults:

- The file ends inside a record, or a byte follows the last complete record.
- A tag other than 2.
- An output index of 1,048,576 or more.
- A height above 2,147,483,646.
- A coinbase byte other than 0 and 1.
- An amount above `MAX_MONEY`, 10,000,000,000 coins of 100,000,000 koinu each, read as an unsigned 64-bit integer.
- A script length that is not in the shortest CompactSize form.
- A script that starts with `OP_RETURN` or has more than 10,000 bytes.
- A record that is not above the record before it in the order of the set.
- A record with the transaction ID of the record before it and another height or coinbase byte.

A manifest is a JSON object with these keys:

| Key | Value |
| --- | --- |
| `format` | `"dogelib-coins/1"` |
| `height` | The height of the last accepted block |
| `block_hash_hex`, `block_hash_display` | The hash of that block, in both byte orders |
| `coins` | The number of records |
| `set_digest_hex` | The digest of the set |
| `set_value` | The sum of the amounts, in koinu, as a string of decimal digits |
| `bytes`, `sha256` | The length and the SHA-256 of the file |

To make a snapshot again, build the Core harness at the pin and run the Core pass on blocks from your own node ([docs/core-harness.md](core-harness.md#the-core-pass)).
The file must have the SHA-256, the digest and the number of coins of the committed manifest.

## Provenance

[`tests/generators.toml`](../tests/generators.toml) records, for each expected-results file, the program that wrote it and the inputs of the run:

- The Core harness, its Core commit and the DogeLib commit of its build.
- The SHA-256 of the range request and of the blocks.
- The oracle build that gave the same results in the same run, and the times of both programs.

`scripts/conformance.py compare` made each run.
It requires that the two `block.validate` responses agree in every field of the full comparison.
It also requires that the checker passes on the oracle's results against the harness's results.
For the ranges with a recorded run on the whole coin set ([docs/comparison-evidence.md](comparison-evidence.md#the-conformance-corpus)), it also requires the block records of that run.
`tests/conformance/SHA256SUMS` pins each expected-results file.

## Versions

Each format has a name with a version: `dogelib-blocks/1`, `dogelib-coins/1`, `dogelib-range-results/1`, and `dogelib-corpus-assets/1` for `release.json`.
The range request is a request of the protocol `dogelib-oracle/1`.
The assets belong to a release with a dated tag.
A change of a published file is a new release with a new tag, and the old tag stays.

## Related documents

- [Design record 0011](design/0011-mainnet-ranges.md): the ranges, the snapshots and the corpus.
- [docs/oracle.md](oracle.md#block-validation): the operation `block.validate` and its record fields.
- [docs/core-harness.md](core-harness.md): the Core harness and the Core pass.
- [docs/comparison-evidence.md](comparison-evidence.md#the-conformance-corpus): the recorded runs of the corpus.
