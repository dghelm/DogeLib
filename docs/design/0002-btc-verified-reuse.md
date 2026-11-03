Q: Also, is there anything from <https://github.com/ProofOfKeags/btc-verified> that we should consider pulling in early on?

**Yes. btc-verified should supply a substantial part of DogeLib’s initial serialization foundation.** After inspecting the actual definitions and theorem statements, I would make the first milestone **reuse and adapt the existing codecs, then prove the Dogecoin-specific compatibility rules**.

The most valuable part is its relationship between a simple specification and a packed-byte implementation. That already demonstrates the kind of optimization guarantee you want: different representations and execution strategies, with a proof that they accept the same inputs and produce the same results.

There are several concrete adaptation tasks, including **a difference between its proof-trust policy and the contribution policy**. Those should be handled during bootstrap.

I reviewed commit `ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce`, the pin already recorded in design record 0001. This assessment is based on source and theorem inspection; I have not built the combined DogeLib dependencies or attempted the port.

## 1. What I would pull in first

| Component | Recommendation | Value to DogeLib |
|---|---|---|
| **Generic prefix codecs and fixed-width encodings** | Reuse early | Avoid repeatedly proving byte order, field composition, and round trips |
| **ByteArray/ByteSlice abstraction lemmas** | Reuse early | Connect convenient mathematical representations to practical byte buffers |
| **Packed codec refinement** | Reuse early | Establish exact equivalence between simple and efficient encoders/decoders |
| **CompactSize and counted lists** | Adapt early | Reuse the generic machinery while adding Dogecoin’s bounds and error contract |
| **Raw Script and transaction component types** | Reuse selectively | Preserve wire bytes and compose transaction serialization |
| **Transaction-ID commitment proofs** | Adapt to DogeLib’s transaction model | Connect serialization properties to commitment properties |
| **Merkle root and implementation-refinement proofs** | Bring in when block work starts | A useful second example of specification versus implementation |
| **Bitcoin’s complete transaction dispatch and consensus rules** | Review individually | These contain Bitcoin-specific parsing choices, constants, and assumptions |

The first three are especially attractive because their usefulness extends beyond Dogecoin.

### Generic codec composition

[`Serialize/Codec.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/Codec.lean) packages an encoder and prefix-consuming decoder together with two laws:

- Encoding followed by decoding returns the value and preserves the trailing bytes.
- Every successful decode consumed exactly the canonical encoding of the returned value.

It then provides composition and transport machinery, including:

- `encode_injective`
- `instCodecProd`
- `Codec.ofEquiv`
- Generic little-endian fixed-width encoding and decoding
- Instances for the ordinary fixed-width integer types

For DogeLib, that means a transaction component can obtain its serialization properties by composing already-proved field codecs.

**One qualification:** this abstraction specifically describes *canonical* codecs. Some historical parsers accept several encodings of the same semantic value. Those need a more permissive contract. We should use this class where its laws match the protocol, and retain separate parser relations where they do not.

## 2. The packed-codec layer is the strongest early reuse opportunity

I would prioritize these files:

- [`Ext/ByteArray.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Ext/ByteArray.lean)
- [`Ext/ByteSlice.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Ext/ByteSlice.lean)
- [`Packed/Codec.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Packed/Codec.lean)

The simple specification operates over lists of bytes. The packed implementation reads from slices of a byte array and appends to byte-array buffers.

Its core obligations are essentially:

```text
bytes produced by packed encoding
  = bytes produced by specification encoding

packed decoding, viewed through the abstraction
  = specification decoding
```

That second equality includes **failure, the decoded value, and the exact remaining bytes**. It is stronger than checking that successful parses return matching values. The actual interface expresses this through `toList_encodeInto` and `abstractParse_decodeSlice`. [Packed codec source](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Packed/Codec.lean).

This is strategically useful for your project because it supplies an existing example of:

> A readable specification, a different implementation representation, and a proof that the change preserves behavior.

DogeLib could inherit that foundation while keeping **legacy signature-preimage equivalence** as its first substantial Dogecoin-specific optimization proof.

I would benchmark the resulting DogeLib implementation independently. Upstream performance measurements do not establish performance for our port, toolchain, or workloads.

## 3. CompactSize is reusable, with an important Dogecoin wrapper

The generic CompactSize implementation is useful, but its accepted domain differs from the Core-compatible reader proposed in the handoff.

btc-verified’s decoder enforces canonical encoding but accepts the full `UInt64` range. Dogecoin Core v1.14.9’s reader additionally rejects decoded values above `MAX_SIZE = 0x02000000`. [btc-verified CompactSize](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/CompactSize.lean); [Dogecoin serialization](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/serialize.h).

A concrete distinguishing input, derived from those definitions, is:

```text
fe 01 00 00 02
```

That canonically encodes `0x02000001`, or 33,554,433:

- The generic btc-verified decoder accepts it.
- The selected Dogecoin Core reader rejects it for exceeding its serialization bound.

That gives us an excellent first DogeLib-specific proof obligation:

```text
dogeDecode(bytes) = success(value, remainder)
  iff
genericDecode(bytes) = success(value, remainder)
  and value <= dogecoinSerializationLimit
```

### How I would implement that boundary

Keep the generic encoding and its proofs available. Add a separately named Dogecoin-compatible bounded reader, then prove its acceptance relation and its bounded round-trip property.

**Do not replace the generic decoder inside an existing unconditional `Codec UInt64` instance while retaining its old laws.** Once the decoder rejects some encodable values, that unconditional inverse law no longer holds. A separate bounded reader or a suitable bounded value type makes the distinction explicit.

The same issue propagates into [`CountedList`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/CountedList.lean). Its type ensures the list length fits in 64 bits. That establishes representability; it does not establish Dogecoin’s size limits or practical resource bounds. The applicable count checks should happen before expensive parsing or allocation.

Upstream decoders also use `Option`, which collapses failure reasons. If DogeLib exposes richer typed errors, we can prove acceptance/value agreement after forgetting those distinctions and separately specify any error categories consumers need.

## 4. Start transaction reuse at `TxBody`

I would investigate adapting the component types and their product-codec structure:

- `OutPoint`
- `Script`
- `TxIn`
- `TxOut`
- `TxBody`

[`TxBody`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Transaction/TxBody.lean) contains the witness-free fields we need: version, ordered inputs, ordered outputs, and locktime. Its ordinary and packed codecs are assembled from those fields.

The top-level [`Tx`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Transaction/Tx.lean) has a more specific purpose. It models Bitcoin’s witness-aware dispatch with:

- A legacy constructor requiring nonempty inputs.
- A special empty transaction constructor.
- A SegWit constructor with witness invariants.
- Parsing choices motivated by Bitcoin Core’s witness-aware decoder.

That is a different contract from DogeLib’s initial **base/no-witness parser**. Starting from the component structure keeps our parsing choices explicit.

### Raw unsigned storage can still preserve signed fields

One useful clarification for the handoff: btc-verified stores output amounts as `UInt64` and versions as `UInt32`. Those types preserve every raw bit pattern. They can therefore be suitable wire representations, provided DogeLib adds the appropriate signed interpretation and proves its correspondence to Core.

For example, all-one amount bits can be interpreted as signed `-1`; they do not need to be lost or rejected during deserialization. The distinction is between **stored bits** and **the meaning assigned to those bits**. [Transaction output source](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Transaction/TxOut.lean).

The raw [`Script`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Script/Script.lean) wrapper is also a good fit: it preserves uninterpreted program bytes and supplies codecs without requiring the program to execute successfully.

## 5. Reconcile proof trust before adopting the proofs

This is the most important addition to the bootstrap plan.

Our contribution policy starts with a strict target whose logical baseline is the ordinary Lean axioms, with additional trust requiring an explicit policy change.

btc-verified’s actual [`Tests/AxiomAudit.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/Tests/AxiomAudit.lean) deliberately allows:

- `propext`
- `Classical.choice`
- `Quot.sound`
- Generated native `bv_decide` axioms matching `._native.bv_decide.ax_*`

This is an intentional upstream policy. It is not an audit failure.

There are relevant uses in the code: `CompactSize.decode_encode` and `encode_head` use `bv_decide` for small bit-vector facts. [CompactSize proof source](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/CompactSize.lean).

**My recommendation is to retain our initial policy and adapt the proofs we need:**

1. Select the exact declarations DogeLib will use.
2. Audit their transitive proof dependencies under the chosen toolchain.
3. Replace relevant native-dependent proof steps with ordinary kernel-checked arguments.
4. Re-run the audit after dependency or toolchain changes.

The two CompactSize facts are concrete initial candidates. I would not assume they exhaust the dependency closure without building and auditing it.

Also, importing a module that contains a native-dependent theorem does not mean every declaration from that module depends on that assumption. The audit should follow the definitions and proofs actually used.

### Toolchain and layout need a small integration experiment

The inspected btc-verified pin uses **Lean 4.30.0-rc2**, while the EthLib version we inspected uses **4.35.0**. A combined dependency setup needs an actual build before we claim compatibility. [btc-verified toolchain](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/lean-toolchain); [EthLib build configuration](https://github.com/ethereum/EthLib/blob/5d4b58402075ba972936bd446e274c0f4d3e11a5/lakefile.lean).

btc-verified also colocates definitions, proofs, and packed instances, and even its generic codec module imports Mathlib. That differs from the separation we proposed. The integration experiment should decide whether narrow dependency imports are sufficient or whether a small adaptation should separate those concerns.

## 6. Choose one SHA-256 foundation deliberately

btc-verified has a concrete, executable SHA-256 implementation, double hashing, length theorems, and known-answer testing. Its inspected source does not contain the independent general FIPS-equivalence theorem we found in EthLib. [btc-verified SHA-256](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Crypto/Sha256.lean).

EthLib’s `hash_eq_spec` theorem therefore makes its SHA-256 implementation a particularly attractive candidate for our shared hash provider. [EthLib SHA-256 proof](https://github.com/ethereum/EthLib/blob/5d4b58402075ba972936bd446e274c0f4d3e11a5/EthLib/Cryptography/Proofs/Hash/Sha256.lean).

My preference would be:

- Reuse btc-verified’s serialization and representation-refinement work.
- Evaluate EthLib as the SHA-256 provider.
- Define Dogecoin’s double-hash composition and byte conventions explicitly.
- Adapt commitment proofs to that selected provider.

Existing btc-verified transaction-ID definitions call its own hash implementation. Switching providers requires an explicit adaptation or an equality theorem; an alias alone does not transfer the proofs.

### Reuse the commitment-proof pattern carefully

[`Tx.txid_binding`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Transaction/Txid.lean) connects equal transaction IDs to equal transaction bodies **or an explicit hash-collision witness**. That is a useful theorem structure for DogeLib.

Its [`CollisionResistant`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Crypto/Collision.lean) helper, however, literally means no collisions exist. It is not a computational security game expressing that collisions are infeasible to find. The repository acknowledges that global collision absence is false for a finite-output hash on an unbounded input domain.

We should preserve the explicit collision-reduction results and introduce an appropriate computational model when we need actual security claims.

## 7. Useful later imports—and work that remains ours

### Merkle refinement is a strong second-stage candidate

The pair of modules:

- [`Crypto/Merkle.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Crypto/Merkle.lean)
- [`Impl/BitcoinCore/Merkle.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Impl/BitcoinCore/Merkle.lean)

provides a structural tree specification and a bottom-up implementation shaped after Core, with actual equivalence theorems.

I would bring this in when block commitments become part of the work. Preserve the theorem hypotheses and the full mutation-check behavior: the source explicitly notes that its abstract canonicality property is weaker than Core’s mutation rejection.

These proofs concern a Lean transcription. They do not verify the C++ binary.

### The generic rule abstraction is worth considering

[`Consensus/Rule.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Consensus/Rule.lean) packages:

- A semantic predicate.
- An executable Boolean check.
- A theorem that the check accepts exactly when the predicate holds.

It also provides composition and conditional enforcement. That could be useful once DogeLib starts assembling contextual validation rules and proposed revisions.

Bitcoin-specific rule assemblies need individual review. The inspected limits module, for example, includes Bitcoin’s monetary bound, coinbase maturity, and block-weight constants. [Consensus limits](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Consensus/Limits.lean).

### Legacy sighash and Script execution remain substantive DogeLib work

The inspected tree does not supply the legacy signature-hash implementation proposed in our handoff. Its Script layer currently provides raw representation and serialization; [`Consensus/ScriptCheck.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Consensus/ScriptCheck.lean) explicitly leaves Script validity as a parameter.

That makes the projects complementary: reusable serialization work can get us to the Dogecoin-specific signing and execution work sooner.

## How I would change the bootstrap plan

I would make the first contribution **“adopt audited codec foundations and define Dogecoin’s bounded decoding contract.”**

Its scope would be:

1. **Select a narrow upstream dependency set:** generic codecs, fixed-width facts, byte representations, and packed refinements.
2. **Resolve toolchain and proof-trust differences:** build the selected modules and audit the declarations we depend on.
3. **Implement the bounded CompactSize adapter:** prove its exact accepted domain, returned value, and remainder.
4. **Compose the base transaction representation:** use the existing field-codec structure with Dogecoin-specific interpretation and limits.
5. **Proceed to legacy signing commitments:** retain the reference-versus-streaming proof as the first substantial new optimization result.

For adoption, I would first try a pinned dependency with narrow imports. If the toolchain or module boundaries make that awkward, use a small, traceable adaptation with upstream provenance and preserved notices. We should keep the generic changes easy to contribute upstream later.

**The main change is that DogeLib can begin with an existing proved serialization substrate. Its first new proofs can concentrate on the boundary between that substrate and Dogecoin’s actual behavior.**
