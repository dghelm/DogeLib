// Adapted from Dogecoin Core e0a1c157791544e818c901bd9341896965afbf9d,
// src/test/auxpow_tests.cpp, helpers and check_auxpow (lines 31-323).
// Copyright (c) 2014-2015 Daniel Kraft
// Distributed under the MIT/X11 software license. See LICENSES/dogecoin-core-MIT.txt.
// The test lock is omitted: this standalone harness has no concurrent chain state.
// A local empty COINBASE_FLAGS replaces the empty test-time global in validation.cpp.
// Explicit mainnet Params replaces the test suite's selected Params().
// BOOST_CHECK sites emit their constructed payload and actual Core verdict.

const CScript COINBASE_FLAGS;

static void
tamperWith(uint256& num)
{
    arith_uint256 modifiable = UintToArith256(num);
    modifiable += 1;
    num = ArithToUint256(modifiable);
}

/**
 * Utility class to construct auxpow's and manipulate them.  This is used
 * to simulate various scenarios.
 */
class CAuxpowBuilder
{
public:
    /** The parent block (with coinbase, not just header).  */
    CBlock parentBlock;

    /** The auxpow's merkle branch (connecting it to the coinbase).  */
    std::vector<uint256> auxpowChainMerkleBranch;
    /** The auxpow's merkle tree index.  */
    int auxpowChainIndex;

    /**
   * Initialise everything.
   * @param baseVersion The parent block's base version to use.
   * @param chainId The parent block's chain ID to use.
   */
    CAuxpowBuilder(int baseVersion, int chainId);

    /**
   * Set the coinbase's script.
   * @param scr Set it to this script.
   */
    void setCoinbase(const CScript& scr);

    /**
   * Build the auxpow merkle branch.  The member variables will be
   * set accordingly.  This has to be done before constructing the coinbase
   * itself (which must contain the root merkle hash).  When we have the
   * coinbase afterwards, the member variables can be used to initialise
   * the CAuxPow object from it.
   * @param hashAux The merge-mined chain's block hash.
   * @param h Height of the merkle tree to build.
   * @param index Index to use in the merkle tree.
   * @return The root hash, with reversed endian.
   */
    std::vector<unsigned char> buildAuxpowChain(const uint256& hashAux, unsigned h, int index);

    /**
   * Build the finished CAuxPow object.  We assume that the auxpowChain
   * member variables are already set.  We use the passed in transaction
   * as the base.  It should (probably) be the parent block's coinbase.
   * @param tx The base tx to use.
   * @return The constructed CAuxPow object.
   */
    CAuxPow get(const CTransactionRef tx) const;

    /**
   * Build the finished CAuxPow object from the parent block's coinbase.
   * @return The constructed CAuxPow object.
   */
    inline CAuxPow
    get() const
    {
        assert(!parentBlock.vtx.empty());
        return get(parentBlock.vtx[0]);
    }

    /**
   * Build a data vector to be included in the coinbase.  It consists
   * of the aux hash, the merkle tree size and the nonce.  Optionally,
   * the header can be added as well.
   * @param header Add the header?
   * @param hashAux The aux merkle root hash.
   * @param h Height of the merkle tree.
   * @param nonce The nonce value to use.
   * @return The constructed data.
   */
    static std::vector<unsigned char> buildCoinbaseData(bool header, const std::vector<unsigned char>& auxRoot, unsigned h, int nonce);
};

CAuxpowBuilder::CAuxpowBuilder(int baseVersion, int chainId)
    : auxpowChainIndex(-1)
{
    parentBlock.SetBaseVersion(baseVersion, chainId);
}

void CAuxpowBuilder::setCoinbase(const CScript& scr)
{
    CMutableTransaction mtx;
    mtx.vin.resize(1);
    mtx.vin[0].prevout.SetNull();
    mtx.vin[0].scriptSig = scr;

    parentBlock.vtx.clear();
    parentBlock.vtx.push_back(MakeTransactionRef(std::move(mtx)));
    parentBlock.hashMerkleRoot = BlockMerkleRoot(parentBlock);
}

std::vector<unsigned char>
CAuxpowBuilder::buildAuxpowChain(const uint256& hashAux, unsigned h, int index)
{
    auxpowChainIndex = index;

    /* Just use "something" for the branch.  Doesn't really matter.  */
    auxpowChainMerkleBranch.clear();
    for (unsigned i = 0; i < h; ++i)
        auxpowChainMerkleBranch.push_back(ArithToUint256(arith_uint256(i)));

    const uint256 hash = CAuxPow::CheckMerkleBranch(hashAux, auxpowChainMerkleBranch, index);

    std::vector<unsigned char> res = ToByteVector(hash);
    std::reverse(res.begin(), res.end());

    return res;
}

CAuxPow
CAuxpowBuilder::get(const CTransactionRef tx) const
{
    CAuxPow res(tx);
    res.InitMerkleBranch(parentBlock, 0);

    res.vChainMerkleBranch = auxpowChainMerkleBranch;
    res.nChainIndex = auxpowChainIndex;
    res.parentBlock = parentBlock;

    return res;
}

std::vector<unsigned char>
CAuxpowBuilder::buildCoinbaseData(bool header, const std::vector<unsigned char>& auxRoot, unsigned h, int nonce)
{
    std::vector<unsigned char> res;

    if (header)
        res.insert(res.end(), UBEGIN(pchMergedMiningHeader),
            UEND(pchMergedMiningHeader));
    res.insert(res.end(), auxRoot.begin(), auxRoot.end());

    const int size = (1 << h);
    res.insert(res.end(), UBEGIN(size), UEND(size));
    res.insert(res.end(), UBEGIN(nonce), UEND(nonce));

    return res;
}

UniValue reconstructAuxPowFixtures()
{
    UniValue rows(UniValue::VARR);
    auto record = [&](int line, const CAuxPow& a, const uint256& hash, int chainId,
                      const Consensus::Params& params, bool expected) {
        CDataStream ds(SER_NETWORK, PROTOCOL_VERSION);
        ds << a;
        UniValue row(UniValue::VOBJ);
        row.pushKV("line", line);
        row.pushKV("payload_hex", HexStr(ds.begin(), ds.end()));
        row.pushKV("hash_aux_block_hex", hex(hash.begin(), hash.end()));
        row.pushKV("chain_id", chainId);
        row.pushKV("strict_chain_id", params.fStrictChainId);
        row.pushKV("expected", expected);
        row.pushKV("valid", a.check(hash, chainId, params));
        rows.push_back(row);
    };
    const Consensus::Params& params = Params(CBaseChainParams::MAIN).GetConsensus(371337);
    CAuxpowBuilder builder(5, 42);
    CAuxPow auxpow;

    const uint256 hashAux = ArithToUint256(arith_uint256(12345));
    const int32_t ourChainId = params.nAuxpowChainId;
    const unsigned height = 30;
    const int nonce = 7;
    int index;

    std::vector<unsigned char> auxRoot, data;
    CScript scr;

    /* Build a correct auxpow.  The height is the maximally allowed one.  */
    index = CAuxPow::getExpectedIndex(nonce, ourChainId, height);
    auxRoot = builder.buildAuxpowChain(hashAux, height, index);
    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height, nonce);
    scr = (CScript() << 2809 << 2013) + COINBASE_FLAGS;
    scr = (scr << OP_2 << data);
    builder.setCoinbase(scr);
    record(204, builder.get(), hashAux, ourChainId, params, true);

    /* An auxpow without any inputs in the parent coinbase tx should be
     handled gracefully (and be considered invalid).  */
    CMutableTransaction mtx(*builder.parentBlock.vtx[0]);
    mtx.vin.clear();
    builder.parentBlock.vtx.clear();
    builder.parentBlock.vtx.push_back (MakeTransactionRef(std::move (mtx)));
    builder.parentBlock.hashMerkleRoot = BlockMerkleRoot(builder.parentBlock);
    record(213, builder.get(), hashAux, ourChainId, params, false);

    /* Check that the auxpow is invalid if we change either the aux block's
     hash or the chain ID.  */
    uint256 modifiedAux(hashAux);
    tamperWith(modifiedAux);
    record(219, builder.get(), modifiedAux, ourChainId, params, false);
    record(220, builder.get(), hashAux, ourChainId + 1, params, false);

    /* Non-coinbase parent tx should fail.  Note that we can't just copy
     the coinbase literally, as we have to get a tx with different hash.  */
    const CTransactionRef oldCoinbase = builder.parentBlock.vtx[0];
    builder.setCoinbase(scr << 5);
    builder.parentBlock.vtx.push_back(oldCoinbase);
    builder.parentBlock.hashMerkleRoot = BlockMerkleRoot(builder.parentBlock);
    auxpow = builder.get(builder.parentBlock.vtx[0]);
    record(229, auxpow, hashAux, ourChainId, params, true);
    auxpow = builder.get(builder.parentBlock.vtx[1]);
    record(231, auxpow, hashAux, ourChainId, params, false);

    /* The parent chain can't have the same chain ID.  */
    CAuxpowBuilder builder2(builder);
    builder2.parentBlock.SetChainId(100);
    record(236, builder2.get(), hashAux, ourChainId, params, true);
    builder2.parentBlock.SetChainId(ourChainId);
    record(238, builder2.get(), hashAux, ourChainId, params, false);

    /* Disallow too long merkle branches.  */
    builder2 = builder;
    index = CAuxPow::getExpectedIndex(nonce, ourChainId, height + 1);
    auxRoot = builder2.buildAuxpowChain(hashAux, height + 1, index);
    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height + 1, nonce);
    scr = (CScript() << 2809 << 2013) + COINBASE_FLAGS;
    scr = (scr << OP_2 << data);
    builder2.setCoinbase(scr);
    record(248, builder2.get(), hashAux, ourChainId, params, false);

    /* Verify that we compare correctly to the parent block's merkle root.  */
    builder2 = builder;
    record(252, builder2.get(), hashAux, ourChainId, params, true);
    tamperWith(builder2.parentBlock.hashMerkleRoot);
    record(254, builder2.get(), hashAux, ourChainId, params, false);

    /* Build a non-header legacy version and check that it is also accepted.  */
    builder2 = builder;
    index = CAuxPow::getExpectedIndex(nonce, ourChainId, height);
    auxRoot = builder2.buildAuxpowChain(hashAux, height, index);
    data = CAuxpowBuilder::buildCoinbaseData(false, auxRoot, height, nonce);
    scr = (CScript() << 2809 << 2013) + COINBASE_FLAGS;
    scr = (scr << OP_2 << data);
    builder2.setCoinbase(scr);
    record(264, builder2.get(), hashAux, ourChainId, params, true);

    /* However, various attempts at smuggling two roots in should be detected.  */

    const std::vector<unsigned char> wrongAuxRoot = builder2.buildAuxpowChain(modifiedAux, height, index);
    std::vector<unsigned char> data2 = CAuxpowBuilder::buildCoinbaseData(false, wrongAuxRoot, height, nonce);
    builder2.setCoinbase(CScript() << data << data2);
    record(271, builder2.get(), hashAux, ourChainId, params, true);
    builder2.setCoinbase(CScript() << data2 << data);
    record(273, builder2.get(), hashAux, ourChainId, params, false);

    data2 = CAuxpowBuilder::buildCoinbaseData(true, wrongAuxRoot, height, nonce);
    builder2.setCoinbase(CScript() << data << data2);
    record(277, builder2.get(), hashAux, ourChainId, params, false);
    builder2.setCoinbase(CScript() << data2 << data);
    record(279, builder2.get(), hashAux, ourChainId, params, false);

    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height, nonce);
    builder2.setCoinbase(CScript() << data << data2);
    record(283, builder2.get(), hashAux, ourChainId, params, false);
    builder2.setCoinbase(CScript() << data2 << data);
    record(285, builder2.get(), hashAux, ourChainId, params, false);

    data2 = CAuxpowBuilder::buildCoinbaseData(false, wrongAuxRoot,
        height, nonce);
    builder2.setCoinbase(CScript() << data << data2);
    record(290, builder2.get(), hashAux, ourChainId, params, true);
    builder2.setCoinbase(CScript() << data2 << data);
    record(292, builder2.get(), hashAux, ourChainId, params, true);

    /* Verify that the appended nonce/size values are checked correctly.  */

    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height, nonce);
    builder2.setCoinbase(CScript() << data);
    record(298, builder2.get(), hashAux, ourChainId, params, true);

    data.pop_back();
    builder2.setCoinbase(CScript() << data);
    record(302, builder2.get(), hashAux, ourChainId, params, false);

    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height - 1, nonce);
    builder2.setCoinbase(CScript() << data);
    record(306, builder2.get(), hashAux, ourChainId, params, false);

    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height, nonce + 3);
    builder2.setCoinbase(CScript() << data);
    record(310, builder2.get(), hashAux, ourChainId, params, false);

    /* Put the aux hash in an invalid merkle tree position.  */

    auxRoot = builder.buildAuxpowChain(hashAux, height, index + 1);
    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height, nonce);
    builder2.setCoinbase(CScript() << data);
    record(317, builder2.get(), hashAux, ourChainId, params, false);

    auxRoot = builder.buildAuxpowChain(hashAux, height, index);
    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height, nonce);
    builder2.setCoinbase(CScript() << data);
    record(322, builder2.get(), hashAux, ourChainId, params, true);
    return rows;
}

// Adapted from Dogecoin Core e0a1c157791544e818c901bd9341896965afbf9d,
// src/test/auxpow_tests.cpp, mineBlock and auxpow_pow (lines 327-451).
// Copyright (c) 2014-2015 Daniel Kraft
// Distributed under the MIT/X11 software license. See LICENSES/dogecoin-core-MIT.txt.
// BOOST_CHECK sites record the exact mined components and Core verdicts.
// The builder and empty COINBASE_FLAGS substitutions are documented above.

UniValue powMiningChecks(UniValue::VARR);

void recordMining(int line, const CBlockHeader& block, uint32_t bits, bool expected)
{
    CDataStream ds(SER_NETWORK, PROTOCOL_VERSION);
    ds << static_cast<const CPureBlockHeader&>(block);
    UniValue row(UniValue::VOBJ);
    row.pushKV("line", line);
    row.pushKV("bytes_hex", HexStr(ds.begin(), ds.end()));
    row.pushKV("target_bits", static_cast<uint64_t>(bits));
    const auto digest = block.GetPoWHash();
    row.pushKV("pow_hash_hex", hex(digest.begin(), digest.end()));
    row.pushKV("expected", expected);
    row.pushKV("valid", CheckProofOfWork(block.GetPoWHash(), bits, Params().GetConsensus(0)));
    powMiningChecks.push_back(row);
}

/**
 * Mine a block (assuming minimal difficulty) that either matches
 * or doesn't match the difficulty target specified in the block header.
 * @param block The block to mine (by updating nonce).
 * @param ok Whether the block should be ok for PoW.
 * @param nBits Use this as difficulty if specified.
 */
static void
mineBlock(CBlockHeader& block, bool ok, int nBits = -1)
{
    if (nBits == -1)
        nBits = block.nBits;

    arith_uint256 target;
    target.SetCompact(nBits);

    block.nNonce = 0;
    while (true) {
        const bool nowOk = (UintToArith256(block.GetPoWHash()) <= target);
        if ((ok && nowOk) || (!ok && !nowOk))
            break;

        ++block.nNonce;
    }

    if (ok)
        recordMining(353, block, nBits, true);
    else
        recordMining(355, block, nBits, false);
}

UniValue reconstructAuxPowPowFixtures()
{
    UniValue rows(UniValue::VARR), hashChecks(UniValue::VARR);
    powMiningChecks = UniValue(UniValue::VARR);
    auto record = [&](int line, const CBlockHeader& block, bool expected) {
        CDataStream pure(SER_NETWORK, PROTOCOL_VERSION);
        pure << static_cast<const CPureBlockHeader&>(block);
        UniValue row(UniValue::VOBJ), payload;
        if (block.auxpow) {
            CDataStream ds(SER_NETWORK, PROTOCOL_VERSION);
            ds << *block.auxpow;
            payload = UniValue(HexStr(ds.begin(), ds.end()));
        }
        row.pushKV("line", line);
        row.pushKV("bytes_hex", HexStr(pure.begin(), pure.end()));
        row.pushKV("payload_hex", payload);
        row.pushKV("expected", expected);
        row.pushKV("valid", CheckAuxPowProofOfWork(block, Params().GetConsensus(371337)));
        rows.push_back(row);
    };
    auto hashCheck = [&](int line, bool valid) {
        UniValue row(UniValue::VOBJ);
        row.pushKV("line", line);
        row.pushKV("valid", valid);
        hashChecks.push_back(row);
    };
    /* Use regtest parameters to allow mining with easy difficulty.  */
    SelectParams(CBaseChainParams::REGTEST);
    const Consensus::Params& params = Params().GetConsensus(371337);

    const arith_uint256 target = (~arith_uint256(0) >> 1);
    CBlockHeader block;
    block.nBits = target.GetCompact();

    /* Verify the block version checks.  */

    block.nVersion = 1;
    mineBlock(block, true);
    record(372, block, true);

    // Dogecoin block version 2 can be both AuxPoW and regular, so test 3

    block.nVersion = 3;
    mineBlock(block, true);
    record(378, block, false);

    block.SetBaseVersion(2, params.nAuxpowChainId);
    mineBlock(block, true);
    record(382, block, true);

    block.SetChainId(params.nAuxpowChainId + 1);
    mineBlock(block, true);
    record(386, block, false);

    /* Check the case when the block does not have auxpow (this is true
     right now).  */

    block.SetChainId(params.nAuxpowChainId);
    block.SetAuxpowFlag(true);
    mineBlock(block, true);
    record(394, block, false);

    block.SetAuxpowFlag(false);
    mineBlock(block, true);
    record(398, block, true);
    mineBlock(block, false);
    record(400, block, false);

    /* ****************************************** */
    /* Check the case that the block has auxpow.  */

    CAuxpowBuilder builder(5, 42);
    CAuxPow auxpow;
    const int32_t ourChainId = params.nAuxpowChainId;
    const unsigned height = 3;
    const int nonce = 7;
    const int index = CAuxPow::getExpectedIndex(nonce, ourChainId, height);
    std::vector<unsigned char> auxRoot, data;

    /* Valid auxpow, PoW check of parent block.  */
    block.SetAuxpowFlag(true);
    auxRoot = builder.buildAuxpowChain(block.GetHash(), height, index);
    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height, nonce);
    builder.setCoinbase(CScript() << data);
    mineBlock(builder.parentBlock, false, block.nBits);
    block.SetAuxpow(new CAuxPow(builder.get()));
    record(420, block, false);
    mineBlock(builder.parentBlock, true, block.nBits);
    block.SetAuxpow(new CAuxPow(builder.get()));
    record(423, block, true);

    /* Mismatch between auxpow being present and block.nVersion.  Note that
     block.SetAuxpow sets also the version and that we want to ensure
     that the block hash itself doesn't change due to version changes.
     This requires some work arounds.  */
    block.SetAuxpowFlag(false);
    const uint256 hashAux = block.GetHash();
    auxRoot = builder.buildAuxpowChain(hashAux, height, index);
    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height, nonce);
    builder.setCoinbase(CScript() << data);
    mineBlock(builder.parentBlock, true, block.nBits);
    block.SetAuxpow(new CAuxPow(builder.get()));
    hashCheck(436, hashAux != block.GetHash());
    block.SetAuxpowFlag(false);
    hashCheck(438, hashAux == block.GetHash());
    record(439, block, false);

    /* Modifying the block invalidates the PoW.  */
    block.SetAuxpowFlag(true);
    auxRoot = builder.buildAuxpowChain(block.GetHash(), height, index);
    data = CAuxpowBuilder::buildCoinbaseData(true, auxRoot, height, nonce);
    builder.setCoinbase(CScript() << data);
    mineBlock(builder.parentBlock, true, block.nBits);
    block.SetAuxpow(new CAuxPow(builder.get()));
    record(448, block, true);
    tamperWith(block.hashMerkleRoot);
    record(450, block, false);
    UniValue result(UniValue::VOBJ), parameters(UniValue::VOBJ);
    parameters.pushKV("nAuxpowChainId", params.nAuxpowChainId);
    parameters.pushKV("fStrictChainId", params.fStrictChainId);
    parameters.pushKV("powLimit_hex", params.powLimit.GetHex());
    result.pushKV("core_revision", "e0a1c157791544e818c901bd9341896965afbf9d");
    result.pushKV("source", "src/test/auxpow_tests.cpp, mineBlock and auxpow_pow, lines 327-451");
    result.pushKV("network", "regtest");
    result.pushKV("selection_height", 371337);
    result.pushKV("mode", "allow_witness");
    result.pushKV("params", parameters);
    result.pushKV("scrypt_variant", "generic, --disable-scrypt-sse2");
    result.pushKV("cases", rows);
    result.pushKV("mining_checks", powMiningChecks);
    result.pushKV("hash_checks", hashChecks);
    return result;
}
