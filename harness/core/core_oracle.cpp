// The Dogecoin Core harness: answers dogelib-oracle/1 requests by running
// Dogecoin Core's own code, so that scripts/compare_core.py can check the
// oracle against Core. docs/oracle.md, section "The Core harness", describes
// its responses, a projection of dogelib-oracle/1.
//
// scripts/build_core_harness.sh builds it against Core's libraries at the
// commit that SOURCES.md pins.
//
// Every result value comes from Core's code, with the exceptions that the
// documentation names: `plan` of sighash.legacy is a label computed here from
// Core's conditions, and sighash.legacy has no `preimage_hex`, because Core
// hashes its preimage without exposing it. The block.check_version verdict
// comes from two transcribed branches and Core predicates.
// block.contextual_check also transcribes D33 and calls Core helpers for compared values.
//
// An exception from Core that is not one of the four mapped read errors ends
// the program with status 3, so it shows as a failed comparison.

#include "arith_uint256.h"
#include "auxpow.h"
#include "primitives/block.h"
#include "crypto/scrypt.h"
#include "chain.h"
#include "checkpoints.h"
#include "validation.h"
#include "chainparams.h"
#include "consensus/merkle.h"
#include "crypto/sha1.h"
#include "dogecoin.h"
#include "hash.h"
#include "pow.h"
#include "pubkey.h"
#include "primitives/pureheader.h"
#include "primitives/transaction.h"
#include "script/interpreter.h"
#include "script/script.h"
#include "serialize.h"
#include "streams.h"
#include "uint256.h"
#include "utilstrencodings.h"
#include "version.h"

#include <univalue.h>

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

// Core passes the hash type as `int` and the input index as `unsigned int`.
static_assert(std::numeric_limits<int>::min() == INT32_MIN && std::numeric_limits<int>::max() == INT32_MAX,
              "int must be a 32-bit two's complement integer");
static_assert(std::numeric_limits<unsigned int>::max() == UINT32_MAX, "unsigned int must have 32 bits");

// Core error() calls this logging sink. Keep logs off the JSONL stream.
int LogPrintStr(const std::string& message)
{
    std::cerr << message;
    return message.size();
}

BlockMap mapBlockIndex;
bool fCheckpointsEnabled = true;

namespace {

const char* const FORMAT = "dogelib-oracle/1-core-projection";

// The stream version of Core's base mode: the reader allows no witness data.
const int BASE_VERSION = PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS;

// A request the harness cannot interpret.
struct RequestError {
    std::string message;
};

// A result that Core reports as an error: the `error` object of the response.
struct SpecError {
    UniValue json;
};

// Core's exception, which the harness does not map.
struct UnmappedCoreError {
    std::string message;
};

UniValue readError(const std::string& reason)
{
    UniValue e(UniValue::VOBJ);
    e.pushKV("kind", "read");
    e.pushKV("reason", reason);
    return e;
}

// The read error for an exception from Core's stream code. Core throws
// std::ios_base::failure with these messages (serialize.h, streams.h). The
// C++11 ABI of libstdc++ appends ": iostream error" to what().
UniValue mapCoreFailure(const std::exception& e)
{
    std::string what = e.what();
    const std::string suffix = ": iostream error";
    if (what.size() >= suffix.size() && what.compare(what.size() - suffix.size(), suffix.size(), suffix) == 0) {
        what.erase(what.size() - suffix.size());
    }
    if (what == "CDataStream::read(): end of data") return readError("truncated");
    if (what == "non-canonical ReadCompactSize()") return readError("non_canonical");
    if (what == "ReadCompactSize(): size too large") return readError("too_large");
    if (what == "Unknown transaction optional data") return readError("unknown_optional_data");
    throw UnmappedCoreError{e.what()};
}

const UniValue& arg(const UniValue& req, const std::string& key)
{
    const UniValue& v = find_value(req, key);
    if (v.isNull() && !req.exists(key)) throw RequestError{"missing argument " + key};
    return v;
}

int hexValue(char c)
{
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

std::vector<unsigned char> argHex(const UniValue& req, const std::string& key)
{
    const UniValue& v = arg(req, key);
    if (!v.isStr()) throw RequestError{"argument " + key + " must be a string of hexadecimal digits"};
    const std::string& s = v.get_str();
    if (s.size() % 2 != 0) throw RequestError{"argument " + key + " must have an even number of hexadecimal digits"};
    std::vector<unsigned char> out;
    out.reserve(s.size() / 2);
    for (size_t i = 0; i < s.size(); i += 2) {
        int hi = hexValue(s[i]), lo = hexValue(s[i + 1]);
        if (hi < 0 || lo < 0) throw RequestError{"argument " + key + " must contain only hexadecimal digits"};
        out.push_back(static_cast<unsigned char>(hi * 16 + lo));
    }
    return out;
}

// The integer value of a JSON number token, by the rule of docs/oracle.md:
// any notation of an integer value, such as 5, 5.0, 5e0 or 50e-1. Values
// outside [lo, hi] and non-integral values are request errors.
int64_t argInt(const UniValue& req, const std::string& key, int64_t lo, int64_t hi)
{
    const UniValue& v = arg(req, key);
    if (!v.isNum()) throw RequestError{"argument " + key + " must be a number"};
    const std::string& tok = v.getValStr();
    size_t i = 0;
    bool negative = false;
    if (i < tok.size() && tok[i] == '-') { negative = true; ++i; }
    std::string digits;
    while (i < tok.size() && tok[i] >= '0' && tok[i] <= '9') digits += tok[i++];
    long long fracLen = 0;
    if (i < tok.size() && tok[i] == '.') {
        ++i;
        while (i < tok.size() && tok[i] >= '0' && tok[i] <= '9') { digits += tok[i++]; ++fracLen; }
    }
    long long exp = 0;
    if (i < tok.size() && (tok[i] == 'e' || tok[i] == 'E')) {
        ++i;
        bool expNegative = false;
        if (i < tok.size() && (tok[i] == '+' || tok[i] == '-')) { expNegative = tok[i] == '-'; ++i; }
        if (i == tok.size()) throw RequestError{"argument " + key + " is not a JSON number"};
        while (i < tok.size() && tok[i] >= '0' && tok[i] <= '9') {
            // Clamp: any exponent this large already decides the result.
            if (exp < 1000000) exp = exp * 10 + (tok[i] - '0');
            ++i;
        }
        if (expNegative) exp = -exp;
    }
    if (i != tok.size() || digits.empty()) throw RequestError{"argument " + key + " is not a JSON number"};
    size_t first = digits.find_first_not_of('0');
    if (first == std::string::npos) {
        if (lo > 0 || hi < 0) throw RequestError{"argument " + key + " is out of range"};
        return 0;
    }
    digits.erase(0, first);
    long long scale = exp - fracLen;
    if (scale < 0) {
        if (static_cast<long long>(digits.size()) <= -scale) throw RequestError{"argument " + key + " must be an integer"};
        std::string dropped = digits.substr(digits.size() + scale);
        if (dropped.find_first_not_of('0') != std::string::npos) throw RequestError{"argument " + key + " must be an integer"};
        digits.erase(digits.size() + scale);
        scale = 0;
    }
    // Normalize before parsing, including the asymmetric signed 64-bit endpoints.
    if (static_cast<long long>(digits.size()) + scale > 19)
        throw RequestError{"argument " + key + " is out of range"};
    digits.append(static_cast<size_t>(scale), '0');
    const std::string limit = negative ? "9223372036854775808" : "9223372036854775807";
    if (digits.size() == 19 && digits > limit)
        throw RequestError{"argument " + key + " is out of range"};
    const uint64_t magnitude = std::stoull(digits);
    const int64_t value = negative ? (magnitude == (uint64_t{1} << 63) ? INT64_MIN : -static_cast<int64_t>(magnitude))
                                   : static_cast<int64_t>(magnitude);
    if (value < lo || value > hi) throw RequestError{"argument " + key + " is out of range"};
    return value;
}

uint32_t argU32(const UniValue& req, const std::string& key)
{
    return static_cast<uint32_t>(argInt(req, key, 0, 4294967295LL));
}

uint64_t argU64(const UniValue& req, const std::string& key)
{
    const UniValue& v = arg(req, key);
    if (!v.isStr()) throw RequestError{"argument " + key + " must be a string of decimal digits"};
    const std::string& s = v.get_str();
    if (s.empty() || (s.size() > 1 && s[0] == '0') || s.find_first_not_of("0123456789") != std::string::npos) {
        throw RequestError{"argument " + key + " must be decimal digits with no sign and no leading zero"};
    }
    if (s.size() > 20 || (s.size() == 20 && s > "18446744073709551615")) {
        throw RequestError{"argument " + key + " must be below 2^64"};
    }
    return std::stoull(s);
}

std::string hex(const unsigned char* begin, const unsigned char* end)
{
    return HexStr(begin, end);
}

template <typename Container>
std::string hexOf(const Container& c)
{
    return HexStr(c.begin(), c.end());
}

void pushHash(UniValue& obj, const std::string& name, const uint256& h)
{
    obj.pushKV(name + "_hex", hex(h.begin(), h.end()));
    obj.pushKV(name + "_display", h.GetHex());
}

// Internal-order hash bytes, without the display-order SetHex conversion.
uint256 argHash(const UniValue& req, const std::string& key)
{
    const auto bytes = argHex(req, key);
    if (bytes.size() != 32) throw RequestError{"argument " + key + " must contain exactly 32 bytes"};
    uint256 result;
    std::copy(bytes.begin(), bytes.end(), result.begin());
    return result;
}

UniValue headerJson(const CPureBlockHeader& h)
{
    UniValue result(UniValue::VOBJ);
    result.pushKV("version", static_cast<uint64_t>(static_cast<uint32_t>(h.nVersion)));
    pushHash(result, "prev_block", h.hashPrevBlock);
    pushHash(result, "merkle_root", h.hashMerkleRoot);
    result.pushKV("time", static_cast<uint64_t>(h.nTime));
    result.pushKV("bits", static_cast<uint64_t>(h.nBits));
    result.pushKV("nonce", static_cast<uint64_t>(h.nNonce));
    return result;
}

UniValue txJson(const CMutableTransaction& tx)
{
    UniValue inputs(UniValue::VARR);
    for (const CTxIn& in : tx.vin) {
        UniValue prevout(UniValue::VOBJ);
        pushHash(prevout, "hash", in.prevout.hash);
        prevout.pushKV("n", static_cast<uint64_t>(in.prevout.n));
        UniValue i(UniValue::VOBJ);
        i.pushKV("prevout", prevout);
        i.pushKV("script_sig_hex", hexOf(in.scriptSig));
        i.pushKV("sequence", static_cast<uint64_t>(in.nSequence));
        inputs.push_back(i);
    }
    UniValue outputs(UniValue::VARR);
    for (const CTxOut& out : tx.vout) {
        UniValue o(UniValue::VOBJ);
        o.pushKV("value", std::to_string(static_cast<uint64_t>(out.nValue)));
        o.pushKV("script_pubkey_hex", hexOf(out.scriptPubKey));
        outputs.push_back(o);
    }
    UniValue t(UniValue::VOBJ);
    t.pushKV("version", static_cast<uint64_t>(static_cast<uint32_t>(tx.nVersion)));
    t.pushKV("inputs", inputs);
    t.pushKV("outputs", outputs);
    t.pushKV("lock_time", static_cast<uint64_t>(tx.nLockTime));
    return t;
}

// Core's reader on `bytes`: the transaction and the stream after it.
CMutableTransaction readTransaction(CDataStream& ds)
{
    CMutableTransaction tx;
    try {
        ds >> tx;
    } catch (const std::ios_base::failure& e) {
        throw SpecError{mapCoreFailure(e)};
    }
    return tx;
}

// A transaction that is all of `bytes`, as tx.decode_base reads it.
CMutableTransaction decodeBaseComplete(const std::vector<unsigned char>& bytes)
{
    CDataStream ds(bytes, SER_NETWORK, BASE_VERSION);
    CMutableTransaction tx = readTransaction(ds);
    if (!ds.empty()) {
        UniValue e(UniValue::VOBJ);
        e.pushKV("kind", "trailing_bytes");
        e.pushKV("count", static_cast<uint64_t>(ds.size()));
        throw SpecError{e};
    }
    return tx;
}

void checkArgs(const UniValue& req, const std::string& op, const std::vector<std::string>& args)
{
    for (const std::string& key : req.getKeys()) {
        if (key == "id" || key == "op") continue;
        bool known = false;
        for (const std::string& a : args) known = known || a == key;
        if (!known) throw RequestError{"unknown argument " + key + " for operation " + op};
    }
}

CPureBlockHeader argHeader(const UniValue& req)
{
    const auto& fields = arg(req, "header");
    if (!fields.isObject()) throw RequestError{"header must be an object"};
    checkArgs(fields, "header", {"version", "prev_block_hex", "merkle_root_hex", "time", "bits", "nonce"});
    // checkArgs permits id and op only at the request boundary.
    if (fields.exists("id") || fields.exists("op")) throw RequestError{"unknown header field"};
    CPureBlockHeader h;
    h.nVersion = static_cast<int32_t>(argU32(fields, "version"));
    h.hashPrevBlock = argHash(fields, "prev_block_hex");
    h.hashMerkleRoot = argHash(fields, "merkle_root_hex");
    h.nTime = argU32(fields, "time");
    h.nBits = argU32(fields, "bits");
    h.nNonce = argU32(fields, "nonce");
    return h;
}

// Work arguments follow docs/oracle.md. No result arithmetic lives here.
bool argBool(const UniValue& req, const std::string& key)
{
    const auto& v = arg(req, key);
    if (!v.isBool()) throw RequestError{"argument " + key + " must be a boolean"};
    return v.get_bool();
}

void selectWorkNetwork(const UniValue& req)
{
    const auto& v = arg(req, "network");
    if (!v.isStr()) throw RequestError{"network must be a string"};
    const auto& network = v.get_str();
    if (network == "mainnet") SelectParams(CBaseChainParams::MAIN);
    else if (network == "testnet") SelectParams(CBaseChainParams::TESTNET);
    else if (network == "regtest") SelectParams(CBaseChainParams::REGTEST);
    else throw RequestError{"unknown network"};
}

// Explicit transaction stream mode for full headers and payloads.
int headerStreamVersion(const UniValue& req)
{
    const auto& mode = arg(req, "mode");
    if (!mode.isStr()) throw RequestError{"mode must be a string"};
    if (mode.get_str() == "base") return BASE_VERSION;
    if (mode.get_str() == "allow_witness") return PROTOCOL_VERSION;
    throw RequestError{"unknown mode"};
}

void requireEmpty(const CDataStream& ds)
{
    if (!ds.empty()) {
        UniValue error(UniValue::VOBJ);
        error.pushKV("kind", "trailing_bytes");
        error.pushKV("count", static_cast<uint64_t>(ds.size()));
        throw SpecError{error};
    }
}

UniValue payloadJson(const CAuxPow& a)
{
    UniValue transaction(UniValue::VOBJ), witnesses(UniValue::VARR);
    for (const auto& in : a.tx->vin) {
        UniValue stack(UniValue::VARR);
        for (const auto& item : in.scriptWitness.stack) stack.push_back(UniValue(hexOf(item)));
        witnesses.push_back(stack);
    }
    CDataStream out(SER_NETWORK, PROTOCOL_VERSION);
    out << *a.tx;
    transaction.pushKV("tx", txJson(CMutableTransaction(*a.tx)));
    transaction.pushKV("witnesses", witnesses);
    transaction.pushKV("has_witness", a.tx->HasWitness());
    transaction.pushKV("serialized_hex", HexStr(out.begin(), out.end()));
    pushHash(transaction, "txid", a.tx->GetHash());
    pushHash(transaction, "wtxid", a.tx->GetWitnessHash());
    UniValue result(UniValue::VOBJ), branch(UniValue::VARR), chain(UniValue::VARR);
    for (const auto& h : a.vMerkleBranch) branch.push_back(UniValue(hex(h.begin(), h.end())));
    for (const auto& h : a.vChainMerkleBranch) chain.push_back(UniValue(hex(h.begin(), h.end())));
    result.pushKV("transaction", transaction);
    pushHash(result, "hash_block", a.hashBlock);
    result.pushKV("merkle_branch_hex", branch);
    result.pushKV("index", static_cast<uint64_t>(static_cast<uint32_t>(a.nIndex)));
    result.pushKV("chain_merkle_branch_hex", chain);
    result.pushKV("chain_index", static_cast<uint64_t>(static_cast<uint32_t>(a.nChainIndex)));
    result.pushKV("parent", headerJson(a.parentBlock));
    return result;
}

// Core's GetSkipHeight (D35), used only to guard BuildSkip on a suffix.
// Adapted from Dogecoin Core e0a1c15, src/chain.cpp, MIT licence.
// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Copyright (c) 2021-2022 The Dogecoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.
int availableSkipHeight(int height)
{
    if (height < 2) return 0;
    auto invert = [](int n) { return n & (n - 1); };
    return (height & 1) ? invert(invert(height - 1)) + 1 : invert(height);
}
// End of the adapted skip-height helper.

// H2 transcription of Dogecoin Core e0a1c157791544e818c901bd9341896965afbf9d,
// src/validation.cpp lines 3066-3119 (SOURCES.md D33). MIT/X11 licence.
// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Copyright (c) 2022-2023 The Dogecoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.
// Return the reject reason in place of CValidationState and peer-management scores.
// Adapter preflight establishes a non-null predecessor and safe adjusted-time sum.
std::string contextualReject(const CBlockHeader& block, const CBlockIndex* pindexPrev, int64_t nAdjustedTime)
{
    const int nHeight = pindexPrev == NULL ? 0 : pindexPrev->nHeight + 1;
    const CChainParams& params = Params();
    const Consensus::Params& consensusParams = params.GetConsensus(nHeight);
    if (!consensusParams.fAllowLegacyBlocks && block.IsLegacy())
        return "late-legacy-block";
    if (consensusParams.fAllowLegacyBlocks && block.IsAuxpow())
        return "early-auxpow-block";
    if (block.nBits != GetNextWorkRequired(pindexPrev, &block, consensusParams))
        return "bad-diffbits";
    if (fCheckpointsEnabled) {
        CBlockIndex* pcheckpoint = Checkpoints::GetLastCheckpoint(params.Checkpoints());
        if (pcheckpoint && nHeight < pcheckpoint->nHeight)
            return "bad-fork-prior-to-checkpoint";
    }
    if (block.GetBlockTime() <= pindexPrev->GetMedianTimePast())
        return "time-too-old";
    if (block.GetBlockTime() > nAdjustedTime + 2 * 60 * 60)
        return "time-too-new";
    if ((block.GetBaseVersion() < 3 && nHeight >= consensusParams.BIP66Height) ||
        (block.GetBaseVersion() < 4 && nHeight >= consensusParams.BIP65Height))
        return strprintf("bad-version(0x%08x)", block.GetBaseVersion());
    return "";
}

// End of the adapted contextual-header checks.

// Reject histories outside the compared caller domain before invoking Core.
// In particular, a truncated recovery walk must not masquerade as genesis.
void checkWorkHistory(const std::vector<CBlockIndex>& chain, const CBlockHeader& candidate,
                      const Consensus::Params& params)
{
    if (chain.empty()) return;
    const CBlockIndex& last = chain.front();
    if (AllowDigishieldMinDifficultyForBlock(&last, &candidate, params)) return;
    const int64_t interval = last.nHeight >= 145000 ? 1 : params.DifficultyAdjustmentInterval();
    if ((last.nHeight + 1) % interval != 0) {
        if (!params.fPowAllowMinDifficultyBlocks ||
            candidate.GetBlockTime() > last.GetBlockTime() + params.nPowTargetSpacing * 2) return;
        const uint32_t limit = UintToArith256(params.powLimit).GetCompact();
        for (const auto& entry : chain) {
            if (entry.nHeight % params.DifficultyAdjustmentInterval() == 0 || entry.nBits != limit) return;
        }
        throw RequestError{"incomplete recovery history is outside the Core comparison domain"};
    }
    const int64_t back = last.nHeight + 1 == interval ? interval - 1 : interval;
    if (back > last.nHeight || static_cast<uint64_t>(back) >= chain.size())
        throw RequestError{"missing retarget ancestor is outside the Core comparison domain"};
}


// Anchor adapter for C8, src/chain.cpp:113-137 at e0a1c157791544e818c901bd9341896965afbf9d.
// GetAncestor asserts below an anchor. Establish the reachable height before calling it.
CBlockIndex* sequenceAncestor(CBlockIndex* entry, int height)
{
    CBlockIndex* walk = entry;
    while (walk && walk->nHeight > height) walk = walk->pprev;
    return walk && walk->nHeight == height ? entry->GetAncestor(height) : nullptr;
}

void sequenceSkip(CBlockIndex* entry)
{
    const CBlockIndex* anchor = entry;
    while (anchor->pprev) anchor = anchor->pprev;
    // C8, chain.cpp:140-147: BuildSkip calls GetAncestor at GetSkipHeight.
    if (entry->pprev && availableSkipHeight(entry->nHeight) >= anchor->nHeight)
        entry->BuildSkip();
}

// H2 transcription of e0a1c157791544e818c901bd9341896965afbf9d,
// src/validation.cpp:2755-2788,3205-3286 (D33), MIT/X11 licence.
// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Copyright (c) 2022-2023 The Dogecoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.
// The request owns the index and failed-list order. Disk state, best-header
// selection, notifications, locks and peer penalties are outside this operation.
// AddToBlockIndex omits nTimeMax (2779), pindexBestHeader (2782-2783)
// and setDirtyBlockIndex (2785).
UniValue headerSequence(const UniValue& req)
{
    checkArgs(req, "block.header_sequence", {"network", "mode", "adjusted_time", "checkpoints_enabled", "index", "failed_blocks", "headers"});
    selectWorkNetwork(req);
    const int version = headerStreamVersion(req);
    const int64_t adjusted = argInt(req, "adjusted_time", INT64_MIN, INT64_MAX - 7200);
    fCheckpointsEnabled = argBool(req, "checkpoints_enabled");
    const auto& entries = arg(req, "index");
    const auto& failed = arg(req, "failed_blocks");
    const auto& headers = arg(req, "headers");
    for (const auto* array : {&entries, &failed, &headers})
        if (!array->isArray() || array->size() > 4096) throw RequestError{"sequence arrays must have at most 4096 entries"};
    // Keep map keys alive until all CBlockIndex objects have been destroyed.
    mapBlockIndex.clear();
    struct ClearMap { ~ClearMap() { mapBlockIndex.clear(); } } clearMap;
    std::vector<std::unique_ptr<CBlockIndex>> owned;
    std::vector<bool> anchors;
    std::vector<uint256> prevHashes;
    auto insert = [&](const CBlockHeader& header) {
        owned.emplace_back(new CBlockIndex(header));
        CBlockIndex* entry = owned.back().get();
        auto found = mapBlockIndex.emplace(header.GetHash(), entry).first;
        entry->phashBlock = &found->first;
        return entry;
    };
    for (size_t i = 0; i < entries.size(); ++i) {
        const auto& raw = entries[i];
        if (!raw.isObject()) throw RequestError{"index entries must be objects"};
        for (const auto& key : raw.getKeys())
            if (key != "header_hex" && key != "height" && key != "anchor" && key != "failed_valid" && key != "failed_child" && key != "scripts_valid" && key != "chain_work")
                throw RequestError{"unknown index field"};
        auto bytes = argHex(raw, "header_hex");
        if (bytes.size() != 80) throw RequestError{"header_hex must contain exactly 80 bytes"};
        CBlockHeader header;
        CDataStream ds(bytes, SER_NETWORK, version);
        ds >> static_cast<CPureBlockHeader&>(header);
        if (mapBlockIndex.count(header.GetHash())) throw RequestError{"duplicate index hash"};
        prevHashes.push_back(header.hashPrevBlock);
        auto* entry = insert(header);
        entry->nHeight = argInt(raw, "height", 0, 2147483646);
        anchors.push_back(argBool(raw, "anchor") || entry->nHeight == 0);
        entry->nStatus = argBool(raw, "scripts_valid") ? BLOCK_VALID_SCRIPTS : BLOCK_VALID_TREE;
        if (argBool(raw, "failed_valid")) entry->nStatus |= BLOCK_FAILED_VALID;
        if (argBool(raw, "failed_child")) entry->nStatus |= BLOCK_FAILED_CHILD;
        if (argHex(raw, "chain_work").size() != 32) throw RequestError{"chain_work must contain exactly 32 bytes"};
        entry->nChainWork.SetHex(arg(raw, "chain_work").get_str());
    }
    for (size_t i = 0; i < owned.size(); ++i) {
        auto* entry = owned[i].get();
        if (!anchors[i]) {
            const auto parent = mapBlockIndex.find(prevHashes[i]);
            if (parent == mapBlockIndex.end() || entry->nHeight != parent->second->nHeight + 1)
                throw RequestError{"index is not well formed"};
            entry->pprev = parent->second;
        } else if (entry->nHeight == 0 && entry->GetBlockHash() != Params().GetConsensus(0).hashGenesisBlock)
            throw RequestError{"index is not well formed"};
    }
    std::vector<CBlockIndex*> ordered;
    for (auto& entry : owned) ordered.push_back(entry.get());
    std::sort(ordered.begin(), ordered.end(), [](const CBlockIndex* a, const CBlockIndex* b) { return a->nHeight < b->nHeight; });
    for (auto* entry : ordered) sequenceSkip(entry);
    std::vector<CBlockIndex*> failedList;
    for (size_t i = 0; i < failed.size(); ++i) {
        UniValue field(UniValue::VOBJ);
        field.pushKV("hash", failed[i]);
        if (argHex(field, "hash").size() != 32) throw RequestError{"failed hash must contain exactly 32 bytes"};
        uint256 hash; hash.SetHex(arg(field, "hash").get_str());
        const auto found = mapBlockIndex.find(hash);
        if (found == mapBlockIndex.end() || !(found->second->nStatus & BLOCK_FAILED_VALID))
            throw RequestError{"index is not well formed"};
        failedList.push_back(found->second);
    }
    std::vector<CBlockHeader> decoded;
    size_t total = 0;
    // Match the Lean adapter: check every string size before decoding any hex
    // or full header, so a later size refusal precedes an earlier read error.
    for (size_t i = 0; i < headers.size(); ++i) {
        if (!headers[i].isStr()) throw RequestError{"headers must contain hexadecimal strings"};
        const size_t length = headers[i].get_str().size();
        if (length > 2097152) throw RequestError{"header exceeds 1 MiB"};
        total += length / 2;
    }
    if (total > 16777216) throw RequestError{"headers exceed 16 MiB"};
    std::vector<std::vector<unsigned char>> headerBytes;
    for (size_t i = 0; i < headers.size(); ++i) {
        UniValue field(UniValue::VOBJ); field.pushKV("header", headers[i]);
        headerBytes.push_back(argHex(field, "header"));
    }
    for (const auto& bytes : headerBytes) {
        CDataStream ds(bytes, SER_NETWORK, version);
        CBlockHeader header;
        try { ds >> header; } catch (const std::ios_base::failure& e) { throw SpecError{mapCoreFailure(e)}; }
        requireEmpty(ds);
        decoded.push_back(header);
    }
    UniValue added(UniValue::VARR), marks(UniValue::VARR), last, failedAt, reason, dos, code;
    std::vector<std::string> marked;
    auto reject = [&](size_t position, const std::string& why, int score, int rejectCode) {
        failedAt = UniValue(static_cast<uint64_t>(position)); reason = UniValue(why);
        dos = UniValue(score); code = UniValue(rejectCode); last = UniValue();
    };
    for (size_t i = 0; i < decoded.size(); ++i) {
        const auto& block = decoded[i];
        const uint256 hash = block.GetHash();
        const auto known = mapBlockIndex.find(hash);
        // C1, validation.cpp:3212-3222: genesis bypass and duplicate fast path.
        if (hash != Params().GetConsensus(0).hashGenesisBlock) {
            if (known != mapBlockIndex.end()) {
                if (known->second->nStatus & BLOCK_FAILED_MASK) { reject(i, "duplicate", 0, 0); break; }
                last = UniValue(hash.GetHex()); continue;
            }
            // C4, validation.cpp:2927-2937 and C1:3224-3234.
            if (!CheckAuxPowProofOfWork(block, Params().GetConsensus(0))) { reject(i, "high-hash", 50, 16); break; }
            const auto parent = mapBlockIndex.find(block.hashPrevBlock);
            if (parent == mapBlockIndex.end()) { reject(i, "bad-prevblk", 10, 0); break; }
            auto* prev = parent->second;
            if (prev->nStatus & BLOCK_FAILED_MASK) { reject(i, "bad-prevblk", 100, 16); break; }
            if (prev->nHeight >= 2147483646) throw RequestError{"heightOutOfRange"};
            // Adapter preflight: refuse truncated median and retarget views before
            // contextualReject calls GetNextWorkRequired (pow.cpp:84).
            std::vector<CBlockIndex> view;
            for (auto* walk = prev; walk; walk = walk->pprev) view.push_back(*walk);
            if (view.size() < static_cast<size_t>(std::min(11, prev->nHeight + 1)))
                throw RequestError{"short contextual view"};
            checkWorkHistory(view, block, Params().GetConsensus(prev->nHeight + 1));
            // C1:3238-3239, with scores from C5:3066-3119.
            const std::string why = contextualReject(block, prev, adjusted);
            if (!why.empty()) {
                const bool scored = why == "late-legacy-block" || why == "early-auxpow-block" || why == "bad-diffbits" || why == "bad-fork-prior-to-checkpoint";
                reject(i, why, scored ? 100 : 0, why == "bad-fork-prior-to-checkpoint" ? 67 : why.find("bad-version") == 0 ? 17 : 16); break;
            }
            // C1:3241-3256. Request order replaces pointer-address order.
            if (!prev->IsValid(BLOCK_VALID_SCRIPTS)) {
                for (const auto* member : failedList) {
                    if (sequenceAncestor(prev, member->nHeight) == member) {
                        for (auto* walk = prev; walk != member; walk = walk->pprev) {
                            marked.push_back(walk->GetBlockHash().GetHex());
                            walk->nStatus |= BLOCK_FAILED_CHILD;
                        }
                        reject(i, "bad-prevblk", 100, 16); break;
                    }
                }
                if (!reason.isNull()) break;
            }
        }
        // C3, validation.cpp:2755-2788. Search before insertion follows the
        // accepted fixed-point convention of design 0008, amendment 13.1.
        if (known == mapBlockIndex.end()) {
            const auto parent = mapBlockIndex.find(block.hashPrevBlock);
            CBlockIndex* parentEntry = parent == mapBlockIndex.end() ? nullptr : parent->second;
            if (parentEntry && parentEntry->nHeight >= 2147483646)
                throw RequestError{"heightOutOfRange"};
            // Insertion can rehash BlockMap. Retain the stable entry pointer,
            // rather than an iterator into the map (D69, validation.h:169).
            auto* entry = insert(block);
            if (parentEntry) { entry->pprev = parentEntry; entry->nHeight = parentEntry->nHeight + 1; }
            sequenceSkip(entry);
            entry->nChainWork = (entry->pprev ? entry->pprev->nChainWork : 0) + GetBlockProof(*entry);
            entry->RaiseValidity(BLOCK_VALID_TREE);
            UniValue value(UniValue::VOBJ);
            value.pushKV("hash", hash.GetHex()); value.pushKV("height", entry->nHeight);
            value.pushKV("chain_work", entry->nChainWork.GetHex()); added.push_back(value);
        }
        last = UniValue(hash.GetHex());
    }
    std::sort(marked.begin(), marked.end());
    for (const auto& hash : marked) marks.push_back(UniValue(hash));
    UniValue result(UniValue::VOBJ);
    result.pushKV("valid", reason.isNull()); result.pushKV("failed_at", failedAt);
    result.pushKV("reject_reason", reason); result.pushKV("dos", dos); result.pushKV("reject_code", code);
    result.pushKV("last_hash", last); result.pushKV("added", added); result.pushKV("marked_failed_child", marks);
    return result;
}
// End of the H2 sequence transcription.

// Check every pinned enum position when Core headers compile this table.
constexpr ScriptError SCRIPT_ERRORS[] = {
#define SCRIPT_ERROR(value, name) value,
#include "script_error_names.inc"
#undef SCRIPT_ERROR
};
constexpr bool orderedErrors(size_t n) {
    return n == 0 || (SCRIPT_ERRORS[n - 1] == n - 1 && orderedErrors(n - 1));
}
static_assert(sizeof(SCRIPT_ERRORS) / sizeof(*SCRIPT_ERRORS) == SCRIPT_ERR_ERROR_COUNT,
              "script error table must cover every Core enum");
static_assert(orderedErrors(SCRIPT_ERR_ERROR_COUNT), "script error table must retain enum order");

const char* scriptErrorName(ScriptError error)
{
    switch (error) {
#define SCRIPT_ERROR(value, name) case value: return name;
#include "script_error_names.inc"
#undef SCRIPT_ERROR
    default: throw UnmappedCoreError{"unmapped ScriptError"};
    }
}

void scriptResourceLimit()
{
    UniValue error(UniValue::VOBJ);
    error.pushKV("kind", "adapter");
    error.pushKV("reason", "resource_limit");
    throw SpecError{error};
}


std::vector<unsigned char> scriptBytes(const UniValue& req, const std::string& key)
{
    const auto& value = arg(req, key);
    if (value.isStr() && value.get_str().size() > 2097152) scriptResourceLimit();
    return argHex(req, key);
}

std::string scriptChecker(const UniValue& req, bool evaluation)
{
    const auto& value = find_value(req, "checker");
    bool present = false;
    for (const auto& key : req.getKeys()) if (key == "checker") present = true;
    if (!present && evaluation) return "none";
    if (!value.isStr()) throw RequestError{"checker must be a string"};
    const auto name = value.get_str();
    if (name != "base" && name != (evaluation ? "none" : "transaction")) throw RequestError{"unknown checker"};
    return name;
}

void scriptAdapterFailure(const std::string& reason)
{
    UniValue error(UniValue::VOBJ);
    error.pushKV("kind", "adapter");
    error.pushKV("reason", reason);
    throw SpecError{error};
}

UniValue run(const UniValue& req)
{
    const UniValue& opv = arg(req, "op");
    if (!opv.isStr()) throw RequestError{"argument op must be a string"};
    const std::string& op = opv.get_str();
    UniValue ok(UniValue::VOBJ);

    if (op == "oracle.version") {
        checkArgs(req, op, {});
        ok.pushKV("format", FORMAT);
    } else if (op == "pubkey.verify") {
        checkArgs(req, op, {"pubkey_hex", "sig_hex", "digest_hex"});
        const auto key = scriptBytes(req, "pubkey_hex");
        const auto sig = scriptBytes(req, "sig_hex");
        const auto digest = argHash(req, "digest_hex");
        ok.pushKV("valid", CPubKey(key.begin(), key.end()).Verify(digest, sig));
    } else if (op == "script.read_op") {
        checkArgs(req, op, {"bytes_hex", "cursor"});
        const auto bytes = scriptBytes(req, "bytes_hex");
        if (bytes.size() > 1048576) scriptResourceLimit();
        const auto start = argU32(req, "cursor");
        if (start > bytes.size()) throw RequestError{"cursor exceeds script length"};
        const CScript script(bytes.begin(), bytes.end());
        auto pc = script.begin() + start;
        opcodetype opcode;
        std::vector<unsigned char> pushed;
        const bool read = script.GetOp(pc, opcode, pushed);
        const auto cursor = pc - script.begin();
        ok.pushKV("cursor", static_cast<int64_t>(cursor));
        if (read) {
            ok.pushKV("result", "instruction");
            ok.pushKV("opcode", static_cast<int>(opcode));
            ok.pushKV("bytes_hex", hexOf(std::vector<unsigned char>(script.begin() + start, pc)));
            ok.pushKV("pushed_hex", hexOf(pushed));
        } else if (start == bytes.size()) {
            ok.pushKV("result", "at_end");
        } else {
            const auto original = bytes[start];
            const unsigned width = original == OP_PUSHDATA1 ? 1 : original == OP_PUSHDATA2 ? 2 : original == OP_PUSHDATA4 ? 4 : 0;
            ok.pushKV("result", "truncated");
            ok.pushKV("opcode", static_cast<int>(original));
            ok.pushKV("part", width && cursor == start + 1 ? "length_field" : "payload");
        }
    } else if (op == "script.eval") {
        checkArgs(req, op, {"bytes_hex", "flags", "stack_hex", "checker"});
        const auto bytes = scriptBytes(req, "bytes_hex");
        if (bytes.size() > 1048576) scriptResourceLimit();
        const auto flags = argU32(req, "flags");
        const auto& items = arg(req, "stack_hex");
        if (!items.isArray()) throw RequestError{"stack_hex must be an array"};
        if (items.size() > 4096) scriptResourceLimit();
        std::vector<std::vector<unsigned char>> stack;
        size_t total = 0;
        for (size_t i = 0; i < items.size(); ++i) {
            UniValue item(UniValue::VOBJ);
            item.pushKV("item", items[i]);
            if (items[i].isStr()) {
                total += items[i].get_str().size() / 2;
                if (total > 4194304) scriptResourceLimit();
            }
            auto data = scriptBytes(item, "item");
            if (data.size() > 1048576) scriptResourceLimit();
            stack.push_back(std::move(data));
        }
        scriptChecker(req, true);
        const CScript script(bytes.begin(), bytes.end());
        ScriptError error = SCRIPT_ERR_UNKNOWN_ERROR;
        const bool accepted = EvalScript(stack, script, flags, BaseSignatureChecker(), SIGVERSION_BASE, &error);
        ok.pushKV("result", accepted ? "accepted" : "rejected");
        ok.pushKV("script_error", scriptErrorName(error));
        if (accepted) {
            UniValue result(UniValue::VARR);
            for (const auto& item : stack) result.push_back(UniValue(hexOf(item)));
            ok.pushKV("stack_hex", result);
        }
    } else if (op == "script.verify_legacy") {
        checkArgs(req, op, {"tx_hex", "input_index", "prevout_script_hex", "flags", "checker"});
        const auto bytes = argHex(req, "tx_hex");
        const auto index = argU32(req, "input_index");
        const auto script = scriptBytes(req, "prevout_script_hex");
        const auto flags = argU32(req, "flags");
        const auto checker = scriptChecker(req, false);
        CMutableTransaction mtx;
        try {
            mtx = decodeBaseComplete(bytes);
        } catch (SpecError& e) {
            e.json.pushKV("argument", "tx_hex");
            throw;
        }
        if (index >= mtx.vin.size()) scriptAdapterFailure("input_index_out_of_range");
        if (mtx.vin.size() >= (uint64_t{1} << 32) || mtx.vout.size() >= (uint64_t{1} << 32))
            scriptAdapterFailure("context_bounds");
        if (mtx.vin[index].scriptSig.size() > 1048576) scriptResourceLimit();
        const CTransaction tx(mtx);
        const CScript spk(script.begin(), script.end());
        ScriptError error = SCRIPT_ERR_UNKNOWN_ERROR;
        // Core asserts these flag dependencies even for diagnostic requests.
        // Reject the unsafe combinations instead of changing the caller's flags.
        if (((flags & SCRIPT_VERIFY_WITNESS) && !(flags & SCRIPT_VERIFY_P2SH)) ||
            ((flags & SCRIPT_VERIFY_CLEANSTACK) &&
             (!(flags & SCRIPT_VERIFY_P2SH) || !(flags & SCRIPT_VERIFY_WITNESS))))
            throw RequestError{"Core VerifyScript flag dependencies are not satisfied"};
        const bool accepted = checker == "base"
            ? VerifyScript(tx.vin[index].scriptSig, spk, nullptr, flags, BaseSignatureChecker(), &error)
            : VerifyScript(tx.vin[index].scriptSig, spk, nullptr, flags, TransactionSignatureChecker(&tx, index, 0), &error);
        ok.pushKV("result", accepted ? "accepted" : "rejected");
        ok.pushKV("script_error", scriptErrorName(error));
    } else if (op == "hash.ripemd160" || op == "hash.hash160" || op == "hash.sha1") {
        checkArgs(req, op, {"bytes_hex"});
        const auto bytes = argHex(req, "bytes_hex");
        static const unsigned char blank[1] = {};
        const auto data = bytes.empty() ? blank : bytes.data();
        unsigned char digest[20];
        if (op == "hash.ripemd160") CRIPEMD160().Write(data, bytes.size()).Finalize(digest);
        else if (op == "hash.hash160") CHash160().Write(data, bytes.size()).Finalize(digest);
        else CSHA1().Write(data, bytes.size()).Finalize(digest);
        ok.pushKV("digest_hex", hex(digest, digest + 20));
    } else if (op == "scrypt.hash") {
        checkArgs(req, op, {"bytes_hex"});
        const auto bytes = argHex(req, "bytes_hex");
        if (bytes.size() != 80) throw RequestError{"bytes_hex must contain exactly 80 bytes"};
        unsigned char digest[32];
        std::vector<char> scratch(SCRYPT_SCRATCHPAD_SIZE);
        scrypt_1024_1_1_256_sp_generic(reinterpret_cast<const char*>(bytes.data()),
                                    reinterpret_cast<char*>(digest), scratch.data());
        ok.pushKV("digest_hex", hex(digest, digest + 32));
    } else if (op == "block.header.read" || op == "block.check_pow" || op == "auxpow.check") {
        if (op == "block.header.read") checkArgs(req, op, {"bytes_hex", "mode"});
        else if (op == "block.check_pow") checkArgs(req, op, {"bytes_hex", "mode", "network", "selection_height", "payload_hex"});
        else checkArgs(req, op, {"bytes_hex", "mode", "hash_hex", "chain_id", "strict_chain_id"});
        const auto version = headerStreamVersion(req);
        const auto bytes = argHex(req, "bytes_hex");
        CDataStream ds(bytes, SER_NETWORK, version);
        CBlockHeader h;
        CAuxPow a;
        try {
            if (op == "auxpow.check") ds >> a;
            else if (op == "block.check_pow" && req.exists("payload_hex")) {
                if (bytes.size() != 80) throw RequestError{"split bytes_hex must contain exactly 80 bytes"};
                ds >> static_cast<CPureBlockHeader&>(h);
                if (!arg(req, "payload_hex").isNull()) {
                    CDataStream payload(argHex(req, "payload_hex"), SER_NETWORK, version);
                    h.auxpow.reset(new CAuxPow());
                    payload >> *h.auxpow;
                    requireEmpty(payload);
                }
            } else ds >> h;
        } catch (const std::ios_base::failure& e) { throw SpecError{mapCoreFailure(e)}; }
        if (op == "block.header.read") {
            UniValue full(UniValue::VOBJ);
            full.pushKV("pure", headerJson(h));
            full.pushKV("auxpow", h.auxpow ? payloadJson(*h.auxpow) : UniValue());
            ok.pushKV("header", full);
            ok.pushKV("consumed", static_cast<uint64_t>(bytes.size() - ds.size()));
            ok.pushKV("rest_hex", HexStr(ds.begin(), ds.end()));
        } else {
            requireEmpty(ds);
            if (op == "auxpow.check") {
                Consensus::Params params = Params(CBaseChainParams::MAIN).GetConsensus(0);
                params.fStrictChainId = argBool(req, "strict_chain_id");
                const auto hash = argHash(req, "hash_hex");
                const auto chainId = argInt(req, "chain_id", INT32_MIN, INT32_MAX);
                ok.pushKV("valid", a.check(hash, chainId, params));
            } else {
                selectWorkNetwork(req);
                const auto height = argInt(req, "selection_height", 0, INT32_MAX);
                ok.pushKV("valid", CheckAuxPowProofOfWork(h, Params().GetConsensus(height)));
            }
        }
    } else if (op == "block.check_version") {
        checkArgs(req, op, {"bytes_hex", "network", "selection_height"});
        const auto bytes = argHex(req, "bytes_hex");
        if (bytes.size() != 80) throw RequestError{"bytes_hex must contain exactly 80 bytes"};
        CDataStream ds(bytes, SER_NETWORK, PROTOCOL_VERSION);
        CPureBlockHeader h;
        ds >> h;
        selectWorkNetwork(req);
        const auto& params = Params().GetConsensus(argInt(req, "selection_height", 0, INT32_MAX));
        // The two branches of ContextualCheckBlockHeader, D33 lines 3072-3086.
        bool valid = true;
        if (!params.fAllowLegacyBlocks && h.IsLegacy()) valid = false;
        else if (params.fAllowLegacyBlocks && h.IsAuxpow()) valid = false;
        ok.pushKV("valid", valid);
    } else if (op == "header.read") {
        checkArgs(req, op, {"bytes_hex"});
        const auto bytes = argHex(req, "bytes_hex");
        CDataStream ds(bytes, SER_NETWORK, PROTOCOL_VERSION);
        CPureBlockHeader h;
        try {
            ds >> h;
        } catch (const std::ios_base::failure& e) {
            throw SpecError{mapCoreFailure(e)};
        }
        ok.pushKV("header", headerJson(h));
        ok.pushKV("consumed", static_cast<uint64_t>(bytes.size() - ds.size()));
        ok.pushKV("rest_hex", HexStr(ds.begin(), ds.end()));
    } else if (op == "header.encode" || op == "header.hash") {
        checkArgs(req, op, {"header"});
        const auto h = argHeader(req);
        if (op == "header.hash") pushHash(ok, "hash", h.GetHash());
        else {
            CDataStream ds(SER_NETWORK, PROTOCOL_VERSION);
            ds << h;
            ok.pushKV("bytes_hex", HexStr(ds.begin(), ds.end()));
        }
    } else if (op == "merkle.compute") {
        checkArgs(req, op, {"leaves_hex"});
        const auto& entries = arg(req, "leaves_hex");
        if (!entries.isArray()) throw RequestError{"leaves_hex must be an array"};
        if (static_cast<uint64_t>(entries.size()) > (uint64_t{1} << 31))
            throw RequestError{"leaves_hex must have at most 2^31 entries"};
        std::vector<uint256> leaves;
        leaves.reserve(entries.size());
        for (size_t i = 0; i < entries.size(); ++i) {
            UniValue field(UniValue::VOBJ);
            const auto key = "leaves_hex[" + std::to_string(i) + "]";
            field.pushKV(key, entries[i]);
            leaves.push_back(argHash(field, key));
        }
        bool mutated;
        const auto root = ComputeMerkleRoot(leaves, &mutated);
        pushHash(ok, "root", root);
        ok.pushKV("mutated", mutated);
    } else if (op == "work.set_compact") {
        checkArgs(req, op, {"compact"});
        arith_uint256 value;
        bool negative, overflow;
        value.SetCompact(argU32(req, "compact"), &negative, &overflow);
        ok.pushKV("value_hex", value.GetHex());
        ok.pushKV("negative", negative);
        ok.pushKV("overflow", overflow);
    } else if (op == "work.get_compact") {
        checkArgs(req, op, {"value_hex", "negative"});
        const auto bytes = argHex(req, "value_hex");
        if (bytes.size() != 32) throw RequestError{"value_hex must contain exactly 32 bytes"};
        arith_uint256 value;
        value.SetHex(arg(req, "value_hex").get_str());
        ok.pushKV("compact", static_cast<uint64_t>(value.GetCompact(argBool(req, "negative"))));
    } else if (op == "work.calculate_next") {
        checkArgs(req, op, {"network", "selection_height", "last_height", "last_time", "last_bits", "first_time"});
        selectWorkNetwork(req);
        const auto& params = Params().GetConsensus(argU32(req, "selection_height"));
        CBlockIndex last;
        last.nHeight = argInt(req, "last_height", 0, 2147483646);
        last.nTime = argU32(req, "last_time");
        last.nBits = argU32(req, "last_bits");
        const auto bits = CalculateDogecoinNextWorkRequired(&last, argU32(req, "first_time"), params);
        ok.pushKV("bits", static_cast<uint64_t>(bits));
    } else if (op == "block.header_sequence") {
        ok = headerSequence(req);
    } else if (op == "work.next" || op == "block.contextual_check") {
        const bool contextual = op == "block.contextual_check";
        if (contextual) checkArgs(req, op, {"bytes_hex", "network", "chain", "adjusted_time", "checkpoints_enabled", "known_checkpoints"});
        else checkArgs(req, op, {"network", "chain", "candidate_time"});
        selectWorkNetwork(req);
        const auto& entries = arg(req, "chain");
        if (!entries.isArray()) throw RequestError{"chain must be an array"};
        std::vector<CBlockIndex> chain(entries.size());
        for (size_t i = 0; i < chain.size(); ++i) {
            const auto& entry = entries[i];
            if (!entry.isObject()) throw RequestError{"chain entries must be objects"};
            for (const auto& key : entry.getKeys()) {
                if (key != "height" && key != "time" && key != "bits") throw RequestError{"unknown chain entry field"};
            }
            chain[i].nHeight = argInt(entry, "height", 0, 2147483646);
            chain[i].nTime = argU32(entry, "time");
            chain[i].nBits = argU32(entry, "bits");
            if (i && chain[i-1].nHeight != chain[i].nHeight + 1) throw RequestError{"inconsistent chain heights"};
        }
        CBlockHeader candidate;
        int64_t adjustedTime = 0;
        std::vector<CBlockIndex> checkpointEntries;
        mapBlockIndex.clear();
        if (contextual) {
            const auto bytes = argHex(req, "bytes_hex");
            if (bytes.size() != 80) throw RequestError{"bytes_hex must contain exactly 80 bytes"};
            CDataStream ds(bytes, SER_NETWORK, PROTOCOL_VERSION);
            ds >> static_cast<CPureBlockHeader&>(candidate);
            adjustedTime = argInt(req, "adjusted_time", INT64_MIN, INT64_MAX - 7200);
            fCheckpointsEnabled = argBool(req, "checkpoints_enabled");
            const auto& known = arg(req, "known_checkpoints");
            if (!known.isArray()) throw RequestError{"known_checkpoints must be an array"};
            checkpointEntries.resize(known.size());
            for (size_t i = 0; i < checkpointEntries.size(); ++i) {
                UniValue field(UniValue::VOBJ);
                field.pushKV("height", known[i]);
                const auto height = argInt(field, "height", 0, INT32_MAX);
                const auto& table = Params().Checkpoints().mapCheckpoints;
                const auto found = table.find(height);
                if (found == table.end()) throw RequestError{"known checkpoint height is outside the network table"};
                checkpointEntries[i].nHeight = height;
            }
            if (chain.empty() || chain.size() < std::min(11, chain.front().nHeight + 1))
                throw RequestError{"contextual view is empty or too short for median"};
        } else candidate.nTime = argU32(req, "candidate_time");
        const auto& params = Params().GetConsensus(chain.empty() ? 0 : chain.front().nHeight + 1);
        checkWorkHistory(chain, candidate, params);
        // Build from oldest to newest, with stable addresses and real pprev links.
        for (size_t i = chain.size(); i-- > 0;) {
            if (i + 1 < chain.size()) {
                chain[i].pprev = &chain[i+1];
                if (availableSkipHeight(chain[i].nHeight) >= chain.back().nHeight)
                    chain[i].BuildSkip();
            }
        }
        if (contextual) {
            for (auto& entry : checkpointEntries)
                mapBlockIndex[Params().Checkpoints().mapCheckpoints.at(entry.nHeight)] = &entry;
            const auto reason = contextualReject(candidate, &chain.front(), adjustedTime);
            ok.pushKV("valid", reason.empty());
            ok.pushKV("reject_reason", reason.empty() ? UniValue() : UniValue(reason));
            mapBlockIndex.clear();
        } else {
            const auto bits = GetNextWorkRequired(chain.empty() ? nullptr : &chain.front(), &candidate, params);
            ok.pushKV("bits", static_cast<uint64_t>(bits));
        }
    } else if (op == "compactsize.encode") {
        checkArgs(req, op, {"value"});
        uint64_t n = argU64(req, "value");
        CDataStream ds(SER_NETWORK, PROTOCOL_VERSION);
        WriteCompactSize(ds, n);
        ok.pushKV("bytes_hex", HexStr(ds.begin(), ds.end()));
    } else if (op == "compactsize.read") {
        checkArgs(req, op, {"bytes_hex"});
        std::vector<unsigned char> bytes = argHex(req, "bytes_hex");
        CDataStream ds(bytes, SER_NETWORK, PROTOCOL_VERSION);
        uint64_t n;
        try {
            n = ReadCompactSize(ds);
        } catch (const std::ios_base::failure& e) {
            throw SpecError{mapCoreFailure(e)};
        }
        ok.pushKV("value", std::to_string(n));
        ok.pushKV("consumed", static_cast<uint64_t>(bytes.size() - ds.size()));
        ok.pushKV("rest_hex", HexStr(ds.begin(), ds.end()));
    } else if (op == "tx.read_base") {
        checkArgs(req, op, {"bytes_hex"});
        std::vector<unsigned char> bytes = argHex(req, "bytes_hex");
        CDataStream ds(bytes, SER_NETWORK, BASE_VERSION);
        CMutableTransaction tx = readTransaction(ds);
        ok.pushKV("tx", txJson(tx));
        ok.pushKV("consumed", static_cast<uint64_t>(bytes.size() - ds.size()));
        ok.pushKV("rest_hex", HexStr(ds.begin(), ds.end()));
    } else if (op == "tx.decode_base") {
        checkArgs(req, op, {"bytes_hex"});
        std::vector<unsigned char> bytes = argHex(req, "bytes_hex");
        CMutableTransaction tx = decodeBaseComplete(bytes);
        CDataStream out(SER_NETWORK, BASE_VERSION);
        out << tx;
        ok.pushKV("tx", txJson(tx));
        ok.pushKV("serialized_hex", HexStr(out.begin(), out.end()));
        pushHash(ok, "txid", CTransaction(tx).GetHash());
    } else if (op == "tx.read_witness" || op == "tx.decode_witness") {
        checkArgs(req, op, {"bytes_hex"});
        std::vector<unsigned char> bytes = argHex(req, "bytes_hex");
        CDataStream ds(bytes, SER_NETWORK, PROTOCOL_VERSION);
        CMutableTransaction tx = readTransaction(ds);
        if (op == "tx.decode_witness" && !ds.empty()) {
            UniValue e(UniValue::VOBJ);
            e.pushKV("kind", "trailing_bytes");
            e.pushKV("count", static_cast<uint64_t>(ds.size()));
            throw SpecError{e};
        }
        CDataStream out(SER_NETWORK, PROTOCOL_VERSION);
        out << tx;
        UniValue witnesses(UniValue::VARR);
        for (const CTxIn& in : tx.vin) {
            UniValue stack(UniValue::VARR);
            for (const auto& item : in.scriptWitness.stack) stack.push_back(UniValue(hexOf(item)));
            witnesses.push_back(stack);
        }
        const CTransaction immutable(tx);
        ok.pushKV("tx", txJson(tx));
        ok.pushKV("witnesses", witnesses);
        ok.pushKV("has_witness", immutable.HasWitness());
        ok.pushKV("serialized_hex", HexStr(out.begin(), out.end()));
        pushHash(ok, "txid", immutable.GetHash());
        pushHash(ok, "wtxid", immutable.GetWitnessHash());
        if (op == "tx.read_witness") {
            ok.pushKV("consumed", static_cast<uint64_t>(bytes.size() - ds.size()));
            ok.pushKV("rest_hex", HexStr(ds.begin(), ds.end()));
        }
    } else if (op == "sighash.legacy") {
        checkArgs(req, op, {"tx_hex", "script_code_hex", "input_index", "hash_type"});
        std::vector<unsigned char> txBytes = argHex(req, "tx_hex");
        std::vector<unsigned char> codeBytes = argHex(req, "script_code_hex");
        uint32_t nIn = argU32(req, "input_index");
        uint32_t hashTypeBits = static_cast<uint32_t>(argInt(req, "hash_type", -2147483648LL, 4294967295LL));
        // Core's `int nHashType`: the same 32 bits, read as two's complement.
        int nHashType = static_cast<int32_t>(hashTypeBits);
        CMutableTransaction mtx;
        try {
            mtx = decodeBaseComplete(txBytes);
        } catch (SpecError& e) {
            e.json.pushKV("argument", "tx_hex");
            throw;
        }
        const CTransaction tx(mtx);
        const CScript code(codeBytes.begin(), codeBytes.end());
        uint256 digest = SignatureHash(code, tx, nIn, nHashType, 0, SIGVERSION_BASE);
        // The label of Core's two early returns (interpreter.cpp lines 1225 to 1235).
        bool fixed = nIn >= tx.vin.size() || ((nHashType & 0x1f) == SIGHASH_SINGLE && nIn >= tx.vout.size());
        static const uint256 one(uint256S("0000000000000000000000000000000000000000000000000000000000000001"));
        // Core returns one on both early returns. A hash of a preimage could
        // equal one too, so only this direction is checked.
        if (fixed && digest != one) {
            throw UnmappedCoreError{"plan fixed_digest, but Core's digest is not one"};
        }
        ok.pushKV("plan", fixed ? "fixed_digest" : "hash_bytes");
        pushHash(ok, "digest", digest);
    } else {
        throw RequestError{"unknown operation " + op};
    }
    return ok;
}

std::string trimAscii(const std::string& s)
{
    const char* ws = " \t\n\r\f\v";
    size_t b = s.find_first_not_of(ws);
    if (b == std::string::npos) return "";
    size_t e = s.find_last_not_of(ws);
    return s.substr(b, e - b + 1);
}

UniValue respond(const std::string& line)
{
    UniValue id;
    UniValue result(UniValue::VOBJ);
    try {
        UniValue req;
        if (!req.read(line)) throw RequestError{"invalid JSON"};
        if (!req.isObject()) throw RequestError{"the request must be a JSON object"};
        id = find_value(req, "id");
        result.pushKV("ok", run(req));
    } catch (const RequestError& e) {
        UniValue err(UniValue::VOBJ);
        err.pushKV("kind", "request");
        err.pushKV("message", e.message);
        result.pushKV("error", err);
    } catch (const SpecError& e) {
        result.pushKV("error", e.json);
    }
    UniValue response(UniValue::VOBJ);
    response.pushKV("id", id);
    response.pushKVs(result);
    return response;
}

#include "auxpow_fixtures.inc"

} // namespace

int main(int argc, char** argv)
{
    if (argc == 2 && std::string(argv[1]) == "--auxpow-pow-fixtures") {
        std::cout << reconstructAuxPowPowFixtures().write() << std::endl;
        return 0;
    }
    if (argc == 2 && std::string(argv[1]) == "--check-auxpow-fixtures") {
        std::cout << reconstructAuxPowFixtures().write() << std::endl;
        return 0;
    }
    if (argc == 2 && std::string(argv[1]) == "--version") {
        UniValue v(UniValue::VOBJ);
        v.pushKV("format", FORMAT);
        std::cout << v.write() << std::endl;
        return 0;
    }
    if (argc != 1) {
        std::cerr << "usage: core-oracle [--version | --check-auxpow-fixtures | --auxpow-pow-fixtures]\n"
                  << "Reads one JSON request per line of standard input. See docs/oracle.md." << std::endl;
        return 2;
    }
    ECCVerifyHandle ecc;
    std::string line;
    while (std::getline(std::cin, line)) {
        std::string trimmed = trimAscii(line);
        if (trimmed.empty()) continue;
        try {
            std::cout << respond(trimmed).write() << std::endl;
        } catch (const UnmappedCoreError& e) {
            std::cerr << "core-oracle: unmapped Core exception: " << e.message << std::endl;
            return 3;
        } catch (const std::exception& e) {
            std::cerr << "core-oracle: unexpected exception: " << e.what() << std::endl;
            return 3;
        }
    }
    return 0;
}
