// The Dogecoin Core harness: answers dogelib-oracle/3 requests by running
// Dogecoin Core's own code, so that scripts/compare_core.py can check the
// oracle against Core. docs/oracle.md, section "The Core harness", describes
// its responses, a projection of dogelib-oracle/3.
//
// scripts/build_core_harness.sh builds it against Core's libraries at the
// commit that SOURCES.md pins.
//
// Every result value comes from Core's code, with two exceptions that the
// documentation names: `plan` of sighash.legacy is a label computed here from
// Core's conditions, and sighash.legacy has no `preimage_hex`, because Core
// hashes its preimage without exposing it.
//
// An exception from Core that is not one of the four mapped read errors ends
// the program with status 3, so it shows as a failed comparison.

#include "arith_uint256.h"
#include "chain.h"
#include "chainparams.h"
#include "dogecoin.h"
#include "pow.h"
#include "primitives/transaction.h"
#include "script/interpreter.h"
#include "script/script.h"
#include "serialize.h"
#include "streams.h"
#include "uint256.h"
#include "utilstrencodings.h"
#include "version.h"

#include <univalue.h>

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

// Core passes the hash type as `int` and the input index as `unsigned int`.
static_assert(std::numeric_limits<int>::min() == INT32_MIN && std::numeric_limits<int>::max() == INT32_MAX,
              "int must be a 32-bit two's complement integer");
static_assert(std::numeric_limits<unsigned int>::max() == UINT32_MAX, "unsigned int must have 32 bits");

namespace {

const char* const FORMAT = "dogelib-oracle/3-core-projection";

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
    // Every bound is below 10^11 in magnitude.
    if (static_cast<long long>(digits.size()) + scale > 11) throw RequestError{"argument " + key + " is out of range"};
    digits.append(static_cast<size_t>(scale), '0');
    int64_t magnitude = std::stoll(digits);
    int64_t value = negative ? -magnitude : magnitude;
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

UniValue run(const UniValue& req)
{
    const UniValue& opv = arg(req, "op");
    if (!opv.isStr()) throw RequestError{"argument op must be a string"};
    const std::string& op = opv.get_str();
    UniValue ok(UniValue::VOBJ);

    if (op == "oracle.version") {
        checkArgs(req, op, {});
        ok.pushKV("format", FORMAT);
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
    } else if (op == "work.next") {
        checkArgs(req, op, {"network", "chain", "candidate_time"});
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
        candidate.nTime = argU32(req, "candidate_time");
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
        const auto bits = GetNextWorkRequired(chain.empty() ? nullptr : &chain.front(), &candidate, params);
        ok.pushKV("bits", static_cast<uint64_t>(bits));
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

} // namespace

int main(int argc, char** argv)
{
    if (argc == 2 && std::string(argv[1]) == "--version") {
        UniValue v(UniValue::VOBJ);
        v.pushKV("format", FORMAT);
        std::cout << v.write() << std::endl;
        return 0;
    }
    if (argc != 1) {
        std::cerr << "usage: core-oracle [--version]\n"
                  << "Reads one JSON request per line of standard input. See docs/oracle.md." << std::endl;
        return 2;
    }
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
