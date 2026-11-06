// Generate test-only signed spends with Core at the SOURCES.md pin.
// Private scalars 1, 2, 3 and 4 are public test data. Never fund these keys.
// CKey::Sign uses RFC 6979 with test_case=0. No DogeLib code signs a digest.
#include "key.h"
#include "hash.h"
#include "primitives/transaction.h"
#include "script/interpreter.h"
#include "streams.h"
#include "utilstrencodings.h"
#include "version.h"
#include <univalue.h>
#include <openssl/bn.h>
#include <array>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <algorithm>

// Core's random.cpp reports an entropy failure through this logging adapter.
// Keep the node logger and its server dependencies outside the fixture tool.
int LogPrintStr(const std::string& text) { std::cerr << text; return text.size(); }

namespace {
using Bytes = std::vector<unsigned char>;
const char* PIN = "e0a1c157791544e818c901bd9341896965afbf9d";
const unsigned FLAGS = SCRIPT_VERIFY_P2SH | SCRIPT_VERIFY_STRICTENC | SCRIPT_VERIFY_DERSIG |
    SCRIPT_VERIFY_LOW_S | SCRIPT_VERIFY_NULLDUMMY | SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY;

template<class T> std::string hex(const T& value) { return HexStr(value.begin(), value.end()); }
std::string txHex(const CMutableTransaction& tx) {
    CDataStream stream(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    stream << tx;
    return hex(stream);
}
const char* errorName(ScriptError error) {
    switch (error) {
#define SCRIPT_ERROR(value, name) case value: return name;
#include "script_error_names.inc"
#undef SCRIPT_ERROR
    default: throw std::runtime_error("unmapped ScriptError");
    }
}
CKey testKey(unsigned scalar, bool compressed = true) {
    Bytes secret(32, 0);
    secret.back() = scalar;
    CKey key;
    key.Set(secret.begin(), secret.end(), compressed);
    if (!key.IsValid()) throw std::runtime_error("invalid test key");
    return key;
}
CScript redeemScript(bool hybrid) {
    CScript script;
    script << OP_IF << OP_2;
    for (unsigned i = 1; i <= 3; ++i) {
        CPubKey pub = testKey(i).GetPubKey();
        script << Bytes(pub.begin(), pub.end());
    }
    CPubKey recovery = testKey(4, !hybrid).GetPubKey();
    Bytes pub(recovery.begin(), recovery.end());
    if (hybrid) pub[0] = 6 | (pub.back() & 1);
    script << OP_3 << OP_CHECKMULTISIG << OP_ELSE << int64_t(1000000)
           << OP_CHECKLOCKTIMEVERIFY << OP_DROP << pub << OP_CHECKSIG << OP_ENDIF;
    return script;
}
CScript outputScript(const CScript& redeem) {
    const auto hash = Hash160(redeem.begin(), redeem.end());
    return CScript() << OP_HASH160 << Bytes(hash.begin(), hash.end()) << OP_EQUAL;
}
CMutableTransaction transaction() {
    CMutableTransaction tx;
    tx.nVersion = 1;
    tx.nLockTime = 1000000;
    tx.vin.resize(1);
    tx.vin[0].prevout = COutPoint(uint256S("1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"), 0);
    tx.vin[0].nSequence = 0xfffffffe;
    tx.vout.emplace_back(100000000, CScript() << OP_TRUE);
    return tx;
}
// Replace S with n-S, then encode the positive DER integer with its sign byte.
Bytes highS(const Bytes& sig) {
    const size_t rlen = sig.at(3), soff = 6 + rlen, slen = sig.at(5 + rlen);
    BIGNUM* rawOrder = nullptr;
    const int parsed = BN_hex2bn(&rawOrder, "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");
    using Bn = std::unique_ptr<BIGNUM, decltype(&BN_free)>;
    Bn order(rawOrder, BN_free);
    Bn s(BN_bin2bn(sig.data() + soff, slen, nullptr), BN_free);
    if (!parsed || !order || !s || !BN_sub(s.get(), order.get(), s.get()))
        throw std::runtime_error("high S conversion failed");
    Bytes encoded(BN_num_bytes(s.get()));
    BN_bn2bin(s.get(), encoded.data());
    if (encoded.front() & 0x80) encoded.insert(encoded.begin(), 0);
    Bytes result{0x30, static_cast<unsigned char>(4 + rlen + encoded.size()), 0x02,
                 static_cast<unsigned char>(rlen)};
    result.insert(result.end(), sig.begin() + 4, sig.begin() + 4 + rlen);
    result.push_back(0x02);
    result.push_back(encoded.size());
    result.insert(result.end(), encoded.begin(), encoded.end());
    result.push_back(SIGHASH_ALL);
    return result;
}

void emit(const std::string& id, const std::string& mutation, const std::string& field,
          const std::vector<unsigned>& signers, CMutableTransaction tx,
          bool resign = false, bool reverse = false, bool otherBranch = false,
          bool high = false, unsigned flags = FLAGS, bool hybrid = false) {
    const bool recovery = signers.size() == 1;
    const CScript redeem = redeemScript(hybrid);
    const CScript spk = outputScript(redeem);
    const CMutableTransaction signing = resign ? tx : transaction();
    const uint256 digest = SignatureHash(redeem, CTransaction(signing), 0, SIGHASH_ALL, 0, SIGVERSION_BASE);
    std::vector<Bytes> sigs;
    UniValue signatures(UniValue::VARR), keys(UniValue::VARR), signerIds(UniValue::VARR);
    for (unsigned i = 1; i <= 4; ++i) {
        CKey key = testKey(i, !(hybrid && i == 4));
        CPubKey pub = key.GetPubKey();
        Bytes publicBytes(pub.begin(), pub.end());
        if (hybrid && i == 4) publicBytes[0] = 6 | (publicBytes.back() & 1);
        UniValue entry(UniValue::VOBJ);
        entry.pushKV("id", int(i));
        entry.pushKV("private_key_hex", hex(key));
        entry.pushKV("pubkey_hex", hex(publicBytes));
        keys.push_back(entry);
    }
    for (unsigned scalar : signers) {
        Bytes sig;
        if (!testKey(scalar).Sign(digest, sig, 0)) throw std::runtime_error("signing failed");
        sig.push_back(SIGHASH_ALL);
        sigs.push_back(sig);
        signatures.push_back(hex(sig));
        signerIds.push_back(int(scalar));
    }
    if (high) sigs[0] = highS(sigs[0]);
    if (reverse) std::reverse(sigs.begin(), sigs.end());
    UniValue spendSigs(UniValue::VARR);
    CScript unlocking;
    if (!recovery) unlocking << OP_0;
    for (const Bytes& sig : sigs) { unlocking << sig; spendSigs.push_back(hex(sig)); }
    unlocking << ((recovery != otherBranch) ? OP_0 : OP_1) << Bytes(redeem.begin(), redeem.end());
    tx.vin[0].scriptSig = unlocking;
    const CTransaction spend(tx);
    ScriptError error = SCRIPT_ERR_UNKNOWN_ERROR;
    const bool valid = VerifyScript(unlocking, spk, nullptr, flags,
                                   TransactionSignatureChecker(&spend, 0, 0), &error);
    const uint256 spendDigest = SignatureHash(redeem, spend, 0, SIGHASH_ALL, 0, SIGVERSION_BASE);
    UniValue record(UniValue::VOBJ);
    record.pushKV("id", id);
    record.pushKV("mutation", mutation);
    record.pushKV("changed_field", field);
    record.pushKV("core_revision", PIN);
    record.pushKV("generator", "harness/core/core_signer.cpp");
    record.pushKV("generator_source_blob", CORE_SIGNER_BLOB);
    record.pushKV("branch", recovery ? "recovery" : "multisig");
    record.pushKV("keys", keys);
    record.pushKV("signers", signerIds);
    record.pushKV("unsigned_tx_hex", txHex(signing));
    record.pushKV("digest_hex", hex(digest));
    record.pushKV("signatures_hex", signatures);
    record.pushKV("spend_signatures_hex", spendSigs);
    record.pushKV("redeem_script_hex", hex(redeem));
    record.pushKV("script_pubkey_hex", hex(spk));
    record.pushKV("tx_hex", txHex(tx));
    record.pushKV("spend_digest_hex", hex(spendDigest));
    record.pushKV("input_index", 0);
    record.pushKV("amount", 0);
    record.pushKV("hash_type", SIGHASH_ALL);
    record.pushKV("flags", int(flags));
    record.pushKV("resigned", resign);
    record.pushKV("core_valid", valid);
    record.pushKV("core_error", errorName(error));
    std::cout << record.write() << '\n';
}
void generate() {
    for (const auto& pair : std::vector<std::vector<unsigned>>{{1,2}, {1,3}, {2,3}})
        emit("multisig-" + std::to_string(pair[0]) + std::to_string(pair[1]), "none", "none", pair, transaction());
    emit("recovery", "none", "none", {4}, transaction());
    for (bool recovery : {false, true}) {
        const std::vector<unsigned> signers = recovery ? std::vector<unsigned>{4} : std::vector<unsigned>{1,2};
        const std::string prefix = recovery ? "recovery-" : "multisig-";
        auto tx = transaction(); tx.vout[0].nValue += 1;
        emit(prefix + "output-value", "committed field", "vout[0].nValue", signers, tx);
        tx = transaction(); tx.vout[0].scriptPubKey << OP_NOP;
        emit(prefix + "output-script", "committed field", "vout[0].scriptPubKey", signers, tx);
        tx = transaction(); tx.nVersion = 2;
        emit(prefix + "version", "committed field", "nVersion", signers, tx);
        tx = transaction(); tx.vin[0].prevout.n = 1;
        emit(prefix + "outpoint", "committed field", "vin[0].prevout.n", signers, tx);
        emit(prefix + "selector", "branch selector", "scriptSig.selector", signers, transaction(), false, false, true);
        emit(prefix + "high-s", "high S", "scriptSig.signature[0].S", signers, transaction(), false, false, false, true);
        emit(prefix + "high-s-allowed", "high S without LOW_S", "scriptSig.signature[0].S,flags.LOW_S", signers,
             transaction(), false, false, false, true, FLAGS & ~SCRIPT_VERIFY_LOW_S);
    }
    emit("multisig-reversed", "signature order", "scriptSig.signatures", {1,2}, transaction(), false, true);
    auto tx = transaction(); tx.nLockTime = 999999;
    emit("recovery-low-locktime-stale", "lock time below 1000000", "nLockTime", {4}, tx);
    emit("recovery-low-locktime-resigned", "lock time below 1000000", "nLockTime", {4}, tx, true);
    tx = transaction(); tx.nLockTime = 1000001;
    emit("recovery-locktime-stale", "lock time at least 1000000 and below 500000000", "nLockTime", {4}, tx);
    tx = transaction(); tx.vin[0].nSequence = 0xffffffff;
    emit("recovery-final-sequence", "final sequence", "vin[0].nSequence", {4}, tx, true);
    emit("recovery-hybrid", "hybrid key without STRICTENC", "redeemScript.recoveryKey,flags.STRICTENC", {4},
         transaction(), true, false, false, false, FLAGS & ~SCRIPT_VERIFY_STRICTENC, true);
    emit("recovery-hybrid-strict", "hybrid key with STRICTENC", "redeemScript.recoveryKey", {4},
         transaction(), true, false, false, false, FLAGS, true);
}
}
int main(int argc, char**) {
    if (argc != 1) { std::cerr << "usage: core-signer\n"; return 2; }
    ECC_Start();
    int result = 0;
    try { ECCVerifyHandle verify; generate(); }
    catch (const std::exception& e) { std::cerr << e.what() << '\n'; result = 1; }
    ECC_Stop();
    return result;
}
