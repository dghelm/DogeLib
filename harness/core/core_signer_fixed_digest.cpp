// Generate test-only spends that reach the fixed digest of SIGHASH_SINGLE, with Core at the SOURCES.md pin.
// core_signer_main.cpp includes this file after core_signer.cpp, and uses that file's helpers.
// Private scalars 1, 2 and 3 are public test data. Never fund these keys.
//
// D3, interpreter.cpp: 1225-1236: SignatureHash returns `one` when the hash type is SINGLE
// and nIn is at least the number of outputs. Each record has Core's own digest, signatures,
// VerifyScript verdict and ScriptError name. No DogeLib code supplies a value.

namespace {
const unsigned SINGLE = SIGHASH_SINGLE;
const unsigned LOOSE = FLAGS & ~SCRIPT_VERIFY_STRICTENC;

Bytes publicKey(unsigned scalar) {
    CPubKey pub = testKey(scalar).GetPubKey();
    return Bytes(pub.begin(), pub.end());
}

// One output script of the test keys, and the data that unlocks it.
struct Coin {
    std::string name;
    CScript spk;                   // the previous scriptPubKey
    CScript redeem;                // the P2SH redeem script, or empty
    CScript code;                  // the script code that EvalScript passes to CheckSig
    std::vector<unsigned> signers; // test scalars, in signature order
    bool multisig;
};

// OP_DUP OP_HASH160 <hash> OP_EQUALVERIFY [OP_CODESEPARATOR] OP_CHECKSIG, or OP_CHECKSIGVERIFY OP_1.
Coin p2pkh(bool verify, bool separator) {
    const Bytes pub = publicKey(1);
    const auto hash = Hash160(pub.begin(), pub.end());
    CScript tail;
    if (verify) tail << OP_CHECKSIGVERIFY << OP_1; else tail << OP_CHECKSIG;
    CScript spk;
    spk << OP_DUP << OP_HASH160 << Bytes(hash.begin(), hash.end()) << OP_EQUALVERIFY;
    if (separator) spk << OP_CODESEPARATOR;
    spk += tail;
    const std::string name = std::string("p2pkh") + (verify ? "-verify" : "") + (separator ? "-codeseparator" : "");
    return Coin{name, spk, CScript(), separator ? tail : spk, {1}, false};
}

// OP_2 <P1> <P2> <P3> OP_3 [OP_CODESEPARATOR] OP_CHECKMULTISIG, or OP_CHECKMULTISIGVERIFY OP_1.
// With p2sh, the script is the redeem script of OP_HASH160 <hash> OP_EQUAL.
Coin multisig(bool verify, bool separator, bool p2sh) {
    CScript tail;
    if (verify) tail << OP_CHECKMULTISIGVERIFY << OP_1; else tail << OP_CHECKMULTISIG;
    CScript script;
    script << OP_2;
    for (unsigned i = 1; i <= 3; ++i) script << publicKey(i);
    script << OP_3;
    if (separator) script << OP_CODESEPARATOR;
    script += tail;
    const std::string name = std::string(p2sh ? "p2sh-multisig" : "multisig") + (verify ? "-verify" : "") +
        (separator ? "-codeseparator" : "");
    return Coin{name, p2sh ? outputScript(script) : script, p2sh ? script : CScript(),
                separator ? tail : script, {1, 2}, true};
}

COutPoint outpoint(unsigned char fill, unsigned n) {
    uint256 hash;
    std::fill(hash.begin(), hash.end(), fill);
    return COutPoint(hash, n);
}

// The signing transaction: two inputs and one output. Input 1 has no output with its index.
CMutableTransaction fixedBase() {
    CMutableTransaction tx;
    tx.nVersion = 1;
    tx.nLockTime = 0;
    tx.vin.resize(2);
    tx.vin[0].prevout = outpoint(0x11, 0);
    tx.vin[0].nSequence = 0xffffffff;
    tx.vin[1].prevout = outpoint(0x22, 1);
    tx.vin[1].nSequence = 0xfffffffe;
    tx.vout.emplace_back(100000000, CScript() << OP_TRUE);
    return tx;
}

// Sign `signing` at `signIndex` for `signCoin` with each hash type, then spend `coin` at `index` of `tx`.
void emitFixed(const std::string& id, const std::string& group, const std::string& change,
               const Coin& signCoin, const CMutableTransaction& signing, unsigned signIndex,
               const std::vector<unsigned>& hashTypes, const Coin& coin, CMutableTransaction tx,
               unsigned index, unsigned flags) {
    if (hashTypes.size() != coin.signers.size() || signCoin.signers != coin.signers)
        throw std::runtime_error("signer mismatch");
    UniValue keys(UniValue::VARR), signerIds(UniValue::VARR), types(UniValue::VARR);
    UniValue digests(UniValue::VARR), spendDigests(UniValue::VARR), signatures(UniValue::VARR);
    for (unsigned i = 1; i <= 3; ++i) {
        UniValue entry(UniValue::VOBJ);
        entry.pushKV("id", int(i));
        entry.pushKV("private_key_hex", hex(testKey(i)));
        entry.pushKV("pubkey_hex", hex(publicKey(i)));
        keys.push_back(entry);
    }
    CScript unlocking;
    if (coin.multisig) unlocking << OP_0;
    for (size_t i = 0; i < hashTypes.size(); ++i) {
        const uint256 digest = SignatureHash(signCoin.code, CTransaction(signing), signIndex, hashTypes[i], 0,
                                             SIGVERSION_BASE);
        Bytes sig;
        if (!testKey(coin.signers[i]).Sign(digest, sig, 0)) throw std::runtime_error("signing failed");
        sig.push_back(hashTypes[i]);
        unlocking << sig;
        signerIds.push_back(int(coin.signers[i]));
        types.push_back(int(hashTypes[i]));
        digests.push_back(hex(digest));
        signatures.push_back(hex(sig));
    }
    if (!coin.multisig) unlocking << publicKey(coin.signers[0]);
    if (!coin.redeem.empty()) unlocking << Bytes(coin.redeem.begin(), coin.redeem.end());
    tx.vin.at(index).scriptSig = unlocking;
    const CTransaction spend(tx);
    ScriptError error = SCRIPT_ERR_UNKNOWN_ERROR;
    const bool valid = VerifyScript(unlocking, coin.spk, nullptr, flags,
                                   TransactionSignatureChecker(&spend, index, 0), &error);
    for (unsigned hashType : hashTypes)
        spendDigests.push_back(hex(SignatureHash(coin.code, spend, index, hashType, 0, SIGVERSION_BASE)));
    UniValue record(UniValue::VOBJ);
    record.pushKV("id", id);
    record.pushKV("group", group);
    record.pushKV("change", change);
    record.pushKV("core_revision", PIN);
    record.pushKV("generator", "harness/core/core_signer_fixed_digest.cpp");
    record.pushKV("keys", keys);
    record.pushKV("signers", signerIds);
    record.pushKV("hash_types", types);
    record.pushKV("signing_coin", signCoin.name);
    record.pushKV("signing_tx_hex", txHex(signing));
    record.pushKV("signing_input_index", int(signIndex));
    record.pushKV("signing_script_code_hex", hex(signCoin.code));
    record.pushKV("digests_hex", digests);
    record.pushKV("signatures_hex", signatures);
    record.pushKV("coin", coin.name);
    record.pushKV("script_pubkey_hex", hex(coin.spk));
    record.pushKV("redeem_script_hex", hex(coin.redeem));
    record.pushKV("script_code_hex", hex(coin.code));
    record.pushKV("tx_hex", txHex(tx));
    record.pushKV("input_index", int(index));
    record.pushKV("output_count", int(tx.vout.size()));
    record.pushKV("spend_digests_hex", spendDigests);
    record.pushKV("flags", int(flags));
    record.pushKV("core_valid", valid);
    record.pushKV("core_error", errorName(error));
    std::cout << record.write() << '\n';
}

void generateFixedDigest() {
    const std::vector<Coin> plain{p2pkh(false, false), multisig(false, false, false), multisig(false, false, true)};
    for (const Coin& coin : plain) {
        const std::vector<unsigned> single(coin.signers.size(), SINGLE);
        const std::string p = coin.name + "-";
        const CMutableTransaction base = fixedBase();
        emitFixed(p + "baseline", "baseline", "none", coin, base, 1, single, coin, base, 1, FLAGS);

        // The same signatures in spends that differ from the signing transaction.
        CMutableTransaction tx = base;
        tx.vin[1].prevout = outpoint(0x33, 7);
        tx.vin[1].nSequence = 5;
        emitFixed(p + "outpoint-sequence", "transplant", "vin[1].prevout,vin[1].nSequence", coin, base, 1, single,
                  coin, tx, 1, FLAGS);
        tx = base;
        tx.vin.resize(3);
        tx.vin[2].prevout = outpoint(0x44, 2);
        tx.vin[2].nSequence = 0xffffffff;
        emitFixed(p + "index", "transplant", "nIn=2,vin.size=3", coin, base, 1, single, coin, tx, 2, FLAGS);
        tx = CMutableTransaction();
        tx.nVersion = 1;
        tx.vin.resize(1);
        tx.vin[0].prevout = outpoint(0x55, 0);
        tx.vin[0].nSequence = 0xffffffff;
        emitFixed(p + "no-outputs", "transplant", "nIn=0,vin.size=1,vout.size=0", coin, base, 1, single,
                  coin, tx, 0, FLAGS);
        tx = base;
        tx.nVersion = 2;
        tx.nLockTime = 500000001;
        tx.vin[0].prevout = outpoint(0x66, 3);
        tx.vin[0].nSequence = 0;
        tx.vout[0] = CTxOut(1, CScript() << OP_RETURN);
        emitFixed(p + "locktime-outputs", "transplant", "nVersion,nLockTime,vin[0],vout[0]", coin, base, 1, single,
                  coin, tx, 1, FLAGS);
        const std::vector<unsigned> acp(coin.signers.size(), SINGLE | SIGHASH_ANYONECANPAY);
        emitFixed(p + "anyonecanpay", "hash type", "hash type 0x83", coin, base, 1, acp, coin, base, 1, FLAGS);

        // The boundary: one more output, so the digest of input 1 is no longer fixed.
        tx = base;
        tx.vout.emplace_back(1, CScript() << OP_TRUE);
        emitFixed(p + "boundary", "boundary", "vout.size=2", coin, base, 1, single, coin, tx, 1, FLAGS);
    }

    // Another script code: the same signatures spend an output whose script has OP_CODESEPARATOR.
    const CMutableTransaction base = fixedBase();
    emitFixed("p2pkh-codeseparator", "transplant", "scriptCode", p2pkh(false, false), base, 1, {SINGLE},
              p2pkh(false, true), base, 1, FLAGS);
    emitFixed("multisig-codeseparator", "transplant", "scriptCode", multisig(false, false, false), base, 1,
              {SINGLE, SINGLE}, multisig(false, true, false), base, 1, FLAGS);
    emitFixed("p2sh-multisig-codeseparator", "transplant", "scriptCode", multisig(false, false, true), base, 1,
              {SINGLE, SINGLE}, multisig(false, true, true), base, 1, FLAGS);

    // Undefined hash types whose low five bits are SINGLE, without and with STRICTENC.
    for (unsigned hashType : {0x23u, 0xa3u, 0xe3u}) {
        char text[3];
        snprintf(text, sizeof text, "%02x", hashType);
        for (const Coin& coin : {p2pkh(false, false), multisig(false, false, false)}) {
            const std::vector<unsigned> types(coin.signers.size(), hashType);
            const std::string id = coin.name + "-hashtype-" + text;
            emitFixed(id, "undefined hash type", std::string("hash type 0x") + text + ",flags.STRICTENC", coin,
                      base, 1, types, coin, base, 1, LOOSE);
            emitFixed(id + "-strict", "undefined hash type", std::string("hash type 0x") + text, coin,
                      base, 1, types, coin, base, 1, FLAGS);
        }
    }

    // OP_CHECKSIGVERIFY and OP_CHECKMULTISIGVERIFY.
    for (const Coin& coin : {p2pkh(true, false), multisig(true, false, false)}) {
        const std::vector<unsigned> single(coin.signers.size(), SINGLE);
        const std::string p = coin.name + "-";
        emitFixed(p + "baseline", "baseline", "none", coin, base, 1, single, coin, base, 1, FLAGS);
        CMutableTransaction tx = base;
        tx.vin.resize(3);
        tx.vin[2].prevout = outpoint(0x44, 2);
        tx.vin[2].nSequence = 0xffffffff;
        emitFixed(p + "index", "transplant", "nIn=2,vin.size=3", coin, base, 1, single, coin, tx, 2, FLAGS);
        tx = base;
        tx.vout.emplace_back(1, CScript() << OP_TRUE);
        emitFixed(p + "boundary", "boundary", "vout.size=2", coin, base, 1, single, coin, tx, 1, FLAGS);
    }

    // Mixed hash types: the ALL signature commits to the transaction, and the SINGLE signature does not.
    const Coin mixed = multisig(false, false, false);
    emitFixed("multisig-mixed-baseline", "mixed hash types", "none", mixed, base, 1, {SINGLE, SIGHASH_ALL},
              mixed, base, 1, FLAGS);
    CMutableTransaction tx = base;
    tx.vin[1].prevout = outpoint(0x33, 7);
    emitFixed("multisig-mixed-outpoint", "mixed hash types", "vin[1].prevout", mixed, base, 1,
              {SINGLE, SIGHASH_ALL}, mixed, tx, 1, FLAGS);
}
}
