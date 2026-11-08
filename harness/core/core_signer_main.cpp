// Request entry point. Keep the fixture generator and its source blob unchanged.
#define main fixtureMain
#include "core_signer.cpp"
#undef main

namespace {
// All Core references here use e0a1c157791544e818c901bd9341896965afbf9d.
// D94, univalue/include/univalue.h: 24–47, 64–82, 84–153, 172–180:
// JSON construction, access, type tests, arrays, object members, read and write.
// D93, utilstrencodings.h: 94–111: HexStr, called by the fixture hex helper.
Bytes requestHex(const UniValue& request, const char* name) {
    const UniValue& value = find_value(request, name);
    if (!value.isStr()) throw std::runtime_error(std::string(name) + " must be hex");
    const std::string text = value.get_str();
    if (text.size() % 2 || text.find_first_not_of("0123456789abcdefABCDEF") != std::string::npos)
        throw std::runtime_error(std::string(name) + " must be hex");
    // D38, src/utilstrencodings.cpp: 74–99, ParseHex.
    return ParseHex(text);
}
int requestInt(const UniValue& value, int lo, int hi) {
    if (!value.isNum()) throw std::runtime_error("expected integer");
    const int n = value.get_int();
    if (n < lo || n > hi) throw std::runtime_error("integer outside signing domain");
    return n;
}
UniValue signRequest(const UniValue& request) {
    if (!request.isObject()) throw std::runtime_error("expected object");
    const Bytes bytes = requestHex(request, "tx_hex");
    if (bytes.size() > 100000) throw std::runtime_error("transaction exceeds 100000 bytes");
    // D21, src/streams.h: 192–195, 242, 342–352, 379–383.
    // D4, transaction.h: 210–243,
    // 399–401: base-only transaction deserialization.
    CDataStream stream(bytes, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    CMutableTransaction tx;
    stream >> tx;
    if (!stream.empty()) throw std::runtime_error("trailing transaction bytes");
    const int n = requestInt(find_value(request, "input_index"), 0, 3);
    if (tx.vin.empty() || tx.vin.size() > 4 || tx.vout.size() > 5 || unsigned(n) >= tx.vin.size())
        throw std::runtime_error("expected 1–4 inputs, 0–5 outputs and an input index");
    const Bytes code = requestHex(request, "script_code_hex");
    if (code.size() > 10000) throw std::runtime_error("script exceeds 10000 bytes");
    const int hashType = requestInt(find_value(request, "hash_type"), 0, 255);
    const UniValue& ids = find_value(request, "key_ids");
    if (!ids.isArray() || ids.empty() || ids.size() > 3)
        throw std::runtime_error("expected 1–3 key identifiers");
    // D3, interpreter.cpp: 1225–1246. Amount is unused in SIGVERSION_BASE.
    const uint256 digest = SignatureHash(CScript(code.begin(), code.end()), CTransaction(tx),
                                         n, hashType, 0, SIGVERSION_BASE);
    UniValue signatures(UniValue::VARR);
    for (unsigned i = 0; i < ids.size(); ++i) {
        const int scalar = requestInt(ids[i], 1, 4);
        Bytes signature;
        // testKey calls D92, key.h: 72–85, 92–93 (Set, IsValid).
        // D91, key.cpp: 169–182, Sign with RFC 6979 and test_case=0.
        if (!testKey(scalar).Sign(digest, signature, 0)) throw std::runtime_error("sign failed");
        signature.push_back(hashType);
        signatures.push_back(hex(signature));
    }
    UniValue result(UniValue::VOBJ);
    result.pushKV("digest_hex", hex(digest));
    result.pushKV("signatures_hex", signatures);
    result.pushKV("CORE_SIGNER_BLOB", CORE_SIGNER_BLOB);
    result.pushKV("request_source_blob", CORE_SIGNER_REQUEST_BLOB);
    return result;
}
void signStream() {
    std::string line;
    while (std::getline(std::cin, line)) {
        UniValue request, response(UniValue::VOBJ);
        try {
            if (!request.read(line)) throw std::runtime_error("invalid JSON");
            response.pushKV("id", find_value(request, "id"));
            response.pushKV("ok", signRequest(request));
        } catch (const std::exception& error) {
            if (!response.exists("id")) response.pushKV("id", UniValue());
            UniValue refusal(UniValue::VOBJ);
            refusal.pushKV("kind", "refusal");
            refusal.pushKV("reason", error.what());
            response.pushKV("error", refusal);
        }
        std::cout << response.write() << std::endl;
    }
}
}
int main(int argc, char** argv) {
    if (argc == 2 && std::string(argv[1]) == "--version") {
        UniValue version(UniValue::VOBJ);
        version.pushKV("core_pin", PIN);
        version.pushKV("CORE_SIGNER_BLOB", CORE_SIGNER_BLOB);
        version.pushKV("request_source_blob", CORE_SIGNER_REQUEST_BLOB);
        std::cout << version.write() << std::endl;
        return 0;
    }
    if (argc != 2 || std::string(argv[1]) != "--sign") return fixtureMain(argc, argv);
    // D91, key.cpp: 300–324. D50, pubkey.cpp: 299–316, ECCVerifyHandle.
    ECC_Start();
    { ECCVerifyHandle verify; signStream(); }
    ECC_Stop();
    return 0;
}
