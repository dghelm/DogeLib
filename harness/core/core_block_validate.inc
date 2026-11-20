// block.validate: Core's five checks of a new mainnet block, in the order of
// AcceptBlock and ConnectBlock (SOURCES.md D33, D110 and D114; design record
// 0010, section 5), on a chain and a coin set that the request supplies and
// the harness carries from each accepted block to the next.
//
// core_oracle.cpp includes this file inside its anonymous namespace.
//
// Every verdict comes from Core's CheckBlockHeader, ContextualCheckBlockHeader,
// CheckBlock, ContextualCheckBlock and ConnectBlock. The code here builds
// their inputs, refuses a request whose chain is too short for Core's reads,
// and computes the digests of docs/oracle.md from Core's own coin entries.
//
// The harness choices of design record 0010, section 5:
// - No script-check threads, and a null hashAssumeValid, which are Core's
//   defaults. ConnectBlock then checks every script in input order.
// - ConnectBlock runs with fJustCheck true on a new CCoinsViewCache over the
//   carried set. On success the harness sets the best block and flushes the
//   cache, because fJustCheck returns before SetBestBlock. On rejection the
//   cache is discarded, because UpdateCoins runs before the coinbase check.
// - mapBlockIndex holds the entry of the view's best block, which CheckInputs
//   reads for the spend height.
//
// Coin-set snapshots (design record 0011, section 3, and docs/oracle.md):
// - `coins_file` names a snapshot in the format dogelib-coins/1, in the place
//   of `coins`. readSnapshot loads the whole file into the carried set.
// - `snapshot_heights` with `snapshot_dir` writes the carried set as a
//   snapshot after the accepted block at each listed height, and
//   `digest_heights` reports the digest of the set at each listed height.
// - visitSet is the only code that walks the carried set. The digest and the
//   snapshot writer read the set through it, one CCoins entry at a time, in
//   the order of the transaction IDs. A set in Core's CCoinsViewDB needs
//   another visitSet alone, over the cursor of that view, which visits the
//   same entries in the same order (src/txdb.cpp, lines 93 to 104).
//
// force_csv_active (design record 0012, section 10.2 and decision 12): with
// the value true, each block also runs with the CSV state forced to ACTIVE,
// on the state before the block. The harness seeds THRESHOLD_ACTIVE for CSV
// at the boundary that the block reads, runs the five checks, and removes the
// seed. Core's own ContextualCheckBlock and ConnectBlock then run their CSV
// branches (D110, lines 3127 to 3140, and D114, lines 1906 to 1911 and 1948
// to 1959), and no line of Core's source changes. The block record gains the
// object `forced` with the result. The forced run never changes the carried
// state: only the run without the seed carries the coin set and the chain to
// the next block. A block without a predecessor, and a block with the genesis
// hash, get no seed, and their `forced` object is the result without it.
// No mainnet chain reaches the state ACTIVE (csv_never_lockedIn). The object
// shows what Core's code does in a state that Core never enters. It is not
// mainnet behavior, and it is not a Core comparison of the baseline.

// The carried coin set: a CCoinsView over a map, as CCoinsViewTest of Core's
// src/test/coins_tests.cpp, without that class's random choices. An entry that
// is pruned leaves the map.
class MemoryCoinsView : public CCoinsView
{
public:
    std::map<uint256, CCoins> coins;
    uint256 best;

    bool GetCoins(const uint256& txid, CCoins& out) const
    {
        const auto it = coins.find(txid);
        if (it == coins.end()) return false;
        out = it->second;
        return true;
    }
    bool HaveCoins(const uint256& txid) const { return coins.count(txid) != 0; }
    uint256 GetBestBlock() const { return best; }
    bool BatchWrite(CCoinsMap& mapCoins, const uint256& hashBlock)
    {
        for (CCoinsMap::iterator it = mapCoins.begin(); it != mapCoins.end();) {
            if (it->second.flags & CCoinsCacheEntry::DIRTY) {
                if (it->second.coins.IsPruned()) coins.erase(it->first);
                else coins[it->first] = it->second.coins;
            }
            mapCoins.erase(it++);
        }
        if (!hashBlock.IsNull()) best = hashBlock;
        return true;
    }
};

// The record of one coin under a tag: the tag, the outpoint, the height, the
// coinbase flag and the serialized output (docs/oracle.md, "Digests").
CDataStream coinRecord(unsigned char tag, const COutPoint& outpoint, const CCoins& entry, const CTxOut& out)
{
    CDataStream record(SER_NETWORK, PROTOCOL_VERSION);
    record << tag << outpoint << static_cast<uint32_t>(entry.nHeight) << static_cast<unsigned char>(entry.fCoinBase ? 1 : 0) << out;
    return record;
}

// One step of a digest chain: the double SHA-256 of the digest so far and the record.
void digestRecord(uint256& digest, const CDataStream& record)
{
    CHash256 hasher;
    hasher.Write(digest.begin(), 32);
    hasher.Write(reinterpret_cast<const unsigned char*>(record.data()), record.size());
    hasher.Finalize(digest.begin());
}

void digestCoin(uint256& digest, unsigned char tag, const COutPoint& outpoint, const CCoins& entry, const CTxOut& out)
{
    digestRecord(digest, coinRecord(tag, outpoint, entry, out));
}

// The whole set: its digest, the number of its coins, and the sum of their
// amounts as a string of decimal digits.
struct SetSummary {
    uint256 digest;
    uint64_t count = 0;
    std::string value;
};

// The decimal digits of an unsigned 128-bit number.
std::string decimal(unsigned __int128 n)
{
    std::string digits;
    do {
        digits.insert(digits.begin(), static_cast<char>('0' + static_cast<int>(n % 10)));
        n /= 10;
    } while (n != 0);
    return digits;
}

// Every entry of the carried set, in the order of the transaction IDs.
// std::map visits them in the order of uint256::Compare, which compares the
// bytes. This function is the only walk of the set (see the head of the file).
template <typename Visit>
void visitSet(const MemoryCoinsView& store, Visit visit)
{
    for (const auto& item : store.coins) visit(item.first, item.second);
}

// The summary of the whole set. `sink`, when it is not null, gets the record
// of each coin in the order of the digest: the bytes of a snapshot file. The
// sum of the amounts can exceed the int64_t range of CAmount, so it is a
// 128-bit sum: each amount is at most MAX_MONEY, so no sum of fewer than 2^64
// coins overflows it.
template <typename Store>
SetSummary setDigest(const Store& store, const std::function<void(const CDataStream&)>* sink = nullptr)
{
    SetSummary summary;
    unsigned __int128 value = 0;
    visitSet(store, [&](const uint256& txid, const CCoins& entry) {
        for (size_t n = 0; n < entry.vout.size(); ++n) {
            const CTxOut& out = entry.vout[n];
            if (out.IsNull()) continue;
            const CDataStream record = coinRecord(2, COutPoint(txid, static_cast<uint32_t>(n)), entry, out);
            digestRecord(summary.digest, record);
            if (sink) (*sink)(record);
            ++summary.count;
            if (!MoneyRange(out.nValue)) throw UnmappedCoreError{"a coin of the set has an amount outside MoneyRange"};
            value += static_cast<unsigned __int128>(out.nValue);
        }
    });
    summary.value = decimal(value);
    return summary;
}

UniValue validateFailure(const std::string& reason, int64_t index = -1)
{
    UniValue error(UniValue::VOBJ);
    error.pushKV("kind", "block_validate");
    error.pushKV("reason", reason);
    if (index >= 0) error.pushKV("index", index);
    return error;
}

// A fault of a snapshot file. `record` is the position of the coin record.
UniValue coinsFileFailure(const std::string& reason, int64_t record = -1)
{
    UniValue error(UniValue::VOBJ);
    error.pushKV("kind", "block_validate");
    error.pushKV("reason", reason);
    if (record >= 0) error.pushKV("record", record);
    return error;
}

// The digest and the number of the coins of a snapshot file.
struct SnapshotStart {
    uint256 digest;
    uint64_t count = 0;
};

// Read a snapshot in the format dogelib-coins/1 into the empty set `store`
// (docs/oracle.md, "Coin-set snapshots"). The file is the coin records of a
// whole set under the tag 2, in the order of the digest. The checks and their
// order are those of the oracle's reader.
SnapshotStart readSnapshot(const std::string& path, MemoryCoinsView& store)
{
    std::ifstream file(path, std::ios::binary);
    if (!file) throw SpecError{coinsFileFailure("coins_file_unreadable")};
    auto littleEndian = [](const unsigned char* p, int bytes) -> uint64_t {
        uint64_t n = 0;
        for (int i = bytes; i-- > 0;) n = n << 8 | p[i];
        return n;
    };
    SnapshotStart start;
    uint256 lastTxid;
    uint32_t lastIndex = 0;
    CCoins* current = nullptr;
    std::vector<unsigned char> script;
    for (int64_t record = 0;; ++record) {
        // Fills `to` with `count` bytes. False at the end of the file before the first byte.
        auto fill = [&](unsigned char* to, std::streamsize count, bool first) -> bool {
            file.read(reinterpret_cast<char*>(to), count);
            if (file.bad()) throw SpecError{coinsFileFailure("coins_file_unreadable")};
            if (first && file.gcount() == 0) return false;
            if (file.gcount() != count) throw SpecError{coinsFileFailure("coins_file_truncated", record)};
            return true;
        };
        // The fixed part: the tag, the outpoint, the height, the coinbase byte and the amount.
        unsigned char head[50];
        if (!fill(head, 50, true)) break;
        if (head[0] != 2) throw SpecError{coinsFileFailure("coins_file_tag", record)};
        uint256 txid;
        std::copy(head + 1, head + 33, txid.begin());
        const uint64_t index = littleEndian(head + 33, 4);
        const uint64_t height = littleEndian(head + 37, 4);
        const unsigned char coinbase = head[41];
        const uint64_t amount = littleEndian(head + 42, 8);
        if (index > 1048575) throw SpecError{coinsFileFailure("coins_file_index", record)};
        if (height > 2147483646) throw SpecError{coinsFileFailure("coins_file_height", record)};
        if (coinbase > 1) throw SpecError{coinsFileFailure("coins_file_coinbase", record)};
        // A negative int64_t amount, such as the -1 of a null output, is above MAX_MONEY as uint64_t.
        if (amount > static_cast<uint64_t>(MAX_MONEY)) throw SpecError{coinsFileFailure("coins_file_value", record)};
        // The length of the script, in the shortest CompactSize form.
        unsigned char size[8];
        fill(size, 1, false);
        uint64_t length = size[0];
        if (size[0] >= 253) {
            const int bytes = size[0] == 253 ? 2 : size[0] == 254 ? 4 : 8;
            fill(size, bytes, false);
            length = littleEndian(size, bytes);
            const uint64_t least = bytes == 2 ? 253 : bytes == 4 ? 0x10000ULL : 0x100000000ULL;
            if (length < least) throw SpecError{coinsFileFailure("coins_file_script_length", record)};
        }
        // A script above MAX_SCRIPT_SIZE is unspendable, so the reader does not read it.
        if (length > MAX_SCRIPT_SIZE) throw SpecError{coinsFileFailure("coins_file_script", record)};
        script.resize(length);
        if (length != 0) fill(script.data(), static_cast<std::streamsize>(length), false);
        const CScript scriptPubKey(script.begin(), script.end());
        if (scriptPubKey.IsUnspendable()) throw SpecError{coinsFileFailure("coins_file_script", record)};
        // The order of the set: the transaction IDs by their bytes, then the output indexes.
        const bool sameTxid = current && txid == lastTxid;
        if (current && !(lastTxid < txid || (sameTxid && lastIndex < index)))
            throw SpecError{coinsFileFailure("coins_file_order", record)};
        if (sameTxid) {
            if (static_cast<uint64_t>(current->nHeight) != height || current->fCoinBase != (coinbase == 1))
                throw SpecError{coinsFileFailure("coins_file_entry", record)};
        } else {
            current = &store.coins.emplace_hint(store.coins.end(), txid, CCoins())->second;
            current->fCoinBase = coinbase == 1;
            current->nHeight = static_cast<int>(height);
            current->nVersion = 1;
        }
        current->vout.resize(index + 1);
        current->vout[index] = CTxOut(static_cast<CAmount>(amount), scriptPubKey);
        lastTxid = txid;
        lastIndex = static_cast<uint32_t>(index);
        digestCoin(start.digest, 2, COutPoint(txid, lastIndex), *current, current->vout[index]);
        ++start.count;
    }
    return start;
}

// Write the set as the snapshot file `name` of the directory `dir`, through a
// temporary file. The result is the record of the snapshot in the response.
template <typename Store>
UniValue writeSnapshot(const Store& store, const std::string& dir, int height, const uint256& hash)
{
    const std::string name = "coins-" + std::to_string(height) + ".bin";
    const std::string path = dir + "/" + name;
    const std::string temporary = path + ".tmp";
    std::ofstream file(temporary, std::ios::binary | std::ios::trunc);
    if (!file) throw SpecError{coinsFileFailure("snapshot_unwritable")};
    CSHA256 hasher;
    uint64_t bytes = 0;
    const std::function<void(const CDataStream&)> sink = [&](const CDataStream& record) {
        file.write(record.data(), static_cast<std::streamsize>(record.size()));
        hasher.Write(reinterpret_cast<const unsigned char*>(record.data()), record.size());
        bytes += record.size();
    };
    const SetSummary summary = setDigest(store, &sink);
    file.close();
    if (!file || std::rename(temporary.c_str(), path.c_str()) != 0) throw SpecError{coinsFileFailure("snapshot_unwritable")};
    unsigned char sha256[CSHA256::OUTPUT_SIZE];
    hasher.Finalize(sha256);
    UniValue snapshot(UniValue::VOBJ);
    snapshot.pushKV("height", height);
    pushHash(snapshot, "hash", hash);
    snapshot.pushKV("file", name);
    snapshot.pushKV("bytes", bytes);
    snapshot.pushKV("sha256", hex(sha256, sha256 + CSHA256::OUTPUT_SIZE));
    snapshot.pushKV("set_digest_hex", hex(summary.digest.begin(), summary.digest.end()));
    snapshot.pushKV("set_coins", summary.count);
    snapshot.pushKV("set_value", summary.value);
    return snapshot;
}

// A list of heights in increasing order, or the empty list without the argument.
std::vector<int> argHeights(const UniValue& req, const std::string& key)
{
    std::vector<int> heights;
    if (!req.exists(key)) return heights;
    const UniValue& list = arg(req, key);
    if (!list.isArray()) throw RequestError{key + " must be an array"};
    for (size_t i = 0; i < list.size(); ++i) {
        UniValue field(UniValue::VOBJ);
        field.pushKV(key, list[i]);
        heights.push_back(static_cast<int>(argInt(field, key, 0, 2147483646)));
        if (i > 0 && heights[i - 1] >= heights[i]) throw RequestError{key + " must be in increasing order"};
    }
    return heights;
}

// The supplied coin set. The checks are those of the oracle's adapter.
void readCoins(const UniValue& req, MemoryCoinsView& store)
{
    const auto& entries = arg(req, "coins");
    if (!entries.isArray()) throw RequestError{"coins must be an array"};
    for (size_t i = 0; i < entries.size(); ++i) {
        const auto& entry = entries[i];
        if (!entry.isObject()) throw RequestError{"coins must contain objects"};
        for (const auto& key : entry.getKeys())
            if (key != "txid_hex" && key != "coinbase" && key != "height" && key != "outputs") throw RequestError{"unknown coin field"};
        const uint256 txid = argHash(entry, "txid_hex");
        CCoins coins;
        coins.fCoinBase = argBool(entry, "coinbase");
        coins.nHeight = static_cast<int>(argInt(entry, "height", 0, 2147483646));
        coins.nVersion = 1;
        const auto& outputs = arg(entry, "outputs");
        if (!outputs.isArray()) throw RequestError{"outputs must be an array"};
        if (outputs.empty()) throw RequestError{"a coin entry needs an output"};
        for (size_t j = 0; j < outputs.size(); ++j) {
            const auto& output = outputs[j];
            if (!output.isObject()) throw RequestError{"outputs must contain objects"};
            for (const auto& key : output.getKeys())
                if (key != "n" && key != "value" && key != "script_hex") throw RequestError{"unknown output field"};
            const size_t n = static_cast<size_t>(argInt(output, "n", 0, 1048575));
            if (n < coins.vout.size() && !coins.vout[n].IsNull()) throw RequestError{"duplicate output index"};
            const uint64_t value = argU64(output, "value");
            // Design record 0010, section 3: every supplied amount is from 0 to MAX_MONEY.
            if (value > static_cast<uint64_t>(MAX_MONEY)) throw SpecError{validateFailure("coin_value_out_of_range")};
            const auto script = argHex(output, "script_hex");
            if (script.size() > MAX_SIZE) throw RequestError{"script_hex is too long"};
            const CScript scriptPubKey(script.begin(), script.end());
            if (scriptPubKey.IsUnspendable()) throw RequestError{"a supplied coin must be spendable"};
            if (n >= coins.vout.size()) coins.vout.resize(n + 1);
            coins.vout[n] = CTxOut(static_cast<CAmount>(value), scriptPubKey);
        }
        if (store.coins.count(txid)) throw RequestError{"duplicate coin transaction ID"};
        store.coins[txid] = coins;
    }
}

// With CSV forced active, ConnectBlock runs SequenceLocks (D114, lines 1948 to
// 1959) on each transaction that is not a coinbase and has a version of at
// least 2 as an unsigned value. CalculateSequenceLocks (D110, lines 309 to
// 359) reads each input whose sequence has bit 31 clear, with the height c of
// its coin:
// - A height lock adds c + 65535 - 1 at most, in `int`. The harness refuses a
//   coin height from 2^31 - 65535, where that sum can overflow (design record
//   0012, section 7.2).
// - A time lock reads the median time past of the ancestor at max(c - 1, 0)
//   (line 348). That ancestor and its ten predecessors must be inside the
//   supplied chain, and at or below the predecessor of the block. The harness
//   refuses another read, because GetAncestor would return null or leave the
//   chain.
// The scan changes nothing and calls no Core function that can assert. The
// coin of an input is the entry of the carried set, or an earlier transaction
// of the block, whose coins have the height of the block. When both exist the
// scan tests both heights. It does not follow ConnectBlock's early exits, so
// it can refuse a request that Core would reject before SequenceLocks.
void refuseSequenceLockOutsideDomain(const CBlock& block, const MemoryCoinsView& store, const CBlockIndex* tip, int oldest, int height)
{
    if (!tip) return;
    std::set<uint256> created;
    auto test = [&](int coinHeight, bool timeLock) {
        if (!timeLock) {
            if (coinHeight > std::numeric_limits<int>::max() - 65535)
                throw RequestError{"a forced height lock reads a coin height outside the int domain"};
            return;
        }
        const int at = std::max(coinHeight - 1, 0);
        if (at > tip->nHeight || at - std::min(10, at) < oldest)
            throw RequestError{"a forced time lock reads an ancestor outside the chain"};
    };
    for (const auto& tx : block.vtx) {
        if (!tx->IsCoinBase() && static_cast<uint32_t>(tx->nVersion) >= 2) {
            for (const auto& in : tx->vin) {
                if (in.nSequence & CTxIn::SEQUENCE_LOCKTIME_DISABLE_FLAG) continue;
                const bool timeLock = (in.nSequence & CTxIn::SEQUENCE_LOCKTIME_TYPE_FLAG) != 0;
                const auto entry = store.coins.find(in.prevout.hash);
                if (entry != store.coins.end()) test(entry->second.nHeight, timeLock);
                if (created.count(in.prevout.hash)) test(height, timeLock);
            }
        }
        created.insert(tx->GetHash());
    }
}

UniValue blockValidate(const UniValue& req)
{
    // The blocks come from `blocks_hex`, or from the file that `blocks_file` names.
    const bool fromFile = req.exists("blocks_file");
    // The coin set comes from `coins`, or from the snapshot that `coins_file` names.
    const bool coinsFromFile = req.exists("coins_file");
    checkArgs(req, "block.validate", {"mode", "check_pow", "check_merkle_root", "adjusted_time", "chain",
                                      "bip34_ancestor_hex", coinsFromFile ? "coins_file" : "coins",
                                      fromFile ? "blocks_file" : "blocks_hex",
                                      "snapshot_heights", "snapshot_dir", "digest_heights", "force_csv_active"});
    const bool forceCsvActive = req.exists("force_csv_active") && argBool(req, "force_csv_active");
    if (fromFile && !arg(req, "blocks_file").isStr()) throw RequestError{"blocks_file must be a string"};
    if (coinsFromFile && !fromFile) throw RequestError{"coins_file needs blocks_file"};
    if (coinsFromFile && !arg(req, "coins_file").isStr()) throw RequestError{"coins_file must be a string"};
    const std::vector<int> snapshotHeights = argHeights(req, "snapshot_heights");
    const std::vector<int> digestHeights = argHeights(req, "digest_heights");
    if (req.exists("snapshot_heights") != req.exists("snapshot_dir"))
        throw RequestError{"snapshot_heights and snapshot_dir go together"};
    if (req.exists("snapshot_dir") && !arg(req, "snapshot_dir").isStr()) throw RequestError{"snapshot_dir must be a string"};
    LOCK(cs_main);
    SelectParams(CBaseChainParams::MAIN);
    const int version = headerStreamVersion(req);
    const bool checkPow = argBool(req, "check_pow");
    const bool checkMerkle = argBool(req, "check_merkle_root");
    const int64_t adjustedTime = argInt(req, "adjusted_time", INT64_MIN, INT64_MAX - 7200);
    const int bip34Height = Params().GetConsensus(0).BIP34Height;

    // The supplied chain, oldest first, with stable addresses. Later entries
    // are the accepted blocks.
    const auto& entries = arg(req, "chain");
    if (!entries.isArray()) throw RequestError{"chain must be an array"};
    std::deque<CBlockIndex> chain;
    std::deque<uint256> hashes;
    for (size_t i = entries.size(); i-- > 0;) {
        const auto& e = entries[i];
        if (!e.isObject()) throw RequestError{"chain entries must be objects"};
        for (const auto& key : e.getKeys())
            if (key != "height" && key != "time" && key != "bits") throw RequestError{"unknown chain entry field"};
        chain.emplace_back();
        // The oracle's adapter refuses a predecessor at height 2147483646 or above (bodyStates).
        // Core can represent the candidate height 2147483647. The limit is the adapter's, and
        // docs/oracle.md states it, so no request compares that height.
        chain.back().nHeight = static_cast<int>(argInt(e, "height", 0, 2147483645));
        chain.back().nTime = argU32(e, "time");
        chain.back().nBits = argU32(e, "bits");
        if (chain.size() > 1 && chain[chain.size() - 2].nHeight + 1 != chain.back().nHeight)
            throw RequestError{"inconsistent chain heights"};
    }
    const bool supplied = !chain.empty();
    const int oldest = supplied ? chain.front().nHeight : 0;
    for (size_t i = 1; i < chain.size(); ++i) {
        chain[i].pprev = &chain[i - 1];
        if (availableSkipHeight(chain[i].nHeight) >= oldest) chain[i].BuildSkip();
    }
    CBlockIndex* tip = supplied ? &chain.back() : nullptr;

    // The ancestor at BIP34Height, which ConnectBlock reads for the BIP30 rule
    // (D101, line 1877). Inside the supplied chain the entry of that height
    // gets the hash. Below the chain, the oldest entry gets a predecessor that
    // is its own predecessor and skip entry, as unknownAncestor above, so
    // GetAncestor returns it for every lower height. The reads below refuse a
    // request whose chain is too short for any other walk.
    const UniValue& ancestorArg = arg(req, "bip34_ancestor_hex");
    const bool above = tip && tip->nHeight >= bip34Height;
    if (ancestorArg.isNull() == above)
        throw RequestError{"bip34_ancestor_hex must be a hash exactly when the predecessor is at or above height 1034383"};
    uint256 ancestorHash;
    CBlockIndex anchor;
    if (above) {
        ancestorHash = argHash(req, "bip34_ancestor_hex");
        if (oldest <= bip34Height) {
            chain[static_cast<size_t>(bip34Height - oldest)].phashBlock = &ancestorHash;
        } else {
            anchor.pprev = &anchor;
            anchor.pskip = &anchor;
            anchor.phashBlock = &ancestorHash;
            chain.front().pprev = &anchor;
        }
    }

    MemoryCoinsView store;
    SnapshotStart snapshotStart;
    if (coinsFromFile) snapshotStart = readSnapshot(arg(req, "coins_file").get_str(), store);
    else readCoins(req, store);

    // A file has the format of `blocks.bin` of scripts/fetch_blocks.py: for
    // each block the height and the length as 4-byte little-endian integers,
    // then the block. The loop below reads one record at a time.
    const UniValue noBlocks(UniValue::VARR);
    const UniValue& raws = fromFile ? noBlocks : arg(req, "blocks_hex");
    if (!raws.isArray()) throw RequestError{"blocks_hex must be an array"};
    std::ifstream file;
    if (fromFile) {
        file.open(arg(req, "blocks_file").get_str(), std::ios::binary);
        if (!file) throw SpecError{validateFailure("file_unreadable")};
    }
    auto littleEndian = [](const unsigned char* p) {
        return static_cast<uint32_t>(p[0]) | static_cast<uint32_t>(p[1]) << 8 | static_cast<uint32_t>(p[2]) << 16 |
               static_cast<uint32_t>(p[3]) << 24;
    };

    // Core's state for this request, restored on every exit.
    struct Restore {
        bool checkpoints = fCheckpointsEnabled;
        ~Restore() {
            mapBlockIndex.clear();
            versionbitscache.Clear();
            fCheckpointsEnabled = checkpoints;
            harnessResetAdjustedTime();
        }
    } restore;
    mapBlockIndex.clear();
    versionbitscache.Clear();
    fCheckpointsEnabled = false;
    harnessSetAdjustedTime(adjustedTime);

    bool tipHashKnown = false;
    UniValue records(UniValue::VARR);
    UniValue snapshots(UniValue::VARR);
    UniValue setDigests(UniValue::VARR);
    for (size_t index = 0;; ++index) {
        std::vector<unsigned char> bytes;
        int64_t fileHeight = -1;
        if (fromFile) {
            unsigned char head[8];
            file.read(reinterpret_cast<char*>(head), 8);
            // A read that fails is not the end of the file.
            if (file.bad()) throw SpecError{validateFailure("file_unreadable")};
            if (file.gcount() == 0) break;
            if (file.gcount() != 8) throw SpecError{validateFailure("file_truncated", index)};
            fileHeight = littleEndian(head);
            const uint32_t length = littleEndian(head + 4);
            if (length > MAX_SIZE) throw SpecError{validateFailure("file_record_too_long", index)};
            bytes.resize(length);
            file.read(reinterpret_cast<char*>(bytes.data()), length);
            if (file.bad()) throw SpecError{validateFailure("file_unreadable")};
            if (static_cast<uint64_t>(file.gcount()) != length) throw SpecError{validateFailure("file_truncated", index)};
        } else {
            if (index >= raws.size()) break;
            if (!raws[index].isStr()) throw RequestError{"blocks_hex must contain hexadecimal strings"};
            UniValue field(UniValue::VOBJ);
            field.pushKV("blocks_hex", raws[index]);
            bytes = argHex(field, "blocks_hex");
        }
        CDataStream ds(bytes, SER_NETWORK, version);
        CBlock block;
        try {
            ds >> block;
        } catch (const std::ios_base::failure& e) {
            UniValue error = mapCoreFailure(e);
            error.pushKV("index", static_cast<uint64_t>(index));
            throw SpecError{error};
        }
        if (!ds.empty()) {
            UniValue error(UniValue::VOBJ);
            error.pushKV("kind", "trailing_bytes");
            error.pushKV("count", static_cast<uint64_t>(ds.size()));
            error.pushKV("index", static_cast<uint64_t>(index));
            throw SpecError{error};
        }
        if (block.fChecked) throw UnmappedCoreError{"a block from Core's reader has fChecked set"};
        const uint256 hash = block.GetHash();
        const bool genesis = hash == Params().GetConsensus(0).hashGenesisBlock;

        // A block extends the last accepted block. The first block names the
        // supplied predecessor.
        if (genesis) {
            if (tip) throw SpecError{validateFailure("genesis_after_start", index)};
        } else {
            if (!tip) throw SpecError{validateFailure("no_predecessor", index)};
            if (!tipHashKnown) {
                if (tip->nHeight == bip34Height && block.hashPrevBlock != ancestorHash)
                    throw RequestError{"bip34_ancestor_hex must be the predecessor's hash at height 1034383"};
                if (!tip->phashBlock) {
                    hashes.push_back(block.hashPrevBlock);
                    tip->phashBlock = &hashes.back();
                }
                store.best = block.hashPrevBlock;
                mapBlockIndex[block.hashPrevBlock] = tip;
                tipHashKnown = true;
            } else if (block.hashPrevBlock != tip->GetBlockHash()) {
                throw SpecError{validateFailure("not_linked", index)};
            }
        }

        // The reads of Core below the tip must stay inside the supplied chain.
        const int height = tip ? tip->nHeight + 1 : 0;
        // The aligned boundary of the block: the key of its version-bits states. It is null below the first period.
        CBlockIndex* boundary = nullptr;
        if (tip) {
            if (tip->nHeight - std::min(10, tip->nHeight) < oldest) throw RequestError{"chain is too short for the median time"};
            if (!genesis) {
                std::vector<CBlockIndex> recent;
                for (const CBlockIndex* walk = tip; walk && walk != &anchor && recent.size() < 242; walk = walk->pprev)
                    recent.push_back(*walk);
                checkWorkHistory(recent, block, Params().GetConsensus(height));
            }
            const int period = 10080;
            const int aligned = tip->nHeight - ((tip->nHeight + 1) % period);
            if (aligned >= 0) {
                if (aligned - std::min(10, aligned) < oldest) throw RequestError{"chain does not reach the aligned boundary"};
                boundary = tip->GetAncestor(aligned);
                const int64_t boundaryMtp = boundary->GetMedianTimePast();
                // The seed of design record 0010, decision 3, as in block.contextual_check_body.
                if (boundaryMtp >= 1493596800) {
                    versionbitscache.caches[Consensus::DEPLOYMENT_CSV][boundary] = THRESHOLD_FAILED;
                    versionbitscache.caches[Consensus::DEPLOYMENT_SEGWIT][boundary] = THRESHOLD_FAILED;
                } else if (boundaryMtp >= 1462060800) {
                    throw RequestError{"version-bits gap is outside the comparison domain"};
                }
            }
        }

        // A record of a file gives the height of its block.
        if (fromFile && fileHeight != height) throw SpecError{validateFailure("file_height", index)};

        // The five checks on the state before the block. With `forced` false, an
        // accepted block is flushed into the carried set. With `forced` true,
        // the cache is discarded, so the run changes no carried state.
        struct Run {
            bool valid = true;
            CValidationState state;
            std::string function = "CheckBlockHeader";
            uint256 changes;
            uint64_t spent = 0, created = 0;
        };
        auto runChecks = [&](Run& run, bool forced) {
            bool& valid = run.valid;
            CValidationState& state = run.state;
            std::string& function = run.function;
            uint256& changes = run.changes;
            uint64_t& spent = run.spent;
            uint64_t& created = run.created;
            if (!genesis) {
                if (checkPow) valid = CheckBlockHeader(block, state, true);
                if (valid) {
                    function = "ContextualCheckBlockHeader";
                    valid = ContextualCheckBlockHeader(block, state, tip, adjustedTime);
                }
            }
            if (valid) {
                function = "CheckBlock";
                valid = CheckBlock(block, state, checkPow, checkMerkle);
            }
            if (valid) {
                function = "ContextualCheckBlock";
                valid = ContextualCheckBlock(block, state, tip);
            }
            if (valid) {
                function = "ConnectBlock";
                CCoinsViewCache view(&store);
                CBlockIndex candidate(block);
                candidate.pprev = tip;
                candidate.nHeight = height;
                candidate.phashBlock = &hash;
                if (forced) refuseSequenceLockOutsideDomain(block, store, tip, oldest, height);
                valid = ConnectBlock(block, state, &candidate, view, Params(), true);
                if (valid) {
                    // The changes, read from a second cache that repeats Core's
                    // UpdateCoins on the transactions in order. The genesis block
                    // changes nothing (D114, lines 1821 to 1825).
                    if (!genesis) {
                        CCoinsViewCache shadow(&store);
                        for (const auto& tx : block.vtx) {
                            if (!tx->IsCoinBase()) {
                                for (const auto& in : tx->vin) {
                                    const CCoins* coins = shadow.AccessCoins(in.prevout.hash);
                                    if (!coins || !coins->IsAvailable(in.prevout.n))
                                        throw UnmappedCoreError{"an accepted block spends a coin that the view lacks"};
                                    digestCoin(changes, 0, in.prevout, *coins, coins->vout[in.prevout.n]);
                                    ++spent;
                                }
                            }
                            UpdateCoins(*tx, shadow, height);
                            const CCoins* coins = shadow.AccessCoins(tx->GetHash());
                            if (!coins) continue;
                            for (size_t n = 0; n < coins->vout.size(); ++n) {
                                if (coins->vout[n].IsNull()) continue;
                                digestCoin(changes, 1, COutPoint(tx->GetHash(), static_cast<uint32_t>(n)), *coins, coins->vout[n]);
                                ++created;
                            }
                        }
                        // The second cache must end in the state of the cache that ConnectBlock used.
                        auto same = [&](const uint256& txid) {
                            const CCoins* a = view.AccessCoins(txid);
                            const CCoins* b = shadow.AccessCoins(txid);
                            const CCoins none;
                            return (a ? *a : none) == (b ? *b : none);
                        };
                        for (const auto& tx : block.vtx) {
                            if (!same(tx->GetHash())) throw UnmappedCoreError{"the two caches differ after ConnectBlock"};
                            if (tx->IsCoinBase()) continue;
                            for (const auto& in : tx->vin)
                                if (!same(in.prevout.hash)) throw UnmappedCoreError{"the two caches differ after ConnectBlock"};
                        }
                    }
                    if (!forced) {
                        view.SetBestBlock(hash);
                        if (!view.Flush()) throw UnmappedCoreError{"the coin set refused a flush"};
                    }
                }
            }
        };

        // The forced run comes first, on the state before the block. A block
        // that is not applicable gets no seed (design record 0012, section 5).
        UniValue forcedRecord(UniValue::VOBJ);
        if (forceCsvActive) {
            auto& csv = versionbitscache.caches[Consensus::DEPLOYMENT_CSV];
            const bool applicable = tip && !genesis;
            const bool seeded = csv.count(boundary) != 0;
            const ThresholdState before = seeded ? csv[boundary] : THRESHOLD_DEFINED;
            if (applicable) csv[boundary] = THRESHOLD_ACTIVE;
            Run forced;
            runChecks(forced, true);
            if (applicable) {
                if (seeded) csv[boundary] = before;
                else csv.erase(boundary);
            }
            pushVerdict(forcedRecord, forced.valid, forced.state, forced.function);
            forcedRecord.pushKV("changes_digest_hex",
                                forced.valid ? UniValue(hex(forced.changes.begin(), forced.changes.end())) : UniValue());
            forcedRecord.pushKV("spent", forced.valid ? UniValue(forced.spent) : UniValue());
            forcedRecord.pushKV("created", forced.valid ? UniValue(forced.created) : UniValue());
        }

        Run plain;
        runChecks(plain, false);
        const bool valid = plain.valid;
        const CValidationState& state = plain.state;
        const std::string& function = plain.function;
        const uint256& changes = plain.changes;
        const uint64_t spent = plain.spent, created = plain.created;

        UniValue record(UniValue::VOBJ);
        record.pushKV("height", height);
        pushHash(record, "hash", hash);
        pushVerdict(record, valid, state, function);
        record.pushKV("changes_digest_hex", valid ? UniValue(hex(changes.begin(), changes.end())) : UniValue());
        record.pushKV("spent", valid ? UniValue(spent) : UniValue());
        record.pushKV("created", valid ? UniValue(created) : UniValue());
        UniValue digest, value;
        if (valid) {
            // The accepted block becomes the tip, and the only entry of mapBlockIndex.
            hashes.push_back(hash);
            chain.emplace_back(block);
            CBlockIndex& entry = chain.back();
            entry.pprev = tip;
            entry.nHeight = height;
            entry.phashBlock = &hashes.back();
            if (tip && availableSkipHeight(height) >= oldest) entry.BuildSkip();
            tip = &entry;
            tipHashKnown = true;
            mapBlockIndex.clear();
            mapBlockIndex[hash] = tip;
            // A request with `coins_file` has no digest of the whole set in a block record.
            if (!coinsFromFile && height % 1000 == 0) {
                const SetSummary whole = setDigest(store);
                digest = UniValue(hex(whole.digest.begin(), whole.digest.end()));
                value = UniValue(whole.value);
            }
            if (std::binary_search(snapshotHeights.begin(), snapshotHeights.end(), height))
                snapshots.push_back(writeSnapshot(store, arg(req, "snapshot_dir").get_str(), height, hash));
            if (std::binary_search(digestHeights.begin(), digestHeights.end(), height)) {
                const SetSummary whole = setDigest(store);
                UniValue summary(UniValue::VOBJ);
                summary.pushKV("height", height);
                summary.pushKV("set_digest_hex", hex(whole.digest.begin(), whole.digest.end()));
                summary.pushKV("set_coins", whole.count);
                summary.pushKV("set_value", whole.value);
                setDigests.push_back(summary);
            }
        }
        record.pushKV("set_digest_hex", digest);
        record.pushKV("set_value", value);
        if (forceCsvActive) record.pushKV("forced", forcedRecord);
        records.push_back(record);
    }

    const auto whole = setDigest(store);
    UniValue ok(UniValue::VOBJ);
    ok.pushKV("blocks", records);
    // The harness cannot observe an overflow. The comparator sends it no block
    // that the oracle reports as outside the int64 range.
    ok.pushKV("out_of_domain_at", UniValue());
    ok.pushKV("set_digest_hex", hex(whole.digest.begin(), whole.digest.end()));
    ok.pushKV("set_coins", whole.count);
    ok.pushKV("set_value", whole.value);
    if (coinsFromFile) {
        ok.pushKV("start_set_digest_hex", hex(snapshotStart.digest.begin(), snapshotStart.digest.end()));
        ok.pushKV("start_set_coins", snapshotStart.count);
    }
    if (req.exists("snapshot_heights")) ok.pushKV("snapshots", snapshots);
    if (req.exists("digest_heights")) ok.pushKV("set_digests", setDigests);
    return ok;
}
