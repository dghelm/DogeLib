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

// One step of a digest chain: the double SHA-256 of the digest so far, the
// tag, the outpoint, the height, the coinbase flag and the serialized output.
void digestCoin(uint256& digest, unsigned char tag, const COutPoint& outpoint, const CCoins& entry, const CTxOut& out)
{
    CDataStream record(SER_NETWORK, PROTOCOL_VERSION);
    record << tag << outpoint << static_cast<uint32_t>(entry.nHeight) << static_cast<unsigned char>(entry.fCoinBase ? 1 : 0) << out;
    CHash256 hasher;
    hasher.Write(digest.begin(), 32);
    hasher.Write(reinterpret_cast<const unsigned char*>(record.data()), record.size());
    hasher.Finalize(digest.begin());
}

// The digest of the whole set and the number of its coins. std::map visits the
// transaction IDs in the order of uint256::Compare, which compares the bytes.
std::pair<uint256, uint64_t> setDigest(const MemoryCoinsView& store)
{
    uint256 digest;
    uint64_t count = 0;
    for (const auto& item : store.coins) {
        for (size_t n = 0; n < item.second.vout.size(); ++n) {
            if (item.second.vout[n].IsNull()) continue;
            digestCoin(digest, 2, COutPoint(item.first, static_cast<uint32_t>(n)), item.second, item.second.vout[n]);
            ++count;
        }
    }
    return std::make_pair(digest, count);
}

UniValue validateFailure(const std::string& reason, int64_t index = -1)
{
    UniValue error(UniValue::VOBJ);
    error.pushKV("kind", "block_validate");
    error.pushKV("reason", reason);
    if (index >= 0) error.pushKV("index", index);
    return error;
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

UniValue blockValidate(const UniValue& req)
{
    // The blocks come from `blocks_hex`, or from the file that `blocks_file` names.
    const bool fromFile = req.exists("blocks_file");
    checkArgs(req, "block.validate", {"mode", "check_pow", "check_merkle_root", "adjusted_time", "chain",
                                      "bip34_ancestor_hex", "coins", fromFile ? "blocks_file" : "blocks_hex"});
    if (fromFile && !arg(req, "blocks_file").isStr()) throw RequestError{"blocks_file must be a string"};
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
    readCoins(req, store);

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
    for (size_t index = 0;; ++index) {
        std::vector<unsigned char> bytes;
        int64_t fileHeight = -1;
        if (fromFile) {
            unsigned char head[8];
            file.read(reinterpret_cast<char*>(head), 8);
            if (file.gcount() == 0) break;
            if (file.gcount() != 8) throw SpecError{validateFailure("file_truncated", index)};
            fileHeight = littleEndian(head);
            const uint32_t length = littleEndian(head + 4);
            if (length > MAX_SIZE) throw SpecError{validateFailure("file_record_too_long", index)};
            bytes.resize(length);
            file.read(reinterpret_cast<char*>(bytes.data()), length);
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
                CBlockIndex* boundary = tip->GetAncestor(aligned);
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

        CValidationState state;
        bool valid = true;
        std::string function = "CheckBlockHeader";
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
        uint256 changes;
        uint64_t spent = 0, created = 0;
        if (valid) {
            function = "ConnectBlock";
            CCoinsViewCache view(&store);
            CBlockIndex candidate(block);
            candidate.pprev = tip;
            candidate.nHeight = height;
            candidate.phashBlock = &hash;
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
                view.SetBestBlock(hash);
                if (!view.Flush()) throw UnmappedCoreError{"the coin set refused a flush"};
            }
        }

        UniValue record(UniValue::VOBJ);
        record.pushKV("height", height);
        pushHash(record, "hash", hash);
        pushVerdict(record, valid, state, function);
        record.pushKV("changes_digest_hex", valid ? UniValue(hex(changes.begin(), changes.end())) : UniValue());
        record.pushKV("spent", valid ? UniValue(spent) : UniValue());
        record.pushKV("created", valid ? UniValue(created) : UniValue());
        UniValue digest;
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
            if (height % 1000 == 0) {
                const uint256 whole = setDigest(store).first;
                digest = UniValue(hex(whole.begin(), whole.end()));
            }
        }
        record.pushKV("set_digest_hex", digest);
        records.push_back(record);
    }

    const auto whole = setDigest(store);
    UniValue ok(UniValue::VOBJ);
    ok.pushKV("blocks", records);
    // The harness cannot observe an overflow. The comparator sends it no block
    // that the oracle reports as outside the int64 range.
    ok.pushKV("out_of_domain_at", UniValue());
    ok.pushKV("set_digest_hex", hex(whole.first.begin(), whole.first.end()));
    ok.pushKV("set_coins", whole.second);
    return ok;
}
