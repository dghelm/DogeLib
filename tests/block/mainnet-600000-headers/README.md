# Mainnet headers around height 600,000

`headers.txt` contains the four raw 80-byte Dogecoin mainnet pure headers at heights 599,998–600,001.
Each line contains a decimal height, one space and the header as 160 hexadecimal digits.
The fixture lets `scripts/fetch_blocks.py` pin the four committed rule-change blocks at these heights.

## Source

The sources are the maintainer's mainnet node and these public Electrum servers:

- `dogecoin.stackwallet.com`, TCP port `50022`, with TLS.
- `electrum2.cipig.net`, TCP port `20060`, with TLS.

The orchestrator approved both Electrum sources before the fetch.
The fetch date is 2026-11-18 (UTC).
This command fetched, checked and wrote the fixture:

```bash
python3 -I scripts/fetch_600000_headers.py
```

The command read the node password as `scripts/fetch_blocks.py` reads it.
It did not print the password.
For each height, it called `getblockhash` and `getblock <hash> false`.
It required the double SHA-256 of the block's first 80 bytes to equal the node's returned hash.

The command sent these newline-terminated requests to each Electrum server:

```json
{"id":1,"method":"server.version","params":["DogeLib","1.4"]}
{"id":2,"method":"blockchain.block.headers","params":[599998,4]}
```

The second response contained four full headers.
Each record has the 80-byte pure header followed by its AuxPoW payload when version bit 8 is set.
The command used the parser of `scripts/check_full_headers.py` to split the records.
It consumed all response bytes and kept each record's first 80 bytes.

The command required certificate-checked TLS and valid JSON-RPC identifiers.
It also required four complete records, predecessor links, and byte-for-byte agreement among all three sources.
It stopped on an unavailable source or any disagreement.
It staged both output files and published them only after every check passed.

## Evidence boundary

All three sources are untrusted.
No existing committed fixture or Core checkpoint reaches these four heights.
Thus their agreement does not authenticate mainnet membership or connect this range to a checkpoint.
It gives independent agreement on the recorded bytes instead of relying only on the maintainer's node.

The four headers link to each other.
The fixture does not pin the block at height 599,997, so it does not authenticate the first predecessor link.
The fixture does not check proof of work, the required difficulty, the AuxPoW payload or any transaction.
The existing Core comparison checks the proof of work and context-free block rules separately.

The hashes in display order are:

| Height | Hash |
| ---: | --- |
| 599,998 | `6ff217f1e1204f2552aefdbdc3eb1cf8857a067b7206dd52d67cdcee1d37d981` |
| 599,999 | `9b72ab55c1dd7b9eb1a2f4dc89f6909fd7b2648581f2223fccf7057116fbe18d` |
| 600,000 | `caa5446c05c8e51cf7985a6cb4da4dc2b730e4ec399dc95b2a094df6bdd4f268` |
| 600,001 | `eb058cbb071b0e4b224f8dd9feb82d1955028acfb864a61588866c240235cb49` |

The header bytes are public chain data, not server software or explorer text.

`SHA256SUMS` pins `headers.txt`.
From this directory, check it with:

```bash
sha256sum -c SHA256SUMS
```
