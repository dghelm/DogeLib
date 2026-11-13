"""block.subsidy requests and their expectations (design record 0010, stage 0010a).

The module builds the requests of the Core comparison and of the oracle test.
No expectation comes from DogeLib:

- SCHEDULE holds the fixed subsidies from height 145,000, read by hand from
  Core's GetDogecoinBlockSubsidy (SOURCES.md D104, src/dogecoin.cpp lines 142
  to 148).
- CORE_VALUES holds random subsidies that Core's own function returned
  through the harness at the pin, with Boost 1.70.0.
  tests/block/mainnet-subsidy-prev-hashes/README.md records the capture.
  The Core comparison computes them again.
"""
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "tests/block/mainnet-subsidy-prev-hashes/prev-hashes.bin"
COIN = 100000000
FIRST_SIMPLIFIED = 145000
BATCH = 1000
MAX_CASES = 65536

# Height -> coins, on any previous hash (D104, lines 142 to 148).
SCHEDULE = {
    145000: 250000, 145001: 250000, 199999: 250000,
    200000: 125000, 299999: 125000,
    300000: 62500, 399999: 62500,
    400000: 31250, 499999: 31250,
    500000: 15625, 599999: 15625,
    600000: 10000, 600001: 10000, 700000: 10000, 1034383: 10000, 3464751: 10000,
    5050000: 10000, 2147483647: 10000,
}

# Mainnet height -> coins, from Core's function on the real previous hash.
# The heights after 144999 in this table are the 30 mainnet heights below
# 145,000 for which the oracle reports a redraw.
CORE_VALUES = {
    1: 68416, 2: 729752, 99999: 971897, 100000: 348070, 144999: 384837,
    1891: 740852, 10809: 53499, 15517: 835074, 20929: 921193, 26090: 449362,
    42921: 12601, 44800: 151266, 45739: 576362, 49218: 449931, 54288: 95335,
    54916: 10083, 55872: 370695, 57253: 428815, 58031: 694635, 58948: 293476,
    60876: 708331, 65727: 175852, 68326: 259739, 68989: 848633, 76613: 369417,
    81944: 694812, 85141: 569144, 107611: 6579, 115083: 218731, 121755: 242666,
    124522: 386253, 128740: 445217, 135453: 149052, 136848: 6794, 141395: 275445,
}

_hashes = None


def prev_hash(height: int) -> bytes:
    """The previous block hash of a mainnet height from 1 to 145,000, in internal order."""
    global _hashes
    if _hashes is None:
        _hashes = FIXTURE.read_bytes()
        assert len(_hashes) == 32 * FIRST_SIMPLIFIED
    assert 1 <= height <= FIRST_SIMPLIFIED
    return _hashes[32 * (height - 1):32 * height]


def case(height: int, prev: bytes) -> dict:
    return {"height": height, "prev_hash_hex": prev.hex()}


def request(cases: list[dict]) -> dict:
    return {"op": "block.subsidy", "cases": cases}


def key(req: dict) -> str:
    return json.dumps({k: v for k, v in req.items() if k != "id"}, sort_keys=True)


def mainnet_requests() -> list[dict]:
    """Every height from 1 to 145,000 on its real previous hash, 1,000 heights in each request."""
    cases = [case(height, prev_hash(height)) for height in range(1, FIRST_SIMPLIFIED + 1)]
    return [request(cases[i:i + BATCH]) for i in range(0, len(cases), BATCH)]


def schedule_request() -> tuple[dict, list[str]]:
    """The fixed schedule on three previous hashes, with the expected subsidies."""
    hashes = [bytes(32), bytes([0xff]) * 32, prev_hash(1)]
    cases, expected = [], []
    for height, coins in SCHEDULE.items():
        for prev in hashes:
            cases.append(case(height, prev))
            expected.append(str(coins * COIN))
    return request(cases), expected


def core_values_request() -> tuple[dict, list[str]]:
    """The mainnet heights of CORE_VALUES, with Core's subsidies."""
    cases = [case(height, prev_hash(height)) for height in CORE_VALUES]
    return request(cases), [str(coins * COIN) for coins in CORE_VALUES.values()]


def boundary_request() -> dict:
    """Heights on each side of the changes at 100,000, 145,000 and 600,000, and height 0.

    Each previous hash occurs at every height, so the same seed meets both
    random ranges and the fixed schedule."""
    hashes = [bytes(32), bytes([0xff]) * 32, prev_hash(1), prev_hash(99999), prev_hash(100000),
              prev_hash(144999), prev_hash(145000)]
    heights = [0, 1, 99999, 100000, 100001, 144999, 145000, 145001, 599999, 600000, 600001]
    return request([case(height, prev) for height in heights for prev in hashes])


EXPECTATIONS = {}


def subsidy_sets() -> list[tuple[str, list[dict]]]:
    schedule, schedule_expected = schedule_request()
    values, values_expected = core_values_request()
    EXPECTATIONS[key(schedule)] = schedule_expected
    EXPECTATIONS[key(values)] = values_expected
    return [
        ("subsidy mainnet heights 1 to 145000", mainnet_requests()),
        ("subsidy boundaries and fixed schedule", [schedule, values, boundary_request()]),
    ]


def in_range(height: int, subsidy: str) -> bool:
    """Whether a subsidy is a value that Core's text allows at a height (D104, lines 138 to 148)."""
    if not isinstance(subsidy, str) or not subsidy.isdigit():
        return False
    koinu = int(subsidy)
    if height >= FIRST_SIMPLIFIED:
        return koinu == ((500000 >> (height // 100000)) if height < 600000 else 10000) * COIN
    most = (1000000 >> (height // 100000)) * COIN
    return koinu % COIN == 0 and 2 * COIN <= koinu <= most


def compare(req: dict, ours: dict, core: dict, peer: str = "core") -> tuple[str, str] | None:
    """None when both programs give the same subsidies, else a failure code and a message.

    `redraws` is a Lean diagnostic and `boost_version` is a harness label.
    The comparison checks their form and compares neither."""
    cases = req["cases"]
    for side, response, extra in (("oracle", ours, "redraws"), (peer, core, "boost_version")):
        ok = response.get("ok")
        if not isinstance(ok, dict) or set(ok) != {"subsidies", extra}:
            return "SUBSIDY", f"{side} must return subsidies and {extra}"
        subsidies = ok["subsidies"]
        if not isinstance(subsidies, list) or len(subsidies) != len(cases):
            return "SUBSIDY", f"{side} must return one subsidy for each case"
        for entry, subsidy in zip(cases, subsidies):
            if not in_range(entry["height"], subsidy):
                return "SUBSIDY", f"{side} returned {subsidy!r} at height {entry['height']}, outside Core's range"
    redraws = ours["ok"]["redraws"]
    if not isinstance(redraws, list) or len(redraws) != len(cases):
        return "SUBSIDY", "oracle must return one redraw count for each case"
    for entry, count in zip(cases, redraws):
        fixed = entry["height"] >= FIRST_SIMPLIFIED
        if (count is not None) == fixed or (not fixed and (type(count) is not int or count < 0)):
            return "SUBSIDY", f"malformed redraw count {count!r} at height {entry['height']}"
    if not isinstance(core["ok"]["boost_version"], str):
        return "SUBSIDY", f"{peer} must name its Boost version"
    if ours["ok"]["subsidies"] != core["ok"]["subsidies"]:
        index = next(i for i, (a, b) in enumerate(zip(ours["ok"]["subsidies"], core["ok"]["subsidies"])) if a != b)
        return "SUBSIDY", (f"case {index}, height {cases[index]['height']}: oracle {ours['ok']['subsidies'][index]}, "
                           f"{peer} {core['ok']['subsidies'][index]}")
    expected = EXPECTATIONS.get(key(req))
    if expected is not None and ours["ok"]["subsidies"] != expected:
        return "SUBSIDY", "both programs disagree with the independent expectation"
    return None
