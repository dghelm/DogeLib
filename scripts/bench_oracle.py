"""Measure hex requests through serialized oracle responses in persistent processes.

Usage: python3 -I scripts/bench_oracle.py BEFORE AFTER
Generated workloads measure elapsed time and provide no independent known answers.
"""

import json
import statistics
import subprocess
import sys
import time


def compact_size(n: int) -> bytes:
    """Encode the counts used by the fixed workloads."""
    return bytes([n]) if n < 253 else b"\xfd" + n.to_bytes(2, "little")


def transaction(inputs: int, outputs: int, script_size: int) -> bytes:
    """Generate base bytes with empty input scripts and repeated output scripts."""
    txin = bytes(36) + b"\x00" + b"\xff" * 4
    txout = (1).to_bytes(8, "little") + compact_size(script_size) + b"\x51" * script_size
    return ((1).to_bytes(4, "little") + compact_size(inputs) + txin * inputs
            + compact_size(outputs) + txout * outputs + bytes(4))


def exchange(proc: subprocess.Popen, request: str) -> tuple[int, dict]:
    """Time writing a complete hex request through reading its response line."""
    start = time.perf_counter_ns()
    proc.stdin.write(request + "\n")
    proc.stdin.flush()
    line = proc.stdout.readline()
    elapsed = time.perf_counter_ns() - start
    if not line:
        raise RuntimeError("oracle stopped before answering")
    response = json.loads(line)
    if "ok" not in response:
        raise RuntimeError(f"generated transaction rejected: {response}")
    return elapsed, response


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    print("shape,size,bytes,operation,reader,ns1,ns2,ns3,ns4,ns5,median_ns", flush=True)
    workloads = [("inputs", n, transaction(n, 1, 0)) for n in (253, 1000)]
    workloads += [("outputs", n, transaction(1, n, 0)) for n in (253, 1000)]
    workloads += [("scripts", n, transaction(1, 4, n)) for n in (4096, 16384)]
    processes = [subprocess.Popen([path], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                 text=True, bufsize=1) for path in sys.argv[1:]]
    try:
        for shape, size, data in workloads:
            for operation in ("tx.read_base", "tx.decode_base", "sighash.legacy"):
                args = {"bytes_hex": data.hex()} if operation != "sighash.legacy" else {
                    "tx_hex": data.hex(), "script_code_hex": "51", "input_index": 0, "hash_type": 1}
                request = json.dumps({"id": "bench", "op": operation, **args}, separators=(",", ":"))
                expected = [exchange(proc, request)[1] for proc in processes]
                if expected[0] != expected[1]:
                    raise RuntimeError("reader variants returned different responses")
                samples = [[], []]
                for run in range(5):
                    # Alternate the order to distribute shared-machine noise.
                    for index in ((0, 1) if run % 2 == 0 else (1, 0)):
                        elapsed, response = exchange(processes[index], request)
                        if response != expected[index]:
                            raise RuntimeError("response changed between repetitions")
                        samples[index].append(elapsed)
                for reader, times in zip(("list", "slice"), samples):
                    fields = [shape, size, len(data), operation, reader, *times, statistics.median(times)]
                    print(",".join(map(str, fields)), flush=True)
    finally:
        for proc in processes:
            proc.stdin.close()
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
            proc.stdout.close()
        if any(proc.returncode != 0 for proc in processes):
            raise RuntimeError("oracle exited unsuccessfully")


if __name__ == "__main__":
    main()
