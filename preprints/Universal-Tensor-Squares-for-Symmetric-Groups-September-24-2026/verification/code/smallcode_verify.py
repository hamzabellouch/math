"""Independent grid-based MN verification and resource-bounded execution."""
import argparse
from collections import Counter
from functools import lru_cache
from math import ceil, factorial, prod
from pathlib import Path
import os
import resource
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
MODULI = (1000000007, 1000000009)


class VerificationError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


@lru_cache(None)
def partitions(n, cap=None):
    if n == 0:
        return ((),)
    if cap is None:
        cap = n
    return tuple((x,) + tail for x in range(min(n, cap), 0, -1)
                 for tail in partitions(n-x, x))


def cells(lam):
    return {(i, j) for i, width in enumerate(lam) for j in range(width)}


@lru_cache(None)
def removals(lam, k):
    outer = cells(lam)
    answer = []
    for mu in partitions(sum(lam)-k):
        inner = cells(mu)
        if not inner <= outer:
            continue
        strip = outer - inner
        if any({(i, j), (i+1, j), (i, j+1), (i+1, j+1)} <= strip
               for i, j in strip):
            continue
        seen = {next(iter(strip))}
        todo = list(seen)
        while todo:
            i, j = todo.pop()
            for neighbor in ((i-1,j), (i+1,j), (i,j-1), (i,j+1)):
                if neighbor in strip and neighbor not in seen:
                    seen.add(neighbor)
                    todo.append(neighbor)
        if seen == strip:
            answer.append((mu, (-1)**(len({i for i, j in strip})-1)))
    return tuple(answer)


@lru_cache(None)
def character(lam, rho):
    if not rho:
        return int(not lam)
    return sum(sign * character(mu, rho[1:]) for mu, sign in removals(lam, rho[0]))


def bounded_run(command, seconds):
    def limits():
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        memory = 1536 * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
        cpu = ceil(seconds) + 1
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu))
    started = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    process = subprocess.Popen(
        command,
        cwd=HERE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, start_new_session=True, preexec_fn=limits)
    try:
        stdout, stderr = process.communicate(timeout=seconds)
        status = str(process.returncode)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
        status = "TIMEOUT"
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    stderr += (f"child_cpu_seconds={after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime:.3f} "
               f"cumulative_child_max_rss_kib={after.ru_maxrss}\n")
    return status, time.monotonic()-started, stdout, stderr


def parse_dump(n, stdout):
    shapes = list(partitions(n))
    count = len(shapes)
    expected = {("partition", i) for i in range(count)}
    expected.update((kind, mod) for kind in ("dimensions", "mixed") for mod in MODULI)
    expected.update(("square", mod, i) for mod in MODULI for i in range(count))
    records = {}
    for number, line in enumerate(stdout.splitlines(), 1):
        fields = line.split()
        if not fields:
            continue
        kind = fields[0]
        require(kind in ("partition", "dimensions", "square", "mixed"),
                f"n={n} line={number}: unknown record {kind!r}")
        try:
            values = tuple(map(int, fields[1:]))
        except ValueError as error:
            raise VerificationError(f"n={n} line={number}: noninteger field") from error
        key_size = 2 if kind == "square" else 1
        require(len(values) >= key_size, f"n={n} line={number}: incomplete record")
        key = (kind, *values[:key_size])
        require(key in expected, f"n={n} line={number}: unexpected key {key}")
        require(key not in records, f"n={n} line={number}: duplicate key {key}")
        payload = values[key_size:]
        if kind == "partition":
            index = key[1]
            require(len(payload) == 1 + len(shapes[index]),
                    f"n={n} line={number}: wrong partition record length")
            require(payload[0] in (0, 1), f"n={n} line={number}: invalid symmetry flag")
            require(payload[1:] == shapes[index],
                    f"n={n} line={number}: incorrect indexed partition")
        else:
            require(len(payload) == count,
                    f"n={n} line={number}: wrong coefficient-vector length")
            require(all(0 <= x < key[1] for x in payload),
                    f"n={n} line={number}: residue outside the field range")
        records[key] = payload
    require(set(records) == expected,
            f"n={n}: missing records {sorted(expected - set(records))}")
    for index, shape in enumerate(shapes):
        transpose = tuple(sum(width >= j for width in shape)
                          for j in range(1, shape[0]+1))
        require(records[("partition", index)][0] == (transpose == shape),
                f"n={n}: incorrect symmetry flag for {shape}")
    return shapes, records


def compare(n, log):
    status, elapsed, stdout, stderr = bounded_run(
        [str(HERE / "smallcode_dump_ubsan"), str(n)], 45)
    log.write(f"dump n={n} status={status} wall_seconds={elapsed:.3f}\n{stderr}")
    log.flush()
    require(status == "0", f"n={n}: dump failed with status={status}; {stderr}")
    shapes, records = parse_dump(n, stdout)
    table = [[character(lam, rho) for rho in shapes] for lam in shapes]
    fact = factorial(n)
    class_sizes = [fact // prod(k**m * factorial(m) for k, m in Counter(rho).items())
                   for rho in shapes]
    for i, row in enumerate(table):
        for j, other in enumerate(table):
            require(sum(a*b*c for a,b,c in zip(row,other,class_sizes)) == fact*(i==j),
                    f"n={n}: independent character orthogonality failed at {i},{j}")
    squares = []
    for row in table:
        numerators = [sum(a*a*b*c for a,b,c in zip(row, other, class_sizes))
                      for other in table]
        require(all(x >= 0 and x % fact == 0 for x in numerators),
                f"n={n}: nonintegral or negative square coefficient")
        squares.append([x//fact for x in numerators])
    mixture = [sum(((3*i+1)%5)*table[i][j] for i in range(len(shapes)))
               for j in range(len(shapes))]
    mixed_numerators = [sum(a*a*b*c for a,b,c in zip(mixture, row, class_sizes))
                        for row in table]
    require(all(x >= 0 and x % fact == 0 for x in mixed_numerators),
            f"n={n}: nonintegral or negative mixed coefficient")
    mixed_exact = [x//fact for x in mixed_numerators]
    dims = [row[-1] for row in table]
    for mod in MODULI:
        require(records[("dimensions", mod)] == tuple(x % mod for x in dims),
                f"n={n} modulus={mod}: dimension mismatch")
        require(records[("mixed", mod)] == tuple(x % mod for x in mixed_exact),
                f"n={n} modulus={mod}: mixed-vector mismatch")
        for index, square in enumerate(squares):
            require(records[("square", mod, index)] == tuple(x % mod for x in square),
                    f"n={n} modulus={mod} index={index}: square-vector mismatch")
    winners = [list(lam) for lam, row in zip(shapes, squares) if all(row)]
    message = (f"PASS n={n} partitions={len(shapes)} all squares, mixed vector, "
               f"dimensions, conjugation; covering_shapes={winners}")
    log.write(message + "\n")
    log.flush()
    print(message, flush=True)


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("compare", "runs"))
    parser.add_argument("degrees", nargs="+", type=int)
    parser.add_argument("--seconds", type=float, default=15)
    parser.add_argument("--log", required=True)
    args = parser.parse_args(argv)
    failures = []
    with (HERE / args.log).open("w") as log:
        log.write("Memory limit per child: 1536 MiB; core dumps disabled.\n")
        if args.mode == "compare":
            log.write("Independent characters use grid-connected, square-free skew diagrams.\n")
            for n in args.degrees:
                compare(n, log)
        else:
            log.write(f"Wall limit per child: {args.seconds} seconds.\n")
            for n in args.degrees:
                status, elapsed, stdout, stderr = bounded_run(
                    [str(HERE / "smallcode_submitted"), str(n)], args.seconds)
                message = f"n={n} status={status} wall_seconds={elapsed:.3f}"
                log.write(f"{message}\nstdout={stdout!r}\nstderr={stderr!r}\n")
                log.flush()
                print(f"{message}; {stderr.strip()}", flush=True)
                if status != "0":
                    failures.append((n, status))
    if failures:
        print(f"FAIL: unsuccessful degree runs: {failures}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
