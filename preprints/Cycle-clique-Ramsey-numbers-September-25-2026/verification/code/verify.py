#!/usr/bin/env python3
"""Run both complete finite computations and retain their actual evidence."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    source = Path(__file__).resolve().parent
    data = source.parent / 'data'
    expected = (data / 'expected-output.txt').read_bytes()
    receipt = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'python': sys.version, 'platform': platform.platform(),
               'interpreter': sys.executable,
               'interpreter_sha256': sha(Path(sys.executable)), 'runs': []}
    for name in ('original', 'independent'):
        destination = output / name
        destination.mkdir(exist_ok=True)
        script = source / (name + '_checker.py')
        command = [sys.executable, '-I', str(script)]
        if name == 'independent':
            command += ['--output', str(destination)]
        begin = time.perf_counter()
        completed = subprocess.run(command, capture_output=True, timeout=1800)
        elapsed = time.perf_counter() - begin
        (destination / 'stdout.txt').write_bytes(completed.stdout)
        (destination / 'stderr.txt').write_bytes(completed.stderr)
        record = {'name': name, 'command': command, 'script_sha256': sha(script),
                  'runtime_seconds': elapsed, 'exit_code': completed.returncode,
                  'stdout_sha256': sha(destination / 'stdout.txt'),
                  'stderr_sha256': sha(destination / 'stderr.txt'),
                  'expected_stdout_equal': completed.stdout == expected}
        receipt['runs'].append(record)
        (output / 'run.json').write_text(json.dumps(receipt, indent=2) + '\n')
        require(completed.returncode == 0, name + ' checker failed')
        require(completed.stdout == expected, name + ' output differs')
        require(completed.stderr == b'', name + ' wrote to stderr')
        print(name + ': complete output agrees', flush=True)
    directory = output / 'independent'
    summary = json.loads((directory / 'summary.json').read_text())
    records = [json.loads(line) for line in (directory / 'certificates.jsonl').read_text().splitlines()]
    domain = {(k, t) for k in range(5, 18)
              for t in range(max(3, k // 2), min(k, 8) + 1)}
    coverage = summary['coverage']
    require(len(domain) == len(coverage) == 42, 'incorrect parameter-pair count')
    require({(r['k'], r['t']) for r in coverage} == domain, 'incorrect parameter domain')
    require(len(records) == summary['total_patterns'] == 3099, 'incorrect pattern count')
    require(summary['unresolved'] == 0, 'unresolved patterns remain')
    require(all(r['classification'] in (1, 2) for r in records), 'invalid acceptance class')
    require(len({(r['k'], r['t'], json.dumps(r['pattern'])) for r in records}) == 3099,
            'repeated pattern instance')
    require(sha(directory / 'certificates.jsonl') == sha(data / 'certificates.jsonl'),
            'deduction traces differ from the supplied complete run')
    require(summary['implementation_sha256'] == sha(source / 'independent_checker.py'),
            'summary does not identify this implementation')
    for row in coverage:
        require(sum(r['k'] == row['k'] and r['t'] == row['t'] for r in records)
                == row['patterns'], 'trace and coverage counts differ')
    receipt['validated'] = {'parameter_pairs': 42, 'patterns': 3099,
                            'unresolved': 0, 'trace_sha256': sha(directory / 'certificates.jsonl'),
                            'trace_matches_delivered_data': True}
    (output / 'run.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('Verified 3099 patterns in all 42 parameter pairs; zero unresolved.', flush=True)


if __name__ == '__main__':
    main()
