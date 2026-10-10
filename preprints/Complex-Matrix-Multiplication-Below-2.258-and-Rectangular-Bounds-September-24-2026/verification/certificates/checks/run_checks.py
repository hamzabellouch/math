#!/usr/bin/env python3
"""Run the small publication checks once and record reproducibility hashes.

Default: standard library only. Pass --numerics to add mpmath diagnostics.
Each child writes canonical JSON. This runner checks stdout against those
exact saved bytes and independently verifies script/data identity hashes.
"""
from pathlib import Path
import argparse
import hashlib
import json
import platform
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--numerics', action='store_true',
                    help='also run 80-digit diagnostics; requires mpmath 1.3.0')
args = parser.parse_args()
directory = Path(__file__).resolve().parent
names = ['verify_rational.py', 'verify_construction.py', 'verify_baseline.py']
if args.numerics:
    names.append('numerical_diagnostics.py')
runs = []
for name in names:
    script = directory/name
    result = subprocess.run([sys.executable, str(script)], cwd=directory,
                            capture_output=True, check=True)
    output = script.with_suffix('.json').read_bytes()
    if result.stdout != output:
        raise SystemExit('stdout differs from saved JSON: '+name)
    parsed = json.loads(output)
    canonical = (json.dumps(parsed, indent=2, sort_keys=True)+'\n').encode()
    if canonical != output:
        raise SystemExit('JSON is not in stable canonical formatting: '+name)
    script_hash = hashlib.sha256(script.read_bytes()).hexdigest()
    if parsed.get('script_sha256') != script_hash or parsed.get('status') != 'passed':
        raise SystemExit('script identity or check status failed: '+name)
    if name == 'verify_baseline.py':
        data_hash = hashlib.sha256((directory/'baseline_data.json').read_bytes()).hexdigest()
        if parsed['data_sha256'] != data_hash:
            raise SystemExit('baseline dataset identity failed')
    runs.append({'script': name, 'script_sha256': script_hash,
                 'output': script.with_suffix('.json').name,
                 'output_sha256': hashlib.sha256(output).hexdigest(),
                 'stdout_matches_saved_bytes': True, 'stable_json_format': True,
                 'exit_code': result.returncode, 'stderr': result.stderr.decode()})
report = {'status': 'passed', 'python_version': platform.python_version(),
          'optional_numerics_run': args.numerics, 'runs': runs,
          'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
rendered = json.dumps(report, indent=2, sort_keys=True)+'\n'
(directory/'execution_report.json').write_text(rendered, encoding='utf-8')
print(rendered, end='')
