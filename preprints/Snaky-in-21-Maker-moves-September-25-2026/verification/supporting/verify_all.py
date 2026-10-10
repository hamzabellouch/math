#!/usr/bin/env python3
"""Run the three separately encoded certificate reconstruction packages."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((here/'CERTIFICATE-SUPPORT-MANIFEST.json').read_text())
    for record in manifest['files']:
        path = here/record['path']
        if (hashlib.sha256(path.read_bytes()).hexdigest() != record['sha256']
                or path.stat().st_size != record['bytes']
                or format(path.stat().st_mode & 0o777,'04o') != record['mode']):
            raise ValueError('support identity mismatch: ' + record['path'])
    results = []
    for route in ('route21','route25','route35'):
        command = [sys.executable,str(here/route/'run_tests.py'),'--output-dir',str(output/route)]
        environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
        run = subprocess.run(command,capture_output=True,text=True,env=environment)
        record = {'route':route,'argv':command,'exit':run.returncode,'stdout':run.stdout,'stderr':run.stderr,
                  'certificate_sha256':hashlib.sha256((here/route/'certificate.txt').read_bytes()).hexdigest()}
        results.append(record)
        print(route + ': ' + ('PASS' if run.returncode == 0 else 'FAIL'), flush=True)
        if run.returncode != 0:
            (output/'report.json').write_text(json.dumps({'status':'FAIL','runs':results},indent=2)+'\n')
            raise SystemExit(run.stderr or run.stdout or 'certificate reconstruction failed')
    display_path = here/'route25'/'certificate-display.txt'
    literal_path = here/'route25'/'certificate.txt'
    display = display_path.read_bytes()
    receipt = json.loads((here/'route25'/'display-identity.json').read_text())
    recovered, index = [], 6
    for line in display.splitlines(keepends=True):
        if line.startswith(b'['):
            match = re.fullmatch(rb'\[([0-9]+)\] ([0-9]{3}(?: [0-9]{3})*)\n',line)
            if match is None or int(match[1]) != index:
                raise ValueError('invalid route25 display row')
            recovered.append(match[2].replace(b' ',b'')+b'\n')
            index += 1
        else:
            recovered.append(line)
    if index != 2016 or b''.join(recovered) != literal_path.read_bytes():
        raise ValueError('route25 display does not roundtrip to literal')
    if hashlib.sha256(display).hexdigest() != receipt['display_sha256'] or hashlib.sha256(literal_path.read_bytes()).hexdigest() != receipt['literal_sha256']:
        raise ValueError('route25 display identity differs from receipt')
    presentation = {'roundtrip_exact':True,'numeric_rows':index-6,'display_sha256':receipt['display_sha256']}
    (output/'report.json').write_text(json.dumps({'status':'PASS','support_manifest_sha256':hashlib.sha256((here/'CERTIFICATE-SUPPORT-MANIFEST.json').read_bytes()).hexdigest(),'runs':results,'route25_presentation':presentation},indent=2)+'\n')
    print('PASS: three distinct literal certificates and independent reconstruction packages')

if __name__ == '__main__':
    main()
