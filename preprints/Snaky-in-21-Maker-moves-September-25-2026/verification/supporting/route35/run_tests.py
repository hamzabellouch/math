#!/usr/bin/env python3
"""Run route-35 data, independence, reconstruction, and rejection checks.

All workers run in isolated Python processes, from an unrelated working
directory, using only this standalone directory and the Python standard library.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True

TABLE_SHA256 = '16d077f0b64df70dd67fb6e9651636d42eaab0ce0f01f46180a57846e38fedc2'
TEMPLATES_SHA256 = '05d1658df1e37236b6d416afd73dd042c2f7223789df7a78e2b8032496136dc3'
CHECKERS = ('verify_certificate.py', 'independent_certificate.py', 'independent_opening.py')
MODES = (('normal', []), ('optimized', ['-O']), ('double_optimized', ['-OO']))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def mutations(raw):
    lines = raw.splitlines(keepends=True)
    return {
        'empty': b'',
        'missing_final_newline': raw[:-1],
        'truncated_last_row': b''.join(lines[:-1]),
        'truncated_half': b''.join(lines[:305]),
        'extra_row': raw + b'616 615a44\n',
        'non_ascii': raw.replace(b'0a03', b'0a\xff3', 1),
        'invalid_letter': raw.replace(b'0a03', b'0i03', 1),
        'missing_offset_digit': raw.replace(b'0a03', b'0a0', 1),
        'negative_child': raw.replace(b'0a03', b'-1a03', 1),
        'self_reference': raw.replace(b'0a03', b'6a03', 1),
        'forward_reference': raw.replace(b'0a03', b'7a03', 1),
        'wrong_row_index': raw.replace(b'6 0a03', b'7 0a03', 1),
        'empty_row': raw.replace(b'6 0a03\n', b'6\n', 1),
        'double_space': raw.replace(b'6 0a03', b'6  0a03', 1),
        'tab_separator': raw.replace(b'6 0a03', b'6\t0a03', 1),
        'crlf': raw.replace(b'\n', b'\r\n'),
        'trailing_garbage': raw.replace(b'6 0a03', b'6 0a03junk', 1),
        'leading_zero_child': raw.replace(b'0a03', b'00a03', 1),
        'extra_placement': raw.replace(b'6 0a03', b'6 0a03 0a03', 1),
    }


PARSER_WORKER = r'''
import json, pathlib, runpy, sys
module = runpy.run_path(sys.argv[1])
cases = pathlib.Path(sys.argv[2])
results = []
for path in sorted(cases.glob('*.txt')):
    try:
        module['reconstruct'](path.read_bytes())
    except ValueError as exc:
        results.append({'case':path.stem,'rejected':True,'exception':'ValueError','reason':str(exc)})
    else:
        raise RuntimeError('Malformed raw input accepted: ' + path.name)
print(json.dumps(results,sort_keys=True))
'''


def call(command, cwd):
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=120)
    return dict(command=command, returncode=result.returncode,
                stdout=result.stdout, stderr=result.stderr)


def run(output_dir=None):
    root = Path(__file__).resolve().parent
    raw = (root / 'certificate.txt').read_bytes()
    require(digest(raw) == TABLE_SHA256, 'Literal certificate identity mismatch')
    manifest = json.loads((root / 'manifest.json').read_text(encoding='ascii'))
    require(manifest['certificate']['sha256'] == TABLE_SHA256, 'Manifest literal pin differs')
    require(manifest['all_templates_sha256'] == TEMPLATES_SHA256, 'Manifest set digest differs')
    for record in manifest['files']:
        path = root / record['path']
        require(path.parent == root, 'Manifest contains a path outside standalone root')
        require(path.is_file(), 'Missing support file: ' + record['path'])
        require(digest(path.read_bytes()) == record['sha256'], 'Support file identity mismatch: ' + record['path'])
        require(path.stat().st_size == record['bytes'], 'Support file size mismatch: ' + record['path'])
        require(format(path.stat().st_mode & 0o777, '04o') == record['mode'],
                'Support file mode mismatch: ' + record['path'])
    independence = []
    for filename in CHECKERS:
        tree = ast.parse((root / filename).read_text())
        require(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)),
                filename + ' contains optimization-sensitive assert')
        imports = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imports += [alias.name.split('.')[0] for alias in node.names]
            if isinstance(node, ast.ImportFrom):
                imports.append((node.module or '').split('.')[0])
        require(not set(imports) & {Path(name).stem for name in CHECKERS},
                filename + ' imports a peer checker')
        independence.append(dict(checker=filename, imports=sorted(imports), assertions=0,
                                 imports_peer_checker=False))
    records = []
    parser_results = []
    cli_results = []
    canonical = None
    with tempfile.TemporaryDirectory(prefix='route35-tests-') as temporary:
        scratch = Path(temporary)
        invalid_dir = scratch / 'invalid'
        invalid_dir.mkdir()
        bad_cases = mutations(raw)
        for name, data in bad_cases.items():
            (invalid_dir / (name + '.txt')).write_bytes(data)
        # Valid grammar with changed data must still fail exact-byte custody.
        byte_change = scratch / 'changed_valid_grammar.txt'
        byte_change.write_bytes(raw.replace(b'0a03', b'0b03', 1))
        for mode, flags in MODES:
            for filename in CHECKERS:
                script = root / filename
                templates_file = scratch / (mode + '-' + filename + '.templates.json')
                command = [sys.executable, '-B', '-I', *flags, str(script),
                           '--certificate', str(root / 'certificate.txt'),
                           '--templates-json', str(templates_file)]
                result = call(command, scratch)
                require(result['returncode'] == 0, filename + ' failed in ' + mode + ': ' + result['stderr'])
                summary = json.loads(result['stdout'])
                require(summary['status'] == 'PASS', filename + ' did not report PASS')
                require(summary['all_templates_sha256'] == TEMPLATES_SHA256,
                        filename + ' reported wrong set digest')
                templates = json.loads(templates_file.read_text())
                require(len(templates) == 616, filename + ' omitted template records')
                require([entry['row'] for entry in templates] == list(range(616)), 'Template IDs differ')
                encoded = json.dumps(templates, sort_keys=True, separators=(',', ':')).encode('ascii')
                require(digest(encoded) == TEMPLATES_SHA256, filename + ' exact set digest differs')
                if canonical is None:
                    canonical = templates
                require(templates == canonical, filename + ' required sets/envelopes/heights differ')
                records.append(dict(mode=mode, checker=filename, result=result, summary=summary,
                                    all_616_templates_equal=True))
                worker = call([sys.executable, '-B', '-I', *flags, '-c', PARSER_WORKER,
                               str(script), str(invalid_dir)], scratch)
                require(worker['returncode'] == 0,
                        filename + ' parser rejection failed in ' + mode + ': ' + worker['stderr'])
                parsed = json.loads(worker['stdout'])
                require(len(parsed) == len(bad_cases), 'Parser did not exercise every malformed case')
                parser_results.append(dict(mode=mode, checker=filename, cases=parsed))
                for path in [*sorted(invalid_dir.glob('*.txt')), byte_change]:
                    rejected = call([sys.executable, '-B', '-I', *flags, str(script),
                                     '--certificate', str(path)], scratch)
                    error_name = ('CertificateError' if 'CertificateError' in rejected['stderr'] else 'ValueError')
                    require(rejected['returncode'] != 0 and error_name in rejected['stderr'],
                            filename + ' did not explicitly reject ' + path.name + ' in ' + mode)
                    cli_results.append(dict(mode=mode, checker=filename, case=path.stem,
                                            returncode=rejected['returncode'],
                                            exception=error_name, stderr=rejected['stderr']))
    report = dict(status='PASS', python_version=sys.version,
                  manifest_sha256=digest((root / 'manifest.json').read_bytes()),
                  verified_support_files=manifest['files'], certificate_sha256=TABLE_SHA256,
                  certificate_bytes=len(raw), data_rows=610, templates=616, placements=1837,
                  local_reply_classes=26703, all_templates_sha256=TEMPLATES_SHA256,
                  all_required_sets_envelopes_heights_equal=True,
                  successful_reconstructions=len(records), optimization_modes=[name for name,_ in MODES],
                  malformed_variants=len(bad_cases), malformed_parser_rejections=sum(len(r['cases']) for r in parser_results),
                  cli_rejections=len(cli_results), independence=independence,
                  finite_checks_are_not_semantic_induction_or_kernel_evidence=True)
    if output_dir is not None:
        output_dir.mkdir(parents=True, exist_ok=True)
        (output_dir / 'report.json').write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
        (output_dir / 'runs.json').write_text(json.dumps(records, indent=2, sort_keys=True)+'\n')
        (output_dir / 'parser-rejections.json').write_text(json.dumps(parser_results, indent=2, sort_keys=True)+'\n')
        (output_dir / 'cli-rejections.json').write_text(json.dumps(cli_results, indent=2, sort_keys=True)+'\n')
        (output_dir / 'all-templates.json').write_text(json.dumps(canonical,sort_keys=True,separators=(',',':'))+'\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    print(json.dumps(run(args.output_dir), indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
