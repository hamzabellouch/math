#!/usr/bin/env python3
"""Run both independent route-21 implementations, including negative tests."""
import argparse
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def worker(module_path, fixture, board_shift=None):
    spec = importlib.util.spec_from_file_location('checked_module', module_path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    if board_shift is not None:
        result = module.verify(Path(fixture).read_bytes())
        envelope = {tuple(point) for point in result['cards'][-1]['T']}
        dx, dy = board_shift
        translated = {(x + dx, y + dy) for x, y in envelope}
        require(len(translated) == len(envelope) == 251, 'translation changed cardinality')
        try:
            module.check_finite_board(translated)
        except ValueError as error:
            require(str(error) == 'final envelope is outside the 17-by-17 board',
                    'unexpected finite-board rejection')
            print('ValueError: ' + str(error))
            return
        raise ValueError('translated final envelope was accepted')
    try:
        module.verify(Path(fixture).read_bytes())
    except (ValueError, IndexError, StopIteration) as error:
        print(type(error).__name__ + ': ' + str(error))
        return
    raise ValueError('mutated input was accepted by raw reconstruction')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=HERE/'evidence')
    parser.add_argument('--worker', nargs=2, metavar=('MODULE','FIXTURE'))
    parser.add_argument('--board-shift', nargs=2, type=int, metavar=('DX','DY'))
    args = parser.parse_args()
    if args.board_shift is not None and not args.worker:
        parser.error('--board-shift requires --worker')
    if args.worker:
        worker(*args.worker, board_shift=args.board_shift)
        return
    out = args.output_dir.resolve()
    out.mkdir(parents=True,exist_ok=True)
    raw = (HERE/'certificate.txt').read_bytes()
    lines = raw.splitlines(keepends=True)
    mutations = {
        'truncated_file': b''.join(lines[:-1]),
        'missing_final_newline': raw[:-1],
        'empty_file': b'',
        'blank_row': b'\n' + b''.join(lines[1:]),
        'bad_index': raw.replace(b'6 14 ',b'8 14 ',1),
        'leading_zero_index': raw.replace(b'6 14 ',b'06 14 ',1),
        'leading_zero_reference': raw.replace(b'4:100',b'04:100',1),
        'forward_reference': raw.replace(b'4:100',b'6:100',1),
        'negative_reference': raw.replace(b'4:100',b'-4:100',1),
        'symmetry_eight': raw.replace(b'4:100',b'4:800',1),
        'bad_coordinate': raw.replace(b'6 14 ',b'6 1H ',1),
        'extra_colon': raw.replace(b'4:100',b'4::100',1),
        'empty_children': b'6 14\n' + b''.join(lines[1:]),
        'empty_inline': raw.replace(b'4:100',b'(00)',1),
        'unclosed_inline': raw.replace(b'4:100',b'(00 4:100',1),
        'extra_close': raw.replace(b'4:100',b'4:100)',1),
        'trailing_junk': raw.replace(b'4:100',b'4:100 ?!',1),
        'non_ascii': raw.replace(b'4:100',b'4:\xff00',1),
    }
    commands, negative, board_negative = [], [], []
    baseline = None
    for script in ('primary.py','independent.py'):
        tree = ast.parse((HERE/script).read_text())
        require(not any(isinstance(node,ast.Assert) for node in ast.walk(tree)), 'assertions in checker ' + script)
        for mode in ([],['-O'],['-OO']):
            tag = script.removesuffix('.py') + ('-'+mode[0][1:] if mode else '-normal')
            target = out/(tag+'.json')
            command = [sys.executable,*mode,str(HERE/script),'--output',str(target)]
            run = subprocess.run(command,capture_output=True,text=True)
            require(run.returncode == 0, 'checker failed: '+run.stderr)
            result = json.loads(target.read_text())
            arrays = {'cards':result['cards'],'postorder':result['postorder']}
            if baseline is None:
                baseline = arrays
            require(arrays == baseline, 'complete reconstructed data disagreement')
            commands.append({'argv':command,'returncode':run.returncode,'stdout':run.stdout,'stderr':run.stderr,
                             'cards_sha256':digest(arrays['cards']), 'postorder_sha256':digest(arrays['postorder'])})
            for shift in ((-1,0),(1,0),(0,-1),(0,1)):
                board_cmd = [sys.executable,*mode,str(Path(__file__).resolve()),
                             '--worker',str(HERE/script),str(HERE/'certificate.txt'),
                             '--board-shift',*(str(value) for value in shift)]
                probe = subprocess.run(board_cmd,capture_output=True,text=True)
                require(probe.returncode == 0,
                        f'{script} {mode}: finite-board test failed for {shift}: {probe.stderr}')
                board_negative.append({'checker':script,'mode':mode or ['normal'],
                                       'translation':list(shift),'T_size':251,
                                       'rejected':True,'error':probe.stdout.strip()})
            with tempfile.TemporaryDirectory(dir=out) as temporary:
                for name, changed in mutations.items():
                    path = Path(temporary)/(name+'.txt')
                    path.write_bytes(changed)
                    # Direct raw reconstruction bypasses the literal checksum.
                    raw_cmd = [sys.executable,*mode,str(Path(__file__).resolve()),'--worker',str(HERE/script),str(path)]
                    probe = subprocess.run(raw_cmd,capture_output=True,text=True)
                    require(probe.returncode == 0, f'{script} {mode}: raw parser failed to reject {name}: {probe.stderr}')
                    # Public entrypoint must also reject it visibly.
                    cli_cmd = [sys.executable,*mode,str(HERE/script),'--table',str(path)]
                    cli = subprocess.run(cli_cmd,capture_output=True,text=True)
                    require(cli.returncode != 0 and 'SHA256 mismatch' in cli.stderr, 'CLI accepted corrupt bytes')
                    negative.append({'checker':script,'mode':mode or ['normal'],'mutation':name,
                                     'raw_reconstruction_rejected':True,'raw_error':probe.stdout.strip(),
                                     'cli_exit':cli.returncode,'cli_rejection':'literal SHA256 mismatch'})
    report = {'status':'PASS','scope':'Current standalone route21 support paths; mathematical soundness and final article review remain separate.',
              'python':sys.version,'certificate_sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),
              'counts':result['counts'],'endpoint':result['endpoint'],
              'full_numbered_cards_compared':728,'full_postorder_nodes_compared':1620,
              'normal_and_optimized_runs':commands,'negative_tests':negative,
              'finite_board_translation_tests':board_negative,
              'negative_finite_board_tests':len(board_negative),
              'negative_raw_reconstruction_tests':len(negative),'negative_cli_tests':len(negative),
              'assert_nodes_in_checkers':0}
    (out/'report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('normal_and_optimized_runs','negative_tests','finite_board_translation_tests','python')},sort_keys=True))

if __name__ == '__main__':
    main()
