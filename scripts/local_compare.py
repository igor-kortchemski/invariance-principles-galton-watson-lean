#!/usr/bin/env python3
"""Run local comparison and kernel replay diagnostics, without a Linux sandbox.

Usage: python3 -I scripts/local_compare.py OUTPUT [--reuse-solution PREVIOUS_OUTPUT]
Reuse requires identical recorded proof sources, configuration and toolchain;
only Challenge.lean may have changed. Comparison and kernel replay run afresh.
This does not dispatch CI, publish, submit, or produce an official Palomar report.
"""
import hashlib
import argparse
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
PRIMITIVES = "Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String Char String.mk optParam autoParam semiOutParam outParam Quot Quot.mk Quot.lift Quot.ind".split()


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output')
    parser.add_argument('--reuse-solution', type=Path)
    args = parser.parse_args()
    out = Path(args.output).resolve()
    if ROOT == out or ROOT in out.parents:
        raise SystemExit('Put diagnostic output outside the checkout.')
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        raise SystemExit('Refusing a nonempty output directory.')
    os.chdir(ROOT)
    config_path = ROOT / 'comparator.json'
    config = json.loads(config_path.read_text())
    source_paths = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z']).decode().split('\0')
    checked_paths = sorted({p for p in source_paths if p and (p.endswith('.lean') or
        p in ['comparator.json', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'])})
    evidence = {'official_palomar_report': False, 'status': 'running',
                'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                'git_status': subprocess.check_output(['git', 'status', '--porcelain'], text=True),
                'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
                'source_sha256': {p: digest(ROOT / p) for p in checked_paths}}

    def run(label, args, output=None):
        print(label, flush=True)
        with (out / 'commands.log').open('a') as log:
            log.write(shlex.join([str(x) for x in args]) + '\n')
        stdout_path = output or out / (label + '.log')
        with stdout_path.open('w') as stdout, (out / (label + '.stderr')).open('w') as stderr:
            result = subprocess.run([str(x) for x in args], stdout=stdout, stderr=stderr)
        if result.returncode:
            raise RuntimeError(f'{label} exited {result.returncode}; see {out}')

    try:
        prefix = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_SYSROOT'], text=True).strip()
        bin_path = Path(prefix) / 'bin'
        targets = PRIMITIVES + config['theorem_names'] + config['definition_names'] + config['permitted_axioms']
        run('build', ['lake', 'build', 'Challenge', 'Solution'])
        for side in ['challenge', 'solution']:
            if side == 'solution' and args.reuse_solution:
                previous = args.reuse_solution.resolve()
                recorded = json.loads((previous / 'result.json').read_text())['source_sha256']
                if set(recorded) != set(evidence['source_sha256']) or any(
                    digest(ROOT / p) != d for p, d in recorded.items() if p != 'Challenge.lean'):
                    raise RuntimeError('Cannot reuse the export: proof sources or configuration changed.')
                original_digest = digest(previous / 'solution.ndjson')
                shutil.copyfile(previous / 'solution.ndjson', out / 'solution.ndjson')
                if digest(out / 'solution.ndjson') != original_digest:
                    raise RuntimeError('Copied solution export differs.')
                evidence['reused_solution_export_sha256'] = original_digest
                print('reused unchanged solution export; comparison and replay will run afresh', flush=True)
                continue
            run(side + '-export', ['lake', 'env', bin_path / 'leanexport', config[side + '_module'], '--', *targets], out / (side + '.ndjson'))
        run('compile', ['lake', 'env', 'lean', '-c', out / 'diag.c', 'scripts/LocalComparatorDiagnostic.lean'])
        run('link', [bin_path / 'leanc', out / 'diag.c', '-o', out / 'diagnostic',
                     f'-L{bin_path.parent / "lib/lean"}', '-lLeanExport', '-lLake', '-lLean', '-lStd', '-lInit', '-lleancpp', '-lleanrt'])
        run('compare', [out / 'diagnostic', config_path, out / 'challenge.ndjson', out / 'solution.ndjson'])
        run('leanchecker', [bin_path / 'leanchecker', '--silent', '--from-export', out / 'solution.ndjson'])
        nanoda_config = out / 'nanoda-config.json'
        nanoda_config.write_text(json.dumps({'use_stdin': False, 'export_file_path': str(out / 'solution.ndjson'),
            'permitted_axioms': config['permitted_axioms'], 'unpermitted_axiom_hard_error': True,
            'num_threads': 2, 'nat_extension': True, 'string_extension': True}) + '\n')
        run('nanoda', [bin_path / 'nanoda_bin', nanoda_config])
        if any(digest(ROOT / p) != d for p, d in evidence['source_sha256'].items()):
            raise RuntimeError('Sources changed during verification.')
        evidence.update(status='passed', challenge_sha256=digest(out / 'challenge.ndjson'),
                        solution_sha256=digest(out / 'solution.ndjson'))
    except Exception as exc:
        evidence.update(status='failed', error=str(exc))
        raise
    finally:
        (out / 'result.json').write_text(json.dumps(evidence, indent=2) + '\n')


if __name__ == '__main__':
    main()
