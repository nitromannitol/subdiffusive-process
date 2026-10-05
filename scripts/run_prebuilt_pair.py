#!/usr/bin/env python3
"""Compile a fresh audit pair, export it, and replay every required kernel."""
import argparse
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

import prebuilt_artifacts

PAIRS = {'ProcessConvergence', 'QuantitativeHomogenization', 'AnomalousHolderRegularity'}
# Exact primitive/builtin targets used by this pinned Lake comparator.
PRIMITIVES = ['Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div',
              'Nat.mod', 'Nat.beq', 'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor',
              'Nat.shiftLeft', 'Nat.shiftRight', 'String.ofList', 'Char.ofNat',
              'List', 'eagerReduce', 'Nat', 'String', 'String.mk', 'Char',
              'optParam', 'autoParam', 'semiOutParam', 'outParam']
BUILTINS = ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind']
AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']
# Match the release Lake targets when elaborating fresh audit modules directly.
LEAN_OPTIONS = ['-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                '-Dlinter.unusedVariables=true', '-Dlinter.unusedSectionVars=true',
                '-Dlinter.unusedSimpArgs=true', '-Dlinter.unnecessarySimpa=true',
                '-Dlinter.deprecated=true', '-Dwarn.classDefReducibility=false']


def run(args, root, log, output=None):
    print('+ ' + ' '.join(map(str, args)), flush=True)
    with log.open('wb') as diagnostic:
        if output:
            with output.open('wb') as exported:
                result = subprocess.Popen(args, cwd=root, stdout=exported, stderr=subprocess.PIPE)
                for chunk in iter(lambda: result.stderr.read1(65536), b''):
                    diagnostic.write(chunk)
                    diagnostic.flush()
                    sys.stdout.buffer.write(chunk)
                    sys.stdout.buffer.flush()
                result.wait()
        else:
            result = subprocess.Popen(args, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            for chunk in iter(lambda: result.stdout.read1(65536), b''):
                diagnostic.write(chunk)
                diagnostic.flush()
                sys.stdout.buffer.write(chunk)
                sys.stdout.buffer.flush()
            result.wait()
    # Export NDJSON stays in its file; diagnostic/kernel output streams live.
    if result.returncode:
        raise RuntimeError(f'Command exited {result.returncode}: {args[0]}; log {log}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pair', choices=sorted(PAIRS), required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    start = time.monotonic()
    prebuilt_artifacts.verify(argparse.Namespace(root=str(root)))
    if int(Path('/proc/sys/vm/max_map_count').read_text()) < 131072:
        raise RuntimeError('Raise vm.max_map_count to 262144 before exporting')
    if not shutil.which('bwrap'):
        raise RuntimeError('bubblewrap is required')
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip())
    for tool in ['lean', 'lake', 'leanexport', 'leanchecker', 'nanoda_bin', 'con-ron']:
        if not os.access(prefix / 'bin' / tool, os.X_OK):
            raise RuntimeError('Missing trusted toolchain executable: ' + tool)
    configs = {}
    for pair in sorted(PAIRS):
        path = root / 'SubdiffusiveProcessAudit' / pair / 'comparator.json'
        config = json.loads(path.read_text())
        allowed = {'challenge_module', 'solution_module', 'theorem_names', 'definition_names', 'permitted_axioms', 'enable_nanoda'}
        if set(config) - allowed or len(config['permitted_axioms']) != 3 or set(config['permitted_axioms']) != set(AXIOMS):
            raise RuntimeError('Invalid comparator configuration: ' + pair)
        if not config['theorem_names'] or any(not isinstance(n, str) or not n.strip() for n in config['theorem_names']):
            raise RuntimeError('Missing theorem targets: ' + pair)
        for kind in ['challenge', 'solution']:
            module = f'SubdiffusiveProcessAudit.{pair}.{kind.title()}'
            if config[kind + '_module'] != module or not (root / module.replace('.', '/')).with_suffix('.lean').is_file():
                raise RuntimeError('Wrong audit module: ' + pair)
        configs[pair] = config
    config = configs[args.pair]
    logdir = root / '.lake/comparator-logs/palomar' / args.pair
    logdir.mkdir(parents=True, exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix=args.pair + '.', dir=root / '.lake'))
    print('Fresh audit outputs (retained): ' + str(scratch), flush=True)
    auditlib = scratch / 'lib/lean'
    auditlib.mkdir(parents=True)
    # Construct the search path from the validated manifest. Even `lake env`
    # would try to materialize Git metadata absent from this portable bundle.
    # No package resolution or transitive build is needed for direct elaboration.
    pins = json.loads((root / 'lake-manifest.json').read_text())['packages']
    search = [auditlib, root / '.lake/build/lib/lean']
    search += [root / '.lake/packages' / pin['name'] / '.lake/build/lib/lean' for pin in pins]
    search += [prefix / 'lib/lean']
    lean_path = ':'.join(map(str, search))
    sandbox = ['bwrap', '--ro-bind', '/', '/', '--tmpfs', '/home', '--tmpfs', '/root',
               '--tmpfs', '/run/user', '--tmpfs', '/tmp', '--dir', '/tmp/home',
               '--dev', '/dev', '--proc', '/proc', '--clearenv',
               '--ro-bind', str(root), str(root), '--ro-bind', str(prefix), str(prefix),
               '--bind', str(root / '.lake'), str(root / '.lake'), '--chdir', str(root),
               '--setenv', 'HOME', '/tmp/home',
               '--setenv', 'LEAN_PATH', lean_path,
               '--setenv', 'PATH', str(prefix / 'bin') + ':' + os.environ['PATH'],
               '--unshare-all', '--die-with-parent', '--new-session', '--']
    exports = {}
    timings = {}
    compiled = set()
    active = set()
    def compile_module(module):
        if module in compiled:
            return
        if module in active or not module.startswith('SubdiffusiveProcessAudit.' + args.pair + '.'):
            raise RuntimeError('Invalid or cyclic audit helper import: ' + module)
        active.add(module)
        rel = Path(module.replace('.', '/'))
        source = (root / rel).with_suffix('.lean')
        for imported in re.findall(r'(?m)^\s*(?:public |private )?(?:meta )?import\s+(?:all\s+)?([^\s]+)', source.read_text()):
            if imported.startswith('SubdiffusiveProcessAudit.'):
                compile_module(imported)
        olean = (auditlib / rel).with_suffix('.olean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        run(sandbox + [str(prefix / 'bin/lean'), *LEAN_OPTIONS, '-o', str(olean), str(rel.with_suffix('.lean'))],
            root, logdir / (module.rsplit('.', 1)[-1] + '-build.log'))
        active.remove(module)
        compiled.add(module)
    targets = BUILTINS + config['theorem_names'] + AXIOMS + PRIMITIVES + config.get('definition_names', [])
    for kind in ['challenge', 'solution']:
        t0 = time.monotonic()
        module = config[kind + '_module']
        # Fresh direct elaboration prevents Lake's transitive build graph from
        # rebuilding a source-bound production cache on a different host path.
        compile_module(module)
        output = scratch / f'{kind}.ndjson'
        run(sandbox + [str(prefix / 'bin/leanexport'), module, '--', *targets],
            root, logdir / f'{kind}-export.log', output=output)
        exports[kind] = output
        timings[kind + '_build_export_seconds'] = round(time.monotonic() - t0, 3)
    # A protected config fixes both external checkers to genuine bundled tools.
    config.pop('enable_nanoda', None)
    config['external_kernels'] = {name: [str(prefix / 'bin' / executable)]
                                  for name, executable in [('nanoda', 'nanoda_bin'), ('con-ron', 'con-ron')]}
    # The progress heartbeat (stderr) records con-ron's parse, install and check phases.
    config['external_kernels']['con-ron'].append('--progress=50000')
    protected = scratch / 'comparator.json'
    protected.write_text(json.dumps(config, indent=2) + '\n')
    t0 = time.monotonic()
    # Official --from-export mode still compares the dependency closure, checks
    # allowed axioms and runs Lean/NanoDa/con-ron in its built-in sandbox. Its
    # exports were just generated from freshly compiled, hash-bound sources.
    verdict = logdir / 'comparator.log'
    run([str(prefix / 'bin/lake'), 'comparator', '--config', str(protected),
         '--challenge-from-export', str(exports['challenge']),
         '--solution-from-export', str(exports['solution'])], root, verdict)
    if 'Your solution is okay!' not in verdict.read_text().splitlines():
        raise RuntimeError('Comparator omitted its acceptance verdict')
    timings['kernel_comparison_seconds'] = round(time.monotonic() - t0, 3)
    prebuilt_artifacts.verify(argparse.Namespace(root=str(root)))
    manifest = json.loads((root / '.lake/prebuilt-manifest.json').read_text())
    result = {'pair': args.pair, 'result': 'success', 'source_key': manifest['key'],
              'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
              'kernels': ['Lean', 'NanoDa', 'con-ron'], 'timings': timings,
              'total_seconds': round(time.monotonic() - start, 3)}
    (logdir / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
