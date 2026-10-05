#!/usr/bin/env python3
"""Create and validate portable, source-bound comparator inputs.

These artifacts accelerate elaboration. They are not a kernel verification
receipt: the comparator must still check fresh challenge/solution exports.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def inputs(root):
    files = []
    for directory, subdirs, names in os.walk(root):
        subdirs[:] = sorted(n for n in subdirs if n not in ('.git', '.lake'))
        for name in names:
            p = Path(directory) / name
            rel = p.relative_to(root).as_posix()
            if p.suffix == '.lean' or rel in ('lake-manifest.json', 'lean-toolchain') or (rel.startswith('SubdiffusiveProcessAudit/') and name == 'comparator.json'):
                if p.is_symlink():
                    raise ValueError('Symlink in source inputs: ' + rel)
                files.append((rel, sha(p)))
    return dict(sorted(files))


def input_key(source):
    return hashlib.sha256(json.dumps(source, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def cached_inputs(source):
    # Audit declarations are deliberately absent from the cache bundle and are
    # compiled from the exact consumer sources. Bind cached modules separately.
    return {name: value for name, value in source.items() if not name.startswith('SubdiffusiveProcessAudit/')}


def command(*args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def create(args):
    root, packages, build, out = map(lambda p: Path(p).resolve(), (args.root, args.packages, args.project_build, args.output))
    # A checkout may keep its own .lake/build on another filesystem. Bind the
    # checkout containing that path, while reading artifacts at its real target.
    build_checkout = Path(args.project_build).absolute().parent.parent
    if cached_inputs(inputs(root)) != cached_inputs(inputs(build_checkout)):
        raise ValueError('Project build checkout sources differ from the exported candidate')
    source = inputs(root)
    key = input_key(source)
    out.mkdir(parents=True, exist_ok=False)
    members = {}
    pins = json.loads((root / 'lake-manifest.json').read_text())['packages']
    package_sources = {}
    for pin in pins:
        package = packages / pin['name']
        if command('git', 'rev-parse', 'HEAD', cwd=package) != pin['rev']:
            raise ValueError('Wrong dependency revision: ' + pin['name'])
        if command('git', 'status', '--porcelain', '--untracked-files=no', cwd=package):
            raise ValueError('Modified dependency sources: ' + pin['name'])
        tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=package).decode().split('\0')
        for name in filter(None, tracked):
            p = package / name
            if p.is_symlink():
                p = p.resolve()
                p.relative_to(package.resolve())
            if not p.is_file():
                raise ValueError('Unsupported dependency source: ' + str(p))
            rel = '.lake/packages/' + pin['name'] + '/' + name
            members[rel] = p
            package_sources[rel] = sha(p)
        cached = package / '.lake/build/lib'
        if cached.is_dir():
            for p in sorted(cached.rglob('*')):
                if p.is_file():
                    members['.lake/packages/' + pin['name'] + '/.lake/build/lib/' + p.relative_to(cached).as_posix()] = p
    lib = build / 'lib'
    for p in sorted(lib.rglob('*')):
        if p.is_file() and 'SubdiffusiveProcessAudit' not in p.relative_to(lib).parts:
            members['.lake/build/lib/' + p.relative_to(lib).as_posix()] = p
    for name in source:
        if name.startswith('SubdiffusiveProcess/') and name.endswith('.lean'):
            cached = '.lake/build/lib/lean/' + name.removesuffix('.lean') + '.olean'
            if cached not in members:
                raise ValueError('Missing production olean: ' + cached)
    records = {name: {'sha256': sha(p), 'size': p.stat().st_size} for name, p in sorted(members.items())}
    manifest = {'format': 1, 'key': key, 'sources': source, 'cached_sources': cached_inputs(source), 'package_sources': package_sources,
                'toolchain': (root / 'lean-toolchain').read_text().strip(),
                'lean_version': command('lean', '--version', cwd=root),
                'producer_commit': command('git', 'rev-parse', 'HEAD', cwd=root),
                'pins': {p['name']: p['rev'] for p in pins}, 'files': records}
    archive = out / 'prebuilt.tar.zst'
    with archive.open('wb') as target:
        compressor = subprocess.Popen(['zstd', '-T2', '-3', '-q'], stdin=subprocess.PIPE, stdout=target)
        with tarfile.open(fileobj=compressor.stdin, mode='w|') as tar:
            for name, p in sorted(members.items()):
                info = tar.gettarinfo(str(p), arcname=name)
                if not info.isfile():
                    raise ValueError('Nonregular artifact: ' + name)
                info.uid = info.gid = info.mtime = 0
                info.uname = info.gname = ''
                with p.open('rb') as stream:
                    tar.addfile(info, stream)
        compressor.stdin.close()
        if compressor.wait() != 0:
            raise ValueError('Compression failed')
    # GitHub limits each release asset to 2 GiB. Stream into smaller chunks.
    chunks = []
    with archive.open('rb') as stream:
        while block := stream.read(512 * 1024 * 1024):
            path = out / f'prebuilt.tar.zst.part{len(chunks):03d}'
            path.write_bytes(block)
            chunks.append({'name': path.name, 'sha256': sha(path), 'size': len(block)})
    archive.unlink()  # Own temporary compressed duplicate, never a build artifact.
    manifest['chunks'] = chunks
    (out / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'key': key, 'files': len(records), 'chunks': chunks, 'manifest_sha256': sha(out / 'manifest.json')}, indent=2))


def validate_header(root, manifest):
    if manifest.get('format') != 1 or manifest['key'] != input_key(manifest['sources']):
        raise ValueError('Invalid artifact key or format')
    if manifest['sources'] != inputs(root):
        raise ValueError('Artifact source/configuration hashes differ from this checkout')
    if manifest.get('cached_sources', cached_inputs(manifest['sources'])) != cached_inputs(manifest['sources']):
        raise ValueError('Cached production source binding differs from the candidate')
    if manifest['toolchain'] != (root / 'lean-toolchain').read_text().strip():
        raise ValueError('Artifact toolchain pin differs')
    if manifest['lean_version'] != command('lean', '--version', cwd=root):
        raise ValueError('Installed Lean does not match the artifact producer')
    pins = {p['name']: p['rev'] for p in json.loads((root / 'lake-manifest.json').read_text())['packages']}
    if manifest['pins'] != pins:
        raise ValueError('Artifact dependency pins differ')
    if os.environ.get('GITHUB_ACTIONS') == 'true' and manifest['producer_commit'] != os.environ.get('GITHUB_SHA'):
        raise ValueError('Artifact producer commit differs from the exact Actions candidate')


def restore(args):
    root = Path(args.root).resolve()
    path = Path(args.manifest).resolve()
    if sha(path) != args.manifest_sha256:
        raise ValueError('Manifest SHA256 differs from the pinned workflow input')
    manifest = json.loads(path.read_text())
    validate_header(root, manifest)
    chunk_paths = []
    for chunk in manifest['chunks']:
        p = path.parent / chunk['name']
        if p.name != chunk['name'] or p.stat().st_size != chunk['size'] or sha(p) != chunk['sha256']:
            raise ValueError('Archive chunk mismatch: ' + chunk['name'])
        chunk_paths.append(p)
    # Feed split chunks through stdin as one compressed frame.
    decompressor = subprocess.Popen(['zstd', '-dq', '-c'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    import threading
    def feed():
        try:
            for p in chunk_paths:
                with p.open('rb') as stream:
                    for block in iter(lambda: stream.read(1024 * 1024), b''):
                        decompressor.stdin.write(block)
        finally:
            decompressor.stdin.close()
    feeder = threading.Thread(target=feed)
    feeder.start()
    seen = set()
    try:
        with tarfile.open(fileobj=decompressor.stdout, mode='r|') as tar:
            for item in tar:
                name = item.name
                if name in seen or name not in manifest['files'] or not item.isfile() or '..' in Path(name).parts or not name.startswith('.lake/'):
                    raise ValueError('Unexpected archive member: ' + name)
                target = root / name
                if target.exists() or target.is_symlink():
                    raise ValueError('Restore requires empty artifact paths: ' + name)
                for parent in target.parents:
                    if parent == root:
                        break
                    if parent.is_symlink():
                        raise ValueError('Symlink in extraction path: ' + name)
                target.parent.mkdir(parents=True, exist_ok=True)
                data = tar.extractfile(item)
                h = hashlib.sha256()
                with target.open('xb') as dest:
                    for block in iter(lambda: data.read(1024 * 1024), b''):
                        h.update(block)
                        dest.write(block)
                record = manifest['files'][name]
                if h.hexdigest() != record['sha256'] or target.stat().st_size != record['size']:
                    raise ValueError('Restored artifact hash mismatch: ' + name)
                target.chmod(item.mode & 0o777)
                seen.add(name)
        feeder.join()
        if decompressor.wait() != 0 or seen != set(manifest['files']):
            raise ValueError('Incomplete artifact archive')
    finally:
        if decompressor.poll() is None:
            decompressor.kill()
    (root / '.lake/prebuilt-manifest.json').write_text(json.dumps(manifest, sort_keys=True))
    print(f'Validated and restored {len(seen)} files; source/toolchain key {manifest["key"]}')


def verify(args):
    root = Path(args.root).resolve()
    manifest = json.loads((root / '.lake/prebuilt-manifest.json').read_text())
    validate_header(root, manifest)
    for name, record in manifest['files'].items():
        p = root / name
        if p.is_symlink() or not p.is_file() or p.stat().st_size != record['size'] or sha(p) != record['sha256']:
            raise ValueError('Artifact changed since restore: ' + name)
    print('Prebuilt source, toolchain, dependency and artifact hashes verified: ' + manifest['key'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    create_p = sub.add_parser('create')
    for name in ('root', 'packages', 'project-build', 'output'):
        create_p.add_argument('--' + name, required=True)
    restore_p = sub.add_parser('restore')
    restore_p.add_argument('--root', default='.')
    restore_p.add_argument('--manifest', required=True)
    restore_p.add_argument('--manifest-sha256', required=True)
    verify_p = sub.add_parser('verify')
    verify_p.add_argument('--root', default='.')
    args = parser.parse_args()
    {'create': create, 'restore': restore, 'verify': verify}[args.action](args)


if __name__ == '__main__':
    main()
