#!/usr/bin/env bash
# Run every public theorem comparator. A missing pair or failed check is fatal.
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
mode=pinned
case "${1:-}" in
  '') ;;
  --palomar) mode=palomar ;;
  --help) cat <<'USAGE'
Usage: scripts/run_comparators.sh [--palomar]

The default runs leanprover/comparator with the separately pinned Armstrong
verification tools. Set COMPARATOR_BIN, COMPARATOR_LANDRUN,
COMPARATOR_LEAN4EXPORT and COMPARATOR_NANODA to their executable paths.
--palomar uses this project's bundled lake comparator, NanoDa and con-ron;
it requires bubblewrap. Both modes build the library and every audit pair.
Logs are written under .lake/comparator-logs/<mode>/.
USAGE
    exit 0 ;;
  *) echo "Unknown option: $1" >&2; exit 2 ;;
esac
[ "$#" -le 1 ] || { echo 'Too many arguments' >&2; exit 2; }
for command_name in lake lean python3; do
  command -v "$command_name" >/dev/null || { echo "Missing command: $command_name" >&2; exit 1; }
done
log_dir="$repository_root/.lake/comparator-logs/$mode"
mkdir -p "$log_dir"
config_dir=$(mktemp -d "${TMPDIR:-/tmp}/subdiffusive-comparators.XXXXXXXX")
trap 'rm -rf "$config_dir"' EXIT

# Prepare protected copies, without changing submission configurations. All
# required headline pairs and every additional comparator are checked first.
python3 - "$repository_root" "$config_dir" "$mode" <<'PY'
import json
import pathlib
import re
import sys

root, destination, mode = map(str, sys.argv[1:])
root, destination = pathlib.Path(root), pathlib.Path(destination)
audit = root / 'SubdiffusiveProcessAudit'
required = {'ProcessConvergence', 'QuantitativeHomogenization', 'AnomalousHolderRegularity'}
paths = sorted(audit.rglob('comparator.json'))
missing = required - {p.parent.name for p in paths}
if missing:
    raise SystemExit('Missing required comparator pairs: ' + ', '.join(sorted(missing)))
allowed_keys = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms',
                'definition_names', 'enable_nanoda'}
standard_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
def unique_keys(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError('Duplicate configuration key: ' + key)
        result[key] = value
    return result
manifest = []
for index, path in enumerate(paths):
    config = json.loads(path.read_text(), object_pairs_hook=unique_keys)
    if not isinstance(config, dict) or set(config) - allowed_keys:
        raise SystemExit(f'{path}: unsupported configuration fields')
    axioms = config.get('permitted_axioms')
    if not isinstance(axioms, list) or len(axioms) != 3 or set(axioms) != standard_axioms:
        raise SystemExit(f'{path}: permitted_axioms must be exactly the three standard axioms')
    names = config.get('theorem_names')
    if not isinstance(names, list) or not names or any(not isinstance(n, str) or not n.strip() or any(ord(c)<32 for c in n) for n in names):
        raise SystemExit(f'{path}: theorem_names must be a nonempty list of declaration names')
    for key in ['challenge_module', 'solution_module']:
        module = config.get(key)
        if not isinstance(module, str) or not re.fullmatch(r'SubdiffusiveProcessAudit(?:\.[A-Za-z_][A-Za-z_0-9]*)+', module):
            raise SystemExit(f'{path}: invalid {key}')
        file = root.joinpath(*module.split('.')).with_suffix('.lean')
        if not file.is_file():
            raise SystemExit(f'{path}: missing {key} source {file}')
    # The pinned comparator's default config must never disable its NanoDa replay.
    if mode == 'pinned':
        config['enable_nanoda'] = True
    else:
        config.pop('enable_nanoda', None)
    output = destination / f'{index:03d}.json'
    output.write_text(json.dumps(config, indent=2) + '\n')
    manifest.append(f'{index:03d}\t{path.relative_to(root)}\t{output}')
(destination / 'pairs.tsv').write_text('\n'.join(manifest) + '\n')
print(f'Validated {len(paths)} comparator pairs, including all three main theorems.')
PY

if [ "$mode" = palomar ]; then
  command -v bwrap >/dev/null || { echo 'Missing command: bwrap (bubblewrap)' >&2; exit 1; }
  prefix=$(lean --print-prefix)
  for tool_name in lake leanexport leanchecker nanoda_bin con-ron; do
    [ -x "$prefix/bin/$tool_name" ] || { echo "Toolchain does not bundle $tool_name" >&2; exit 1; }
  done
  # As in PalomarTemplate, the submitter cannot choose external kernels.
  python3 - "$config_dir" "$prefix" <<'PY'
import json
import pathlib
import sys
folder, prefix = sys.argv[1:]
for path in pathlib.Path(folder).glob('*.json'):
    config = json.loads(path.read_text())
    config['external_kernels'] = {
        'nanoda': [f'{prefix}/bin/nanoda_bin'],
        'con-ron': [f'{prefix}/bin/con-ron'],
    }
    path.write_text(json.dumps(config, indent=2) + '\n')
PY
else
  : "${COMPARATOR_BIN:=$HOME/tools/comparator/.lake/build/bin/comparator}"
  : "${COMPARATOR_LANDRUN:=$HOME/tools/bin/landrun}"
  : "${COMPARATOR_LEAN4EXPORT:=$HOME/tools/lean4export/.lake/build/bin/lean4export}"
  : "${COMPARATOR_NANODA:=$HOME/tools/nanoda_lib/target/release/nanoda_bin}"
  export COMPARATOR_LANDRUN COMPARATOR_LEAN4EXPORT COMPARATOR_NANODA
  for tool_path in "$COMPARATOR_BIN" "$COMPARATOR_LANDRUN" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_NANODA"; do
    [ -x "$tool_path" ] || { echo "Missing executable: $tool_path" >&2; exit 1; }
  done
  # A denied write alone is insufficient: also prove the sandbox can execute.
  probe_dir=$(mktemp -d "${TMPDIR:-/tmp}/subdiffusive-landrun.XXXXXXXX")
  probe="$probe_dir/escape"
  if ! "$COMPARATOR_LANDRUN" --best-effort --ro / --rw /dev -ldd -add-exec -- /bin/true; then
    rm -rf "$probe_dir"
    echo 'landrun could not execute the permitted sandbox probe' >&2
    exit 1
  fi
  "$COMPARATOR_LANDRUN" --best-effort --ro / --rw /dev -ldd -add-exec \
    -- /bin/sh -c 'printf escaped > "$1"' sh "$probe" || true
  if [ -e "$probe" ]; then
    rm -rf "$probe_dir"
    echo 'landrun allowed an out-of-sandbox write' >&2
    exit 1
  fi
  rm -rf "$probe_dir"
fi

lake build 2>&1 | tee "$log_dir/library-build.log"
# A fresh persistent checkout gives audit modules empty build paths while
# reusing the already-built production and dependency artifacts. It is retained:
# neither existing nor newly generated oleans are removed by this runner.
run_parent="$repository_root/.lake/comparator-runs"
mkdir -p "$run_parent"
run_root=$(mktemp -d "$run_parent/$mode.XXXXXXXX")
python3 - "$repository_root" "$run_root" <<'PYTHON'
import pathlib
import shutil
import sys
import errno
import fcntl

def copy_cached_file(source, destination):
    # Independent paths are needed inside bubblewrap, which masks the parent
    # checkout. Reflinks preserve space without sharing writable cache files.
    with open(source, 'rb') as original, open(destination, 'wb') as copied:
        try:
            fcntl.ioctl(copied.fileno(), 0x40049409, original.fileno())
        except OSError as error:
            if error.errno not in (errno.EXDEV, errno.EOPNOTSUPP, errno.ENOTTY, errno.EINVAL):
                raise
            shutil.copyfileobj(original, copied, length=1024*1024)
    shutil.copystat(source, destination)
    return destination

source, destination = map(pathlib.Path, sys.argv[1:])
# Freeze the public source tree; never recursively copy its existing build tree.
shutil.copytree(source, destination, dirs_exist_ok=True,
                ignore=shutil.ignore_patterns('.lake', '.git'))
local_lake = destination / '.lake'
local_lake.mkdir()
packages = source / '.lake/packages'
if packages.is_dir():
    shutil.copytree(packages, local_lake / 'packages', copy_function=copy_cached_file)
build = source / '.lake/build'
if build.is_dir():
    # Copy production caches only; the audit modules start with empty paths.
    for path in build.rglob('*'):
        relative = path.relative_to(build)
        if any(part == 'SubdiffusiveProcessAudit' or part.startswith('SubdiffusiveProcessAudit.')
               for part in relative.parts):
            continue
        output = local_lake / 'build' / relative
        if path.is_dir():
            output.mkdir(parents=True, exist_ok=True)
        elif path.is_file():
            output.parent.mkdir(parents=True, exist_ok=True)
            copy_cached_file(path, output)
print('Fresh audit checkout (retained): ' + str(destination))
PYTHON
printf '%s\n' "$run_root" | tee "$log_dir/audit-checkout.txt"
cd "$run_root"
# Avoid inheriting an unrelated checkout's Lean search path. Lake supplies the
# isolated project's own paths and pinned package paths for every command.
unset LEAN_PATH
lake build SubdiffusiveProcessAudit 2>&1 | tee "$log_dir/audit-build.log"

failed=0
checked=0
while IFS=$'\t' read -r index source_config protected_config; do
  printf '\nChecking %s (%s)\n' "$source_config" "$mode"
  log="$log_dir/$index.log"
  if [ "$mode" = palomar ]; then
    if lake comparator --config "$protected_config" 2>&1 | tee "$log"; then
      result=0
    else
      result=1
    fi
  else
    if lake env "$COMPARATOR_BIN" "$protected_config" 2>&1 | tee "$log"; then
      result=0
    else
      result=1
    fi
  fi
  if [ "$result" -eq 0 ] && grep -Fxq 'Your solution is okay!' "$log"; then
    printf '%s: OK\n' "$source_config"
  else
    printf '%s: FAILED\n' "$source_config" >&2
    failed=1
  fi
  checked=$((checked + 1))
done < "$config_dir/pairs.tsv"
[ "$checked" -ge 3 ] || { echo 'Fewer than three comparator pairs ran' >&2; exit 1; }
[ "$failed" -eq 0 ] || exit 1
printf '\nAll %s comparator pairs passed (%s). Logs: %s\n' "$checked" "$mode" "$log_dir"
