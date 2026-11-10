#!/usr/bin/env python3
"""Reproducible source-only challenge and proof handoff; does not publish."""
import gzip
import hashlib
import io
from pathlib import Path
import tarfile

root = Path(__file__).resolve().parents[1]
out = root / 'dist'
out.mkdir(exist_ok=True)
roots = ['Baseline', 'Challenge', 'Solution', 'Tests', 'configs', 'docs', 'scripts', 'vectors', 'vendor']
files = [p for name in roots for p in (root / name).rglob('*')
         if p.is_file() and '__pycache__' not in p.parts]
files += [root / name for name in [
    '.gitignore', 'Baseline.lean', 'Challenge.lean', 'Solution.lean', 'CHALLENGE.md', 'README.md',
    'THIRD_PARTY_NOTICES.md', 'challenge.json', 'lake-manifest.json',
    'lakefile.lean', 'lean-toolchain', 'reference/Cargo.toml',
    'reference/Cargo.lock', 'reference/src/main.rs', 'reference/cpp/probe.h',
]]
payload = {p.relative_to(root).as_posix(): p.read_bytes() for p in files}
payload['SHA256SUMS'] = ''.join(
    f'{hashlib.sha256(data).hexdigest()}  {name}\n'
    for name, data in sorted(payload.items())
).encode()
archive = out / 'ecdsa-p256-digest-source.tar.gz'
with archive.open('wb') as f, gzip.GzipFile(filename='', mode='wb', fileobj=f, mtime=0) as gz:
    with tarfile.open(fileobj=gz, mode='w') as tar:
        for name, data in sorted(payload.items()):
            info = tarfile.TarInfo('ecdsa-p256-digest/' + name)
            info.size = len(data)
            info.mode = 0o755 if name.endswith('.sh') else 0o644
            info.mtime = 0
            tar.addfile(info, io.BytesIO(data))
digest = hashlib.sha256(archive.read_bytes()).hexdigest()
(out / 'SHA256SUMS').write_text(f'{digest}  {archive.name}\n')
print(f'{archive}: {len(payload)} files, SHA-256 {digest}')
print('Challenge and proof source bundle: site registration, toolchain deployment and baseline policy require maintainer review.')
