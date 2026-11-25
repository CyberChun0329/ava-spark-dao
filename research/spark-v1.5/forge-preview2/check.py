#!/usr/bin/env python3
"""Check the published historical frame ledger and bytecode object preimages."""
import csv
import gzip
import hashlib
import json
from pathlib import Path
import sys

p = Path(__file__).resolve().parent
with gzip.open(p / 'bytecode-objects.json.gz', 'rt') as f:
    objects = json.load(f)
expected = {
    'bytecode': '33f7f38902dd297380c87af220384217a804fccbb0cbeee13ece615f00917af7',
    'deployedBytecode': '2b34c4f6a89a994cf7f5a3eb13ec237bb95bdbd95171ddf41f65f86deb30f56a',
}
for key, digest in expected.items():
    assert hashlib.sha256(objects[key]['object'].encode()).hexdigest() == digest, key
with (p / 'frame-headers.tsv').open() as f:
    rows = list(csv.DictReader(f, delimiter='\t'))
assert len(rows) == 52
for scope, count, total in [('lesson', 46, 12247794), ('recharge', 3, 438605), ('test-funding', 3, 74237)]:
    selected = [r for r in rows if r['scope'] == scope]
    assert len(selected) == count and sum(int(r['gas']) for r in selected) == total, scope
assert sum(r['call'].endswith('::registerEvidence') for r in rows if r['scope'] == 'lesson') == 15
assert len({int(r['trace_line']) for r in rows}) == len(rows)
print('PASS: bytecode object hashes and 52 selected frame totals')

for name in sys.argv[1:]:
    artifact_path = Path(name)
    artifact = json.loads(artifact_path.read_text())
    for section, saved in objects.items():
        compared = {field: artifact[section][field] for field in saved}
        assert compared == saved, (artifact_path, section)
    print(f'PASS: creation and runtime objects and link references match {artifact_path.name}')
