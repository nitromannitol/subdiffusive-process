#!/usr/bin/env python3
"""Require one exact standard-axiom report for each headline theorem."""
import pathlib
import re
import sys

expected = {
    'SubdiffusiveProcess.process_convergence',
    'SubdiffusiveProcess.quantitative_homogenization',
    'SubdiffusiveProcess.anomalous_holder_regularity',
}
standard = {'propext', 'Classical.choice', 'Quot.sound'}
log = pathlib.Path(sys.argv[1]).read_text()
if re.search(r'warning:|sorryAx|declaration uses .sorry', log, re.IGNORECASE):
    raise SystemExit('Axiom audit emitted a warning or reported sorryAx')
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
seen = set()
for theorem, axioms in reports:
    if theorem not in expected or theorem in seen:
        raise SystemExit('Unexpected or duplicate axiom report: ' + theorem)
    actual = [a.strip() for a in axioms.split(',')]
    if len(actual) != 3 or set(actual) != standard:
        raise SystemExit('Unexpected axioms for ' + theorem + ': ' + axioms)
    seen.add(theorem)
if seen != expected:
    raise SystemExit('Missing axiom reports: ' + ', '.join(sorted(expected - seen)))
print('All three main theorems use exactly propext, Classical.choice and Quot.sound.')
