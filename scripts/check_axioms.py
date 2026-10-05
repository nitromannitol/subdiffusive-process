#!/usr/bin/env python3
"""Require one exact standard-axiom report for each headline theorem and each audit-export theorem named in CORRESPONDENCE.md."""
import pathlib
import re
import sys

expected = {
    'SubdiffusiveProcess.process_convergence',
    'SubdiffusiveProcess.process_convergence_precise',
    'SubdiffusiveProcess.quantitative_homogenization',
    'SubdiffusiveProcess.anomalous_holder_regularity',
}
# Every audit-export theorem the "Audit exports" table of CORRESPONDENCE.md names by its full name.
audit_exports = {
    'SubdiffusiveProcess.AuditExports.additional_condition_witness',
    'SubdiffusiveProcess.AuditExports.baseline_native_finite',
    'SubdiffusiveProcess.AuditExports.baseline_relabelled_finite',
    'SubdiffusiveProcess.AuditExports.baseline_scores_finite',
    'SubdiffusiveProcess.AuditExports.borelWeights_deletion',
    'SubdiffusiveProcess.AuditExports.boundary_response_identity',
    'SubdiffusiveProcess.AuditExports.boundary_response_identity_of_infrared',
    'SubdiffusiveProcess.AuditExports.cell_ellipticity_moment_uniform',
    'SubdiffusiveProcess.AuditExports.cell_ellipticity_uniform',
    'SubdiffusiveProcess.AuditExports.conditioningEstimate',
    'SubdiffusiveProcess.AuditExports.cutoffClauses',
    'SubdiffusiveProcess.AuditExports.cutoff_coefficient_zero_infrared_shift',
    'SubdiffusiveProcess.AuditExports.cutoff_extrema_moments',
    'SubdiffusiveProcess.AuditExports.deletion_packageClosure',
    'SubdiffusiveProcess.AuditExports.folded_iteration_energy_and_tail',
    'SubdiffusiveProcess.AuditExports.folded_iteration_minimal_scale_tail',
    'SubdiffusiveProcess.AuditExports.foldingComparison',
    'SubdiffusiveProcess.AuditExports.limiting_good_cell_witness',
    'SubdiffusiveProcess.AuditExports.limiting_good_cell_witness_of_limits',
    'SubdiffusiveProcess.AuditExports.neumann_conditioning',
    'SubdiffusiveProcess.AuditExports.neumann_source_infrared_family',
    'SubdiffusiveProcess.AuditExports.normalizedPotential_coefficient',
    'SubdiffusiveProcess.AuditExports.rare_tests_family',
    'SubdiffusiveProcess.AuditExports.resamplingEstimate',
    'SubdiffusiveProcess.AuditExports.response_bank_fixed_cube_translations',
    'SubdiffusiveProcess.AuditExports.response_bank_fixed_cube_translations_of_infrared',
    'SubdiffusiveProcess.AuditExports.theoremA_nongaussian',
}
expected |= audit_exports
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
print('Headline A, precise A, B and C and the %d theorems of the audit exports use exactly propext, Classical.choice and Quot.sound.' % len(audit_exports))
