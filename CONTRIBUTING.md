# Contributing and building

Build the pinned project with:

```bash
lake exe cache get
lake build
```

Use `import SubdiffusiveProcess.MainTheorems` for the three main theorems,
including both the introduction and precise forms of Theorem A.
Every new Lean file should use the module system and public declarations
where appropriate. Keep source statements faithful to the cited paper and
record correspondence by theorem or paper label.

Production code must have no incomplete proofs, custom axioms or
`native_decide`. The main theorem axiom report must contain exactly `propext`,
`Classical.choice` and `Quot.sound`. Run:

```bash
lake build SubdiffusiveProcess.Meta.AxiomsAudit 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

Only the comparator `Challenge.lean` files intentionally contain an incomplete
theorem proof. Run all their completed solutions through both verification
routes described in the README. Missing pairs, missing tools and unsuccessful
kernel checks are failures. Logs are retained in `.lake/comparator-logs/`.

The draft workflows use `workflow_dispatch`; enable the appropriate release
triggers when publishing. A warning-free production build is the CI goal;
this candidate's warning count has not yet been measured.

Treat the pinned dependencies under `.lake/packages/` as read-only. Add project
extensions within `SubdiffusiveProcess/` rather than editing a dependency.
Avoid `lake clean`: it deletes dependency build artifacts and forces a long
rebuild. To force a fresh project build, use a separate retained checkout with fresh
project output paths. The comparator runner
builds audit modules in a fresh persistent checkout under `.lake/comparator-runs/`,
reusing production and dependency artifacts. It retains every audit build and
deletes no oleans.
