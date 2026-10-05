# Paper

This directory contains the paper formalized by this repository,

> Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi,
> *Anomalous scaling limit of a Brownian particle in a log-correlated potential*
> (preprint forthcoming),

with its bibliography and figures, and the compiled PDF.

- [`multifractal.tex`](multifractal.tex) is the main source. It is supported by
  [`defs.tex`](defs.tex), [`refs.bib`](refs.bib) and [`Figures/`](Figures/).
- [`multifractal.pdf`](multifractal.pdf) is the compiled paper.

**Version.** The files are the version of the authors' source at revision
`ebbd14974a1ec21f44300ca747f3e2459cfa6f7b`. [`CORRESPONDENCE.md`](../CORRESPONDENCE.md) maps the statements of this
version, by their LaTeX `\label`, to Lean declarations; the Lean files refer to the paper by
label only. Theorems A, B and C of the introduction carry the labels `t.A`, `t.B` and `t.C`,
and the precise form of Theorem A carries `t.scaling.limit`.

**Building.** With a TeX installation that includes `latexmk`, run this in the present
directory:

```bash
latexmk -pdf multifractal.tex
```

**Rights.** The paper is by Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi, and is included
with their permission. Its publication licence has not been chosen. The repository's
Apache-2.0 licence ([`LICENSE`](../LICENSE)) is the licence of the Lean development.
