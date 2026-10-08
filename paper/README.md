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
`6532069f529ce5e4499526a1267309c7db9dee22`. [`CORRESPONDENCE.md`](../CORRESPONDENCE.md) maps the statements of this
version, by their LaTeX `\label`, to Lean declarations; the Lean files refer to the paper by
label only. Theorems A, B and C of the introduction carry the labels `t.A`, `t.B` and `t.C`,
and the precise form of Theorem A carries `t.scaling.limit`.

**arXiv source.** The reviewed source archive is available in the authors' private
[manuscript repository](https://github.com/nitromannitol/periodic_multifractal_homogenization/blob/6532069f529ce5e4499526a1267309c7db9dee22/arxiv/multifractal-source.zip).

**Building.** With a full TeX Live installation, run this in the present directory:

```bash
pdflatex -no-shell-escape multifractal.tex
bibtex multifractal
pdflatex -no-shell-escape multifractal.tex
pdflatex -no-shell-escape multifractal.tex
```

**Rights.** The paper is by Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi, and is included
with their permission. Its publication licence has not been chosen. The repository's
Apache-2.0 licence ([`LICENSE`](../LICENSE)) is the licence of the Lean development.
