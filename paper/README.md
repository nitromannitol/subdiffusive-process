# Paper

This directory contains the paper sources, bibliography and figures for
*Anomalous scaling limit of a Brownian particle in a log-correlated potential*,
by Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi.

The sources are included with the authors' authorization. The source snapshot
comes from the `main` branch of
[nitromannitol/periodic_multifractal_homogenization](https://github.com/nitromannitol/periodic_multifractal_homogenization).
The shipped paper is pinned to `c79e174c2d28026ed7b1cec31ab86a6f574164a2`.

The main source is [`multifractal.tex`](multifractal.tex), supported by
[`defs.tex`](defs.tex), [`refs.bib`](refs.bib) and [`Figures/`](Figures/).
Build the paper from this directory using a TeX installation with `latexmk`:

```bash
latexmk -pdf multifractal.tex
```

The paper's publication license is not specified here. The repository's
Apache-2.0 license applies to the Lean development.
