module

public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.BilateralField

@[expose] public section

open MeasureTheory
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The common scale coupling (paper 33-37), pinned to the carrier.

The paper extends the layer family to all integer indices, the layer at index
`j` having the law of the root layer rescaled by `3^{-j}`, and fixes ONE
realization of the whole family while the cutoff increases.  That is exactly
`commonScaleLaw`: the infinite product over `j : ℤ` of the scaled layer laws,
a law on `BilateralField d = ℤ → C(R^d, R)`, so a sample is one realization of
every layer at once and the cutoff only changes which finitely many of them
are read.

The rescaling `g_j = g_0(3^{-j} ·)` in law is `scaledLayerLaw`, the pushforward
of the root law under the dilation, and the independence across `j` is the
product structure -- which is what the layer-block independence arguments of
this argument consume. -/
abbrev in_common_scale_coupling (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
    ProbabilityMeasure (BilateralField d) :=
  commonScaleLaw d ν

end SubdiffusiveProcess.Paper
