module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452DoobL2
public import SubdiffusiveProcess.Probability.Diffusion.Packet452GridLimit
public import SubdiffusiveProcess.Probability.Diffusion.LaplacianGenerator
public import SubdiffusiveProcess.Probability.Diffusion.HuntIdentity
public import MarkovProcess.Trajectory.DynkinMartingale

@[expose] public section

/-!
# P-452 seed (i): Doob's `L²` maximal inequality for the Brownian Dynkin martingale

  §3, assembled: under each
`P_x` -- a genuine probability measure, which is what makes Doob applicable at all --

```text
∫ sup_{t ≤ T} M_t² dP_x  ≤  4 ∫ M_T² dP_x,
```

in continuous time, for the Dynkin martingale `M_t(ω) = φ(ω t) − ∫₀ᵗ Δφ(ω r) dr` of any `φ` in
the generator domain.  This is the join of four established pieces and nothing else:

* `Martingale.abs_grid_submartingale` (`Packet452DoobInputs`) turns the `ℝ≥0`-indexed martingale
  into the nonnegative `Filtration ℕ`-submartingale `maximal_ineq` requires, along any monotone
  time map;
* `dyadicTime` (`Packet452GridLimit`) is such a map -- **frozen at `T`**, which is exactly why it
  is monotone on all of `ℕ` and needs no `k ≤ 2ⁿ` side condition;
* `lintegral_sq_sup_abs_le` (`Packet452DoobL2`) is the `L²` inequality on each finite grid,
  constant `4`;
* `lintegral_iSup_le_dyadicGridSup` (`Packet452GridLimit`) passes to the continuous supremum by
  monotone convergence, using continuity of `t ↦ M_t(ω)` **along every path**
  (`continuous_dynkinProcess`) -- not merely a.e., which matters: only genuine path continuity
  makes the grid maxima converge to the true supremum rather than understate it.

`ofReal_sq_sup'` reconciles the two shapes of "maximum of squares" (`ofReal((maxₖ|Mₖ|)²)` from
Doob, `maxₖ ofReal(Mₖ²)` from the grid limit), and `dyadicTime_last` is what makes the right-hand
side the terminal value `M_T` rather than a grid point.

The order of quantifiers is the one Y7 §3.4 insists on: Doob is applied **inside** each fixed
`P_x`, and only the resulting numerical inequality is later integrated against the infinite
Lebesgue measure.  No `IsFiniteMeasure volume` is needed or available.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- **Doob's `L²` maximal inequality for the Brownian Dynkin martingale**, continuous time,
under each `P_x`, constant `4`. -/
theorem lintegral_iSup_sq_dynkinProcess_le
    (f : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain)
    (x : Vec d) (T : ℝ≥0) :
    (∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
        ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f t ω) ^ 2))
        ∂(laplacianContinuousLaw d x))
      ≤ 4 * ∫⁻ ω, ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f T ω) ^ 2)
          ∂(laplacianContinuousLaw d x) := by
  classical
  have hmart : Martingale (isFeller_laplacianSemigroup.dynkinProcess f)
      (ContinuousPath.canonicalFiltration (alpha := Vec d)) (laplacianContinuousLaw d x) :=
    isFeller_laplacianSemigroup.martingale_dynkinProcess isConservative_laplacianSemigroup
      kolmogorovRegular_laplacianSemigroup f x
  have hcont : ∀ ω : ContinuousPath (Vec d), Continuous fun t : ℝ≥0 =>
      ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f t ω) ^ 2) :=
    fun ω => ENNReal.continuous_ofReal.comp
      ((isFeller_laplacianSemigroup.continuous_dynkinProcess f ω).pow 2)
  have hslice : ∀ t : ℝ≥0, Measurable fun ω : ContinuousPath (Vec d) =>
      ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f t ω) ^ 2) := fun t =>
    (((isFeller_laplacianSemigroup.stronglyMeasurable_dynkinProcess f t).measurable).pow_const
      2).ennreal_ofReal
  have hmeas : ∀ n : ℕ, Measurable fun ω : ContinuousPath (Vec d) =>
      dyadicGridSup (fun t : ℝ≥0 =>
        ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f t ω) ^ 2)) T n := by
    intro n
    exact Finset.measurable_range_sup'' (f := fun k ω =>
      ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f (dyadicTime T n k) ω) ^ 2))
      (fun k _ => hslice (dyadicTime T n k))
  refine le_trans (lintegral_iSup_le_dyadicGridSup hcont hmeas) (iSup_le fun n => ?_)
  have hgrid := lintegral_sq_sup_abs_le hmart (dyadicTime T n) (monotone_dyadicTime T n) (2 ^ n)
  simp only [dyadicTime_last] at hgrid
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hgrid
  exact (ofReal_sq_sup' Finset.nonempty_range_add_one
    (fun k => isFeller_laplacianSemigroup.dynkinProcess f (dyadicTime T n k) ω)).symm

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
