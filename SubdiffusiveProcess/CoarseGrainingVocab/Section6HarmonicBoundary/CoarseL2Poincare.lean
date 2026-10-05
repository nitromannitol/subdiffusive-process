module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.OscillationPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryArbitraryH1Circ

@[expose] public section

/-!
# The coarse-grained `L²` Poincare inequality on a triadic cube

`p.coarse.grained.poincare` and `e.nabla.u.detach` and `e.CG.Poincare.mean.zero` (`p.coarse.grained.poincare`, AK.HC
Lemma 2.3) combines with the detachment inequality `e.nabla.u.detach`
(`p.coarse.grained.poincare` and `e.nabla.u.detach` and `e.CG.Poincare.mean.zero`) and the `B^{1-s}_{2,∞} → L̄²` step (`p.coarse.grained.poincare` and `e.nabla.u.detach` and `e.CG.Poincare.mean.zero`) to give
`e.CG.Poincare.mean.zero` (`p.coarse.grained.poincare` and `e.nabla.u.detach` and `e.CG.Poincare.mean.zero`):

```text
‖u − (u)_{𝔠_0}‖_{L̄²(𝔠_0)}
  ≤ C λ_{1,1}^{-1/2}(𝔠_0 ; a) ‖a^{1/2} ∇u‖_{L̄²(𝔠_0)} .
```

This is the manuscript's own tool for pricing a *zeroth-order* scalar against
the coefficient: the left-hand side is a negative-order norm of `∇u`, exactly
the kind coarse graining controls, so the constant is a **coarse-grained**
lower ellipticity and **no pointwise `aCutoff/σ` ratio is paid**.  Compare
 §11.2, which shows that any
price routed through the pointwise conversions
`aCutoff_div_tailAverage_le_one_add_subunitEnvelope` costs `3^{(3/128) s n}`
per power on the parent-oscillation leg, and §12.2, which corrects §11 by
observing that the manuscript never routes this scalar that way.

Both halves are already committed:

* the detachment, at the `s = 1` endpoint where the manuscript's `s ↑ 1` limit
  lands, is
  `Section4Support.Besov.cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm`,
  whose constant `oscillationMultiscalePoincareConstant d` is dimension-only;
* the coarse-grained gradient half, already specialised to `aCutoff` and to a
  single `lambdaS` cap, is
  `Section6HarmonicApproximation.aCutoff_h1Gradient_circPartialNorm_le_of_lambdaSCap`,
  itself built on
  `Homogenization.coarsePoincare_gradient_qone_of_cubeAverageEnergyControl`.

What this module adds is the composition: the passage from the finite-depth
`circ` partial norms (uniform in the depth `N`) to the full `circ` norm that
the detachment consumes, and the resulting single inequality with the
manuscript's scale factor `3^{Q.scale}` in front.  The exponent hypothesis is
`0 < t ≤ 1`: a cap at the small exponent `t = s/3` supplied by
`exists_localBoundaryEllipticityCaps_nextWindow` is transported to the
endpoint exponent `1` inside
`aCutoff_h1Gradient_circPartialNorm_le_of_lambdaSCap` by
`Ch02.lambdaSq_finite_mono`, so nothing is lost and no power of `3^{s n}`
appears.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The dimension-only constant of the coarse-grained `L²` Poincare
inequality: the detachment constant of
`oscillationMultiscalePoincareConstant`, one factor `d` for the coordinate
sum, the `q = 1` geometric discount `(1 - 3^{-1})⁻¹` and one further factor
`d` from the componentwise multiscale gradient bound. -/
def coarseL2PoincareConst (d : ℕ) [NeZero d] : ℝ :=
  oscillationMultiscalePoincareConstant d *
    ((d : ℝ) * ((geometricDiscount 1 1)⁻¹ * (d : ℝ)))

theorem coarseL2PoincareConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ coarseL2PoincareConst d := by
  have hgd : 0 < geometricDiscount 1 1 := geometricDiscount_pos (by norm_num)
  have := oscillationMultiscalePoincareConstant_nonneg d
  unfold coarseL2PoincareConst
  positivity

omit [NeZero d] in
private theorem cubeBesovScaleWeight_neg_one (Q : TriadicCube d) :
    cubeBesovScaleWeight (-1) Q = cubeScaleFactor Q := by
  have hpos : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  unfold cubeBesovScaleWeight
  norm_num

/-- **The coarse-grained `L²` Poincare inequality for `aCutoff`.**
`e.CG.Poincare.mean.zero` (`e.CG.Poincare.mean.zero`).

For an arbitrary `H¹` function on a triadic cube `Q` and any coarse lower
ellipticity cap `λ_{t,1}(Q ; a)⁻¹ ≤ K σ⁻¹` at an exponent `0 < t ≤ 1`, the
normalized `L²` oscillation of `u` is bounded by
`C(d) √(K σ⁻¹) 3^{Q.scale} ‖a^{1/2} ∇u‖_{L̄²(Q)}`.

The constant is dimension-only and the coefficient enters only through the
*coarse* quantity `λ_{t,1}`; in particular no pointwise `aCutoff / σ`
comparison is used. -/
theorem aCutoff_cubeFluctuation_lpNorm_le_of_lambdaSCap
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    {t sigma K : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hcap : (Ch02.lambdaS Q t (aCutoffFamily M L omega))⁻¹ ≤ K * sigma⁻¹) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) ≤
      coarseL2PoincareConst d * Real.sqrt (K * sigma⁻¹) * cubeScaleFactor Q *
        Real.sqrt (cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) u.grad)) := by
  classical
  set A := aCutoffFamily M L omega with hA
  set E : ℝ := Real.sqrt (cubeAverage Q
    (coefficientEnergyDensity (publicCoeffField Q A) u.grad)) with hE
  set Bnd : ℝ :=
    (cubeScaleFactor Q *
      ((geometricDiscount 1 1)⁻¹ * ((d : ℝ) * Real.sqrt (K * sigma⁻¹)))) * E
    with hBnd
  have hcirc : ∀ i : Fin d,
      cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) ≤ Bnd := by
    intro i
    refine cubeBesovCircNorm_le_of_forall_partialNorm_le Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
      (fun x => u.grad x i) (by simp) ?_
    intro N
    have hraw := aCutoff_h1Gradient_circPartialNorm_le_of_lambdaSCap
      M L omega Q u (t := t) (r := 1) (sigma := sigma) (K := K) ht ht1 hcap i N
    simpa only [hA, hE, hBnd, cubeBesovScaleWeight_neg_one] using hraw
  have hsum :
      ∑ i : Fin d, cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i) ≤ (d : ℝ) * Bnd := by
    calc
      ∑ i : Fin d, cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)
          ≤ ∑ _i : Fin d, Bnd := Finset.sum_le_sum fun i _ => hcirc i
      _ = (d : ℝ) * Bnd := by simp
  have hosc :=
    cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm
      Q u
  have hoscConst : 0 ≤ oscillationMultiscalePoincareConstant d :=
    oscillationMultiscalePoincareConstant_nonneg d
  have hfinal :
      cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x) ≤
        oscillationMultiscalePoincareConstant d * ((d : ℝ) * Bnd) :=
    hosc.trans (mul_le_mul_of_nonneg_left hsum hoscConst)
  have hcalc :
      oscillationMultiscalePoincareConstant d * ((d : ℝ) * Bnd) =
        coarseL2PoincareConst d * Real.sqrt (K * sigma⁻¹) * cubeScaleFactor Q * E := by
    unfold coarseL2PoincareConst
    rw [hBnd]
    ring
  rw [hcalc] at hfinal
  simpa only [cubeBesovOscillation, hE] using hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
