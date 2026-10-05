module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedGraphDistance

@[expose] public section

/-!
# Flux decay factor from repaired-graph distance

The per-cell flux estimate carries a factor `theta^(dist/2)`.  The repaired
graph-distance lower bound converts it into the Euclidean exterior decay
factor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

omit [NeZero d] in
/-- Graph-distance decay of the per-cell flux factor.  The factor six is the
paper's loss of three in passing to the preceding triadic radius, followed by
the square-root exponent in `theta^(dist/2)`. -/
theorem repairedStopping_flux_rpow_le_of_not_shortCrossing
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (x0 : Vec d)
    {R epsilon r theta : ℝ} (hR : 0 < R) (hepsilon : 0 ≤ epsilon)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) {k : ℕ}
    (hlower : (3 : ℝ) ^ k * R ≤ r)
    (hupper : r ≤ 3 * ((3 : ℝ) ^ k * R))
    (hgood : ¬ RepairedStoppingShortCrossing source hsource x0 R epsilon k)
    {q : RefinedStoppingCell failure omega base}
    (hmeet :
      (translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) ∩
        (Metric.ball x0 r)ᶜ).Nonempty) :
    theta ^ ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ) / 2) ≤
      theta ^ (epsilon * r / (6 * R)) := by
  have hdist := repairedStoppingGraphDistance_lower_bound_of_not_shortCrossing
    source hsource x0 hR hepsilon hlower hupper hgood hmeet
  have hhalf : epsilon * r / (6 * R) ≤
      (stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ) / 2 := by
    have hscale : epsilon * r / (6 * R) =
        (epsilon * r / (3 * R)) / 2 := by
      field_simp [hR.ne']
      ring
    rw [hscale]
    exact div_le_div_of_nonneg_right hdist (by norm_num)
  exact Real.rpow_le_rpow_of_exponent_ge htheta hthetaOne hhalf

omit [NeZero d] in
/-- Exponential form of the repaired-graph flux decay factor. -/
theorem repairedStopping_flux_rpow_le_exp_of_not_shortCrossing
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (x0 : Vec d)
    {R epsilon r theta : ℝ} (hR : 0 < R) (hepsilon : 0 ≤ epsilon)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) {k : ℕ}
    (hlower : (3 : ℝ) ^ k * R ≤ r)
    (hupper : r ≤ 3 * ((3 : ℝ) ^ k * R))
    (hgood : ¬ RepairedStoppingShortCrossing source hsource x0 R epsilon k)
    {q : RefinedStoppingCell failure omega base}
    (hmeet :
      (translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) ∩
        (Metric.ball x0 r)ᶜ).Nonempty) :
    theta ^ ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ) / 2) ≤
      Real.exp (Real.log theta * (epsilon * r / (6 * R))) := by
  rw [← Real.rpow_def_of_pos htheta]
  exact repairedStopping_flux_rpow_le_of_not_shortCrossing source hsource x0
    hR hepsilon htheta hthetaOne hlower hupper hgood hmeet

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
