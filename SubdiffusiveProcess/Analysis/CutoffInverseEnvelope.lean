import SubdiffusiveProcess.Lane4.Carriers

/-! A measurable reciprocal-coefficient envelope on a fixed compact set. -/
namespace SubdiffusiveProcess.Analysis
open MeasureTheory TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped BigOperators
noncomputable section

/-- A finite-cutoff envelope. No small-disorder or moment assumption is used. -/
def compactCutoffInverseEnvelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (K : Compacts (SpatialCoordinates d)) (ω : BilateralField d) : ℝ :=
  SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * Real.exp
    (‖(H ω).restrict (K : Set (SpatialCoordinates d))‖ +
      ∑ j ∈ Finset.range (N + 1),
        ‖(ω (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))‖ +
      (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)

theorem compactCutoffInverseEnvelope_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (K : Compacts (SpatialCoordinates d)) (ω : BilateralField d) :
    0 < compactCutoffInverseEnvelope M H N K ω :=
  mul_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N) (Real.exp_pos _)

/-- Measurability follows from restriction norms of the actual layers and H. -/
theorem measurable_compactCutoffInverseEnvelope {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (K : Compacts (SpatialCoordinates d)) :
    Measurable (compactCutoffInverseEnvelope M H N K) := by
  have hnorm : Measurable (fun f : C(SpatialCoordinates d, ℝ) =>
      ‖f.restrict (K : Set (SpatialCoordinates d))‖) :=
    (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).norm.measurable
  exact measurable_const.mul (((hnorm.comp hH).add
    (Finset.measurable_sum _ (fun j _ => hnorm.comp (measurable_pi_apply (-(Int.ofNat j)))))).add
      measurable_const).exp

/-- Every reciprocal coefficient in the compact set is bounded, pointwise. -/
theorem cutoffCoefficient_inv_le_compactEnvelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (K : Compacts (SpatialCoordinates d)) (ω : BilateralField d)
    (x : SpatialCoordinates d) (hx : x ∈ (K : Set (SpatialCoordinates d))) :
    (cutoffCoefficient M H ω N x)⁻¹ ≤ compactCutoffInverseEnvelope M H N K ω := by
  have hnorm (f : C(SpatialCoordinates d, ℝ)) :
      -f x ≤ ‖f.restrict (K : Set (SpatialCoordinates d))‖ := by
    have h := (f.restrict (K : Set (SpatialCoordinates d))).neg_norm_le_apply ⟨x, hx⟩
    change -‖f.restrict (K : Set (SpatialCoordinates d))‖ ≤ f x at h
    linarith
  have hpotential : -cutoffPotential H ω N x ≤
      ‖(H ω).restrict (K : Set (SpatialCoordinates d))‖ +
        ∑ j ∈ Finset.range (N + 1),
          ‖(ω (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))‖ := by
    unfold cutoffPotential
    rw [neg_add, ← Finset.sum_neg_distrib]
    exact add_le_add (hnorm _) (Finset.sum_le_sum (fun j _ => hnorm _))
  have hexp := Real.exp_le_exp.mpr
    (add_le_add_right hpotential ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
  have h := mul_le_mul_of_nonneg_left hexp (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).le
  simpa only [cutoffCoefficient, compactCutoffInverseEnvelope, mul_inv_rev, inv_inv,
    ← Real.exp_neg, neg_sub, sub_eq_add_neg, neg_add, neg_neg, add_comm, mul_comm] using h

end
end SubdiffusiveProcess.Analysis
