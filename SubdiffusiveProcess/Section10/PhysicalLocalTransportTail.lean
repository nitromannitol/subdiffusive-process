module

public import SubdiffusiveProcess.Section10.PhysicalLocalTransportInfrared
public import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
public import SubdiffusiveProcess.Analysis.InfraredTruncationBound

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Homogenization Set TopologicalSpace
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalLocalTransport

variable {d : ℕ} [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]

/-- Actual partial infrared fields on the coupling carrier, not a substitute infinite H. -/
theorem partialSum_native (eta : NativeEnvironment d) (q : ℕ) :
    infraredPartialSum (bilateralEnvironment eta) q =
      (positiveAnchoredInfraredTruncation eta q).1.1 := by
  induction q with
  | zero =>
    ext x
    simp [infraredPartialSum, positiveAnchoredInfraredTruncation, zeroNativePotentialField]
  | succ q ih =>
    unfold infraredPartialSum
    rw [Finset.sum_range_succ]
    change infraredPartialSum (bilateralEnvironment eta) q +
      (bilateralEnvironment eta (Int.ofNat (q + 1)) - ContinuousMap.const _
        (bilateralEnvironment eta (Int.ofNat (q + 1)) 0)) = _
    rw [ih]
    ext x
    rfl

/-- Canonical Section 6/native infrared moment projections, uniform in the truncation.
These are the literal oscillation inputs for finite B2-P; no Sobolev bank is assumed. -/
theorem native_truncation_moments (hd : 2 ≤ d) :
    ∃ C : Compacts (Vec d) → ℝ, (∀ K, 0 ≤ C K) ∧
      ∀ (M : GMCModel d) (K : Compacts (Vec d)) (lambda : ℝ), 0 ≤ lambda →
        ∀ q : ℕ,
          Integrable (fun eta => Real.exp (lambda * compactPotentialC1Norm K
            (positiveAnchoredInfraredTruncation eta q))) (nativeLaw M) ∧
          (∫ eta, Real.exp (lambda * compactPotentialC1Norm K
            (positiveAnchoredInfraredTruncation eta q)) ∂nativeLaw M) ≤
            2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) := by
  obtain ⟨C, hC, hCM⟩ := exists_native_infrared_limit hd
  refine ⟨C, hC, ?_⟩
  intro M K lambda hlambda q
  obtain ⟨Hn, _, _, _, _, _, hmom⟩ := hCM M
  obtain ⟨_, _, _, _, htrunc⟩ := hmom K lambda hlambda
  exact ⟨(htrunc q).1, (htrunc q).2.1⟩

/-- The full infrared input is independently available on the exact chaos law. -/
theorem full_infrared_moments (hd : 2 ≤ d) :
    ∃ C : Compacts (Vec d) → ℝ, (∀ K, 0 ≤ C K) ∧
      ∀ (M : GMCModel d) (K : Compacts (Vec d)) (lambda : ℝ), 0 ≤ lambda →
        Integrable (fun xi => Real.exp
          (lambda * ‖(infraredField M xi).restrict (K : Set (Vec d))‖))
          (chaosSampleLaw M).toMeasure ∧
        (∫ xi, Real.exp (lambda * ‖(infraredField M xi).restrict (K : Set (Vec d))‖)
          ∂(chaosSampleLaw M).toMeasure) ≤ 2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) := by
  obtain ⟨C, hC, hCM⟩ := exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  exact ⟨C, hC, fun M K lambda h => hCM M (infraredField M) (infraredField_spec M) K lambda h⟩

/-- A pointwise bound by the two actual supplied infrared observables. -/
theorem tail_value_bound (M : GMCModel d) (K : Compacts (Vec d)) (q : ℕ)
    (eta : NativeEnvironment d) {x : Vec d} (hx : x ∈ (K : Set (Vec d))) :
    |infraredPartialSum (bilateralEnvironment eta) q x - infraredField M (bilateralEnvironment eta) x| ≤
      compactPotentialC1Norm K (positiveAnchoredInfraredTruncation eta q) +
        ‖(infraredField M (bilateralEnvironment eta)).restrict (K : Set (Vec d))‖ := by
  have hpart : |infraredPartialSum (bilateralEnvironment eta) q x| ≤
      compactPotentialC1Norm K (positiveAnchoredInfraredTruncation eta q) := by
    rw [partialSum_native]
    exact (ContinuousMap.norm_coe_le_norm
      (restrictForget K (positiveAnchoredInfraredTruncation eta q)) ⟨x, hx⟩).trans
        (norm_restrictForget_le K (positiveAnchoredInfraredTruncation eta q))
  have hfull : |infraredField M (bilateralEnvironment eta) x| ≤
      ‖(infraredField M (bilateralEnvironment eta)).restrict (K : Set (Vec d))‖ :=
    ContinuousMap.norm_coe_le_norm
      ((infraredField M (bilateralEnvironment eta)).restrict (K : Set (Vec d))) ⟨x, hx⟩
  exact (abs_sub _ _).trans (add_le_add hpart hfull)

/-- Finite densities are bounded above and below by the full bilateral density with
the actual uniform-moment tail price. The same price applies to their coefficients. -/
theorem finite_multiplier_bounds (M : GMCModel d) {l m : ℕ} (hml : m ≤ l)
    (K : Compacts (Vec d)) (eta : NativeEnvironment d) {x : Vec d}
    (hx : x ∈ (K : Set (Vec d))) :
    let T := compactPotentialC1Norm K (positiveAnchoredInfraredTruncation eta (l - m)) +
      ‖(infraredField M (bilateralEnvironment eta)).restrict (K : Set (Vec d))‖
    Real.exp (-T) * cutoffSpeedDensity M (infraredField M) (bilateralEnvironment eta) m x ≤
      finiteLocalSpeed M l m (bilateralEnvironment eta) x ∧
    finiteLocalSpeed M l m (bilateralEnvironment eta) x ≤
      Real.exp T * cutoffSpeedDensity M (infraredField M) (bilateralEnvironment eta) m x := by
  dsimp only
  simp only [(finite_multiplier_identification M hml (bilateralEnvironment eta) x).1]
  have hb := tail_value_bound M K (l - m) eta hx
  exact ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_of_abs_le hb))
      (Real.exp_pos _).le,
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (le_of_abs_le hb)) (Real.exp_pos _).le⟩

end SubdiffusiveProcess.Section10.PhysicalLocalTransport
