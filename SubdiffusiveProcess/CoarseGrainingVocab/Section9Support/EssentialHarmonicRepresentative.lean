import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicIteration
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialContinuousRepresentative
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.InteriorCoefficientLocalization

/-! # Continuous representatives for the actual measurable coefficient -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter Topology
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A constant coefficient normalization preserves the weak equation. -/
theorem essential_harmonic_coefficient_mul {d : ℕ} {U : Set (Vec d)}
    {a : Vec d → ℝ} {u : H1Function U} (hu : IsWeaklyHarmonicOn a U u) (c : ℝ) :
    IsWeaklyHarmonicOn (fun x => c * a x) U u := by
  intro phi
  simp only [mul_smul, vecDot_smul_left]
  rw [integral_const_mul]
  simpa only [vecDot_smul_left, mul_zero] using congrArg (fun t => c * t) (hu phi)

/-- Bounded H¹ weak solutions for `b * theta` have continuous
representatives. No continuity of the bounded factor is required. -/
theorem exists_essential_harmonic_continuousRepresentative {d : ℕ} (hd : 2 ≤ d)
    {U : Set (Vec d)} (hU : IsOpen U) {b theta : Vec d → ℝ}
    (hb0 : ∀ x, 0 < b x) (hb : ContDiff ℝ 1 b)
    (htheta : ∀ x, 1 / 2 ≤ theta x ∧ theta x ≤ 2)
    (hthetaMeas : AEStronglyMeasurable theta (volume.restrict U))
    (u : H1Function U) (hu : IsWeaklyHarmonicOn (fun x => b x * theta x) U u)
    {M : ℝ} (hM : 0 ≤ M) (hub : ∀ᵐ x ∂volume.restrict U, |u.toFun x| ≤ M) :
    ∃ g : Vec d → ℝ, ContinuousOn g U ∧ g =ᵐ[volume.restrict U] u.toFun := by
  obtain ⟨t, ht, ht1, hinterval⟩ := exists_essential_harmonic_shrinking_intervals hd
  apply exists_continuousRepresentative_of_essential_intervals volume hU u.toFun
  intro x hx eps heps
  have hlog : Continuous (fun y => Real.log (b y)) :=
    hb.continuous.log (fun y => (hb0 y).ne')
  obtain ⟨delta, hdelta, hclose⟩ := Metric.continuousAt_iff.1 (hlog.continuousAt (x := x))
    (Real.log 2) (Real.log_pos (by norm_num))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
  let R := min r delta
  have hR : 0 < R := lt_min hr hdelta
  have hdist (y : Vec d) (hy : y ∈ centeredAxisCube x R) : dist y x < R := by
    rw [dist_eq_norm]
    have hn : ‖y - x‖ ≤ R / 2 := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro i
      exact (mem_centeredAxisCube.1 hy i).le
    exact hn.trans_lt (by linarith)
  have hsub : centeredAxisCube x R ⊆ U := fun y hy =>
    hball ((hdist y hy).trans_le (min_le_left r delta))
  have hband := interior_normalized_coefficient_band hb0 htheta (z := x)
    (U := centeredAxisCube x R) (fun y hy => by
      simpa only [Real.dist_eq] using
        (hclose ((hdist y hy).trans_le (min_le_right r delta))).le)
  let v := u.restrict (isOpen_axisCube (fun i => x i - R / 2) R) hsub
  have hv := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.isWeaklyHarmonicOn_restrict
    hU (isOpen_axisCube (fun i => x i - R / 2) R) hsub hu
  have hvn : IsWeaklyHarmonicOn (fun y => (b y * theta y) / b x) (centeredAxisCube x R) v := by
    convert essential_harmonic_coefficient_mul hv (b x)⁻¹ using 1
    ext y
    ring
  have hameas : AEStronglyMeasurable (fun y => (b y * theta y) / b x)
      (volume.restrict (centeredAxisCube x R)) := by
    simpa only [div_eq_mul_inv] using
      (hb.continuous.aestronglyMeasurable.mul (hthetaMeas.mono_set hsub)).mul_const (b x)⁻¹
  have hzero : Tendsto (fun n : ℕ => t ^ n * (2 * M)) atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht.le ht1).mul_const (2 * M)
  obtain ⟨n, hn⟩ := ((hzero.eventually (gt_mem_nhds heps))).exists
  obtain ⟨l, H, _, hwidth, hbound⟩ :=
    hinterval (fun y => (b y * theta y) / b x) x R hR
      ((ae_restrict_mem (isOpen_axisCube (fun i => x i - R / 2) R).measurableSet).mono hband)
      hameas v hvn M hM (ae_restrict_of_ae_restrict_of_subset hsub hub) n
  exact ⟨centeredAxisCube x (R / 8 ^ n), isOpen_axisCube _ _,
    self_mem_centeredAxisCube (by positivity), l, H, hwidth.trans_lt hn, hbound⟩

/-- The continuous representative carries every local H¹ test required
by the frozen `WeakHarmonic` predicate. -/
theorem essential_representative_weakHarmonic {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {a g : Vec d → ℝ} (u : H1Function U)
    (hu : IsWeaklyHarmonicOn a U u) (hg : ContinuousOn g U)
    (hae : g =ᵐ[volume.restrict U] u.toFun) : WeakHarmonic a U g := by
  refine ⟨hg, ?_⟩
  intro W hW _ hWU
  have hsub : W ⊆ U := subset_closure.trans hWU
  refine ⟨u.restrict hW hsub, ae_restrict_of_ae_restrict_of_subset hsub hae.symm, ?_⟩
  have hweak := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.isWeaklyHarmonicOn_restrict hU hW hsub hu
  intro phi
  simpa only [vecDot_smul_left] using hweak phi

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
