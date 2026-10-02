import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserLocalBoundedness

/-! # Affine changes of harmonic values and oscillation normalization -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab (oscillationOn)
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Affine changes of values preserve the actual local weak equation. -/
theorem harmonic_weakHarmonic_affine_value {d : ℕ} {U : Set (Vec d)}
    {a h : Vec d → ℝ} (hh : WeakHarmonic a U h) (p q : ℝ) :
    WeakHarmonic a U (fun x => p * h x + q) := by
  refine ⟨(continuousOn_const.mul hh.1).add continuousOn_const, ?_⟩
  intro W hW hcompact hsub
  obtain ⟨u, hueq, hu⟩ := hh.2 W hW hcompact hsub
  letI : IsFiniteMeasure (volumeMeasureOn W) := ⟨by
    change (volume.restrict W) Set.univ < ⊤
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact (measure_mono (subset_closure (s := W))).trans_lt hcompact.measure_lt_top⟩
  refine ⟨(p • u).addConst q, ?_, ?_⟩
  · filter_upwards [hueq] with x hx
    change p * u.toFun x + q = p * h x + q
    rw [hx]
  · intro phi
    simp only [H1Function.grad_addConst, H1Function.smul_grad,
      vecDot_smul_left]
    simp_rw [show ∀ x, a x * (p * vecDot (u.grad x) (phi.toH1Function.grad x)) =
      p * (a x * vecDot (u.grad x) (phi.toH1Function.grad x)) by intro x; ring]
    rw [integral_const_mul, hu phi, mul_zero]

/-- A bounded function's pairwise differences are bounded by its actual
oscillation supremum. -/
theorem harmonic_abs_sub_le_oscillation {d : ℕ} {U : Set (Vec d)} {h : Vec d → ℝ}
    (hbounded : ∃ K : ℝ, ∀ x ∈ U, |h x| ≤ K) {x y : Vec d}
    (hx : x ∈ U) (hy : y ∈ U) : |h x - h y| ≤ oscillationOn U h := by
  obtain ⟨K, hK⟩ := hbounded
  apply le_csSup
  · refine ⟨2 * K, ?_⟩
    rintro t ⟨v, hv, w, hw, rfl⟩
    exact (abs_sub (h v) (h w)).trans (by linarith [hK v hv, hK w hw])
  · exact ⟨x, hx, y, hy, rfl⟩

/-- A lower endpoint of the range gives a normalization in the exact
oscillation interval without assuming extrema are attained. -/
theorem exists_harmonic_oscillation_shift {d : ℕ} {U : Set (Vec d)}
    (hne : U.Nonempty) {h : Vec d → ℝ}
    (hbounded : ∃ K : ℝ, ∀ x ∈ U, |h x| ≤ K) :
    ∃ m : ℝ, ∀ x ∈ U, 0 ≤ h x - m ∧ h x - m ≤ oscillationOn U h := by
  obtain ⟨K, hK⟩ := hbounded
  have hbelow : BddBelow (h '' U) := by
    refine ⟨-K, ?_⟩
    rintro t ⟨x, hx, rfl⟩
    linarith [(abs_le.mp (hK x hx)).1]
  refine ⟨sInf (h '' U), ?_⟩
  intro x hx
  constructor
  · exact sub_nonneg.mpr (csInf_le hbelow ⟨x, hx, rfl⟩)
  · have hlow : h x - oscillationOn U h ≤ sInf (h '' U) := by
      apply le_csInf (hne.image h)
      rintro t ⟨y, hy, rfl⟩
      have hd := harmonic_abs_sub_le_oscillation ⟨K, hK⟩ hx hy
      linarith [le_abs_self (h x - h y)]
    linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
