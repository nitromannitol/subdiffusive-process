import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderContinuous
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Uniform Hölder bounds from scalar representatives

Banach–Steinhaus upgrades scalar Hölder bounds with a constant depending on the
test vector to a Hölder bound for a Hilbert-space-valued representer. The exponent
is fixed before quantifying over the test vectors. Thus qualitative local
regularity of every resolvent output suffices for the uniform bound required by
`ResolventRegularityDatum.holder_repr`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderUniformBoundedness

/-- A common scalar Hölder exponent gives a norm Hölder bound, by applying
Banach–Steinhaus to normalized differences of the associated linear functionals.
The scalar constant may depend on the test vector. -/
theorem exists_norm_sub_le_of_inner_sub_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {X : Type*} [MetricSpace X] {g : X → H} {K : Set X} {a : ℝ}
    (hscalar : ∀ f : H, ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
      |⟪g x - g y, f⟫| ≤ C * dist x y ^ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖g x - g y‖ ≤ C * dist x y ^ a := by
  let I := {p : K × K // (p.1 : X) ≠ (p.2 : X)}
  let ell : I → H →L[ℝ] ℝ := fun p =>
    (dist (p.1.1 : X) (p.1.2 : X) ^ a)⁻¹ •
      InnerProductSpace.toDual ℝ H (g p.1.1 - g p.1.2)
  have hpoint : ∀ f : H, ∃ C : ℝ, ∀ p : I, ‖ell p f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := hscalar f
    refine ⟨C, ?_⟩
    intro p
    have hdist : 0 < dist (p.1.1 : X) (p.1.2 : X) ^ a :=
      Real.rpow_pos_of_pos (dist_pos.mpr p.2) a
    change |(dist (p.1.1 : X) (p.1.2 : X) ^ a)⁻¹ *
      ⟪g p.1.1 - g p.1.2, f⟫| ≤ C
    rw [abs_mul, abs_of_pos (inv_pos.mpr hdist), ← div_eq_inv_mul]
    exact (div_le_iff₀ hdist).2 (hC _ p.1.1.2 _ p.1.2.2)
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    rw [sub_self, norm_zero]
    exact mul_nonneg (le_max_right C 0) (Real.rpow_nonneg dist_nonneg a)
  · have hdist : 0 < dist x y ^ a := Real.rpow_pos_of_pos (dist_pos.mpr hxy) a
    have hnorm := hC ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
    change ‖(dist x y ^ a)⁻¹ • InnerProductSpace.toDual ℝ H (g x - g y)‖ ≤ C at hnorm
    rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hdist), ← div_eq_inv_mul] at hnorm
    exact ((div_le_iff₀ hdist).1 hnorm).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 0) hdist.le)

/-- Hölder representatives for every output imply a uniform Hölder bound for
the Riesz representer. No proportional bound on their individual constants is
required: uniform boundedness supplies it. -/
theorem exists_norm_repr_sub_le_of_holder_representative
    {X : Type*} [MeasurableSpace X] [MetricSpace X] {mu : Measure X} {Om : Set X}
    {T : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu} {g : X → Lp ℝ 2 mu}
    (hg : ∀ (f : Lp ℝ 2 mu) (w : X → ℝ), ContinuousOn w Om →
      (fun x => (T f) x) =ᵐ[mu] w → ∀ x ∈ Om, ⟪g x, f⟫ = w x)
    {K : Set X} (hKOm : K ⊆ Om) {a : ℝ}
    (hK : ∀ f : Lp ℝ 2 mu, ∃ w : X → ℝ, ContinuousOn w Om ∧
      (fun x => (T f) x) =ᵐ[mu] w ∧ ∃ C : ℝ,
      ∀ x ∈ K, ∀ y ∈ K, |w x - w y| ≤ C * dist x y ^ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖g x - g y‖ ≤ C * dist x y ^ a := by
  apply exists_norm_sub_le_of_inner_sub_le
  intro f
  obtain ⟨w, hwcont, hwae, C, hC⟩ := hK f
  refine ⟨C, ?_⟩
  intro x hx y hy
  rw [inner_sub_left, hg f w hwcont hwae x (hKOm hx),
    hg f w hwcont hwae y (hKOm hy)]
  exact hC x hx y hy

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderUniformBoundedness
