import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Variational minima and source responses

Lax--Milgram constructs weak solutions on a real Hilbert space. Symmetry
then gives the exact affine and source objective gaps, including uniqueness
of the variational extrema. These are the functional-analytic steps used by
the finite-cutoff response construction and localized perturbation argument.
No Sobolev space or model response is postulated here.
-/

open InnerProductSpace
namespace SubdiffusiveProcess

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Coercivity makes zero the only vector with nonpositive quadratic energy. -/
theorem eq_zero_of_coercive_self_le_zero {B : H →L[ℝ] H →L[ℝ] ℝ}
    (hB : IsCoercive B) {v : H} (hv : B v v ≤ 0) : v = 0 := by
  obtain ⟨c, hc, hb⟩ := hB
  by_contra hv0
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  exact (not_lt_of_ge hv) ((mul_pos (mul_pos hc hn) hn).trans_le (hb v))

/-- Lax--Milgram gives the unique solution for an actual continuous linear load. -/
theorem existsUnique_bilin_eq_load [CompleteSpace H]
    {B : H →L[ℝ] H →L[ℝ] ℝ} (hB : IsCoercive B) (L : H →L[ℝ] ℝ) :
    ∃! u : H, ∀ v : H, B u v = L v := by
  let T := hB.continuousLinearEquivOfBilin
  let f := (toDual ℝ H).symm L
  refine ⟨T.symm f, ?_, ?_⟩
  · intro v
    rw [← hB.continuousLinearEquivOfBilin_apply]
    change inner ℝ (T (T.symm f)) v = L v
    rw [T.apply_symm_apply]
    exact toDual_symm_apply
  · intro u hu
    apply T.injective
    rw [T.apply_symm_apply]
    apply (toDual ℝ H).injective
    ext v
    change inner ℝ (T u) v = inner ℝ f v
    rw [hB.continuousLinearEquivOfBilin_apply, hu, toDual_symm_apply]

/-- The source objective loses exactly the energy of the difference from its weak solution. -/
theorem quadratic_objective_gap {B : H →L[ℝ] H →L[ℝ] ℝ}
    (hB : ∀ x y, B x y = B y x) (L : H →L[ℝ] ℝ) {u : H}
    (hu : ∀ v, B u v = L v) (v : H) :
    (2 * L u - B u u) - (2 * L v - B v v) = B (v - u) (v - u) := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hB v u, hu v, hu u]
  ring

/-- The affine weak equation is exactly a minimum, with its full energy gap. -/
theorem affine_energy_gap {B : H →L[ℝ] H →L[ℝ] ℝ}
    (hB : ∀ x y, B x y = B y x) (V : Submodule ℝ H) {u v : H}
    (hu : ∀ w ∈ V, B u w = 0) (hv : v - u ∈ V) :
    B v v = B u u + B (v - u) (v - u) := by
  have hz := hu (v - u) hv
  simp only [map_sub] at hz
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hB v u]
  linarith

/-- A closed variation space admits an affine weak solution and its energy minimum. -/
theorem exists_affine_weak_minimizer [CompleteSpace H]
    {B : H →L[ℝ] H →L[ℝ] ℝ} (hc : IsCoercive B)
    (hs : ∀ x y, B x y = B y x) (V : Submodule ℝ H)
    (hV : IsClosed (V : Set H)) (b : H) :
    ∃ u : H, u - b ∈ V ∧ (∀ v ∈ V, B u v = 0) ∧
      ∀ v : H, v - b ∈ V → B u u ≤ B v v := by
  haveI : IsClosed (V : Set H) := hV
  haveI : CompleteSpace V := IsClosed.completeSpace_coe
  let D := B.bilinearComp V.subtypeL V.subtypeL
  have hd : IsCoercive D := by
    obtain ⟨c, hc, hbound⟩ := hc
    exact ⟨c, hc, fun v => hbound v.val⟩
  let L : V →L[ℝ] ℝ := -((B b).comp V.subtypeL)
  obtain ⟨w, hw, _⟩ := existsUnique_bilin_eq_load hd L
  let u := b + (w : H)
  have hub : u - b ∈ V := by
    simpa only [u, add_sub_cancel_left] using w.property
  have heuler : ∀ v ∈ V, B u v = 0 := by
    intro v hv
    have he := hw ⟨v, hv⟩
    change B (w : H) v = -(B b v) at he
    change B (b + (w : H)) v = 0
    simp only [map_add, ContinuousLinearMap.add_apply]
    linarith
  have hnonneg : ∀ z : H, 0 ≤ B z z := by
    obtain ⟨c, hc, hbound⟩ := hc
    exact fun z => le_trans (mul_nonneg (mul_nonneg hc.le (norm_nonneg z))
      (norm_nonneg z)) (hbound z)
  have hgap : ∀ v, v - b ∈ V → B v v = B u u + B (v - u) (v - u) := by
    intro v hv
    apply affine_energy_gap hs V heuler
    simpa only [sub_sub_sub_cancel_right] using V.sub_mem hv hub
  refine ⟨u, hub, heuler, ?_⟩
  intro v hv
  rw [hgap v hv]
  exact le_add_of_nonneg_right (hnonneg _)

/-- A closed space of allowed variations has a unique affine energy minimizer. -/
theorem existsUnique_affine_minimizer [CompleteSpace H]
    {B : H →L[ℝ] H →L[ℝ] ℝ} (hc : IsCoercive B)
    (hs : ∀ x y, B x y = B y x) (V : Submodule ℝ H)
    (hV : IsClosed (V : Set H)) (b : H) :
    ∃! u : H, u - b ∈ V ∧ ∀ v : H, v - b ∈ V → B u u ≤ B v v := by
  obtain ⟨u, hub, heuler, hmin⟩ := exists_affine_weak_minimizer hc hs V hV b
  refine ⟨u, ⟨hub, hmin⟩, ?_⟩
  intro v hv
  have hmem : v - u ∈ V := by
    simpa only [sub_sub_sub_cancel_right] using V.sub_mem hv.1 hub
  have hgap := affine_energy_gap hs V heuler hmem
  have hz : B (v - u) (v - u) ≤ 0 := by linarith [hv.2 u hub]
  exact sub_eq_zero.mp (eq_zero_of_coercive_self_le_zero hc hz)

/-- Every affine minimizer satisfies the weak Euler equation. -/
theorem affine_minimizer_euler [CompleteSpace H]
    {B : H →L[ℝ] H →L[ℝ] ℝ} (hc : IsCoercive B)
    (hs : ∀ x y, B x y = B y x) (V : Submodule ℝ H)
    (hV : IsClosed (V : Set H)) (b u : H) (hub : u - b ∈ V)
    (hmin : ∀ v : H, v - b ∈ V → B u u ≤ B v v) :
    ∀ v ∈ V, B u v = 0 := by
  obtain ⟨w, hwb, heuler, _⟩ := exists_affine_weak_minimizer hc hs V hV b
  have hmem : u - w ∈ V := by
    simpa only [sub_sub_sub_cancel_right] using V.sub_mem hub hwb
  have hgap := affine_energy_gap hs V heuler hmem
  have hz : B (u - w) (u - w) ≤ 0 := by linarith [hmin w hwb]
  have heq : u = w := sub_eq_zero.mp (eq_zero_of_coercive_self_le_zero hc hz)
  exact heq ▸ heuler

/-- A symmetric coercive source problem has a unique maximizer of its variational objective. -/
theorem existsUnique_source_maximizer [CompleteSpace H]
    {B : H →L[ℝ] H →L[ℝ] ℝ} (hc : IsCoercive B)
    (hs : ∀ x y, B x y = B y x) (L : H →L[ℝ] ℝ) :
    ∃! u : H, ∀ v : H, 2 * L v - B v v ≤ 2 * L u - B u u := by
  obtain ⟨u, hu, _⟩ := existsUnique_bilin_eq_load hc L
  have hg := quadratic_objective_gap hs L hu
  have hnonneg : ∀ z : H, 0 ≤ B z z := by
    obtain ⟨c, hc, hbound⟩ := hc
    exact fun z => le_trans (mul_nonneg (mul_nonneg hc.le (norm_nonneg z))
      (norm_nonneg z)) (hbound z)
  refine ⟨u, ?_, ?_⟩
  · intro v
    have := hg v
    linarith [hnonneg (v - u)]
  · intro v hv
    have hz : B (v - u) (v - u) ≤ 0 := by linarith [hg v, hv u]
    exact sub_eq_zero.mp (eq_zero_of_coercive_self_le_zero hc hz)

/-- Every source maximizer satisfies its weak load equation. -/
theorem source_maximizer_euler [CompleteSpace H]
    {B : H →L[ℝ] H →L[ℝ] ℝ} (hc : IsCoercive B)
    (hs : ∀ x y, B x y = B y x) (L : H →L[ℝ] ℝ) (u : H)
    (hmax : ∀ v : H, 2 * L v - B v v ≤ 2 * L u - B u u) :
    ∀ v : H, B u v = L v := by
  obtain ⟨w, hw, _⟩ := existsUnique_bilin_eq_load hc L
  have hgap := quadratic_objective_gap hs L hw u
  have hz : B (u - w) (u - w) ≤ 0 := by linarith [hmax w]
  have heq : u = w := sub_eq_zero.mp (eq_zero_of_coercive_self_le_zero hc hz)
  exact heq ▸ hw

end SubdiffusiveProcess
