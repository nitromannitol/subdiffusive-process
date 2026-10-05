module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

@[expose] public section

open Filter Set
open scoped Topology

/-! Algebra and lower semicontinuity for the literal extended energy supremum.
Closedness, the form domain and model convergence are separate obligations. -/

namespace SubdiffusiveProcess

theorem iSup_quadraticDual_apply_image
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : H, 0 ≤ inner ℝ x (G x)) (g : H) :
    (⨆ f : H, ((2 * inner ℝ f (G g) - inner ℝ f (G f) : ℝ) : EReal)) =
      ((inner ℝ g (G g) : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun f => ?_
    rw [EReal.coe_le_coe_iff]
    have h := hpos (f - g)
    have hcross : inner ℝ g (G f) = inner ℝ f (G g) := by
      rw [← real_inner_comm]
      exact hsym f g
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
      hcross] at h
    linarith
  · refine le_iSup_of_le g ?_
    rw [EReal.coe_le_coe_iff]
    ring_nf
    exact le_refl (inner ℝ g (G g))

theorem lowerSemicontinuous_iSup_quadraticDual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H →L[ℝ] H) :
    LowerSemicontinuous (fun u : H =>
      ⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) := by
  refine lowerSemicontinuous_iSup fun f => ?_
  exact (EReal.continuous_coe_iff.mpr
    (continuous_const.mul (continuous_const.inner continuous_id) |>.sub continuous_const)).lowerSemicontinuous

/-- Symmetric injectivity gives a dense finite-energy domain for the literal supremum. -/
theorem dense_finite_quadraticDual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (G : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : H, 0 ≤ inner ℝ x (G x))
    (hinj : Function.Injective G) :
    Dense {u : H | (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) < ⊤} := by
  have hself : G.IsSymmetric := hsym
  have hadj : ContinuousLinearMap.adjoint G = G := hself.clm_adjoint_eq
  have hker : LinearMap.ker G.toLinearMap = ⊥ := (LinearMap.ker_eq_bot (f := G.toLinearMap)).mpr hinj
  have hrange_closure : (LinearMap.range G.toLinearMap).topologicalClosure = ⊤ := by
    calc
      (LinearMap.range G.toLinearMap).topologicalClosure =
          (LinearMap.range (ContinuousLinearMap.adjoint G).toLinearMap).topologicalClosure := by rw [hadj]
      _ = (LinearMap.ker G.toLinearMap)ᗮ := (G.orthogonal_ker).symm
      _ = ⊤ := by rw [hker, Submodule.bot_orthogonal_eq_top]
  have hrange_dense : Dense (Set.range G) := by
    change Dense (Set.range G.toLinearMap)
    rw [← LinearMap.coe_range, Submodule.dense_iff_topologicalClosure_eq_top]
    exact hrange_closure
  refine hrange_dense.mono ?_
  rintro u ⟨g, rfl⟩
  change (⨆ f : H, ((2 * inner ℝ f (G g) - inner ℝ f (G f) : ℝ) : EReal)) < ⊤
  rw [iSup_quadraticDual_apply_image G hsym hpos g]
  exact EReal.coe_lt_top _

/-- Translation by an operator image changes the dual energy by the exact finite pairing. -/
theorem quadraticDual_sub_image
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y))
    (u g : H) :
    (⨆ f : H, ((2 * inner ℝ f (u - G g) - inner ℝ f (G f) : ℝ) : EReal)) =
      (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) -
        ((2 * inner ℝ g u - inner ℝ g (G g) : ℝ) : EReal) := by
  let c : ℝ := 2 * inner ℝ g u - inner ℝ g (G g)
  let shift : EReal ≃o EReal :=
    { toFun := fun x => x - (c : EReal)
      invFun := fun x => x + (c : EReal)
      left_inv := fun x => EReal.sub_add_cancel
      right_inv := by
        intro x
        change (x + (c : EReal)) - (c : EReal) = x
        exact EReal.add_sub_cancel_right
      map_rel_iff' := by
        intro x y
        change x + ((-c : ℝ) : EReal) ≤ y + ((-c : ℝ) : EReal) ↔ x ≤ y
        exact (EReal.addLECancellable_coe (-c)).add_le_add_iff_right }
  have htranslate :
      (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) - (c : EReal) =
        ⨆ f : H, (((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) - (c : EReal)) := by
    exact shift.map_iSup _
  rw [htranslate]
  let e : H ≃ H := Equiv.addRight g
  have hreindex :
      (⨆ f : H, (((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) - (c : EReal))) =
        ⨆ f : H, (((2 * inner ℝ (e f) u - inner ℝ (e f) (G (e f)) : ℝ) : EReal) -
          (c : EReal)) := by
    exact (e.iSup_comp (g := fun f : H =>
      (((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) - (c : EReal)))).symm
  rw [hreindex]
  apply iSup_congr
  intro f
  rw [← EReal.coe_sub]
  congr 1
  dsimp [e, c]
  simp only [map_add, inner_add_left, inner_add_right, inner_sub_right]
  have hcross : inner ℝ g (G f) = inner ℝ f (G g) := by
    rw [← real_inner_comm]
    exact hsym f g
  rw [hcross]
  ring

/-- Finite dual energy controls the ambient Hilbert norm. -/
theorem norm_sq_le_operatorNorm_mul_quadraticDual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H →L[ℝ] H) (u : H) (e : ℝ)
    (he : (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) = (e : EReal)) :
    ‖u‖ ^ 2 ≤ ‖G‖ * e := by
  have htest (f : H) : 2 * inner ℝ f u - inner ℝ f (G f) ≤ e := by
    apply EReal.coe_le_coe_iff.mp
    rw [← he]
    exact le_iSup (fun f : H => ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) f
  have he0 : 0 ≤ e := by
    simpa only [inner_zero_left, map_zero, mul_zero, sub_self] using htest 0
  have hquad : ∀ t : ℝ,
      0 ≤ inner ℝ u (G u) * (t * t) + (-2 * ‖u‖ ^ 2) * t + e := by
    intro t
    have ht := htest (t • u)
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at ht
    nlinarith
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  have hq : inner ℝ u (G u) ≤ ‖G‖ * ‖u‖ ^ 2 := by
    calc
      inner ℝ u (G u) ≤ ‖inner ℝ u (G u)‖ := by
        simpa only [Real.norm_eq_abs] using le_abs_self (inner ℝ u (G u))
      _ ≤ ‖u‖ * ‖G u‖ := norm_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖G‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (G.le_opNorm u) (norm_nonneg u)
      _ = ‖G‖ * ‖u‖ ^ 2 := by ring
  have hqmul := mul_le_mul_of_nonneg_right hq he0
  by_cases hu : ‖u‖ ^ 2 = 0
  · rw [hu]
    exact mul_nonneg (norm_nonneg G) he0
  · have hup : 0 < ‖u‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hu)
    nlinarith

end SubdiffusiveProcess
