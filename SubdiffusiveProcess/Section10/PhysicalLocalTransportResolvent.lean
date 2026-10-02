import SubdiffusiveProcess.Section10.PhysicalLocalTransportCoefficients
import SubdiffusiveProcess.Section10.PhysicalAttachmentUniqueness
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalLocalTransport

variable {d : ℕ}

/-- Change coordinates on the actual `C₀` space without changing its norm. -/
def pullback (e : Vec d ≃ₜ Vec d) : C₀(Vec d, ℝ) ≃ₗᵢ[ℝ] C₀(Vec d, ℝ) where
  toLinearEquiv :=
    { toFun := fun f => f.comp e.toCocompactMap
      invFun := fun f => f.comp e.symm.toCocompactMap
      left_inv := fun f => by ext x; simp
      right_inv := fun f => by ext x; simp
      map_add' := fun f g => rfl
      map_smul' := fun r f => rfl }
  norm_map' f := by
    have hbound (h : Vec d ≃ₜ Vec d) (g : C₀(Vec d, ℝ)) :
        ‖g.comp h.toCocompactMap‖ ≤ ‖g‖ :=
      (BoundedContinuousFunction.norm_le (norm_nonneg g)).mpr
        (fun x => g.toBCF.norm_coe_le_norm (h x))
    apply le_antisymm (hbound e f)
    have hh := hbound e.symm (f.comp e.toCocompactMap)
    have hid : (f.comp e.toCocompactMap).comp e.symm.toCocompactMap = f := by
      ext x
      simp
    rwa [hid] at hh

@[simp] theorem pullback_apply (e : Vec d ≃ₜ Vec d) (f : C₀(Vec d, ℝ)) (x : Vec d) :
    pullback e f x = f (e x) := rfl

@[simp] theorem pullback_symm (e : Vec d ≃ₜ Vec d) : (pullback e).symm = pullback e.symm := rfl

def dividedShift (t : ℝ) (ht : 0 < t) (mu : Semigroup.PositiveShift) : Semigroup.PositiveShift :=
  ⟨(mu : ℝ) / t, div_pos mu.property ht⟩

/-- The actual physical resolvent pulled back to local coordinates at the raw clock.
This is an operator construction, with all datum fields proved, rather than a local-law premise. -/
def transportedDatum (D : C0ResolventDatum (Vec d)) (e : Vec d ≃ₜ Vec d)
    (t : ℝ) (ht : 0 < t) : C0ResolventDatum (Vec d) where
  solution mu f := t⁻¹ • pullback e (D.solution (dividedShift t ht mu) (pullback e.symm f))
  solution_add mu f g := by
    simp only [map_add, D.solution_add]
    ext x
    change t⁻¹ * (_ + _) = t⁻¹ * _ + t⁻¹ * _
    ring
  solution_smul mu r f := by
    simp only [map_smul, D.solution_smul, smul_smul]
    rw [mul_comm t⁻¹ r]
  solution_nonneg mu f hf x :=
    mul_nonneg (inv_nonneg.mpr ht.le)
      (D.solution_nonneg _ _ (fun y => hf (e.symm y)) (e x))
  norm_solution_le mu f := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),
      LinearIsometryEquiv.norm_map]
    calc
      t⁻¹ * ‖D.solution (dividedShift t ht mu) (pullback e.symm f)‖ ≤
          t⁻¹ * ((mu : ℝ) / t)⁻¹ * ‖f‖ := by
        have hh := D.norm_solution_le (dividedShift t ht mu) (pullback e.symm f)
        simp only [LinearIsometryEquiv.norm_map, dividedShift] at hh
        exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ht.le)).trans_eq (by ring)
      _ = (mu : ℝ)⁻¹ * ‖f‖ := by field_simp [ht.ne', (show 0 < (mu : ℝ) from mu.property).ne']
  solution_sub_solution mu nu f := by
    have hinv : pullback e.symm
        (t⁻¹ • pullback e (D.solution (dividedShift t ht nu) (pullback e.symm f))) =
        t⁻¹ • D.solution (dividedShift t ht nu) (pullback e.symm f) := by
      simp only [map_smul, ← pullback_symm, LinearIsometryEquiv.symm_apply_apply]
    rw [hinv, D.solution_smul, map_smul]
    ext x
    have hp := congrArg (fun g : C₀(Vec d, ℝ) => g (e x))
      (D.solution_sub_solution (dividedShift t ht mu) (dividedShift t ht nu) (pullback e.symm f))
    change D.solution (dividedShift t ht mu) (pullback e.symm f) (e x) -
        D.solution (dividedShift t ht nu) (pullback e.symm f) (e x) =
      ((nu : ℝ) / t - (mu : ℝ) / t) *
        D.solution (dividedShift t ht mu)
          (D.solution (dividedShift t ht nu) (pullback e.symm f)) (e x) at hp
    change t⁻¹ * D.solution (dividedShift t ht mu) (pullback e.symm f) (e x) -
        t⁻¹ * D.solution (dividedShift t ht nu) (pullback e.symm f) (e x) =
      ((nu : ℝ) - (mu : ℝ)) * (t⁻¹ * (t⁻¹ *
        D.solution (dividedShift t ht mu)
          (D.solution (dividedShift t ht nu) (pullback e.symm f)) (e x)))
    rw [← mul_sub, hp]
    ring

theorem transportedDatum_dense (D : C0ResolventDatum (Vec d))
    (hdense : ∀ mu, DenseRange (D.operator mu)) (e : Vec d ≃ₜ Vec d)
    (t : ℝ) (ht : 0 < t) : ∀ mu, DenseRange ((transportedDatum D e t ht).operator mu) := by
  intro mu
  let A : C₀(Vec d, ℝ) → C₀(Vec d, ℝ) := fun f => t⁻¹ • pullback e f
  have hA : Continuous A := continuous_const.smul (pullback e).continuous
  have hAsur : Function.Surjective A := by
    intro f
    refine ⟨t • pullback e.symm f, ?_⟩
    simp only [A, map_smul, ← pullback_symm, LinearIsometryEquiv.apply_symm_apply,
      smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  exact hAsur.denseRange.comp
    ((hdense (dividedShift t ht mu)).comp (pullback e.symm).surjective.denseRange
      (D.operator _).continuous) hA

/-- The literal local-to-physical affine coordinate map. -/
def physicalCoordinates (m : ℕ) (z : Vec d) : Vec d ≃ₜ Vec d :=
  (Homeomorph.smulOfNeZero ((3 : ℝ) ^ m) (pow_ne_zero _ (by norm_num))).trans
    (Homeomorph.addLeft z)

@[simp] theorem physicalCoordinates_apply (m : ℕ) (z x : Vec d) :
    physicalCoordinates m z x = z + (3 : ℝ) ^ m • x := rfl

@[simp] theorem physicalCoordinates_symm_apply (m : ℕ) (z x : Vec d) :
    (physicalCoordinates m z).symm x = ((3 : ℝ) ^ m)⁻¹ • (x - z) := by
  change ((3 : ℝ) ^ m)⁻¹ • (-z + x) = _
  rw [neg_add_eq_sub]

end SubdiffusiveProcess.Section10.PhysicalLocalTransport
