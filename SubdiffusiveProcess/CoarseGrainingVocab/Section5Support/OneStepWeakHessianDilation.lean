module

public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianTranslation

@[expose] public section

/-!
# Dilation covariance of weak Hessians

This is the dilation companion to the translation API in
`HessianTranslation`.  It is needed to push the fixed-cube harmonic Hessian
witness onto the arbitrary translated axis cubes occurring in the one-step
Neumann comparison.
-/

open MeasureTheory
open scoped Pointwise

namespace Homogenization

noncomputable section

namespace HasWeakPartialDerivOn

/-- A weak partial derivative transported by the positive dilation
`x ↦ a • x`.  The derivative gains the expected factor `a⁻¹`. -/
theorem dilateSet {d : ℕ} {U V : Set (Vec d)} {i : Fin d}
    {u g : Vec d → ℝ} {a : ℝ} (ha : 0 < a) (hV : V = a • U)
    (h : HasWeakPartialDerivOn U i u g) :
    HasWeakPartialDerivOn V i
      (fun x ↦ u (a⁻¹ • x)) (fun x ↦ a⁻¹ * g (a⁻¹ • x)) := by
  intro φ hφ hφ_supp hφ_sub
  let T : Vec d → Vec d := fun x ↦ a⁻¹ • x
  let ψ : Vec d → ℝ := fun y ↦ φ (a • y)
  have ha_ne : a ≠ 0 := ha.ne'
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ, Function.comp_def] using! hφ.comp (contDiff_const_smul a)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (φ ∘ Homeomorph.smulOfNeZero a ha_ne)
    simpa [ψ, Function.comp] using
      hφ_supp.comp_homeomorph (Homeomorph.smulOfNeZero a ha_ne)
  have hψ_sub : tsupport ψ ⊆ U := by
    intro y hy
    have hy' : a • y ∈ tsupport φ := by
      rw [show ψ = φ ∘ Homeomorph.smulOfNeZero a ha_ne by rfl,
        tsupport_comp_eq_preimage φ (Homeomorph.smulOfNeZero a ha_ne)] at hy
      exact hy
    have hyV : a • y ∈ V := hφ_sub hy'
    rw [hV] at hyV
    simpa [Set.mem_smul_set_iff_inv_smul_mem, ha_ne] using hyV
  have hweak := h ψ hψ_smooth hψ_supp hψ_sub
  have hderivψ : ∀ y : Vec d,
      (fderiv ℝ ψ y) (basisVec i) =
        a * (fderiv ℝ φ (a • y)) (basisVec i) := by
    intro y
    have hderiv :
        fderiv ℝ (fun z : Vec d ↦ φ (a • z)) y =
          a • fderiv ℝ φ (a • y) := by
      simpa [ψ] using (fderiv_comp_smul (𝕜 := ℝ) (f := φ) (x := y) a)
    simpa [smul_eq_mul] using
      congrArg (fun L : Vec d →L[ℝ] ℝ ↦ L (basisVec i)) hderiv
  have hmain :
      a * ∫ y in U, u y * (fderiv ℝ φ (a • y)) (basisVec i)
          ∂MeasureTheory.volume =
        -∫ y in U, g y * φ (a • y) ∂MeasureTheory.volume := by
    have hfun :
        (fun y ↦ u y * (fderiv ℝ ψ y) (basisVec i)) =
          fun y ↦ a * (u y * (fderiv ℝ φ (a • y)) (basisVec i)) := by
      funext y
      rw [hderivψ y]
      ring
    rw [hfun, MeasureTheory.integral_const_mul] at hweak
    simpa [ψ] using hweak
  have hchange_left :
      ∫ y in U, u y * (fderiv ℝ φ (a • y)) (basisVec i)
          ∂MeasureTheory.volume =
        (a ^ d)⁻¹ * ∫ x in V,
          u (T x) * (fderiv ℝ φ x) (basisVec i)
            ∂MeasureTheory.volume := by
    rw [hV]
    simpa only [T, smul_smul, inv_mul_cancel₀ ha_ne, one_smul,
      Module.finrank_fin_fun, smul_eq_mul] using!
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume)
        (f := fun x : Vec d ↦
          u (T x) * (fderiv ℝ φ x) (basisVec i))
        (s := U) ha)
  have hchange_right :
      ∫ y in U, g y * φ (a • y) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ * ∫ x in V, g (T x) * φ x ∂MeasureTheory.volume := by
    rw [hV]
    simpa only [T, smul_smul, inv_mul_cancel₀ ha_ne, one_smul,
      Module.finrank_fin_fun, smul_eq_mul] using!
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume)
        (f := fun x : Vec d ↦ g (T x) * φ x)
        (s := U) ha)
  have hpow_ne : a ^ d ≠ 0 := (pow_pos ha d).ne'
  have hchange_right_scaled :
      ∫ x in V, g (T x) * φ x ∂MeasureTheory.volume =
        (a ^ d) * ∫ y in U, g y * φ (a • y) ∂MeasureTheory.volume := by
    rw [hchange_right]
    field_simp [hpow_ne]
  calc
    ∫ x in V, u (a⁻¹ • x) * (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume =
        (a ^ d) * ∫ y in U,
          u y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume := by
      change (∫ x in V, u (T x) * (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume) = _
      rw [hchange_left]
      field_simp [hpow_ne]
    _ = (a ^ d) * (a⁻¹ *
          (a * ∫ y in U,
            u y * (fderiv ℝ φ (a • y)) (basisVec i)
              ∂MeasureTheory.volume)) := by
      field_simp [ha_ne]
    _ = (a ^ d) * (a⁻¹ *
          (-∫ y in U, g y * φ (a • y) ∂MeasureTheory.volume)) := by
      rw [hmain]
    _ = -∫ x in V, a⁻¹ * g (a⁻¹ • x) * φ x
          ∂MeasureTheory.volume := by
      rw [show (fun x ↦ a⁻¹ * g (a⁻¹ • x) * φ x) =
          (fun x ↦ a⁻¹ * (g (a⁻¹ • x) * φ x)) by
        funext x
        ring]
      rw [MeasureTheory.integral_const_mul]
      change _ = -(a⁻¹ * ∫ x in V, g (T x) * φ x
        ∂MeasureTheory.volume)
      rw [hchange_right_scaled]
      ring

end HasWeakPartialDerivOn

namespace HasWeakHessianOn

variable {d : ℕ} {U V : Set (Vec d)} {u : H1Function U}

/-- Push a weak Hessian witness through the normalized `H¹` dilation. -/
noncomputable def dilateSet (H : HasWeakHessianOn U u) {a : ℝ}
    (ha : 0 < a) (hV : V = a • U) :
    HasWeakHessianOn V (u.dilateSet ha hV) where
  hess := fun i j x ↦ a⁻¹ * H.hess i j (a⁻¹ • x)
  hess_memL2 := by
    intro i j
    let T : Vec d → Vec d := fun x ↦ a⁻¹ • x
    have hmap := map_smul_volume_restrict (d := d) (a := a⁻¹)
      (inv_pos.mpr ha) V
    have hpre : a⁻¹ • V = U := by
      rw [hV]
      ext x
      simp [ha.ne']
    have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict V) :=
      (measurable_const_smul a⁻¹).aemeasurable
    have hH_map : MeasureTheory.MemLp (H.hess i j) 2
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) := by
      rw [hmap, hpre]
      exact (H.hess_memL2 i j).smul_measure ENNReal.ofReal_ne_top
    exact (MeasureTheory.MemLp.comp_of_map hH_map hT_meas).const_mul a⁻¹
  weak_second := by
    intro i j
    simpa [H1Function.dilateSet_grad, Pi.smul_apply, smul_eq_mul] using
      (H.weak_second i j).dilateSet ha hV

@[simp] theorem dilateSet_hess (H : HasWeakHessianOn U u) {a : ℝ}
    (ha : 0 < a) (hV : V = a • U) (i j : Fin d) (x : Vec d) :
    (H.dilateSet ha hV).hess i j x = a⁻¹ * H.hess i j (a⁻¹ • x) :=
  rfl

end HasWeakHessianOn

namespace HasWeakHessianOn

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

/-- Push a weak Hessian through a positive dilation and then a translation. -/
noncomputable def dilateTranslate (H : HasWeakHessianOn U u) {a : ℝ}
    (ha : 0 < a) (z : Vec d) :
    HasWeakHessianOn (translateSet z (a • U))
      ((u.dilateSet ha rfl).translate z) :=
  (H.dilateSet ha rfl).translate z

@[simp] theorem dilateTranslate_hess (H : HasWeakHessianOn U u) {a : ℝ}
    (ha : 0 < a) (z : Vec d) (i j : Fin d) (x : Vec d) :
    (H.dilateTranslate ha z).hess i j x =
      a⁻¹ * H.hess i j (a⁻¹ • (x - z)) :=
  rfl

end HasWeakHessianOn

end

end Homogenization
