module

public import SubdiffusiveProcess.Paper.prop_conc_strip_deletion_estimate

@[expose] public section

/-! The common form order bounds both normalized total masses uniformly in the endpoints.
The difference mass carries the square of the endpoint gap, without a growth assumption for that mass. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

variable {C0 : ℝ} {d : ℕ} {Q : Opens (SpatialCoordinates d)}
  {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {slopes : Finset (Fin d → ℝ)}
  {E F Eg Fg : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
    (volume.restrict (Q : Set (SpatialCoordinates d)))}
  {GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E} {GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F}
  {GammaEg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg} {GammaFg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Fg}
  {V0 : Submodule ℝ (DomainL2 Q)} {m M c : ℝ}
  {g : SpatialCoordinates d → ℝ} {B : Set (SpatialCoordinates d)} {G : ℝ}
  {uE uF uEg uFg : (Fin d → ℝ) → DomainL2 Q}
  {QE QF QEg QFg : QuadraticForm ℝ (Fin d → ℝ)} {D Dg nu ze : ℝ}
  {IE IF : DomainL2 Q → DomainL2 Q → ℝ}


/-- Both normalized masses in relative variation are controlled by dimension and the endpoint interval. -/
theorem prop_conc_relative_total_mass
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF) :
    nu ≤ (1 + C0 ^ 2) * ((2 : ℝ) ^ d * ∑ p ∈ slopes, ∑ i : Fin d, (p i) ^ 2) ∧
    ze ≤ (C0 ^ 2 * ((2 : ℝ) ^ d * ∑ p ∈ slopes, ∑ i : Fin d, (p i) ^ 2)) * (M - m) ^ 2 := by
  refine ⟨?_, aux_prop_conc_strip_deletion_estimate_ctx_zeta_bound ctx⟩
  let q : Set (SpatialCoordinates d) := centeredCube z r hr
  have hq := (centeredCube z r hr).isOpen.measurableSet
  have hC0 : 0 < C0 := zero_lt_one.trans_le ctx.hC0
  have hm : 0 < m := (inv_pos.mpr hC0).trans_le ctx.hm
  have hM : 0 ≤ M := (hm.trans_le ctx.hmM).le
  have hinv : m⁻¹ ≤ C0 := (inv_le_comm₀ hm hC0).mpr ctx.hm
  have hratio : m⁻¹ * M ≤ C0 ^ 2 := by
    simpa only [pow_two] using mul_le_mul hinv ctx.hM hM hC0.le
  have hQ0 (p : Fin d → ℝ) : 0 ≤ QE p := by rw [ctx.hQE]; exact ENNReal.toReal_nonneg
  have hF (p : Fin d → ℝ) : (GammaE.measure (uF p) B).toReal ≤ C0 ^ 2 * QE p := by
    have huFE : uF p ∈ E.domain := ctx.hdomEF.symm ▸ ctx.huF p
    have hmin := ctx.hminF p (uE p) (ctx.hdomEF ▸ ctx.huE p)
      (by simpa only [sub_self] using V0.zero_mem)
    have hFu : (GammaF.measure (uF p) q).toReal ≤ M * QE p := by
      exact (hmin.trans (ctx.horder (uE p) (ctx.huE p) q hq).2).trans_eq (by rw [ctx.hQE])
    calc
      _ ≤ (GammaE.measure (uF p) q).toReal := GammaE.toReal_measure_mono huFE ctx.hBq
      _ ≤ m⁻¹ * (GammaF.measure (uF p) q).toReal :=
        (le_inv_mul_iff₀ hm).mpr (ctx.horder (uF p) huFE q hq).1
      _ ≤ m⁻¹ * (M * QE p) := mul_le_mul_of_nonneg_left hFu (inv_nonneg.mpr hm.le)
      _ = (m⁻¹ * M) * QE p := (mul_assoc _ _ _).symm
      _ ≤ C0 ^ 2 * QE p := mul_le_mul_of_nonneg_right hratio (hQ0 p)
  have hpair (p : Fin d → ℝ) : ((GammaE.measure (uE p) + GammaE.measure (uF p)) B).toReal ≤
      (1 + C0 ^ 2) * QE p := by
    rw [Measure.add_apply, ENNReal.toReal_add (GammaE.measure_ne_top (ctx.huE p) B)
      (GammaE.measure_ne_top (ctx.hdomEF.symm ▸ ctx.huF p) B)]
    have he := (GammaE.toReal_measure_mono (ctx.huE p) ctx.hBq).trans_eq (ctx.hQE p).symm
    nlinarith only [he, hF p]
  let A : ℝ := (2 : ℝ) ^ d * ∑ p ∈ slopes, ∑ i : Fin d, (p i) ^ 2
  have hsum : (∑ p ∈ slopes, QE p) ≤ A * D := by
    calc
      _ ≤ ∑ p ∈ slopes, ((2 : ℝ) ^ d * (∑ i : Fin d, (p i) ^ 2) * D) :=
        Finset.sum_le_sum fun p _ => aux_relative_response_variation_quad_bound d QE hQ0 D ctx.hDdef p
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [ctx.hnudef]
  calc
    _ ≤ D⁻¹ * ∑ p ∈ slopes, ((1 + C0 ^ 2) * QE p) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hpair p) (inv_nonneg.mpr ctx.hD.le)
    _ = D⁻¹ * ((1 + C0 ^ 2) * ∑ p ∈ slopes, QE p) := by
      congr 1
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ D⁻¹ * ((1 + C0 ^ 2) * (A * D)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (inv_nonneg.mpr ctx.hD.le)
    _ = (1 + C0 ^ 2) * A := by field_simp [ctx.hD.ne']

end
end SubdiffusiveProcess.Paper
