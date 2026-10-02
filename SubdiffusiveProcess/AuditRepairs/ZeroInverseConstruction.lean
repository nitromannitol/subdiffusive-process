import SubdiffusiveProcess.DirichletForm.FOTDomainHilbert
import SubdiffusiveProcess.DirichletForm.Resolvent
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-! Construction and variational identification of the inverse of a coercive closed form. -/

open MeasureTheory Filter Set Topology
open scoped RealInnerProductSpace

noncomputable section
namespace SubdiffusiveProcess.AuditRepairs

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- The bounded unweighted inverse already supplies a positive energy coercivity constant. -/
theorem norm_sq_le_form_of_dual_energy (E : DirichletForm.ClosedForm m)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (henergy : ∀ u, E.energy u = DirichletForm.dualEnergy G u)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain) :
    ‖u‖ ^ 2 ≤ (‖G‖ + 1) * E.form u u := by
  let C : ℝ := ‖G‖ + 1
  let t : ℝ := C⁻¹
  have hC : 0 < C := by dsimp [C]; positivity
  have ht : 0 < t := inv_pos.mpr hC
  have hcancel : C * t = 1 := mul_inv_cancel₀ hC.ne'
  have hinner : ⟪u, G u⟫ ≤ ‖G‖ * ‖u‖ ^ 2 := by
    calc
      ⟪u, G u⟫ ≤ ‖u‖ * ‖G u‖ := real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖G‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (G.le_opNorm u) (norm_nonneg _)
      _ = ‖G‖ * ‖u‖ ^ 2 := by ring
  have hv := DirichletForm.le_dualEnergy G (t • u) u
  rw [← henergy u, E.energy_of_mem hu] at hv
  have hvreal : 2 * ⟪t • u, u⟫ - ⟪t • u, G (t • u)⟫ ≤ E.form u u := by
    exact_mod_cast hv
  have hv' : 2 * t * ‖u‖ ^ 2 - t ^ 2 * ⟪u, G u⟫ ≤ E.form u u := by
    simpa only [map_smul, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, mul_assoc, pow_two] using hvreal
  have hcoef : t ≤ 2 * t - t ^ 2 * ‖G‖ := by
    have htc : t ^ 2 * C = t := by
      calc
        t ^ 2 * C = t * (C * t) := by ring
        _ = t := by rw [hcancel, mul_one]
    dsimp [C] at htc
    nlinarith [sq_nonneg t]
  have h1 := mul_le_mul_of_nonneg_left hinner (sq_nonneg t)
  have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖u‖)
  have hle : t * ‖u‖ ^ 2 ≤ E.form u u := by nlinarith only [hv', h1, h2]
  have hfinal := mul_le_mul_of_nonneg_left hle hC.le
  simpa only [← mul_assoc, hcancel, one_mul, C] using hfinal

/-- A positive lower energy bound constructs the actual zero resolvent. -/
theorem exists_zero_resolvent (E : DirichletForm.ClosedForm m)
    (C : ℝ) (hC : 0 < C)
    (hcoerc : ∀ u ∈ E.domain, ‖u‖ ^ 2 ≤ C * E.form u u) :
    ∃ G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m, DirichletForm.IsResolvent E 0 G := by
  let H := DirichletForm.FOTConstruction.EnergyHilbert.EnergySpace E
  let i : H →L[ℝ] Lp ℝ 2 m :=
    DirichletForm.FOTConstruction.EnergyHilbert.energyInclusion E
  let A : H →L[ℝ] H := (ContinuousLinearMap.adjoint i).comp i
  let T : H →L[ℝ] H := ContinuousLinearMap.id ℝ H - A
  let B : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp T
  have hB : ∀ x y : H, B x y = E.form x.1 y.1 := by
    intro x y
    change ⟪x - (ContinuousLinearMap.adjoint i) (i x), y⟫ = _
    rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
      DirichletForm.FOTConstruction.EnergyHilbert.energy_inner]
    change E.form x.1 y.1 + ⟪x.1, y.1⟫ - ⟪x.1, y.1⟫ = E.form x.1 y.1
    ring
  have hc : IsCoercive B := by
    refine ⟨(1 + C)⁻¹, inv_pos.mpr (by linarith), ?_⟩
    intro x
    rw [mul_assoc, ← pow_two]
    rw [hB, DirichletForm.FOTConstruction.EnergyHilbert.energy_norm_sq]
    have h := hcoerc x.1 x.2
    have hmul : (1 + C)⁻¹ * (1 + C) = 1 := inv_mul_cancel₀ (by linarith)
    have hle := mul_le_mul_of_nonneg_left
      (show E.form x.1 x.1 + ‖x.1‖ ^ 2 ≤ (1 + C) * E.form x.1 x.1 by
        nlinarith) (inv_nonneg.mpr (by linarith : 0 ≤ 1 + C))
    simpa only [← mul_assoc, hmul, one_mul] using hle
  let S := hc.continuousLinearEquivOfBilin
  let G := i.comp (S.symm.toContinuousLinearMap.comp (ContinuousLinearMap.adjoint i))
  refine ⟨G, ?_⟩
  intro f
  let x : H := S.symm ((ContinuousLinearMap.adjoint i) f)
  refine ⟨x.2, ?_⟩
  intro v hv
  let y : H := ⟨v, hv⟩
  have heq := hc.continuousLinearEquivOfBilin_apply x y
  have hx : S x = (ContinuousLinearMap.adjoint i) f := S.apply_symm_apply _
  rw [show hc.continuousLinearEquivOfBilin x = S x from rfl, hx,
    ContinuousLinearMap.adjoint_inner_left, hB] at heq
  change ⟪f, v⟫ = E.form (G f) v at heq
  simpa only [zero_mul, zero_add] using heq.symm

/-- The dense form domain makes a zero resolvent injective. -/
theorem zero_resolvent_injective {E : DirichletForm.ClosedForm m}
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : DirichletForm.IsResolvent E 0 G) :
    Function.Injective G := by
  intro f g hfg
  have hinner : ∀ v ∈ E.domain, ⟪f - g, v⟫ = 0 := by
    intro v hv
    have hf := hG.eq f hv
    have hg := hG.eq g hv
    rw [hfg] at hf
    simp only [zero_mul, zero_add] at hf hg
    rw [inner_sub_left, ← hf, ← hg, sub_self]
  have hall : ∀ v : Lp ℝ 2 m, ⟪f - g, v⟫ = 0 := by
    intro v
    exact E.denseDomain.induction hinner (isClosed_eq (by fun_prop) continuous_const) v
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp (hall (f - g)))

/-- The quadratic inverse response is the maximum of the dual variational functional. -/
theorem zero_resolvent_isLUB {E : DirichletForm.ClosedForm m}
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : DirichletForm.IsResolvent E 0 G)
    (f : Lp ℝ 2 m) :
    IsLUB {t : ℝ | ∃ u : Lp ℝ 2 m,
      u ∈ E.domain ∧ t = 2 * ⟪f, u⟫ - E.form u u} ⟪f, G f⟫ := by
  have hmem := hG.mem_domain f
  have hdiag : E.form (G f) (G f) = ⟪f, G f⟫ := by
    simpa only [zero_mul, zero_add] using hG.eq f hmem
  have hupper : ∀ u ∈ E.domain, 2 * ⟪f, u⟫ - E.form u u ≤ ⟪f, G f⟫ := by
    intro u hu
    have hcross : E.form (G f) u = ⟪f, u⟫ := by
      simpa only [zero_mul, zero_add] using hG.eq f hu
    have hnn := E.form_nonneg (u - G f) (E.domain.sub_mem hu hmem)
    have hsub := E.form_sub_self hu hmem
    have hsym := E.form_symm u hu (G f) hmem
    rw [hsub, hsym, hcross, hdiag] at hnn
    linarith
  refine ⟨?_, ?_⟩
  · rintro t ⟨u, hu, rfl⟩
    exact hupper u hu
  · intro t ht
    apply ht
    refine ⟨G f, hmem, ?_⟩
    rw [hdiag]
    ring

end SubdiffusiveProcess.AuditRepairs
