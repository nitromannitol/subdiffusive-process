module

public import SubdiffusiveProcess.Paper.lem_relvar
public import SubdiffusiveProcess.Paper.relative_response_variation
public import Mathlib.Tactic

@[expose] public section

/-! Normalized masked-core masses controlled by the original core and strip measures.
These extracted deterministic/probabilistic estimates do not supply the model-specific influence bound. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

variable {C0 : ℝ} {d : ℕ} {Q : Opens (SpatialCoordinates d)}
  {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {slopes : Finset (Fin d → ℝ)}
  {E F Eg Fg : DirichletForm.ClosedForm
    (volume.restrict (Q : Set (SpatialCoordinates d)))}
  {GammaE : DirichletForm.EnergyMeasure E} {GammaF : DirichletForm.EnergyMeasure F}
  {GammaEg : DirichletForm.EnergyMeasure Eg} {GammaFg : DirichletForm.EnergyMeasure Fg}
  {V0 : Submodule ℝ (DomainL2 Q)} {m M c : ℝ}
  {g : SpatialCoordinates d → ℝ} {B : Set (SpatialCoordinates d)} {G : ℝ}
  {uE uF uEg uFg : (Fin d → ℝ) → DomainL2 Q}
  {QE QF QEg QFg : QuadraticForm ℝ (Fin d → ℝ)} {D Dg nu ze : ℝ}
  {IE IF : DomainL2 Q → DomainL2 Q → ℝ}

/-- The core energy after deleting strips, for the E-minimizer in the
actual limiting weighted-form context (paper 3427–3431). -/
theorem aux_prop_conc_masked_core_mass_masked_E_core
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (p : Fin d → ℝ) (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A)
    (hAq : A ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    (GammaEg.measure (uEg p) A).toReal ≤
      2 * Real.exp G * (GammaE.measure (uE p) A).toReal +
        2 * (G ^ 2 * Real.exp (3 * G)) * (GammaE.measure (uE p) B).toReal := by
  have hue : uE p ∈ Eg.domain := ctx.hdomEg.symm ▸ ctx.huE p
  have hud : uEg p - uE p ∈ Eg.domain := Eg.domain.sub_mem (ctx.huEg p) hue
  have htri := aux_relative_response_variation_measure_sub_le GammaEg
    (ctx.huEg p) hue hA
  have hweight := (aux_lem_relvar_weighted_measure_bounds GammaE GammaEg ctx.hdomEg
    g ctx.hg G (fun x => ctx.hG.1 ⟨x, rfl⟩) ctx.hweightE (ctx.huE p) hA).2
  have hlocal : (GammaEg.measure (uEg p - uE p) A).toReal ≤
      (GammaEg.measure (uEg p - uE p)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
    ENNReal.toReal_mono (GammaEg.measure_ne_top hud _) (measure_mono hAq)
  have hpert := (aux_lem_relvar_cor14_pointwise ctx p).1
  calc
    _ ≤ 2 * (GammaEg.measure (uE p) A).toReal +
        2 * (GammaEg.measure (uEg p - uE p) A).toReal := htri
    _ ≤ 2 * (Real.exp G * (GammaE.measure (uE p) A).toReal) +
        2 * (G ^ 2 * Real.exp (3 * G) * (GammaE.measure (uE p) B).toReal) :=
      add_le_add (mul_le_mul_of_nonneg_left hweight (by norm_num))
        (mul_le_mul_of_nonneg_left (hlocal.trans hpert) (by norm_num))
    _ = _ := by ring

/- The following algebra keeps the energy measures opaque. -/
theorem aux_prop_conc_masked_core_mass_masked_pair_core
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (CL : ℝ) (hCL : 0 ≤ CL) (p : Fin d → ℝ)
    (hz : (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      CL * G ^ 2 * Real.exp (CL * G) *
        ((GammaE.measure (uF p - uE p) B).toReal +
          (M - m) ^ 2 * (GammaE.measure (uE p) B).toReal))
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A)
    (hAq : A ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    (GammaEg.measure (uEg p) A).toReal + (GammaEg.measure (uFg p) A).toReal ≤
      2 * Real.exp G *
        ((GammaE.measure (uE p) A).toReal + (GammaE.measure (uF p) A).toReal) +
      (6 * G ^ 2 * Real.exp (3 * G) +
        4 * CL * G ^ 2 * Real.exp (CL * G) * (2 + C0 ^ 2)) *
        ((GammaE.measure (uE p) B).toReal + (GammaE.measure (uF p) B).toReal) := by
  have huF : uF p ∈ E.domain := ctx.hdomEF.symm ▸ ctx.huF p
  have huFg : uFg p ∈ Eg.domain := ctx.hdomEg.symm ▸ (ctx.hdomFg ▸ ctx.huFg p)
  have huF' : uF p ∈ Eg.domain := ctx.hdomEg.symm ▸ huF
  have huE' : uE p ∈ Eg.domain := ctx.hdomEg.symm ▸ ctx.huE p
  have hvF : uFg p - uF p ∈ Eg.domain := Eg.domain.sub_mem huFg huF'
  have hvE : uEg p - uE p ∈ Eg.domain := Eg.domain.sub_mem (ctx.huEg p) huE'
  have hzmem := Eg.domain.sub_mem hvF hvE
  have htriF := aux_relative_response_variation_measure_sub_le GammaEg huFg huF' hA
  have htriV := aux_relative_response_variation_measure_sub_le GammaEg hvF hvE hA
  have hweight := (aux_lem_relvar_weighted_measure_bounds GammaE GammaEg ctx.hdomEg
    g ctx.hg G (fun x => ctx.hG.1 ⟨x, rfl⟩) ctx.hweightE huF hA).2
  have hvEA := (GammaEg.toReal_measure_mono hvE hAq).trans
    (aux_lem_relvar_cor14_pointwise ctx p).1
  have hzA := (GammaEg.toReal_measure_mono hzmem hAq).trans hz
  have hw := aux_lem_relvar_measure_sub_le GammaE huF (ctx.huE p) ctx.hB
  have hC0 : 0 ≤ C0 := le_trans zero_le_one ctx.hC0
  have hm : 0 < m := lt_of_lt_of_le
    (inv_pos.mpr (lt_of_lt_of_le zero_lt_one ctx.hC0)) ctx.hm
  have hgap : 0 ≤ M - m := sub_nonneg.mpr ctx.hmM
  have hgapC : M - m ≤ C0 := by linarith only [hm, ctx.hM]
  have hgap2 : (M - m) ^ 2 ≤ C0 ^ 2 := (sq_le_sq₀ hgap hC0).2 hgapC
  have heB : 0 ≤ (GammaE.measure (uE p) B).toReal := ENNReal.toReal_nonneg
  have hfB : 0 ≤ (GammaE.measure (uF p) B).toReal := ENNReal.toReal_nonneg
  have hsz : (GammaE.measure (uF p - uE p) B).toReal +
        (M - m) ^ 2 * (GammaE.measure (uE p) B).toReal ≤
      (2 + C0 ^ 2) *
        ((GammaE.measure (uE p) B).toReal + (GammaE.measure (uF p) B).toReal) := by
    nlinarith only [hw, mul_le_mul_of_nonneg_right hgap2 heB,
      mul_nonneg (sq_nonneg C0) hfB]
  have hzA' := hzA.trans (mul_le_mul_of_nonneg_left hsz
    (mul_nonneg (mul_nonneg hCL (sq_nonneg G)) (Real.exp_nonneg _)))
  have hE := aux_prop_conc_masked_core_mass_masked_E_core ctx p A hA hAq
  have hF : (GammaEg.measure (uFg p) A).toReal ≤
      2 * Real.exp G * (GammaE.measure (uF p) A).toReal +
        4 * (G ^ 2 * Real.exp (3 * G)) * (GammaE.measure (uE p) B).toReal +
        4 * (CL * G ^ 2 * Real.exp (CL * G)) * (2 + C0 ^ 2) *
          ((GammaE.measure (uE p) B).toReal + (GammaE.measure (uF p) B).toReal) := by
    nlinarith only [htriF, htriV, hweight, hvEA, hzA']
  nlinarith only [hE, hF,
    mul_nonneg (mul_nonneg (sq_nonneg G) (Real.exp_nonneg (3 * G))) hfB]

/-- Extracted normalize masked mass estimate. -/
theorem aux_prop_conc_masked_core_mass_normalize_masked_mass
    (D Dg G Sg S T a b : ℝ) (hD : 0 < D) (hSg : 0 ≤ Sg)
    (hden : Real.exp (-G) * D ≤ Dg) (hnum : Sg ≤ a * S + b * T) :
    Dg⁻¹ * Sg ≤ Real.exp G * (a * (D⁻¹ * S) + b * (D⁻¹ * T)) := by
  have hinv : Dg⁻¹ ≤ Real.exp G * D⁻¹ := by
    calc
      _ ≤ (Real.exp (-G) * D)⁻¹ := inv_anti₀ (mul_pos (Real.exp_pos _) hD) hden
      _ = _ := by rw [mul_inv_rev, ← Real.exp_neg, neg_neg, mul_comm]
  calc
    Dg⁻¹ * Sg ≤ (Real.exp G * D⁻¹) * Sg := mul_le_mul_of_nonneg_right hinv hSg
    _ ≤ (Real.exp G * D⁻¹) * (a * S + b * T) :=
      mul_le_mul_of_nonneg_left hnum (mul_nonneg (Real.exp_nonneg _) (inv_nonneg.mpr hD.le))
    _ = _ := by ring


/-- Absorb the quadratic layer norm into an exponential, without losing the
normalization factor from the perturbed denominator. -/
theorem aux_prop_conc_masked_core_mass_masked_envelope (C0 CL G : ℝ) (hCL : 0 ≤ CL) (hG : 0 ≤ G) :
    let C := 10 + CL + 4 * CL * (2 + C0 ^ 2)
    Real.exp G * (2 * Real.exp G) ≤ C * Real.exp (C * G) ∧
      Real.exp G * (6 * G ^ 2 * Real.exp (3 * G) +
        4 * CL * G ^ 2 * Real.exp (CL * G) * (2 + C0 ^ 2)) ≤
        C * Real.exp (C * G) := by
  let C := 10 + CL + 4 * CL * (2 + C0 ^ 2)
  change _ ≤ C * Real.exp (C * G) ∧ _ ≤ C * Real.exp (C * G)
  have hcoef : 0 ≤ 4 * CL * (2 + C0 ^ 2) := by positivity
  have hC2 : 2 ≤ C := by dsimp [C]; linarith only [hCL, hcoef]
  have hC6 : 6 ≤ C := by dsimp [C]; linarith only [hCL, hcoef]
  have hCL3 : CL + 3 ≤ C := by dsimp [C]; linarith only [hcoef]
  have hcoeff : 6 + 4 * CL * (2 + C0 ^ 2) ≤ C := by
    dsimp [C]; linarith only [hCL]
  have hmono (a : ℝ) (ha : a ≤ C) : Real.exp (a * G) ≤ Real.exp (C * G) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hG)
  have hs (a : ℝ) : Real.exp G * (G ^ 2 * Real.exp (a * G)) ≤
      Real.exp ((a + 3) * G) := by
    calc
      _ ≤ Real.exp G * (Real.exp (2 * G) * Real.exp (a * G)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (aux_lem_relvar_sq_exp G hG) (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  constructor
  · calc
      Real.exp G * (2 * Real.exp G) = 2 * Real.exp (2 * G) := by
        rw [show (2 : ℝ) * G = G + G by ring, Real.exp_add]; ring
      _ ≤ 2 * Real.exp (C * G) := mul_le_mul_of_nonneg_left (hmono 2 hC2) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2 (Real.exp_nonneg _)
  · have h3 : Real.exp G * (G ^ 2 * Real.exp (3 * G)) ≤ Real.exp (C * G) :=
      (hs 3).trans (hmono (3 + 3) (by norm_num; exact hC6))
    have hcl := (hs CL).trans (hmono (CL + 3) hCL3)
    calc
      _ = 6 * (Real.exp G * (G ^ 2 * Real.exp (3 * G))) +
          (4 * CL * (2 + C0 ^ 2)) *
            (Real.exp G * (G ^ 2 * Real.exp (CL * G))) := by ring
      _ ≤ 6 * Real.exp (C * G) + (4 * CL * (2 + C0 ^ 2)) * Real.exp (C * G) :=
        add_le_add (mul_le_mul_of_nonneg_left h3 (by norm_num))
          (mul_le_mul_of_nonneg_left hcl hcoef)
      _ = (6 + 4 * CL * (2 + C0 ^ 2)) * Real.exp (C * G) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)


/-- The normalized masked core mass of paper 3429–3431. The constant is
chosen before the dimension, forms, layer, endpoint gap, and core. -/
theorem aux_prop_conc_masked_core_mass_masked_core_sum (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {d : ℕ} {Q : Opens (SpatialCoordinates d)}
  {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {slopes : Finset (Fin d → ℝ)}
  {E F Eg Fg : DirichletForm.ClosedForm
    (volume.restrict (Q : Set (SpatialCoordinates d)))}
  {GammaE : DirichletForm.EnergyMeasure E} {GammaF : DirichletForm.EnergyMeasure F}
  {GammaEg : DirichletForm.EnergyMeasure Eg} {GammaFg : DirichletForm.EnergyMeasure Fg}
  {V0 : Submodule ℝ (DomainL2 Q)} {m M c : ℝ}
  {g : SpatialCoordinates d → ℝ} {B : Set (SpatialCoordinates d)} {G : ℝ}
  {uE uF uEg uFg : (Fin d → ℝ) → DomainL2 Q}
  {QE QF QEg QFg : QuadraticForm ℝ (Fin d → ℝ)} {D Dg nu ze : ℝ}
  {IE IF : DomainL2 Q → DomainL2 Q → ℝ}
    (_ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (A : Set (SpatialCoordinates d)) (_hA : MeasurableSet A)
    (_hAq : A ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))),
    Dg⁻¹ * (∑ p ∈ slopes,
      ((GammaEg.measure (uEg p) A).toReal + (GammaEg.measure (uFg p) A).toReal)) ≤
      C * Real.exp (C * G) *
        (D⁻¹ * (∑ p ∈ slopes,
          ((GammaE.measure (uE p) A).toReal + (GammaE.measure (uF p) A).toReal)) + nu) := by
  obtain ⟨CL, hCL, hL⟩ := lem_relvar_localized_weighted_minimizer_difference C0 hC0
  let C := 10 + CL + 4 * CL * (2 + C0 ^ 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro d Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg GammaFg V0 m M c g B G
    uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF ctx A hA hAq
  have hG : 0 ≤ G := (abs_nonneg (g 0)).trans (ctx.hG.1 ⟨0, rfl⟩)
  have hpt (p : Fin d → ℝ) (hp : p ∈ slopes) :=
    hL d ctx.hd slopes ctx.hslopes Q z r hr ctx.hQ ctx.hinside E F Eg Fg
      GammaE GammaF GammaEg GammaFg ctx.hdomEF ctx.hdomEg ctx.hdomFg V0 ctx.hzero
      m M c ctx.hm ctx.hmM ctx.hM ctx.hmc ctx.hcM ctx.horder
      g ctx.hg B ctx.hB ctx.hBq ctx.hsupp G ctx.hG ctx.hbdd
      ctx.hweightE ctx.hweightF ctx.hweightE_cross ctx.hweightF_cross
      uE uF uEg uFg ctx.huE ctx.huF ctx.huEg ctx.huFg
      ctx.htraceF ctx.htraceEg ctx.htraceFg ctx.hminE ctx.hminF ctx.hminEg ctx.hminFg p hp
  have hsum := Finset.sum_le_sum (s := slopes)
    (fun p hp => aux_prop_conc_masked_core_mass_masked_pair_core ctx CL hCL.le p (hpt p hp) A hA hAq)
  conv_rhs at hsum => rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hnorm := aux_prop_conc_masked_core_mass_normalize_masked_mass D Dg G _ _ _ _ _ ctx.hD
    (Finset.sum_nonneg (fun _ _ => add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
    (aux_lem_relvar_Dg_bounds ctx).1 hsum
  have hnu : D⁻¹ * (∑ p ∈ slopes,
      ((GammaE.measure (uE p) B).toReal + (GammaE.measure (uF p) B).toReal)) = nu := by
    rw [ctx.hnudef]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [Measure.add_apply, ENNReal.toReal_add (GammaE.measure_ne_top (ctx.huE p) B)
      (GammaE.measure_ne_top (ctx.hdomEF.symm ▸ ctx.huF p) B)]
  rw [hnu] at hnorm
  have hnu0 := (aux_lem_relvar_nu_basics ctx).1
  have hA0 : 0 ≤ D⁻¹ * (∑ p ∈ slopes,
      ((GammaE.measure (uE p) A).toReal + (GammaE.measure (uF p) A).toReal)) :=
    mul_nonneg (inv_nonneg.mpr ctx.hD.le)
      (Finset.sum_nonneg (fun _ _ => add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
  obtain ⟨ha, hb⟩ := aux_prop_conc_masked_core_mass_masked_envelope C0 CL G hCL.le hG
  refine hnorm.trans ?_
  calc
    _ = (Real.exp G * (2 * Real.exp G)) *
        (D⁻¹ * (∑ p ∈ slopes,
          ((GammaE.measure (uE p) A).toReal + (GammaE.measure (uF p) A).toReal))) +
        (Real.exp G * (6 * G ^ 2 * Real.exp (3 * G) +
          4 * CL * G ^ 2 * Real.exp (CL * G) * (2 + C0 ^ 2))) * nu := by ring
    _ ≤ C * Real.exp (C * G) *
        (D⁻¹ * (∑ p ∈ slopes,
          ((GammaE.measure (uE p) A).toReal + (GammaE.measure (uF p) A).toReal))) +
        (C * Real.exp (C * G)) * nu :=
      add_le_add (mul_le_mul_of_nonneg_right ha hA0) (mul_le_mul_of_nonneg_right hb hnu0)
    _ = _ := by ring


/-- Extracted normalized pair mass estimate. -/
theorem aux_prop_conc_masked_core_mass_normalized_pair_mass
    {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}
    {E : DirichletForm.ClosedForm μ} (Gamma : DirichletForm.EnergyMeasure E)
    (u v : ι → Lp ℝ 2 μ) (hu : ∀ i, u i ∈ E.domain) (hv : ∀ i, v i ∈ E.domain)
    (s : Finset ι) (D : ℝ) (hD : 0 < D) (A : Set X) :
    ((ENNReal.ofReal D⁻¹ • (∑ i ∈ s,
      (Gamma.measure (u i) + Gamma.measure (v i)))) A).toReal =
      D⁻¹ * ∑ i ∈ s, ((Gamma.measure (u i) A).toReal + (Gamma.measure (v i) A).toReal) := by
  rw [aux_relative_response_variation_normalized_sum_toReal D hD s _ A (by
    intro i _
    exact (ENNReal.add_lt_top.mpr ⟨(Gamma.measure_ne_top (hu i) A).lt_top,
      (Gamma.measure_ne_top (hv i) A).lt_top⟩).ne)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.add_apply, ENNReal.toReal_add (Gamma.measure_ne_top (hu i) A)
    (Gamma.measure_ne_top (hv i) A)]


/-- Strip deletion at the limiting-form level, expressed using the paper's
literal normalized energy measures. No regularity of the difference measure
is used. The constant depends only on C0. -/
theorem prop_conc_masked_core_mass (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {d : ℕ} {Q : Opens (SpatialCoordinates d)}
  {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {slopes : Finset (Fin d → ℝ)}
  {E F Eg Fg : DirichletForm.ClosedForm
    (volume.restrict (Q : Set (SpatialCoordinates d)))}
  {GammaE : DirichletForm.EnergyMeasure E} {GammaF : DirichletForm.EnergyMeasure F}
  {GammaEg : DirichletForm.EnergyMeasure Eg} {GammaFg : DirichletForm.EnergyMeasure Fg}
  {V0 : Submodule ℝ (DomainL2 Q)} {m M c : ℝ}
  {g : SpatialCoordinates d → ℝ} {B : Set (SpatialCoordinates d)} {G : ℝ}
  {uE uF uEg uFg : (Fin d → ℝ) → DomainL2 Q}
  {QE QF QEg QFg : QuadraticForm ℝ (Fin d → ℝ)} {D Dg nu ze : ℝ}
  {IE IF : DomainL2 Q → DomainL2 Q → ℝ}
    (_ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (A : Set (SpatialCoordinates d)) (_hA : MeasurableSet A)
    (_hAq : A ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))),
    let nu0 : Measure (SpatialCoordinates d) := ENNReal.ofReal D⁻¹ •
      (∑ p ∈ slopes, (GammaE.measure (uE p) + GammaE.measure (uF p)))
    let nug : Measure (SpatialCoordinates d) := ENNReal.ofReal Dg⁻¹ •
      (∑ p ∈ slopes, (GammaEg.measure (uEg p) + GammaEg.measure (uFg p)))
    (nug A).toReal ≤ C * Real.exp (C * G) * ((nu0 A).toReal + (nu0 B).toReal) := by
  obtain ⟨C, hC, hmass⟩ := aux_prop_conc_masked_core_mass_masked_core_sum C0 hC0
  refine ⟨C, hC, ?_⟩
  intro d Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg GammaFg V0 m M c g B G
    uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF ctx A hA hAq
  dsimp only
  have huF : ∀ p, uF p ∈ E.domain := fun p => ctx.hdomEF.symm ▸ ctx.huF p
  have huFg : ∀ p, uFg p ∈ Eg.domain := fun p =>
    ctx.hdomEg.symm ▸ (ctx.hdomFg ▸ ctx.huFg p)
  have hnub : ((ENNReal.ofReal D⁻¹ • (∑ p ∈ slopes,
      (GammaE.measure (uE p) + GammaE.measure (uF p)))) B).toReal = nu := by
    rw [aux_relative_response_variation_normalized_sum_toReal D ctx.hD slopes _ B (by
      intro p _
      exact (ENNReal.add_lt_top.mpr ⟨(GammaE.measure_ne_top (ctx.huE p) B).lt_top,
        (GammaE.measure_ne_top (huF p) B).lt_top⟩).ne)]
    exact ctx.hnudef.symm
  rw [aux_prop_conc_masked_core_mass_normalized_pair_mass GammaEg uEg uFg ctx.huEg huFg slopes Dg
      (aux_lem_relvar_Dg_bounds ctx).2.1 A,
    aux_prop_conc_masked_core_mass_normalized_pair_mass GammaE uE uF ctx.huE huF slopes D ctx.hD A, hnub]
  exact hmass ctx A hA hAq

end
end Paper
