import SubdiffusiveProcess.Paper.lem_relvar
import SubdiffusiveProcess.Paper.relative_response_variation
import Mathlib.Tactic

/-! Local relative variation, total difference energy, and strip-deletion estimates.
These extracted deterministic/probabilistic estimates do not supply the model-specific influence bound. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

/-- The relative-variation estimate, applied directly to the actual local
weighted-minimizer context used by the resampling construction. -/
theorem aux_prop_conc_strip_deletion_estimate_relative_variation_ctx (C0 : ℝ) (hC0 : 1 ≤ C0) :
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
    (p : Fin d → ℝ), p ∈ slopes →
      |(QFg p - c * QEg p) / Dg - (QF p - c * QE p) / D| ≤
        C * G * Real.exp (C * G) * ((M - m) * nu + Real.sqrt (nu * ze)) := by
  obtain ⟨CL, hCL, hL⟩ := lem_relvar_localized_weighted_minimizer_difference C0 hC0
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  obtain ⟨CD, hCD, hDassembly⟩ :=
    lem_relvar_normalized_response_denominator_assembly (10 * (C0 + 1)) (by linarith only [hC0])
  have hHpos : (0 : ℝ) < 1 + C0 + CL + CD := by linarith only [hC0, hCL, hCD]
  refine ⟨100 * (1 + C0 + CL + CD) ^ 3, by positivity, ?_⟩
  intro d Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg GammaFg V0 m M c g B G
    uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF ctx p hp
  have hL_p :=
    hL d ctx.hd slopes ctx.hslopes Q z r hr ctx.hQ ctx.hinside E F Eg Fg
      GammaE GammaF GammaEg GammaFg ctx.hdomEF ctx.hdomEg ctx.hdomFg V0 ctx.hzero
      m M c ctx.hm ctx.hmM ctx.hM ctx.hmc ctx.hcM ctx.horder
      g ctx.hg B ctx.hB ctx.hBq ctx.hsupp G ctx.hG ctx.hbdd
      ctx.hweightE ctx.hweightF ctx.hweightE_cross ctx.hweightF_cross
      uE uF uEg uFg ctx.huE ctx.huF ctx.huEg ctx.huFg
      ctx.htraceF ctx.htraceEg ctx.htraceFg ctx.hminE ctx.hminF ctx.hminEg ctx.hminFg p hp
  obtain ⟨hnu_nonneg, hze_nonneg, -, -, hze_sqrt, -, -, -⟩ :=
    aux_lem_relvar_nu_basics ctx
  obtain ⟨hEu_le, hw_le_ze, -⟩ := aux_lem_relvar_p_bounds ctx p hp
  obtain ⟨hDg_lower, _, hDg_diff⟩ := aux_lem_relvar_Dg_bounds ctx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := aux_lem_relvar_term_bounds ctx p hp
  have hnum_id := aux_lem_relvar_num_identity ctx p
  have hbase_D := aux_lem_relvar_base_D ctx p hp
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.mpr hC0pos) ctx.hm
  have hdel : 0 ≤ M - m := sub_nonneg.mpr ctx.hmM
  have hG0 : 0 ≤ G := (abs_nonneg (g 0)).trans (ctx.hG.1 ⟨0, rfl⟩)
  have hden := hDassembly G (M - m) D Dg nu (QF p - c * QE p)
    hG0 hdel ctx.hD hnu_nonneg hDg_lower hbase_D hDg_diff
  have hzq : (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      CL * G ^ 2 * Real.exp (CL * G) * (D * ze + (M - m) ^ 2 * (D * nu)) := by
    refine hL_p.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    gcongr
  exact aux_lem_relvar_assembly C0 CL CD (1 + C0 + CL + CD)
    (100 * (1 + C0 + CL + CD) ^ 3) G m M D Dg nu ze
    ((GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
    (QF p - c * QE p) (QFg p - c * QEg p) _ _ _ _ _ _ _
    hC0 hCL hCD rfl rfl hG0 hmpos ctx.hmM ctx.hM ctx.hD hnu_nonneg hze_nonneg hze_sqrt hzq
    hnum_id b1 b2 b3 b4 b5 b6 ENNReal.toReal_nonneg b7 hDg_lower hden

/-- A strip estimate needs only total zeta mass, never growth of zeta.
Its square root still carries one full endpoint-gap factor. -/
theorem aux_prop_conc_strip_deletion_estimate_relative_strip_mass (gap nu ze Z K a : ℝ)
    (hgap : 0 ≤ gap) (hnu : 0 ≤ nu) (hZ : 0 ≤ Z) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hn : nu ≤ K * a) (hz : ze ≤ Z * gap ^ 2) :
    gap * nu + Real.sqrt (nu * ze) ≤
      gap * (K * a + Real.sqrt Z * Real.sqrt K * Real.sqrt a) := by
  have hs : Real.sqrt (nu * ze) ≤ Real.sqrt (K * a * (Z * gap ^ 2)) :=
    Real.sqrt_le_sqrt ((mul_le_mul_of_nonneg_left hz hnu).trans
      (mul_le_mul_of_nonneg_right hn (mul_nonneg hZ (sq_nonneg gap))))
  have heq : Real.sqrt (K * a * (Z * gap ^ 2)) =
      gap * (Real.sqrt Z * Real.sqrt K * Real.sqrt a) := by
    rw [Real.sqrt_mul (mul_nonneg hK ha), Real.sqrt_mul hK,
      Real.sqrt_mul hZ, Real.sqrt_sq_eq_abs, abs_of_nonneg hgap]
    ring
  rw [heq] at hs
  exact (add_le_add (mul_le_mul_of_nonneg_left hn hgap) hs).trans_eq (by ring)

section
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

/-- The common affine minimizers have the paper's squared endpoint-gap
difference-energy bound; it is derived from their variational property. -/
theorem aux_prop_conc_strip_deletion_estimate_ctx_difference_energy
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (p : Fin d → ℝ) :
    (GammaE.measure (uF p - uE p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      ((M - m) / m) ^ 2 * QE p := by
  obtain ⟨zQ, rQ, hrQ, hQ⟩ := ctx.hQ
  subst Q
  have hm : 0 < m := lt_of_lt_of_le
    (inv_pos.mpr (lt_of_lt_of_le zero_lt_one ctx.hC0)) ctx.hm
  have he (v : DomainL2 (centeredCube zQ rQ hrQ)) (hv : v ∈ V0) :
      (GammaE.measure (uE p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaE.measure (uE p + v) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
    ctx.hminE p _ (E.domain.add_mem (ctx.huE p) (ctx.hzero.le_domain hv))
      (by simpa only [add_sub_cancel_left] using hv)
  have hf (v : DomainL2 (centeredCube zQ rQ hrQ)) (hv : v ∈ V0) :
      (GammaF.measure (uF p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaF.measure (uF p + v) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    apply ctx.hminF p _
      (F.domain.add_mem (ctx.huF p) (ctx.hdomEF ▸ ctx.hzero.le_domain hv))
    simpa only [add_sub_right_comm] using V0.add_mem (ctx.htraceF p) hv
  have hdif := (lem_diff d ctx.hd zQ rQ hrQ z r hr ctx.hinside E F GammaE GammaF
    ctx.hdomEF V0 ctx.hzero m M c hm ctx.hmc ctx.hcM ctx.horder
    (uE p) (uF p) (ctx.huE p) (ctx.huF p) (ctx.htraceF p) he hf).2.1
  simpa only [ctx.hQE] using hdif

/-- The normalized difference mass on every changed set has a squared gap
bound derived from the common form order. No local regularity of zeta is used. -/
theorem aux_prop_conc_strip_deletion_estimate_ctx_zeta_bound
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    : ze ≤ (C0 ^ 2 * ((2 : ℝ) ^ d * ∑ p ∈ slopes, ∑ i : Fin d, (p i) ^ 2)) * (M - m) ^ 2 := by
  let A : ℝ := (2 : ℝ) ^ d * ∑ p ∈ slopes, ∑ i : Fin d, (p i) ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hQ0 : ∀ p, 0 ≤ QE p := fun p => (ctx.hQE p).symm ▸ ENNReal.toReal_nonneg
  have hs : ∑ p ∈ slopes, QE p ≤ A * D := by
    calc
      _ ≤ ∑ p ∈ slopes, ((2 : ℝ) ^ d * (∑ i : Fin d, (p i) ^ 2) * D) :=
        Finset.sum_le_sum fun p _ =>
          aux_relative_response_variation_quad_bound d QE hQ0 D ctx.hDdef p
      _ = A * D := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hb (p : Fin d → ℝ) :
      (GammaE.measure (uF p - uE p) B).toReal ≤ ((M - m) / m) ^ 2 * QE p :=
    (GammaE.toReal_measure_mono (E.domain.sub_mem (ctx.hdomEF.symm ▸ ctx.huF p)
      (ctx.huE p)) ctx.hBq).trans (aux_prop_conc_strip_deletion_estimate_ctx_difference_energy ctx p)
  have hsum : ∑ p ∈ slopes, (GammaE.measure (uF p - uE p) B).toReal ≤
      ((M - m) / m) ^ 2 * (A * D) := by
    calc
      _ ≤ ∑ p ∈ slopes, ((M - m) / m) ^ 2 * QE p := Finset.sum_le_sum fun p _ => hb p
      _ = ((M - m) / m) ^ 2 * ∑ p ∈ slopes, QE p := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
  have hratio := (aux_relative_response_variation_ratio_bounds C0 m M
    ctx.hC0 ctx.hm ctx.hmM ctx.hM).2.2.2
  rw [ctx.hzedef]
  calc
    _ ≤ D⁻¹ * (((M - m) / m) ^ 2 * (A * D)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr ctx.hD.le)
    _ = ((M - m) / m) ^ 2 * A := by field_simp [ctx.hD.ne']
    _ ≤ (C0 ^ 2 * (M - m) ^ 2) * A := mul_le_mul_of_nonneg_right hratio hA
    _ = (C0 ^ 2 * A) * (M - m) ^ 2 := by ring

end

/-- The strip contribution to relative response has a full gap factor.
Only the nu growth estimate is supplied; the zeta bound is proved above. -/
theorem prop_conc_strip_deletion_estimate (C0 : ℝ) (hC0 : 1 ≤ C0) :
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
    (K a : ℝ), 0 ≤ K → 0 ≤ a → nu ≤ K * a →
    ∀ p ∈ slopes,
      |(QFg p - c * QEg p) / Dg - (QF p - c * QE p) / D| ≤
        (C * G * Real.exp (C * G)) * (M - m) *
          (K * a +
            Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d * ∑ v ∈ slopes, ∑ i : Fin d, (v i) ^ 2)) *
              Real.sqrt K * Real.sqrt a) := by
  obtain ⟨C, hC, hvar⟩ := aux_prop_conc_strip_deletion_estimate_relative_variation_ctx C0 hC0
  refine ⟨C, hC, ?_⟩
  intro d Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg GammaFg V0 m M c g B G
    uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF ctx K a hK ha hn p hp
  have hG : 0 ≤ G := (abs_nonneg (g 0)).trans (ctx.hG.1 ⟨0, rfl⟩)
  have hmass := aux_prop_conc_strip_deletion_estimate_relative_strip_mass (M - m) nu ze
    (C0 ^ 2 * ((2 : ℝ) ^ d * ∑ v ∈ slopes, ∑ i : Fin d, (v i) ^ 2)) K a
    (sub_nonneg.mpr ctx.hmM) (aux_lem_relvar_nu_basics ctx).1
    (by positivity) hK ha hn (aux_prop_conc_strip_deletion_estimate_ctx_zeta_bound ctx)
  exact (hvar ctx p hp).trans ((mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (mul_nonneg hC.le hG) (Real.exp_nonneg _))).trans_eq (by ring))

end
end Paper
