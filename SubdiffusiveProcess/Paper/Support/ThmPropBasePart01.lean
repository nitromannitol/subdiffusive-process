module

public import SubdiffusiveProcess.Paper.prop_conc_local_affine_order
public import SubdiffusiveProcess.Paper.prop_conc_local_affine_identified_order
-- Working candidate. Two local supplier interfaces remain unproved; see STATEMENT-ISSUE.md.
public import SubdiffusiveProcess.Paper.thm_prop_affine_parameters
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.comparison_half_density
public import SubdiffusiveProcess.Paper.lem_affine
public import SubdiffusiveProcess.Paper.lem_boundary
public import SubdiffusiveProcess.Paper.lem_endpoints
public import SubdiffusiveProcess.Paper.lem_mass
public import SubdiffusiveProcess.Paper.lem_replace
public import SubdiffusiveProcess.Paper.lem_saving
public import SubdiffusiveProcess.Paper.prop_density
public import SubdiffusiveProcess.Paper.thm_C0
public import SubdiffusiveProcess.Paper.zero_endpoint_gap
public import SubdiffusiveProcess.Paper.optimal_endpoints
public import SubdiffusiveProcess.Paper.thm_prop_pointwise
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Paper.in_represented_bounds
public import SubdiffusiveProcess.Paper.in_represented_enum
public import SubdiffusiveProcess.Paper.in_represented_mosco
public import SubdiffusiveProcess.Paper.in_represented_catalogue
public import SubdiffusiveProcess.Paper.prop_regularity
public import SubdiffusiveProcess.Paper.prop_locality
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.lem_sincos
public import SubdiffusiveProcess.Paper.cor_32

public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import SubdiffusiveProcess.Lane3.RelativeConcentration
public import SubdiffusiveProcess.Paper.prop_conc
public import SubdiffusiveProcess.Paper.paper_responses_bank
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.lem_skeleton
public import SubdiffusiveProcess.Paper.lem_band
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import SubdiffusiveProcess.Paper.lem_truncation
public import SubdiffusiveProcess.Paper.obl_BH_compact_preimage_nullity
public import SubdiffusiveProcess.Paper.obl_BH_energy_measure_convergence
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq
public import SubdiffusiveProcess.DirichletForm.FOTProduct
public import SubdiffusiveProcess.Compactness.SequentialCompactness
public import SubdiffusiveProcess.Paper.prop_gluing_smooth_mesh
public import SubdiffusiveProcess.Paper.lem_skeleton_smooth_approx
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.uniform_response_input
public import SubdiffusiveProcess.Paper.conv_represented_estimates_change_input
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import Mathlib.Probability.ProductMeasure
public import SubdiffusiveProcess.Sobolev.ReflectionResponses
public import SubdiffusiveProcess.Lane4.Scaling
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import SubdiffusiveProcess.Sobolev.DomainPoincare


@[expose] public section




section


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- Transfer the reciprocal improvement using only the five scalar energies
and endpoints. Keeping this calculation separate avoids traversing represented
catalogue and operator terms during arithmetic normalization. -/
theorem aux_thm_prop_reciprocal_endpoint_bound
    (m M k E F : ℝ) (hm : 0 < m) (hM : 0 < M) (hmM : m ≤ M)
    (hk : 0 ≤ k) (hF : 0 ≤ F)
    (hEF : E ≤ (m⁻¹ - k * (m⁻¹ - M⁻¹)) * F)
    (hprod : (m + k * m / M * (M - m)) * (m⁻¹ - k * (m⁻¹ - M⁻¹)) ≤ 1) :
    (m + k * m / M * (M - m)) * E ≤ F := by
  have hpos : 0 ≤ m + k * m / M * (M - m) :=
    add_nonneg hm.le (mul_nonneg (div_nonneg (mul_nonneg hk hm.le) hM.le) (sub_nonneg.mpr hmM))
  calc
    (m + k * m / M * (M - m)) * E ≤
        (m + k * m / M * (M - m)) * ((m⁻¹ - k * (m⁻¹ - M⁻¹)) * F) :=
      mul_le_mul_of_nonneg_left hEF hpos
    _ = ((m + k * m / M * (M - m)) * (m⁻¹ - k * (m⁻¹ - M⁻¹))) * F :=
      (mul_assoc _ _ _).symm
    _ ≤ 1 * F := mul_le_mul_of_nonneg_right hprod hF
    _ = F := one_mul _

end Paper



set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace Paper


end Paper



set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal BigOperators

namespace Paper

/-- The sum of absolute matrix entries is Lipschitz for its own norm. -/
theorem aux_thm_prop_matrix_norm_difference
    {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    |(∑ i, ∑ j, |A i j|) - (∑ i, ∑ j, |B i j|)| ≤
      ∑ i, ∑ j, |A i j - B i j| := by
  have hsub : (∑ i, ∑ j, |A i j|) - (∑ i, ∑ j, |B i j|) =
      ∑ i, ∑ j, (|A i j| - |B i j|) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => (Finset.sum_sub_distrib _ _).symm)
  rw [hsub]
  calc
    |∑ i, ∑ j, (|A i j| - |B i j|)| ≤
        ∑ i, |∑ j, (|A i j| - |B i j|)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(|A i j| - |B i j|)| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j - B i j| :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
        (fun j _ => abs_abs_sub_abs_le_abs_sub _ _))

/-- The scalar matrix-norm difference inherits the entrywise difference moment. -/
theorem aux_thm_prop_matrix_norm_eLp_difference
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : Ω → Matrix (Fin d) (Fin d) ℝ) (p : ℝ≥0∞) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun om => (∑ i, ∑ j, |A om i j|) - (∑ i, ∑ j, |B om i j|)) p P ≤
      SubdiffusiveProcess.RawLp.eLpNorm (fun om => ∑ i, ∑ j, |A om i j - B om i j|) p P := by
  apply SubdiffusiveProcess.RawLp.eLpNorm_mono_ae
  filter_upwards [] with om
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => abs_nonneg (A om i j - B om i j))))]
  exact aux_thm_prop_matrix_norm_difference (A om) (B om)

theorem aux_thm_prop_matrix_norm_guarded_difference
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : Ω → Matrix (Fin d) (Fin d) ℝ) (p : ℝ≥0∞)
    (hA : AEStronglyMeasurable (fun om => ∑ i, ∑ j, |A om i j|) P)
    (hB : AEStronglyMeasurable (fun om => ∑ i, ∑ j, |B om i j|) P) :
    eLpNorm (fun om => (∑ i, ∑ j, |A om i j|) - (∑ i, ∑ j, |B om i j|)) p P ≤
      eLpNorm (fun om => ∑ i, ∑ j, |A om i j - B om i j|) p P := by
  have h := aux_thm_prop_matrix_norm_eLp_difference P A B p
  have hm : AEStronglyMeasurable (fun om =>
      (∑ i, ∑ j, |A om i j|) - (∑ i, ∑ j, |B om i j|)) P := hA.sub hB
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hm] at h
  exact h.trans (SubdiffusiveProcess.RawLp.eLpNorm_le_guarded _ _ _)

end Paper



set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

namespace Paper
noncomputable section

theorem aux_thm_prop_matrix_extra_chain
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (field : Ω → BilateralField d) (hfield_meas : Measurable field)
    (hfield_map : Measure.map field P = (chaosSampleLaw model).toMeasure)
    (H1 : ℕ) (hH1 : 1 ≤ H1)
    (thetap : ℝ) (hthetap0 : 0 < thetap) (hthetap1 : thetap < 1)
    (p Cbound q r K A lam0 : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hr1 : r < 1)
    (hCbound : 0 ≤ Cbound) (hKdef : K = lam0 * (1 - r) / 2) (hlam0 : 0 < lam0) (hApos : 0 < A)
    (hbudget : ∀ k : ℕ,
      2 * ((2 * (Cbound / q * q ^ k) / (K * r ^ k)) ^ p) ≤ Real.exp (-(A * ((k : ℝ) + 1))))
    (hAbeats : 1 + ((H1 * d : ℕ) : ℝ) * Real.log 3 ≤
      A * thetap / 24 + Real.log (1 - Real.exp (-A / 2)))
    (Band : ℕ → ℕ → MeasurableSpace Ω)
    (hBand_def : ∀ (n H : ℕ), Band n H =
      ⨆ (j : ℤ) (_h : |j + ((H1 * n : ℕ) : ℤ)| ≤ (H : ℤ)),
        (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
          (fun omega : Ω => field omega j))
    (Bk : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) →
      Ω → Matrix (Fin d) (Fin d) ℝ)
    (hTest_meas : ∀ n w, Measurable (fun om => ∑ i : Fin d, ∑ j : Fin d, |Bk n w om i j|))
    (hTest_moment : ∀ n w, eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d, |Bk n w om i j|)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cbound)
    (hMatrix_err : ∀ n w (H : ℕ), eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
      |Bk n w om i j - (P[fun om' => Bk n w om' i j | Band n H]) om|)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cbound * q ^ H)) :
    ∃ Bextra : Ω → ℝ, Measurable Bextra ∧ (∀ omega, 0 ≤ Bextra omega) ∧
      ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
        ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
          (Nat.card {j : Fin J // ¬ ((∑ i : Fin d, ∑ l : Fin d,
            |Bk (j.val + 1) (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩) omega i l|) ≤ lam0)} : ℝ) ≤
            thetap * (J : ℝ) + Bextra omega := by
  have hTestB_meas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (H : ℕ),
      StronglyMeasurable[Band n H]
        (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d,
          |(P[fun om' => Bk n w om' i j | Band n H]) omega|) := by
    intro n w H
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    apply Finset.stronglyMeasurable_fun_sum
    intro j _
    exact continuous_abs.comp_stronglyMeasurable stronglyMeasurable_condExp
  have hBand_le : ∀ (n H : ℕ), Band n H ≤ (inferInstance : MeasurableSpace Ω) := by
    intro n H
    rw [hBand_def n H]
    apply iSup_le; intro j; apply iSup_le; intro _hj
    exact ((measurable_pi_apply j).comp hfield_meas).comap_le
  have hTestB_ae : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (H : ℕ),
      AEStronglyMeasurable
        (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d,
          |(P[fun om' => Bk n w om' i j | Band n H]) omega|) P :=
    fun n w H => ((hTestB_meas n w H).mono (hBand_le n H)).aestronglyMeasurable
  have hTest_ae : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      AEStronglyMeasurable (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) P :=
    fun n w => (hTest_meas n w).aestronglyMeasurable
  have hTest_err : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (H : ℕ),
      eLpNorm (fun om => (∑ i : Fin d, ∑ j : Fin d, |Bk n w om i j|) -
        (∑ i : Fin d, ∑ j : Fin d, |(P[fun om' => Bk n w om' i j | Band n H]) om|))
        (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cbound * q ^ H) := by
    intro n w H
    exact (aux_thm_prop_matrix_norm_guarded_difference P (Bk n w)
      (fun om i j => (P[fun om' => Bk n w om' i j | Band n H]) om)
      (ENNReal.ofReal p) (hTest_ae n w) (hTestB_ae n w H)).trans (hMatrix_err n w H)
  exact aux_cor_32_extra_chain P model field hfield_meas hfield_map H1 hH1 thetap hthetap0
    hthetap1 p Cbound q r K A lam0 hp hq hq1 hr hr1 hCbound hKdef hlam0 hApos hbudget hAbeats
    Band hBand_def
    (fun n w omega => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|)
    (fun n w H omega => ∑ i : Fin d, ∑ j : Fin d,
      |(P[fun om' => Bk n w om' i j | Band n H]) omega|)
    hTest_meas hTest_ae hTestB_meas hTestB_ae hTest_moment hTest_err

end
end Paper



set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

namespace Paper
noncomputable section

/-- A small-context matrix estimate used in every extra-good cell. -/
theorem aux_thm_prop_concentration_matrix_test
    {d : ℕ} (A F B : Matrix (Fin d) (Fin d) ℝ)
    (ck vol eps c0 m M : ℝ)
    (heps : 0 < eps) (hc0 : 0 < c0) (hmM : m ≤ M) (hvol : 0 < vol)
    (hTrPos : 0 < Matrix.trace A)
    (hEllip : ∀ xi : Fin d → ℝ,
      c0 * Matrix.trace A * (xi ⬝ᵥ xi) ≤ xi ⬝ᵥ A.mulVec xi)
    (hB : B = (Matrix.trace A)⁻¹ • (F - ck • A))
    (hSum : (∑ i : Fin d, ∑ j : Fin d, |B i j|) ≤ eps * c0 * (M - m))
    (xi : Fin d → ℝ) :
    |vol * (xi ⬝ᵥ F.mulVec xi) - ck * vol * (xi ⬝ᵥ A.mulVec xi)| ≤
      eps * (M - m) * vol * (xi ⬝ᵥ A.mulVec xi) := by
  have hvol_pos : 0 < vol := hvol
  have h_key : F - ck • A =
      (Matrix.trace (A)) • B := by
    have hTr_ne_zero : Matrix.trace (A) ≠ 0 := by linarith
    rw [hB]
    rw [smul_smul, mul_inv_cancel₀ hTr_ne_zero, one_smul]
  have h_diff : (vol) *
      (xi ⬝ᵥ (F).mulVec xi) -
      ck * (vol) *
        (xi ⬝ᵥ (A).mulVec xi) =
      (vol) *
        (Matrix.trace (A)) *
        (xi ⬝ᵥ (B).mulVec xi) := by
    calc
      (vol) *
          (xi ⬝ᵥ (F).mulVec xi) -
        ck * (vol) *
          (xi ⬝ᵥ (A).mulVec xi) =
        (vol) *
          ((xi ⬝ᵥ (F).mulVec xi) -
            ck * (xi ⬝ᵥ (A).mulVec xi)) := by ring
      _ = (vol) *
          (xi ⬝ᵥ ((F - ck • A).mulVec xi)) := by
        simp [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul]
      _ = (vol) *
          (xi ⬝ᵥ (((Matrix.trace (A)) • B).mulVec xi)) := by
        rw [h_key]
      _ = (vol) *
          (Matrix.trace (A)) *
          (xi ⬝ᵥ (B).mulVec xi) := by
        simp [smul_mulVec, dotProduct_smul, mul_assoc]
  rw [h_diff]
  have hvol_pos' : 0 ≤ (vol) := by
    positivity
  rw [abs_mul, abs_mul, abs_of_pos hvol_pos]
  have h_nonneg_tr : 0 ≤ Matrix.trace (A) := hTrPos.le
  rw [abs_of_nonneg h_nonneg_tr]
  have hxixi_nonneg : 0 ≤ xi ⬝ᵥ xi :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (xi i)
  have hineq1 : (vol) *
      (Matrix.trace (A)) *
      |xi ⬝ᵥ (B).mulVec xi| ≤
      (vol) *
        (Matrix.trace (A)) *
        ((∑ i : Fin d, ∑ j : Fin d, |B i j|) * (xi ⬝ᵥ xi)) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hvol_pos.le h_nonneg_tr)
    exact aux_cor_32_abs_quadratic_form_le (B) xi
  have hSum' : (∑ i : Fin d, ∑ j : Fin d, |B i j|) ≤ eps * c0 * (M - m) := hSum
  have hM_minus_m_nonneg : 0 ≤ M - m := by
    have : m ≤ M := hmM
    linarith
  have h_sum_nonneg : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, |B i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hineq2 : (vol) *
      (Matrix.trace (A)) *
      ((∑ i : Fin d, ∑ j : Fin d, |B i j|) * (xi ⬝ᵥ xi)) ≤
      (vol) *
        (Matrix.trace (A)) *
        ((eps * c0) * (M - m) * (xi ⬝ᵥ xi)) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hvol_pos.le h_nonneg_tr)
    exact mul_le_mul_of_nonneg_right hSum' hxixi_nonneg
  have hkey : (Matrix.trace (A)) * (xi ⬝ᵥ xi) ≤
      (1 / c0) * (xi ⬝ᵥ (A).mulVec xi) := by
    have h := hEllip xi
    have e1 : (1 / c0 : ℝ) *
        (c0 * Matrix.trace (A) * (xi ⬝ᵥ xi)) =
        Matrix.trace (A) * (xi ⬝ᵥ xi) := by
      rw [show (1 / c0 : ℝ) * (c0 * Matrix.trace (A) * (xi ⬝ᵥ xi)) =
          (1 / c0 * c0) * (Matrix.trace (A) * (xi ⬝ᵥ xi)) from by ring,
        one_div, inv_mul_cancel₀ (ne_of_gt hc0), one_mul]
    calc
      Matrix.trace (A) * (xi ⬝ᵥ xi) =
          (1 / c0) * (c0 * Matrix.trace (A) * (xi ⬝ᵥ xi)) := e1.symm
      _ ≤ (1 / c0) * (xi ⬝ᵥ (A).mulVec xi) := by
        apply mul_le_mul_of_nonneg_left h
        positivity
  have hineq3 : (vol) *
      (Matrix.trace (A)) *
      ((eps * c0) * (M - m) * (xi ⬝ᵥ xi)) ≤
      (vol) *
        ((eps * c0) / c0) * (M - m) *
        (xi ⬝ᵥ (A).mulVec xi) := by
    have h_factor : (Matrix.trace (A)) * ((eps * c0) * (M - m) * (xi ⬝ᵥ xi)) ≤
        ((eps * c0) / c0) * (M - m) * (xi ⬝ᵥ (A).mulVec xi) := by
      calc
        (Matrix.trace (A)) * ((eps * c0) * (M - m) * (xi ⬝ᵥ xi)) =
            ((eps * c0) * (M - m)) * ((Matrix.trace (A)) * (xi ⬝ᵥ xi)) := by ring
        _ ≤ ((eps * c0) * (M - m)) * ((1 / c0) * (xi ⬝ᵥ (A).mulVec xi)) :=
          mul_le_mul_of_nonneg_left hkey
            (mul_nonneg (mul_pos heps hc0).le hM_minus_m_nonneg)
        _ = ((eps * c0) / c0) * (M - m) * (xi ⬝ᵥ (A).mulVec xi) := by ring
    calc
      (vol) *
          (Matrix.trace (A)) *
          ((eps * c0) * (M - m) * (xi ⬝ᵥ xi)) =
        (vol) *
          ((Matrix.trace (A)) *
            ((eps * c0) * (M - m) * (xi ⬝ᵥ xi))) := by ring
      _ ≤ (vol) *
          (((eps * c0) / c0) * (M - m) * (xi ⬝ᵥ (A).mulVec xi)) :=
        mul_le_mul_of_nonneg_left h_factor hvol_pos.le
      _ = (vol) *
          ((eps * c0) / c0) * (M - m) * (xi ⬝ᵥ (A).mulVec xi) := by ring
  have h_epsPrime_div_c0 : (eps * c0) / c0 = eps := by
    rw [mul_div_assoc, div_self (ne_of_gt hc0), mul_one]
  rw [h_epsPrime_div_c0] at hineq3
  have h_total : (vol) *
      (Matrix.trace (A)) *
      |xi ⬝ᵥ (B).mulVec xi| ≤
      (vol) * eps * (M - m) *
        (xi ⬝ᵥ (A).mulVec xi) := by
    linarith
  simpa [abs_mul, abs_of_nonneg hvol_pos', abs_of_nonneg h_nonneg_tr,
    mul_comm, mul_left_comm, mul_assoc] using h_total

/-- The probabilistic all-chain estimate for the actual matrix test. -/
theorem aux_thm_prop_concentration_extra_chain
    (d : ℕ)
    (H1 : ℕ) (hH1 : 1 ≤ H1)
    (eps : ℝ) (heps : 0 < eps)
    (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta < 1)
    (c0 : ℝ) (hc0 : 0 < c0)
    (p : ℝ) (hp : 0 < p)
    (Cp : ℝ) (hCp : 0 < Cp)
    (aexp : ℝ) (haexp : 0 < aexp)
    (hpRate : 2 * (2 * Real.log 2 + 1 + (48 / theta) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (hfield_meas : Measurable field)
        (hfield_map : Measure.map field P = (chaosSampleLaw model).toMeasure)
        (m M : ℝ) (hmM : m ≤ M),
      ∀ (Bk : (n : ℕ) →
        (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω → Matrix (Fin d) (Fin d) ℝ),
      let Band : ℕ → ℕ → MeasurableSpace Ω := fun n H =>
        ⨆ (j : ℤ) (_h : |j + ((H1 * n : ℕ) : ℤ)| ≤ (H : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun omega : Ω => field omega j)
      ∀ (hTest_meas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
        Measurable (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|))
      (hBkMoment : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          eLpNorm
              (fun omega => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w omega i j|)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cp * model.delta * (M - m)))
      (hBkBand : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (Hband : ℕ),
          eLpNorm
              (fun omega => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w omega i j -
                  ((P[fun omega => Bk n w omega i j |
                    Band n Hband]) omega)|)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal
              (Cp * model.delta * (M - m) *
                (3 : ℝ) ^ (-aexp * (Hband : ℝ)))),
      let Good2 : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω :=
        fun n w => {omega | (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤ eps * c0 * (M - m)}
 ∃ Bextra : Ω → ℝ, Measurable Bextra ∧ (∀ omega, 0 ≤ Bextra omega) ∧
        ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
          ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
            (Nat.card {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
                (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
              (theta / 2) * (J : ℝ) + Bextra omega := by
  obtain ⟨A, gq, gr, K0, delta0, hApos, hqeq, hgq, hgq1, hgr, hgr1, hK0def, hK0pos, hdelta0pos,
      hbudget0, hAbeats⟩ :=
    aux_cor_32_rate_and_delta0 H1 d theta eps c0 p Cp aexp htheta htheta1 heps hc0 hp hCp haexp
      hpRate
  refine ⟨delta0, hdelta0pos, ?_⟩
  intro _ _ model hmodel Ω _ P _ field hfield_meas hfield_map m M hmM Bk Band
    hTest_meas hBkMoment hBkBand Good2
  have hBand_def : ∀ (n H : ℕ), Band n H =
      ⨆ (j : ℤ) (_h : |j + ((H1 * n : ℕ) : ℤ)| ≤ (H : ℤ)),
        (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
          (fun omega : Ω => field omega j) := fun n H => rfl
  have hthetap0 : 0 < theta / 2 := by linarith
  have hthetap1 : theta / 2 < 1 := by linarith
  rcases hmM.lt_or_eq with hMgt | hMeq
  · -- M > m: the genuine construction.
    have hMm_pos : 0 < M - m := by linarith
    have hMm_ne : (M - m) ≠ 0 := ne_of_gt hMm_pos
    have hdeltapos : 0 < model.delta := model.shellPrefix.delta_pos
    set Cbound : ℝ := Cp * model.delta * (M - m) with hCbounddef
    set lam0 : ℝ := eps * c0 * (M - m) with hlam0def
    set K : ℝ := K0 * (M - m) with hKdef2
    have hCbound_nonneg : 0 ≤ Cbound := by positivity
    have hlam0_pos : 0 < lam0 := by positivity
    have hKdefFull : K = lam0 * (1 - gr) / 2 := by
      rw [hKdef2, hlam0def, hK0def]; ring
    have hbudget : ∀ k : ℕ, 2 * ((2 * (Cbound / gq * gq ^ k) / (K * gr ^ k)) ^ p) ≤
        Real.exp (-(A * ((k : ℝ) + 1))) := by
      have hb0 := hbudget0 model.delta hdeltapos hmodel
      have := aux_cor_32_budget_scale p (Cp * model.delta) gq K0 A gr (M - m)
        (ne_of_gt hgq) (ne_of_gt hK0pos) (ne_of_gt hgr) hMm_ne hb0
      rw [hCbounddef, hKdef2]
      exact this
    have hTest_moment : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
        eLpNorm (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|)
            (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cbound := by
      intro n w; rw [hCbounddef]; exact hBkMoment n w
    have hMatrix_err : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (H : ℕ),
        eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
          |Bk n w om i j - (P[fun om' => Bk n w om' i j | Band n H]) om|)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cbound * gq ^ H) := by
      intro n w H
      have hqH : Cbound * gq ^ H = Cp * model.delta * (M - m) * (3 : ℝ) ^ (-aexp * (H : ℝ)) := by
        rw [hCbounddef, hqeq]
        congr 1
        rw [← Real.rpow_natCast ((3:ℝ) ^ (-aexp)) H, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      rw [hqH]
      exact hBkBand n w H
    obtain ⟨Bextra, hBextraMeas, hBextraNonneg, hExtra⟩ :=
      aux_thm_prop_matrix_extra_chain P model field hfield_meas hfield_map H1 hH1 (theta / 2) hthetap0
        hthetap1 p Cbound gq gr K A lam0 hp hgq hgq1 hgr hgr1 hCbound_nonneg hKdefFull
        hlam0_pos hApos hbudget hAbeats Band hBand_def Bk hTest_meas hTest_moment hMatrix_err
    exact ⟨Bextra, hBextraMeas, hBextraNonneg, hExtra⟩
  · -- M = m: `hBkMoment` forces the test to vanish a.e., so `Good2` holds a.e. trivially.
    refine ⟨fun _ => 0, measurable_const, fun _ => le_refl 0, ?_⟩
    have hgood2ae : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
        ∀ᵐ omega ∂P, omega ∈ Good2 n w := by
      intro n w
      have hle := hBkMoment n w
      rw [← hMeq, sub_self, mul_zero, ENNReal.ofReal_zero] at hle
      have hmomZero : eLpNorm (fun omega => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|)
          (ENNReal.ofReal p) P = 0 := le_antisymm hle (zero_le)
      have hp0 : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
      have hae0 : (fun omega => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) =ᵐ[P]
          (fun _ => (0 : ℝ)) :=
        (eLpNorm_eq_zero_iff hp0).mp hmomZero
      filter_upwards [hae0] with omega homega
      show (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤ eps * c0 * (M - m)
      rw [homega, ← hMeq, sub_self, mul_zero]
    obtain ⟨Sigma0, hSigma0meas, hSigma0P, hSigma0prop⟩ :=
      aux_exists_measurable_full_measure_of_ae P
        (fun omega => ∀ qi : Σ n : ℕ, Fin n → OddGridIndex d (subdivisionHalfWidth H1),
          omega ∈ Good2 qi.1 qi.2)
        (ae_all_iff.mpr (fun qi => hgood2ae qi.1 qi.2))
    have hSigma0ae : ∀ᵐ omega ∂P, omega ∈ Sigma0 := by
      have hcompl : P Sigma0ᶜ = 0 := by
        rw [prob_compl_eq_one_sub hSigma0meas, hSigma0P, tsub_self]
      rw [ae_iff]
      exact hcompl
    filter_upwards [hSigma0ae] with omega homega J hJ pi
    have hall : ∀ j : Fin J, omega ∈ Good2 (j.val + 1)
        (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩) :=
      fun j => hSigma0prop omega homega ⟨j.val + 1, fun t => pi ⟨t.val, by omega⟩⟩
    have hempty : IsEmpty {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
        (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} :=
      ⟨fun j => j.2 (hall j.1)⟩
    have hcard0 : Nat.card {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
        (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} = 0 :=
      @Nat.card_of_isEmpty _ hempty
    rw [hcard0]
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := by positivity
    have : (0:ℝ) ≤ (theta / 2) * (J : ℝ) := by positivity
    simpa using this

/-- Local matrix moment and band estimates give the actual measurable extra
concentration test and all-chain bound. The proof uses cor_32's proved witness
machinery and requires no outside-root catalogue. -/
theorem aux_thm_prop_concentration_events
    (d : ℕ)
    (H1 : ℕ) (hH1 : 1 ≤ H1)
    (eps : ℝ) (heps : 0 < eps)
    (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta < 1)
    (c0 : ℝ) (hc0 : 0 < c0)
    (p : ℝ) (hp : 0 < p)
    (Cp : ℝ) (hCp : 0 < Cp)
    (aexp : ℝ) (haexp : 0 < aexp)
    (hpRate : 2 * (2 * Real.log 2 + 1 + (48 / theta) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3) :
    ∃ delta0 epsPrime : ℝ, 0 < delta0 ∧ 0 < epsPrime ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (hfield_meas : Measurable field)
        (hfield_map : Measure.map field P = (chaosSampleLaw model).toMeasure)
        (m M : ℝ) (hmM : m ≤ M)
        (vol : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℝ)
        (hvol : ∀ n w, 0 < vol n w),
      ∀ (AE AF : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω →
          Matrix (Fin d) (Fin d) ℝ)
        (hAEmeas : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (i j : Fin d),
          Measurable (fun omega : Ω => AE n w omega i j))
        (hAFmeas : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (i j : Fin d),
          Measurable (fun omega : Ω => AF n w omega i j)),
      let ck : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℝ :=
        (fun n w =>
          ∫ omega, Matrix.trace (AF n w omega) /
            Matrix.trace (AE n w omega) ∂P)
      let Bk : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω →
          Matrix (Fin d) (Fin d) ℝ :=
        fun n w omega =>
          (Matrix.trace (AE n w omega))⁻¹ •
            (AF n w omega - ck n w • AE n w omega)
      let Band : ℕ → ℕ → MeasurableSpace Ω := fun n H =>
        ⨆ (j : ℤ) (_h : |j + ((H1 * n : ℕ) : ℤ)| ≤ (H : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun omega : Ω => field omega j)
      ∀ (BaseGood : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω)
        (hBaseMeas : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          MeasurableSet (BaseGood n w))
        (hBaseCondition : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (omega : Ω), omega ∈ BaseGood n w →
          0 < Matrix.trace (AE n w omega) ∧
            ∀ (xi : Fin d → ℝ),
              c0 * Matrix.trace (AE n w omega) * (xi ⬝ᵥ xi) ≤
                xi ⬝ᵥ (AE n w omega).mulVec xi)
        (hBaseChain : ∃ Bbase : Ω → ℝ,
          Measurable Bbase ∧ (∀ omega, 0 ≤ Bbase omega) ∧
          ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
            ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
              Nat.card {j : Fin J //
                ¬ omega ∈ BaseGood (j.val + 1)
                  (fun t : Fin (j.val + 1) =>
                    pi ⟨t.val, by omega⟩)} ≤
                (theta / 2) * (J : ℝ) + Bbase omega)
      (hBkMoment : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          eLpNorm
              (fun omega => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w omega i j|)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cp * model.delta * (M - m)))
      (hBkBand : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (Hband : ℕ),
          eLpNorm
              (fun omega => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w omega i j -
                  ((P[fun omega => Bk n w omega i j |
                    Band n Hband]) omega)|)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal
              (Cp * model.delta * (M - m) *
                (3 : ℝ) ^ (-aexp * (Hband : ℝ)))),
      let ExtraGood : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω :=
        fun n w =>
          {omega | omega ∈ BaseGood n w ∧
            (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤
              epsPrime * (M - m)}
      (∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          MeasurableSet (ExtraGood n w)) ∧
      (∃ Bnew : Ω → ℝ,
        Measurable Bnew ∧ (∀ omega, 0 ≤ Bnew omega) ∧
          (∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
            ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
              Nat.card {j : Fin J //
                ¬ omega ∈ ExtraGood (j.val + 1)
                  (fun t : Fin (j.val + 1) =>
                    pi ⟨t.val, by omega⟩)} ≤
                theta * (J : ℝ) + Bnew omega) ∧
          ∀ (n : ℕ)
            (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω),
            omega ∈ ExtraGood n w →
            ∀ xi : Fin d → ℝ,
              |(vol n w) *
                  (xi ⬝ᵥ (AF n w omega).mulVec xi) -
                ck n w * (vol n w) *
                  (xi ⬝ᵥ (AE n w omega).mulVec xi)| ≤
                eps * (M - m) *
                  (vol n w) *
                  (xi ⬝ᵥ (AE n w omega).mulVec xi)) := by
  obtain ⟨delta0, hdelta0pos, hchain⟩ :=
    aux_thm_prop_concentration_extra_chain d H1 hH1 eps heps theta htheta htheta1
      c0 hc0 p hp Cp hCp aexp haexp hpRate
  refine ⟨delta0, eps * c0, hdelta0pos, mul_pos heps hc0, ?_⟩
  intro _ _ model hmodel
  intro Ω _ P _ field hfield_meas hfield_map m M hmM vol hvol AE AF hAEmeas hAFmeas
  intro ck Bk Band
  intro BaseGood hBaseMeas hBaseCondition hBaseChain
    hBkMoment hBkBand
  intro ExtraGood
  refine ⟨?_, ?_⟩
  · 
    intro n w
    exact aux_cor_32_extragood_measurable AE AF hAEmeas hAFmeas ck BaseGood hBaseMeas
      (eps * c0 * (M - m)) n w
  · -- Extract Bbase from hBaseChain (already a hypothesis of cor_32, from good_event/prop_allchain
    obtain ⟨Bbase, hBbaseMeas, hBbaseNonneg, hBbaseBound⟩ := hBaseChain
    let Good2 : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω :=
      fun n w => {omega | (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤ eps * c0 * (M - m)}
    have hExtraGood_eq : ∀ n w, ExtraGood n w = {omega | omega ∈ BaseGood n w ∧ omega ∈ Good2 n w} := by
      intro n w; rfl
    have hExtraTest : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω),
        omega ∈ ExtraGood n w → ∀ xi : Fin d → ℝ,
          |(vol n w) *
              (xi ⬝ᵥ (AF n w omega).mulVec xi) -
            ck n w * (vol n w) *
              (xi ⬝ᵥ (AE n w omega).mulVec xi)| ≤
            eps * (M - m) *
              (vol n w) *
              (xi ⬝ᵥ (AE n w omega).mulVec xi) := by
      intro n w omega hExi xi
      obtain ⟨hTr, hEllip⟩ := hBaseCondition n w omega hExi.1
      exact aux_thm_prop_concentration_matrix_test (AE n w omega) (AF n w omega)
        (Bk n w omega) (ck n w) (vol n w) eps c0 m M heps hc0 hmM (hvol n w)
        hTr hEllip rfl hExi.2 xi
    have hExtraChain : ∃ Bextra : Ω → ℝ, Measurable Bextra ∧ (∀ omega, 0 ≤ Bextra omega) ∧
        ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
          ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
            (Nat.card {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
                (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
              (theta / 2) * (J : ℝ) + Bextra omega := by
      exact hchain model hmodel Ω P field hfield_meas hfield_map m M hmM Bk
        (fun n w => aux_cor_32_test_measurable AE AF hAEmeas hAFmeas ck n w)
        hBkMoment hBkBand
    obtain ⟨Bextra, hBextraMeas, hBextraNonneg, hExtra⟩ := hExtraChain
    obtain ⟨Bnew, hBnewMeas, hBnewNonneg, hBound⟩ :=
      aux_cor_32_hBound_of_base_and_extra H1 P BaseGood Good2 theta Bbase Bextra
        hBbaseMeas hBbaseNonneg hBextraMeas hBextraNonneg hBbaseBound hExtra
    refine ⟨Bnew, hBnewMeas, hBnewNonneg, ?_, hExtraTest⟩
    filter_upwards [hBound] with omega h J hJ pi
    have h' := h J hJ pi
    simpa [hExtraGood_eq, Set.mem_setOf_eq] using h'

end

end Paper





set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

namespace Paper
noncomputable section

theorem aux_thm_prop_fine_concentration_extra_chain
    (d : ℕ)
    (H1 : ℕ) (hH1 : 1 ≤ H1)
    (eps : ℝ) (heps : 0 < eps)
    (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta < 1)
    (c0 : ℝ) (hc0 : 0 < c0)
    (p : ℝ) (hp : 0 < p)
    (Cp : ℝ) (hCp : 0 < Cp)
    (aexp : ℝ) (haexp : 0 < aexp)
    (hpRate : 2 * (2 * Real.log 2 + 1 + (48 / theta) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (k0 : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (hfield_meas : Measurable field)
        (hfield_map : Measure.map field P = (chaosSampleLaw model).toMeasure)
        (m M : ℝ) (hmM : m ≤ M),
      ∀ (Bk : (n : ℕ) →
        (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω → Matrix (Fin d) (Fin d) ℝ),
      let Band : ℕ → ℕ → MeasurableSpace Ω := fun n H =>
        ⨆ (j : ℤ) (_h : |j + ((H1 * n : ℕ) : ℤ)| ≤ (H : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun omega : Ω => field omega j)
      ∀ (hTest_meas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
        Measurable (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|))
      (hBkMoment : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)), k0 ≤ n →
          eLpNorm
              (fun omega => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w omega i j|)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cp * model.delta * (M - m)))
      (hBkBand : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (Hband : ℕ), k0 ≤ n →
          eLpNorm
              (fun omega => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w omega i j -
                  ((P[fun omega => Bk n w omega i j |
                    Band n Hband]) omega)|)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal
              (Cp * model.delta * (M - m) *
                (3 : ℝ) ^ (-aexp * (Hband : ℝ)))),
      let Good2 : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω :=
        fun n w => {omega | k0 ≤ n →
          (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤ eps * c0 * (M - m)}
 ∃ Bextra : Ω → ℝ, Measurable Bextra ∧ (∀ omega, 0 ≤ Bextra omega) ∧
        ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
          ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
            (Nat.card {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
                (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
              (theta / 2) * (J : ℝ) + Bextra omega := by
  obtain ⟨delta0, hdelta0, hchain⟩ := aux_thm_prop_concentration_extra_chain
    d H1 hH1 eps heps theta htheta htheta1 c0 hc0 p hp Cp hCp aexp haexp hpRate
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel k0 Ω _ P _ field hfield hfieldlaw m M hmM Bk Band hmeas hmom hband Good2
  classical
  let B : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) →
      Ω → Matrix (Fin d) (Fin d) ℝ := fun n w om => if k0 ≤ n then Bk n w om else 0
  have hBmeas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      Measurable (fun om => ∑ i : Fin d, ∑ j : Fin d, |B n w om i j|) := by
    intro n w
    by_cases hn : k0 ≤ n
    · simpa only [B, if_pos hn] using hmeas n w
    · simpa only [B, if_neg hn, Matrix.zero_apply, abs_zero, Finset.sum_const_zero] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  have hBmom : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d, |B n w om i j|) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * model.delta * (M - m)) := by
    intro n w
    by_cases hn : k0 ≤ n
    · simpa only [B, if_pos hn] using hmom n w hn
    · simpa only [B, if_neg hn, Matrix.zero_apply, abs_zero, Finset.sum_const_zero,
        eLpNorm_zero'] using (zero_le)
  have hBband : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (Hband : ℕ),
      eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
        |B n w om i j - (P[fun om' => B n w om' i j | Band n Hband]) om|)
        (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * model.delta * (M - m) * (3 : ℝ) ^ (-aexp * (Hband : ℝ))) := by
    intro n w Hband
    by_cases hn : k0 ≤ n
    · simpa only [B, if_pos hn] using hband n w Hband hn
    · simp only [B, if_neg hn, Matrix.zero_apply]
      change eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
        |(0 : ℝ) - (P[(0 : Ω → ℝ) | Band n Hband]) om|) (ENNReal.ofReal p) P ≤ _
      rw [condExp_zero]
      simpa only [Pi.zero_apply, sub_self, abs_zero, Finset.sum_const_zero, eLpNorm_zero'] using
        (zero_le)
  have heq (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) :
      {om | (∑ i : Fin d, ∑ j : Fin d, |B n w om i j|) ≤ eps * c0 * (M - m)} = Good2 n w := by
    ext om
    by_cases hn : k0 ≤ n
    · simp only [Good2, B, if_pos hn, mem_setOf_eq, hn, true_implies]
    · have hnonneg : 0 ≤ eps * c0 * (M - m) :=
        mul_nonneg (mul_pos heps hc0).le (sub_nonneg.mpr hmM)
      simp only [Good2, B, if_neg hn, Matrix.zero_apply, abs_zero,
        Finset.sum_const_zero, mem_setOf_eq, hn, false_implies, hnonneg]
  obtain ⟨Bextra, hBe, hBpos, hgood⟩ := hchain model hmodel Ω P field hfield hfieldlaw
    m M hmM B hBmeas hBmom hBband
  refine ⟨Bextra, hBe, hBpos, ?_⟩
  simpa only [heq] using hgood

end
end Paper



set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

namespace Paper
noncomputable section

/-- Deterministic eligibility masks restrict the matrix tests to actual represented
cells. The all-chain estimate keeps the same constants and allowance. -/

theorem aux_thm_prop_masked_concentration_extra_chain
    (d : ℕ)
    (H1 : ℕ) (hH1 : 1 ≤ H1)
    (eps : ℝ) (heps : 0 < eps)
    (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta < 1)
    (c0 : ℝ) (hc0 : 0 < c0)
    (p : ℝ) (hp : 0 < p)
    (Cp : ℝ) (hCp : 0 < Cp)
    (aexp : ℝ) (haexp : 0 < aexp)
    (hpRate : 2 * (2 * Real.log 2 + 1 + (48 / theta) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (hfield_meas : Measurable field)
        (hfield_map : Measure.map field P = (chaosSampleLaw model).toMeasure)
        (m M : ℝ) (hmM : m ≤ M),
      ∀ (Bk : (n : ℕ) →
        (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω → Matrix (Fin d) (Fin d) ℝ),
      ∀ (Allowed : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Prop),
      let Band : ℕ → ℕ → MeasurableSpace Ω := fun n H =>
        ⨆ (j : ℤ) (_h : |j + ((H1 * n : ℕ) : ℤ)| ≤ (H : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun omega : Ω => field omega j)
      ∀ (hTest_meas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
        Measurable (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|))
      (hBkMoment : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)), Allowed n w →
          eLpNorm
              (fun omega => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w omega i j|)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cp * model.delta * (M - m)))
      (hBkBand : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (Hband : ℕ), Allowed n w →
          eLpNorm
              (fun omega => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w omega i j -
                  ((P[fun omega => Bk n w omega i j |
                    Band n Hband]) omega)|)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal
              (Cp * model.delta * (M - m) *
                (3 : ℝ) ^ (-aexp * (Hband : ℝ)))),
      let Good2 : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω :=
        fun n w => {omega | Allowed n w →
          (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤ eps * c0 * (M - m)}
 ∃ Bextra : Ω → ℝ, Measurable Bextra ∧ (∀ omega, 0 ≤ Bextra omega) ∧
        ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
          ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
            (Nat.card {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
                (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
              (theta / 2) * (J : ℝ) + Bextra omega := by
  obtain ⟨delta0, hdelta0, hchain⟩ := aux_thm_prop_concentration_extra_chain
    d H1 hH1 eps heps theta htheta htheta1 c0 hc0 p hp Cp hCp aexp haexp hpRate
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel Ω _ P _ field hfield hfieldlaw m M hmM Bk Allowed Band hmeas hmom hband Good2
  classical
  let B : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) →
      Ω → Matrix (Fin d) (Fin d) ℝ := fun n w om => if Allowed n w then Bk n w om else 0
  have hBmeas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      Measurable (fun om => ∑ i : Fin d, ∑ j : Fin d, |B n w om i j|) := by
    intro n w
    by_cases hn : Allowed n w
    · simpa only [B, if_pos hn] using hmeas n w
    · simpa only [B, if_neg hn, Matrix.zero_apply, abs_zero, Finset.sum_const_zero] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  have hBmom : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d, |B n w om i j|) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * model.delta * (M - m)) := by
    intro n w
    by_cases hn : Allowed n w
    · simpa only [B, if_pos hn] using hmom n w hn
    · simpa only [B, if_neg hn, Matrix.zero_apply, abs_zero, Finset.sum_const_zero,
        eLpNorm_zero'] using (zero_le)
  have hBband : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (Hband : ℕ),
      eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
        |B n w om i j - (P[fun om' => B n w om' i j | Band n Hband]) om|)
        (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * model.delta * (M - m) * (3 : ℝ) ^ (-aexp * (Hband : ℝ))) := by
    intro n w Hband
    by_cases hn : Allowed n w
    · simpa only [B, if_pos hn] using hband n w Hband hn
    · simp only [B, if_neg hn, Matrix.zero_apply]
      change eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
        |(0 : ℝ) - (P[(0 : Ω → ℝ) | Band n Hband]) om|) (ENNReal.ofReal p) P ≤ _
      rw [condExp_zero]
      simpa only [Pi.zero_apply, sub_self, abs_zero, Finset.sum_const_zero, eLpNorm_zero'] using
        (zero_le)
  have heq (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) :
      {om | (∑ i : Fin d, ∑ j : Fin d, |B n w om i j|) ≤ eps * c0 * (M - m)} = Good2 n w := by
    ext om
    by_cases hn : Allowed n w
    · simp only [Good2, B, if_pos hn, mem_setOf_eq, hn, true_implies]
    · have hnonneg : 0 ≤ eps * c0 * (M - m) :=
        mul_nonneg (mul_pos heps hc0).le (sub_nonneg.mpr hmM)
      simp only [Good2, B, if_neg hn, Matrix.zero_apply, abs_zero,
        Finset.sum_const_zero, mem_setOf_eq, hn, false_implies, hnonneg]
  obtain ⟨Bextra, hBe, hBpos, hgood⟩ := hchain model hmodel Ω P field hfield hfieldlaw
    m M hmM B hBmeas hBmom hBband
  refine ⟨Bextra, hBe, hBpos, ?_⟩
  simpa only [heq] using hgood

end
end Paper


end

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff

namespace Paper

theorem aux_thm_prop_endpoint_invariance_bounds_side_fields
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (hbundle : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N) :
    ∃ (D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)))
      (phi : D → Homogenization.H1Function (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
      (alpha : ℝ),
      Dense (D : Set (DomainL2 (centeredCube z0 r0 hr0))) ∧
      (∀ f : D, ContDiff ℝ (⊤ : ℕ∞) (phi f).toFun ∧
        HasCompactSupport (phi f).toFun ∧
        tsupport (phi f).toFun ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
        (sobolevDataOfH1 (phi f)).1 = f.val) ∧
      (∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
        ∃ Kset : Set (SpatialCoordinates d),
          IsCompact Kset ∧ Kset ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
          ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
            (vN n).val.1
              =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vcN n ∧
            ContinuousOn (vcN n) (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) ∧
            (∀ x ∈ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
            Lane4.IsHolderOn alpha
              (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ∧
            Lane4.cAlphaNorm alpha
              (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
            responseForm S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
              (vN n) (vN n) ≤ M ∧
            ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
              |vcN n x - (phi f).toFun x| ≤ Cphi * (r0 / (3 : ℝ) ^ k)) ∧
      (∀ f : SpatialCoordinates d → ℝ, Continuous f → HasCompactSupport f →
        tsupport f ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) →
        ∀ ε : ℝ, 0 < ε →
        ∃ g : D, ∀ x : SpatialCoordinates d, |(phi g).toFun x - f x| ≤ ε) := by
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨D, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨hDdense, hbundle⟩ := hbundle
  obtain ⟨phi, hbundle⟩ := hbundle
  obtain ⟨hPhi, hbundle⟩ := hbundle
  obtain ⟨alpha, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨hFiniteMesh, hbundle⟩ := hbundle
  obtain ⟨hsmooth, _⟩ := hbundle
  exact ⟨D, phi, alpha, hDdense, hPhi, hFiniteMesh, hsmooth⟩

theorem aux_thm_prop_endpoint_invariance_hFM_fields
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0)) (N : ℕ → ℕ)
    (D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)))
    (phi : D → Homogenization.H1Function (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
    (alpha : ℝ) (g : D) (Cphi : ℝ) (k0 : ℕ) (k : ℕ) (hk0k : k0 ≤ k)
    (hFM : ∀ k : ℕ, k0 ≤ k →
      ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧ Kset ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
          (vN n).val.1
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vcN n ∧
          ContinuousOn (vcN n) (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
          Lane4.IsHolderOn alpha
            (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ∧
          Lane4.cAlphaNorm alpha
            (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
          responseForm S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
            (vN n) (vN n) ≤ M ∧
          ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
            |vcN n x - (phi g).toFun x| ≤ Cphi * (r0 / (3 : ℝ) ^ k)) :
    ∃ (vN : ℕ → S.space) (vcN : ℕ → SpatialCoordinates d → ℝ) (M : ℝ),
      (∀ n : ℕ, (vN n).val.1
        =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vcN n) ∧
      (∀ n : ℕ, responseForm S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
        (vN n) (vN n) ≤ M) ∧
      (∀ n : ℕ, ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
        |vcN n x - (phi g).toFun x| ≤ Cphi * (r0 / (3 : ℝ) ^ k)) := by
  obtain ⟨vN, vcN, Kset, -, -, M, hM0, hconj⟩ := hFM k hk0k
  exact ⟨vN, vcN, M, fun n => (hconj n).1, fun n => (hconj n).2.2.2.2.2.1,
    fun n => (hconj n).2.2.2.2.2.2⟩

theorem aux_thm_prop_endpoint_invariance_hk_of_Cphi
    (Cphi : ℝ) (hCphi0 : 0 ≤ Cphi) (k0 : ℕ) (r0 : ℝ) (hr0 : 0 < r0)
    (ε' : ℝ) (hε'pos : 0 < ε') :
    ∃ k : ℕ, k0 ≤ k ∧ Cphi * (r0 / (3 : ℝ) ^ k) ≤ ε' := by
  rcases eq_or_lt_of_le hCphi0 with hCphi0eq | hCphi0pos
  · exact ⟨k0, le_refl k0, by rw [← hCphi0eq]; simp; positivity⟩
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (div_pos hε'pos (mul_pos hCphi0pos hr0)) (show (1 / 3 : ℝ) < 1 by norm_num)
    refine ⟨max n k0, le_max_right n k0, ?_⟩
    have hpow : (1 / 3 : ℝ) ^ (max n k0) ≤ (1 / 3 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left n k0)
    have hstep : (1 / 3 : ℝ) ^ (max n k0) * (Cphi * r0) < ε' := by
      calc (1 / 3 : ℝ) ^ (max n k0) * (Cphi * r0)
          ≤ (1 / 3 : ℝ) ^ n * (Cphi * r0) :=
            mul_le_mul_of_nonneg_right hpow (mul_pos hCphi0pos hr0).le
        _ < (ε' / (Cphi * r0)) * (Cphi * r0) :=
            mul_lt_mul_of_pos_right hn (mul_pos hCphi0pos hr0)
        _ = ε' := div_mul_cancel₀ ε' (mul_pos hCphi0pos hr0).ne'
    have hrw : Cphi * (r0 / (3 : ℝ) ^ (max n k0)) =
        (1 / 3 : ℝ) ^ (max n k0) * (Cphi * r0) := by
      rw [div_pow, one_pow]; ring
    rw [hrw]; exact hstep.le

theorem aux_thm_prop_endpoint_invariance_norm_bound
    {d : ℕ} (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (φ : DomainL2 (centeredCube z0 r0 hr0)) (fc : SpatialCoordinates d → ℝ)
    (hφfc : (φ : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] fc)
    (ε ε' : ℝ) (hε : 0 < ε) (hε'pos : 0 < ε')
    (hε'def : ε' = ε / (2 * Real.sqrt
      ((volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal)))
    (v : DomainL2 (centeredCube z0 r0 hr0)) (vc w : SpatialCoordinates d → ℝ)
    (hveq : (v : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vc)
    (rk : ℝ)
    (hbnd : ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
      |vc x - w x| ≤ rk)
    (hg : ∀ x : SpatialCoordinates d, |w x - fc x| ≤ ε') (hkbound : rk ≤ ε') :
    ‖v - φ‖ ≤ ε := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))
    with hQdef
  have hvolQ : volume Q = ENNReal.ofReal (r0 ^ d) := centeredCube_volume z0 hr0
  have hvolQne : volume Q ≠ ⊤ := by rw [hvolQ]; exact ENNReal.ofReal_ne_top
  have hptbound : ∀ x ∈ Q, |vc x - fc x| ≤ 2 * ε' := by
    intro x hx
    have h1 : |vc x - w x| ≤ rk := hbnd x (subset_closure hx)
    have h2 : |w x - fc x| ≤ ε' := hg x
    have := abs_sub_le (vc x) (w x) (fc x)
    linarith [hkbound]
  have hae : ∀ᵐ x ∂(volume.restrict Q), ‖(v - φ) x‖ ≤ 2 * ε' := by
    have hbase : ∀ᵐ x ∂(volume.restrict Q), x ∈ Q ∧
        v x = vc x ∧ (φ : SpatialCoordinates d → ℝ) x = fc x := by
      filter_upwards [ae_restrict_mem (centeredCube z0 r0 hr0).isOpen.measurableSet,
        hveq, hφfc] with x hx h1 h2 using ⟨hx, h1, h2⟩
    filter_upwards [hbase, Lp.coeFn_sub v φ] with x hx hsub
    rw [hsub]
    show ‖v x - φ x‖ ≤ 2 * ε'
    rw [hx.2.1, hx.2.2, Real.norm_eq_abs]
    exact hptbound x hx.1
  have hL2 : ‖v - φ‖ ≤ (2 * ε') * Real.sqrt ((volume.restrict Q Set.univ).toReal) := by
    refine DirichletForm.ClosedForm.norm_le_of_ae_indicator_bound MeasurableSet.univ
      (by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hvolQne) (by positivity) ?_
    filter_upwards [hae] with x hx
    rwa [Set.indicator_univ]
  rw [MeasureTheory.Measure.restrict_apply_univ] at hL2
  have hsqrtne : Real.sqrt ((volume Q).toReal) ≠ 0 := by
    rw [hvolQ, ENNReal.toReal_ofReal (by positivity)]
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hfinal : (2 * ε') * Real.sqrt ((volume Q).toReal) = ε := by
    have hgoal : (2 * ε') * Real.sqrt ((volume Q).toReal)
        = ε' * (2 * Real.sqrt ((volume Q).toReal)) := by ring
    rw [hgoal, hε'def]
    exact div_mul_cancel₀ ε (mul_ne_zero two_ne_zero hsqrtne)
  linarith [hL2, hfinal.symm.le, hfinal.le]

theorem aux_thm_prop_endpoint_invariance_fc_setup
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (hbundle : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N)
    (fc : SpatialCoordinates d → ℝ) (hfcSmooth : ContDiff ℝ (⊤ : ℕ∞) fc)
    (hfcSupp : HasCompactSupport fc)
    (hfcTsupp : tsupport fc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)))
      (phi : D → Homogenization.H1Function (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
      (alpha : ℝ),
      (∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
        ∃ Kset : Set (SpatialCoordinates d),
          IsCompact Kset ∧ Kset ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
          ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
            (vN n).val.1
              =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vcN n ∧
            ContinuousOn (vcN n) (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) ∧
            (∀ x ∈ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
            Lane4.IsHolderOn alpha
              (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ∧
            Lane4.cAlphaNorm alpha
              (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
            responseForm S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
              (vN n) (vN n) ≤ M ∧
            ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
              |vcN n x - (phi f).toFun x| ≤ Cphi * (r0 / (3 : ℝ) ^ k)) ∧
      ∃ (ε' : ℝ), (ε' = ε / (2 * Real.sqrt
        ((volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal)) ∧ 0 < ε') ∧
      ∃ (g : D), ∀ x : SpatialCoordinates d, |(phi g).toFun x - fc x| ≤ ε' := by
  obtain ⟨D, phi, alpha, _hDdense, _hPhi, hFiniteMesh, hsmooth⟩ :=
    aux_thm_prop_endpoint_invariance_bounds_side_fields hd model H om z0 r0 hr0 S G N hbundle
  have hvolQ : volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))
      = ENNReal.ofReal (r0 ^ d) := centeredCube_volume z0 hr0
  have hvolQtoReal : (volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal
      = r0 ^ d := by rw [hvolQ, ENNReal.toReal_ofReal (by positivity)]
  have hsqrtpos : 0 < Real.sqrt
      ((volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal) := by
    rw [hvolQtoReal]; exact Real.sqrt_pos.mpr (by positivity)
  let ε' : ℝ := ε / (2 * Real.sqrt
    ((volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal))
  have hε'def : ε' = ε / (2 * Real.sqrt
      ((volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal)) := rfl
  have hε'pos : 0 < ε' := div_pos hε (by linarith [hsqrtpos])
  obtain ⟨g, hg⟩ := hsmooth fc hfcSmooth.continuous hfcSupp hfcTsupp ε' hε'pos
  exact ⟨D, phi, alpha, hFiniteMesh, ε', ⟨hε'def, hε'pos⟩, g, hg⟩

theorem aux_thm_prop_endpoint_invariance_hmesh_of_bounds_side
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (hbundle : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N) :
    ∀ φ : DomainL2 (centeredCube z0 r0 hr0),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
          (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε) := by
  intro φ hφex ε hε
  obtain ⟨fc, hfcSmooth, hfcSupp, hfcTsupp, hφfc⟩ := hφex
  obtain ⟨D, phi, alpha, hFiniteMesh, ε', ⟨hε'def, hε'pos⟩, g, hg⟩ :=
    aux_thm_prop_endpoint_invariance_fc_setup hd model H om z0 r0 hr0 S G N hbundle
      fc hfcSmooth hfcSupp hfcTsupp ε hε
  clear hbundle hfcSmooth hfcSupp hfcTsupp
  obtain ⟨Cphi, hCphi0, k0, hFM⟩ := hFiniteMesh g
  clear hFiniteMesh
  have hk : ∃ k : ℕ, k0 ≤ k ∧ Cphi * (r0 / (3 : ℝ) ^ k) ≤ ε' :=
    aux_thm_prop_endpoint_invariance_hk_of_Cphi Cphi hCphi0 k0 r0 hr0 ε' hε'pos
  obtain ⟨k, hk0k, hkbound⟩ := hk
  clear hCphi0
  obtain ⟨vN, vcN, M, hvNeqAll, hrespAll, hbndAll⟩ :=
    aux_thm_prop_endpoint_invariance_hFM_fields hd model H om z0 r0 hr0 S N D phi alpha g Cphi k0
      k hk0k hFM
  refine ⟨vN, M, hrespAll, fun n => ?_⟩
  have hvNeq := hvNeqAll n
  have hbnd := hbndAll n
  exact aux_thm_prop_endpoint_invariance_norm_bound z0 r0 hr0 φ fc hφfc ε ε' hε hε'pos hε'def
    (vN n).val.1 (vcN n) (phi g).toFun hvNeq (Cphi * (r0 / (3 : ℝ) ^ k)) hbnd hg hkbound

theorem aux_thm_prop_regularity_instance_killed_gdense
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hGmem : ∀ f : DomainL2 (centeredCube z r hr), G f ∈ E.toClosedForm.domain)
    (hRange : ∀ v ∈ E.toClosedForm.domain, ∀ ε : ℝ, 0 < ε →
      ∃ f0 : DomainL2 (centeredCube z r hr), E.toClosedForm.energyNormSq (v - G f0) < ε)
    (hGbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : DomainL2 (centeredCube z r hr),
      E.toClosedForm.energyNormSq (G f) ≤ C * ‖f‖ ^ 2)
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (hDdense : Dense (D : Set (DomainL2 (centeredCube z r hr)))) :
    ∀ v ∈ E.toClosedForm.domain, ∀ ε : ℝ, 0 < ε →
      ∃ f : D, E.toClosedForm.energyNormSq (v - G f.val) < ε := by
  obtain ⟨C, hC0, hGbound⟩ := hGbound
  intro v hv ε hε
  obtain ⟨f0, hf0⟩ := hRange v hv (ε / 16) (by positivity)
  set δ : ℝ := Real.sqrt (ε / 16) / (Real.sqrt C + 1) with hδdef
  have hδpos : 0 < δ := by positivity
  obtain ⟨f', hf'D, hf'dist⟩ :=
    Metric.mem_closure_iff.mp (hDdense f0) δ hδpos
  refine ⟨⟨f', hf'D⟩, ?_⟩
  have hlin : G f0 - G f' = G (f0 - f') := (G.map_sub f0 f').symm
  have hCsq : C ≤ (Real.sqrt C + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt hC0, Real.sqrt_nonneg C]
  have hδsq : δ ^ 2 = (ε / 16) / (Real.sqrt C + 1) ^ 2 := by
    rw [hδdef, div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ ε / 16 by positivity)]
  have hδsq_eq : δ ^ 2 * (Real.sqrt C + 1) ^ 2 = ε / 16 := by
    rw [hδsq]
    have hne : (Real.sqrt C + 1) ^ 2 ≠ 0 := by positivity
    field_simp
  have hCδsq : C * δ ^ 2 ≤ ε / 16 := by
    rw [← hδsq_eq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hCsq) (sq_nonneg δ)]
  have hbound2 : E.toClosedForm.energyNormSq (G f0 - G f') ≤ ε / 16 := by
    rw [hlin]
    calc E.toClosedForm.energyNormSq (G (f0 - f'))
        ≤ C * ‖f0 - f'‖ ^ 2 := hGbound (f0 - f')
      _ ≤ C * δ ^ 2 := by
          gcongr
          rw [← dist_eq_norm]
          exact hf'dist.le
      _ ≤ ε / 16 := hCδsq
  have htri := E.toClosedForm.sqrt_energyNormSq_sub_le hv (hGmem f0) (hGmem f')
  have h1 : Real.sqrt (E.toClosedForm.energyNormSq (v - G f0)) < Real.sqrt (ε / 16) :=
    Real.sqrt_lt_sqrt (E.toClosedForm.energyNormSq_nonneg
      (E.toClosedForm.domain.sub_mem hv (hGmem f0))) hf0
  have h2 : Real.sqrt (E.toClosedForm.energyNormSq (G f0 - G f')) ≤ Real.sqrt (ε / 16) :=
    Real.sqrt_le_sqrt hbound2
  have hsum := add_lt_add_of_lt_of_le h1 h2
  have hfinal : Real.sqrt (E.toClosedForm.energyNormSq (v - G f')) <
      Real.sqrt (ε / 16) + Real.sqrt (ε / 16) := lt_of_le_of_lt htri hsum
  have hle : Real.sqrt (ε / 16) + Real.sqrt (ε / 16) ≤ Real.sqrt ε := by
    have heq : Real.sqrt (ε / 16) + Real.sqrt (ε / 16) = Real.sqrt (ε / 4) := by
      rw [show ε / 16 = (ε / 4) * (1 / 4 : ℝ) by ring, Real.sqrt_mul (by positivity),
        show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    rw [heq]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlt : Real.sqrt (E.toClosedForm.energyNormSq (v - G f')) < Real.sqrt ε :=
    lt_of_lt_of_le hfinal hle
  have hnn : 0 ≤ E.toClosedForm.energyNormSq (v - G f') :=
    E.toClosedForm.energyNormSq_nonneg (E.toClosedForm.domain.sub_mem hv (hGmem f'))
  have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hlt
  simpa only [Real.sq_sqrt hnn, Real.sq_sqrt hε.le] using hsq

theorem aux_thm_prop_regularity_instance_killed
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (N : ℕ → ℕ)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ v : DomainL2 (centeredCube z r hr),
      E.toClosedForm.energy v = limitFormEnergy G v)
    (hGmem : ∀ f : DomainL2 (centeredCube z r hr), G f ∈ E.toClosedForm.domain)
    (hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      E.toClosedForm.energy v ≤
        liminf (fun n => ((responseForm S
          (Lane4.cutoffPositiveCoefficient model H om (N n) z hr) (vN n) (vN n) : ℝ) :
            EReal)) atTop)
    (hbundle : aux_in_represented_bounds_side d hd model H om z r hr S G N)
    (hRange : ∀ v ∈ E.toClosedForm.domain, ∀ ε : ℝ, 0 < ε →
      ∃ f0 : DomainL2 (centeredCube z r hr), E.toClosedForm.energyNormSq (v - G f0) < ε)
    (hGbound : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ f : DomainL2 (centeredCube z r hr),
      E.toClosedForm.energyNormSq (G f) ≤ Cb * ‖f‖ ^ 2) :
    (∃ C : Set (DomainL2 (centeredCube z r hr)),
      DirichletForm.IsCoreOn E.toClosedForm
        (centeredCube z r hr : Set (SpatialCoordinates d)) C) ∧
    DirichletForm.IsRegular E.toClosedForm := by
  obtain ⟨KN, hKN, Kstar, hKstar, hfrac, hcoercive, hInterp, t, ht, htd, hcutoffs,
    D, hDcount, hDdense, phi, hPhi, alpha, eta, halpha_gt, halpha_lt, heta_pos, heta_lt,
    u, uc, hU, hUrep, hUconv, hUholder, rho, hrho, chi, hChi, w, hW, hCollarError,
    hFiniteMesh, hsmooth, -⟩ := hbundle
  haveI : Countable D := hDcount
  have hGdense := aux_thm_prop_regularity_instance_killed_gdense d z r hr G E hGmem hRange hGbound D hDdense
  exact prop_regularity d hd z r hr S hS
    (fun n => Lane4.cutoffPositiveCoefficient model H om (N n) z hr)
    E G hE hGmem hLower D hDdense phi hPhi hGdense
    alpha eta t halpha_gt halpha_lt heta_pos ht heta_lt
    u uc hU hUrep hUconv hUholder rho hrho chi hChi w hW hCollarError hFiniteMesh hsmooth

theorem aux_thm_prop_hregularity_supply
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N0 : ℕ → ℕ)
    (hbundle0 : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 Sspace0 G0 N0) :
    ∃ K : ℝ, 0 < K ∧
      (∀ (n : ℕ) (v : Sspace0.space),
        cubeFractionalL2Seminorm hd z0 r0 hr0 Lane4.threeQuarterOrder
            (fun _ : Fin 1 => v.val.1) < ⊤ ∧
        ‖v.val.1‖ ^ 2 + volume.real (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd z0 r0 hr0 Lane4.threeQuarterOrder
                (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
          K * responseForm Sspace0
            (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) v v) ∧
      ∃ D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)),
        (D : Set (DomainL2 (centeredCube z0 r0 hr0))).Countable ∧
        Dense (D : Set (DomainL2 (centeredCube z0 r0 hr0))) ∧
        (∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
          HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
          (f.val : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] fc) ∧
      CubeFractionalInterpolationInput d hd := by
  obtain ⟨KN, hKN, Kstar, hKstar, hfrac, hcoercive, hInterp, t, ht, htd, hcutoffs,
    D, hDcountRaw, hDdense, phi, hPhi, alpha, eta, halpha_gt, halpha_lt, heta_pos, heta_lt,
    u, uc, hU, hUrep, hUconv, hUholder, rho, hrho, chi, hChi, w, hW, hCollarError,
    hFiniteMesh, hsmooth, -⟩ := hbundle0
  haveI : Countable D := hDcountRaw
  have hDcountSet : Countable (D : Set (DomainL2 (centeredCube z0 r0 hr0))) := hDcountRaw
  refine ⟨max Kstar 1, lt_of_lt_of_le one_pos (le_max_right Kstar 1), fun n v => ⟨hfrac v, ?_⟩,
    D, Set.countable_coe_iff.mp hDcountSet, hDdense, fun f => ?_, hInterp⟩
  · have h1 := hcoercive n v
    have h2 : KN n ≤ max Kstar 1 := (hKstar n).trans (le_max_left Kstar 1)
    have h3 := responseForm_nonneg Sspace0
      (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) v
    calc ‖v.val.1‖ ^ 2 + volume.real (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd z0 r0 hr0 Lane4.threeQuarterOrder
                (fun _ : Fin 1 => v.val.1)).toReal) ^ 2
        ≤ KN n * responseForm Sspace0
            (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) v v := h1
      _ ≤ max Kstar 1 * responseForm Sspace0
            (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) v v :=
          mul_le_mul_of_nonneg_right h2 h3
  · obtain ⟨hC1, hC2, hC3, hC4⟩ := hPhi f
    refine ⟨(phi f).toFun, hC1, hC2, hC3, ?_⟩
    have hb := sobolevDataOfH1_fst_coeFn (phi f)
    rwa [hC4] at hb

theorem aux_thm_prop_hregularity_hRange_of_root
    {d : ℕ} {z0 : SpatialCoordinates d} {r0 : ℝ} {hr0 : 0 < r0}
    (G0 Rroot : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (EForm : _root_.DirichletForm (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (hE : ∀ v : DomainL2 (centeredCube z0 r0 hr0),
      EForm.toClosedForm.energy v = limitFormEnergy G0 v)
    (hSymmC : ∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (G0 x) y = inner ℝ x (G0 y))
    (hRsymm : ∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (Rroot x) y = inner ℝ x (Rroot y))
    (hRcomp : Rroot.comp Rroot = G0)
    (hRinj : Function.Injective Rroot)
    (hRdom : limitFormDomain G0 = Set.range Rroot)
    (hGmem : ∀ f : DomainL2 (centeredCube z0 r0 hr0), G0 f ∈ EForm.toClosedForm.domain)
    (hEdomIff : ∀ v0 : DomainL2 (centeredCube z0 r0 hr0),
      v0 ∈ EForm.toClosedForm.domain ↔ v0 ∈ limitFormDomain G0) :
    ∀ v ∈ EForm.toClosedForm.domain, ∀ ε : ℝ, 0 < ε →
      ∃ f0 : DomainL2 (centeredCube z0 r0 hr0),
        EForm.toClosedForm.energyNormSq (v - G0 f0) < ε := by
  have hdenseR : Dense (Set.range Rroot : Set (DomainL2 (centeredCube z0 r0 hr0))) := by
    have h := aux_prop_killed_inverse_dirichlet_form_root_dense Rroot hRsymm hRinj
    rw [LinearMap.coe_range] at h
    simpa using h
  intro v hv ε hε
  have hvdom : v ∈ limitFormDomain G0 := (hEdomIff v).mp hv
  rw [hRdom] at hvdom
  obtain ⟨wv, hwv⟩ := hvdom
  set δ : ℝ := Real.sqrt (ε / (2 * (1 + ‖Rroot‖ ^ 2))) with hδdef
  have hδpos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨y, hyR, hydist⟩ := Metric.mem_closure_iff.mp (hdenseR wv) δ hδpos
  obtain ⟨f0, hf0⟩ := hyR
  refine ⟨f0, ?_⟩
  have hGf0 : G0 f0 = Rroot (Rroot f0) := by
    rw [← ContinuousLinearMap.comp_apply, hRcomp]
  have hnorm : ‖wv - Rroot f0‖ < δ := by
    rw [← hf0] at hydist; rwa [dist_eq_norm] at hydist
  have hveq : v - G0 f0 = Rroot (wv - Rroot f0) := by
    rw [map_sub, hwv, hGf0]
  have hmemsub : v - G0 f0 ∈ EForm.toClosedForm.domain :=
    EForm.toClosedForm.domain.sub_mem hv (hGmem f0)
  have hval : EForm.toClosedForm.energy (v - G0 f0) =
      (EForm.toClosedForm.form (v - G0 f0) (v - G0 f0) : EReal) :=
    EForm.toClosedForm.energy_of_mem hmemsub
  have hdual := aux_prop_killed_inverse_dirichlet_form_dual_energy_root_range G0 Rroot
    hSymmC hRsymm hRcomp hRinj (wv - Rroot f0)
  rw [real_inner_self_eq_norm_sq] at hdual
  have heq2 : limitFormEnergy G0 (Rroot (wv - Rroot f0)) =
      ((‖wv - Rroot f0‖ ^ 2 : ℝ) : EReal) := hdual
  have hchain : (EForm.toClosedForm.form (v - G0 f0) (v - G0 f0) : EReal) =
      ((‖wv - Rroot f0‖ ^ 2 : ℝ) : EReal) := by
    rw [← hval, hE, hveq]; exact heq2
  have hformeq : EForm.toClosedForm.form (v - G0 f0) (v - G0 f0) = ‖wv - Rroot f0‖ ^ 2 := by
    exact_mod_cast hchain
  have hnormle : ‖v - G0 f0‖ ≤ ‖Rroot‖ * ‖wv - Rroot f0‖ := by
    rw [hveq]; exact Rroot.le_opNorm _
  have h1 : ‖v - G0 f0‖ ^ 2 ≤ ‖Rroot‖ ^ 2 * ‖wv - Rroot f0‖ ^ 2 := by
    have hh := mul_self_le_mul_self (norm_nonneg _) hnormle
    nlinarith [hh]
  have hsqlt : ‖wv - Rroot f0‖ ^ 2 < δ ^ 2 := by
    have hh := mul_self_lt_mul_self (norm_nonneg _) hnorm
    nlinarith [hh]
  have hδsq2 : 2 * ((1 + ‖Rroot‖ ^ 2) * δ ^ 2) = ε := by
    rw [← mul_assoc, hδdef, Real.sq_sqrt (by positivity), mul_comm]
    exact div_mul_cancel₀ ε (by positivity)
  have hhalf : (1 + ‖Rroot‖ ^ 2) * δ ^ 2 = ε / 2 := by linarith [hδsq2]
  have hstep : (1 + ‖Rroot‖ ^ 2) * ‖wv - Rroot f0‖ ^ 2 < (1 + ‖Rroot‖ ^ 2) * δ ^ 2 :=
    mul_lt_mul_of_pos_left hsqlt (by positivity)
  show EForm.toClosedForm.form (v - G0 f0) (v - G0 f0) + ‖v - G0 f0‖ ^ 2 < ε
  rw [hformeq]
  nlinarith [h1, hstep, hhalf]

theorem aux_thm_prop_hregularity_hGbound_of_root
    {d : ℕ} {z0 : SpatialCoordinates d} {r0 : ℝ} {hr0 : 0 < r0}
    (G0 Rroot : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (EForm : _root_.DirichletForm (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (hE : ∀ v : DomainL2 (centeredCube z0 r0 hr0),
      EForm.toClosedForm.energy v = limitFormEnergy G0 v)
    (hSymmC : ∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (G0 x) y = inner ℝ x (G0 y))
    (hRsymm : ∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (Rroot x) y = inner ℝ x (Rroot y))
    (hRcomp : Rroot.comp Rroot = G0)
    (hRinj : Function.Injective Rroot)
    (hGmem : ∀ f : DomainL2 (centeredCube z0 r0 hr0), G0 f ∈ EForm.toClosedForm.domain) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ f : DomainL2 (centeredCube z0 r0 hr0),
      EForm.toClosedForm.energyNormSq (G0 f) ≤ Cb * ‖f‖ ^ 2 := by
  refine ⟨‖Rroot‖ ^ 2 + ‖G0‖ ^ 2, by positivity, fun f => ?_⟩
  have hmemf : G0 f ∈ EForm.toClosedForm.domain := hGmem f
  have hGf : G0 f = Rroot (Rroot f) := by rw [← ContinuousLinearMap.comp_apply, hRcomp]
  have hdual2 := aux_prop_killed_inverse_dirichlet_form_dual_energy_root_range G0 Rroot
    hSymmC hRsymm hRcomp hRinj (Rroot f)
  rw [real_inner_self_eq_norm_sq] at hdual2
  have heq3 : limitFormEnergy G0 (G0 f) = ((‖Rroot f‖ ^ 2 : ℝ) : EReal) := by
    rw [hGf]; exact hdual2
  have hval2 : EForm.toClosedForm.energy (G0 f) =
      (EForm.toClosedForm.form (G0 f) (G0 f) : EReal) :=
    EForm.toClosedForm.energy_of_mem hmemf
  have hchain2 : (EForm.toClosedForm.form (G0 f) (G0 f) : EReal) =
      ((‖Rroot f‖ ^ 2 : ℝ) : EReal) := by
    rw [← hval2, hE]; exact heq3
  have hformeq2 : EForm.toClosedForm.form (G0 f) (G0 f) = ‖Rroot f‖ ^ 2 := by
    exact_mod_cast hchain2
  show EForm.toClosedForm.form (G0 f) (G0 f) + ‖G0 f‖ ^ 2 ≤
      (‖Rroot‖ ^ 2 + ‖G0‖ ^ 2) * ‖f‖ ^ 2
  rw [hformeq2]
  have h2 : ‖Rroot f‖ ≤ ‖Rroot‖ * ‖f‖ := Rroot.le_opNorm f
  have h3 : ‖G0 f‖ ≤ ‖G0‖ * ‖f‖ := G0.le_opNorm f
  have h2sq : ‖Rroot f‖ ^ 2 ≤ ‖Rroot‖ ^ 2 * ‖f‖ ^ 2 := by
    have hh := mul_self_le_mul_self (norm_nonneg (Rroot f)) h2
    nlinarith [hh]
  have h3sq : ‖G0 f‖ ^ 2 ≤ ‖G0‖ ^ 2 * ‖f‖ ^ 2 := by
    have hh := mul_self_le_mul_self (norm_nonneg (G0 f)) h3
    nlinarith [hh]
  nlinarith [h2sq, h3sq]

def aux_thm_prop_bounds_pointwise
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) : Prop :=
  ∃ G : Set (BilateralField d), MeasurableSet G ∧ (chaosSampleLaw model).toMeasure Gᶜ = 0 ∧
    ∀ om ∈ G, ∀ i : ℕ,
      (∀ Glim : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)),
        (∀ f : DomainL2 (centeredCube (z i) (r i) (hr i)),
          Tendsto (fun n => (responseSolution (Sspace i)
            (Lane4.cutoffPositiveCoefficient model H om (NE n) (z i) (hr i))
            ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1)
            atTop (𝓝 (Glim f))) →
        aux_in_represented_bounds_side d hd model H om (z i) (r i) (hr i) (Sspace i) Glim NE) ∧
      (∀ Glim : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)),
        (∀ f : DomainL2 (centeredCube (z i) (r i) (hr i)),
          Tendsto (fun n => (responseSolution (Sspace i)
            (Lane4.cutoffPositiveCoefficient model H om (NF n) (z i) (hr i))
            ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1)
            atTop (𝓝 (Glim f))) →
        aux_in_represented_bounds_side d hd model H om (z i) (r i) (hr i) (Sspace i) Glim NF)


theorem aux_thm_prop_bounds_pointwise_ae
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {field : Ω → BilateralField d}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ i, 0 < r i}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i))}
    {NE NF : ℕ → ℕ}
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (hfieldMeas : Measurable field) (hmap : Measure.map field P = (chaosSampleLaw model).toMeasure)
    (hPW : aux_thm_prop_bounds_pointwise d hd model H z r hr Sspace NE NF) :
    in_represented_bounds d hd model H Ω P field z r hr Sspace GE GF NE NF := by
  obtain ⟨G, hGmeas, _hGcompl, hG⟩ := hPW
  have haeField : ∀ᵐ omega ∂P, field omega ∈ G := by
    have hae : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure, om ∈ G := by
      rw [ae_iff]
      exact _hGcompl
    rw [← hmap] at hae
    exact ae_of_ae_map hfieldMeas.aemeasurable hae
  have hformula : ∀ i N omega f, GN i N omega f =
      (responseSolution (Sspace i)
        (Lane4.cutoffPositiveCoefficient model H (field omega) N (z i) (hr i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1 :=
    hJoint.2.2.2.2.2.2.1
  have htendsto : ∀ᵐ omega ∂P, ∀ i,
      Tendsto (fun n => GN i (NE n) omega) atTop (𝓝 (GE i omega)) ∧
      Tendsto (fun n => GN i (NF n) omega) atTop (𝓝 (GF i omega)) :=
    hJoint.2.2.2.2.2.2.2
  filter_upwards [haeField, htendsto] with omega hom htends i
  refine ⟨?_, ?_⟩
  · apply (hG (field omega) hom i).1 (GE i omega)
    intro f
    have heval : Tendsto (fun n => GN i (NE n) omega f) atTop (𝓝 (GE i omega f)) :=
      ((ContinuousLinearMap.apply ℝ (DomainL2 (centeredCube (z i) (r i) (hr i))) f).continuous.tendsto
        (GE i omega)).comp (htends i).1
    simpa only [hformula i (NE _) omega f] using heval
  · apply (hG (field omega) hom i).2 (GF i omega)
    intro f
    have heval : Tendsto (fun n => GN i (NF n) omega f) atTop (𝓝 (GF i omega f)) :=
      ((ContinuousLinearMap.apply ℝ (DomainL2 (centeredCube (z i) (r i) (hr i))) f).continuous.tendsto
        (GF i omega)).comp (htends i).2
    simpa only [hformula i (NF _) omega f] using heval

end Paper
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Paper

theorem aux_thm_prop_property_of_limit {V : Type*} [TopologicalSpace V] [T2Space V]
    (GN : ℕ → V) (G : V) (hconv : Tendsto GN atTop (𝓝 G))
    (property : V → Prop) (hconv_of : ∀ x, property x → Tendsto GN atTop (𝓝 x))
    (hex : ∃! x, property x) : property G := by
  obtain ⟨x, hx, _⟩ := hex
  have hxG : x = G := tendsto_nhds_unique (hconv_of x hx) hconv
  exact hxG ▸ hx

theorem aux_thm_prop_inverse_limit_form
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (hcontract : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
        ((v.val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
            (fun x => T (u.val.1 x))) ∧
        responseForm S (a n) v v ≤ responseForm S (a n) u u)
    (GN : ℕ → DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (hGN : ∀ (n : ℕ) (f : DomainL2 (centeredCube z R hR)), GN n f =
      (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (K : ℝ) (hK : 0 < K)
    (hCoercive : ∀ (n : ℕ) (v : S.space),
      cubeFractionalL2Seminorm hd z R hR Lane4.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z R hR Lane4.threeQuarterOrder
              (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
        K * responseForm S (a n) v v)
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    (hDcount : (D : Set (DomainL2 (centeredCube z R hR))).Countable)
    (hDdense : Dense (D : Set (DomainL2 (centeredCube z R hR))))
    (hDsmooth : ∀ f : D,
      ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (f.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fc)
    (hresponse : ∀ f : D, CauchySeq (fun n => inner ℝ f.val (GN n f.val)))
    (hmesh : ∀ φ : DomainL2 (centeredCube z R hR),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm S (a n) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (hconv : Tendsto GN atTop (𝓝 G)) :
    ∃ (EForm : _root_.DirichletForm
        (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
      (Rroot : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR)),
      (∀ v : DomainL2 (centeredCube z R hR),
        EForm.toClosedForm.energy v = limitFormEnergy G v) ∧
      (∀ x y : DomainL2 (centeredCube z R hR), inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x y : DomainL2 (centeredCube z R hR), inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
      Rroot.comp Rroot = G ∧
      limitFormDomain G = Set.range Rroot ∧
      Function.Injective Rroot ∧
      (∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z R hR)),
        (∀ f : DomainL2 (centeredCube z R hR),
          Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
        EForm.toClosedForm.energy v ≤
          liminf (fun n => ((responseForm S
            (a n) (vN n) (vN n) : ℝ) :
              EReal)) atTop) := by
  let EN : ℕ → DomainL2 (centeredCube z R hR) → EReal := fun n u =>
    sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧ e = (responseForm S (a n) w w : EReal)}
  have hEN : ∀ n u, EN n u =
      sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧ e = (responseForm S (a n) w w : EReal)} :=
    fun _ _ => rfl
  have hGc := aux_thm_prop_property_of_limit GN G hconv _
    (fun _ h => h.1.1)
    (prop_killed_inverse d hd z R hR S hS a hcontract GN hGN
      hInterp K hK hCoercive D hDcount hDdense hDsmooth hresponse EN hEN hmesh)
  obtain ⟨Rroot, hRsymm, _hRpos, hRcomp, hRdom⟩ := hGc.2.1
  obtain ⟨EForm, hEForm, _hHNC⟩ := hGc.2.2.1
  refine ⟨EForm, Rroot, hEForm, hGc.1.2.2.1, hRsymm, hRcomp, hRdom,
    aux_prop_killed_inverse_dirichlet_form_root_injective G Rroot hRcomp hGc.1.2.2.2.2, ?_⟩
  intro vN v hv
  rw [hEForm]
  exact aux_prop_killed_inverse_moscoS S a G EN hEN hGc.2.2.2.1.1 vN v hv

theorem aux_thm_prop_response_cauchy {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (GN : ℕ → V →L[ℝ] V) (G : V →L[ℝ] V)
    (hconv : Tendsto GN atTop (𝓝 G)) (f : V) :
    CauchySeq (fun n => inner ℝ f (GN n f)) := by
  have heval := ((ContinuousLinearMap.apply ℝ V f).continuous.tendsto G).comp hconv
  exact (tendsto_const_nhds.inner heval).cauchySeq

theorem aux_thm_prop_hregularity_construct
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (hSspace0 : Sspace0.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (hcontract0 : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : Sspace0.space,
        ∃ v : Sspace0.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) v v ≤
            responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) u u)
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N0 : ℕ → ℕ)
    (GN0 : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGN0 : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), GN0 n f =
      (responseSolution Sspace0
          (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0)
          ((sobolevVolumeLoad f).comp Sspace0.space.subtypeL)).val.1)
    (hGN0tendsto : Tendsto GN0 atTop (𝓝 G0))
    (K : ℝ) (hK0 : 0 < K)
    (hCoercive : ∀ (n : ℕ) (v : Sspace0.space),
      cubeFractionalL2Seminorm hd z0 r0 hr0 Lane4.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z0 r0 hr0 Lane4.threeQuarterOrder
              (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
        K * responseForm Sspace0
          (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) v v)
    (D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)))
    (hDcount : (D : Set (DomainL2 (centeredCube z0 r0 hr0))).Countable)
    (hDdense : Dense (D : Set (DomainL2 (centeredCube z0 r0 hr0))))
    (hDsmooth : ∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
      HasCompactSupport fc ∧
      tsupport fc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
      (f.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] fc)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (hbundle0 : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 Sspace0 G0 N0) :
    ∃ (EForm : _root_.DirichletForm
        (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
      (Rroot : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0)),
      (∀ v : DomainL2 (centeredCube z0 r0 hr0),
        EForm.toClosedForm.energy v = limitFormEnergy G0 v) ∧
      (∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (G0 x) y = inner ℝ x (G0 y)) ∧
      (∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
      Rroot.comp Rroot = G0 ∧
      limitFormDomain G0 = Set.range Rroot ∧
      Function.Injective Rroot ∧
      (∀ (vN : ℕ → Sspace0.space) (v : DomainL2 (centeredCube z0 r0 hr0)),
        (∀ f : DomainL2 (centeredCube z0 r0 hr0),
          Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
        EForm.toClosedForm.energy v ≤
          liminf (fun n => ((responseForm Sspace0
            (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) (vN n) (vN n) : ℝ) :
              EReal)) atTop) := by
  exact aux_thm_prop_inverse_limit_form d hd z0 r0 hr0 Sspace0 hSspace0
    (fun n => Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0)
    (fun n => hcontract0 (N0 n)) GN0 hGN0 hInterp K hK0 hCoercive D hDcount hDdense hDsmooth
    (fun f => aux_thm_prop_response_cauchy GN0 G0 hGN0tendsto f.val)
    (aux_thm_prop_endpoint_invariance_hmesh_of_bounds_side hd model H om z0 r0 hr0
      Sspace0 G0 N0 hbundle0) G0 hGN0tendsto

theorem aux_thm_prop_hregularity_side
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (hSspace0 : Sspace0.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (hcontract0 : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : Sspace0.space,
        ∃ v : Sspace0.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) v v ≤
            responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) u u)
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N0 : ℕ → ℕ)
    (GN0 : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGN0 : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), GN0 n f =
      (responseSolution Sspace0
          (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0)
          ((sobolevVolumeLoad f).comp Sspace0.space.subtypeL)).val.1)
    (hGN0tendsto : Tendsto GN0 atTop (𝓝 G0))
    (hbundle0 : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 Sspace0 G0 N0) :
    ∃ E : _root_.DirichletForm
        (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))),
      E.domain = limitFormDomain G0 ∧
      (∀ v : DomainL2 (centeredCube z0 r0 hr0),
        E.toClosedForm.energy v = limitFormEnergy G0 v) ∧
      ∃ Cc : Set (DomainL2 (centeredCube z0 r0 hr0)),
        DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) Cc := by
  obtain ⟨K, hK0, hCoercive, D, hDcount, hDdense, hDsmooth, hInterp⟩ :=
    aux_thm_prop_hregularity_supply hd model H om z0 r0 hr0 Sspace0 G0 N0 hbundle0
  obtain ⟨EForm, Rroot, hE, hSymmC, hRsymm, hRcomp, hRdom, hRinj, hLower⟩ :=
    aux_thm_prop_hregularity_construct hd model H om z0 r0 hr0 Sspace0 hSspace0 hcontract0 G0 N0 GN0 hGN0
      hGN0tendsto K hK0 hCoercive D hDcount hDdense hDsmooth hInterp hbundle0
  have hEdomIff : ∀ v0 : DomainL2 (centeredCube z0 r0 hr0),
      v0 ∈ EForm.toClosedForm.domain ↔ v0 ∈ limitFormDomain G0 := by
    intro v0
    show v0 ∈ EForm.toClosedForm.domain ↔ limitFormEnergy G0 v0 < ⊤
    rw [← hE v0]
    exact (EForm.toClosedForm.energy_lt_top_iff v0).symm
  have hGmem : ∀ f : DomainL2 (centeredCube z0 r0 hr0), G0 f ∈ EForm.toClosedForm.domain := by
    intro f
    refine (hEdomIff (G0 f)).mpr ?_
    rw [hRdom]
    exact ⟨Rroot f, by rw [← ContinuousLinearMap.comp_apply, hRcomp]⟩
  have hRange := aux_thm_prop_hregularity_hRange_of_root G0 Rroot EForm hE hSymmC hRsymm hRcomp hRinj
    hRdom hGmem hEdomIff
  have hGbound := aux_thm_prop_hregularity_hGbound_of_root G0 Rroot EForm hE hSymmC hRsymm hRcomp hRinj
    hGmem
  obtain ⟨⟨Cc, hCc⟩, _hIsRegular⟩ :=
    aux_thm_prop_regularity_instance_killed d hd z0 r0 hr0 Sspace0 hSspace0 model H om N0 G0 EForm
      hE hGmem hLower hbundle0 hRange hGbound
  exact ⟨EForm, Set.ext hEdomIff, hE, Cc, hCc⟩

theorem aux_thm_prop_regularity_pair {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (hBounds : in_represented_bounds d hd model H Ω P field z r hr Sspace GE GF NE NF) :
    ∀ᵐ omega ∂P, ∀ i : ℕ,
      (∃ E : _root_.DirichletForm
          (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
        E.domain = limitFormDomain (GE i omega) ∧
        (∀ v : DomainL2 (centeredCube (z i) (r i) (hr i)),
          E.toClosedForm.energy v = limitFormEnergy (GE i omega) v) ∧
        ∃ Cc : Set (DomainL2 (centeredCube (z i) (r i) (hr i))),
          DirichletForm.IsCoreOn E.toClosedForm
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) Cc) ∧
      (∃ F : _root_.DirichletForm
          (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
        F.domain = limitFormDomain (GF i omega) ∧
        (∀ v : DomainL2 (centeredCube (z i) (r i) (hr i)),
          F.toClosedForm.energy v = limitFormEnergy (GF i omega) v) ∧
        ∃ Cc : Set (DomainL2 (centeredCube (z i) (r i) (hr i))),
          DirichletForm.IsCoreOn F.toClosedForm
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) Cc) := by
  have hS := hJoint.2.2.2.2.2.1
  have hGN := hJoint.2.2.2.2.2.2.1
  filter_upwards [hBounds, hJoint.2.2.2.2.2.2.2] with omega hb ht i
  constructor
  · exact aux_thm_prop_hregularity_side hd model H (field omega) (z i) (r i) (hr i)
      (Sspace i) (hS i)
      (fun n => hcontract (z i) (r i) (hr i) (Sspace i) (hS i)
        (Lane4.cutoffPositiveCoefficient model H (field omega) n (z i) (hr i)))
      (GE i omega) NE (fun n => GN i (NE n) omega)
      (fun n f => hGN i (NE n) omega f) (ht i).1 (hb i).1
  · exact aux_thm_prop_hregularity_side hd model H (field omega) (z i) (r i) (hr i)
      (Sspace i) (hS i)
      (fun n => hcontract (z i) (r i) (hr i) (Sspace i) (hS i)
        (Lane4.cutoffPositiveCoefficient model H (field omega) n (z i) (hr i)))
      (GF i omega) NF (fun n => GN i (NF n) omega)
      (fun n f => hGN i (NF n) omega f) (ht i).2 (hb i).2

theorem aux_thm_prop_core_locality
    (d : ℕ) (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (hS : S.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (Gn : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGnEq : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), Gn n f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hGnTendsto : Tendsto Gn atTop (𝓝 G))
    (hbundle : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N) :
    ∀ (u v : DomainL2 (centeredCube z0 r0 hr0)) (hu : MemFormCore G u) (hv : MemFormCore G v)
    (uc vc : SpatialCoordinates d → ℝ)
    (huc : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] uc)
    (hvc : (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vc)
    (hucont : Continuous uc) (hvcont : Continuous vc)
    (hvsupp : HasCompactSupport vc)
    (husuppQ : tsupport uc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
    (hvsuppQ : tsupport vc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
    (husupp : HasCompactSupport uc)
    (c : ℝ) (W : Set (SpatialCoordinates d)) (hW : IsOpen W)
    (hsupp : tsupport vc ⊆ W) (hconst : ∀ x ∈ W, uc x = c),
    limitFormBilinear G u v = 0 := by
  have hMosco := aux_in_represented_mosco_free d hd model H om z0 r0 hr0 S G N Gn hGnEq hGnTendsto
  obtain ⟨KN, hKN, Kstar, hKstar, hfrac, hcoercive, hInterp, t, ht, htd, hcutoffs, _⟩ := hbundle
  exact prop_locality d hd z0 r0 hr0 S hS
    (fun n => Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0) G
    hMosco.1 hMosco.2.1 hMosco.2.2 KN hKN Kstar hKstar hfrac hcoercive hInterp
    t ht htd hcutoffs





theorem aux_thm_prop_energy_measure_support
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}
    {E : DirichletForm.ClosedForm mu} (Gamma : DirichletForm.EnergyMeasure E)
    {U : Set X} (hU : MeasurableSet U) {Cc : Set (Lp ℝ 2 mu)}
    (hCc : DirichletForm.IsCoreOn E U Cc) {u : Lp ℝ 2 mu} (hu : u ∈ E.domain) :
    Gamma.measure u Uᶜ = 0 := by
  have hsqrt : Real.sqrt (Gamma.measure u Uᶜ).toReal ≤ 0 := by
    refine le_of_forall_pos_le_add fun eps heps => ?_
    obtain ⟨w, hwC, hsmall⟩ := hCc.denseEnergy u hu (eps ^ 2) (sq_pos_of_pos heps)
    have hw := hCc.memCoreOn w hwC
    have hw0 : Gamma.measure w Uᶜ = 0 := by
      obtain ⟨hwE, wc, hwc, _hwcompact, hwsupport, hwae⟩ := hw
      exact measure_mono_null (compl_subset_compl.mpr hwsupport)
        (Gamma.measure_compl_tsupport w hwE wc hwc hwae)
    have hdiff := E.domain.sub_mem hu hw.mem_domain
    have hbound : (Gamma.measure (u - w) Uᶜ).toReal ≤ eps ^ 2 :=
      (Gamma.toReal_measure_le_form hdiff Uᶜ).trans
        (E.form_le_energyNormSq.trans hsmall.le)
    have hs := aux_energy_order_of_form_order_sqrt_le Gamma hu hw.mem_domain hU.compl
    rw [hw0, ENNReal.toReal_zero, Real.sqrt_zero, zero_add] at hs
    exact (hs.trans (Real.sqrt_le_sqrt hbound)).trans_eq
      (by rw [Real.sqrt_sq heps.le, zero_add])
  have hz : (Gamma.measure u Uᶜ).toReal = 0 := by
    have hs0 := le_antisymm hsqrt (Real.sqrt_nonneg _)
    have hsq := Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ (Gamma.measure u Uᶜ).toReal)
    rw [hs0, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsq
    exact hsq.symm
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (Gamma.measure_ne_top hu Uᶜ)

end Paper

namespace Paper

theorem aux_thm_prop_form_eq_zero_of_bilinear
    {d : ℕ} {Q : TopologicalSpace.Opens (SpatialCoordinates d)}
    (F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hF : ∀ w, F.energy w = limitFormEnergy G w)
    (u v : DomainL2 Q) (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    (h0 : limitFormBilinear G u v = 0) : F.form u v = 0 := by
  unfold limitFormBilinear at h0
  rw [← hF (u + v), ← hF (u - v),
    F.energy_of_mem (F.domain.add_mem hu hv),
    F.energy_of_mem (F.domain.sub_mem hu hv)] at h0
  have h4 : (4 : EReal) = ((4 : ℝ) : EReal) := (EReal.coe_natCast (n := 4)).symm
  rw [h4, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_eq_zero] at h0
  have hA : F.form (u + v) (u + v) = F.form u u + 2 * F.form u v + F.form v v :=
    F.form_add_self hu hv
  have hB : F.form (u - v) (u - v) = F.form u u - 2 * F.form u v + F.form v v := by
    rw [F.form_sub_left hu hv (F.domain.sub_mem hu hv),
      F.form_sub_right hu hu hv, F.form_sub_right hv hu hv, F.form_symm v hv u hu]
    ring
  rw [hA, hB] at h0
  linarith

theorem aux_thm_prop_form_core_locality
    (d : ℕ) (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (hS : S.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (Gn : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGnEq : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), Gn n f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hGnTendsto : Tendsto Gn atTop (𝓝 G))
    (hbundle : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N)
    (E : DirichletForm.ClosedForm
      (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    ∀ u v : DomainL2 (centeredCube z0 r0 hr0),
      E.MemCoreOn (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) u →
      E.MemCoreOn (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → E.form u v = 0 := by
  intro u v hu hv uc vc huc hvc hcu hcv hsu hsv hsuQ hsvQ c W hW hsupp hconst
  have hu' : MemFormCore G u :=
    ⟨by
        show limitFormEnergy G u < ⊤
        rw [← hE u]
        exact (E.energy_lt_top_iff u).2 hu.1,
      hu.2⟩
  have hv' : MemFormCore G v :=
    ⟨by
        show limitFormEnergy G v < ⊤
        rw [← hE v]
        exact (E.energy_lt_top_iff v).2 hv.1,
      hv.2⟩
  have hbi := aux_thm_prop_core_locality d hd model H om z0 r0 hr0 S hS G N Gn
    hGnEq hGnTendsto hbundle u v hu' hv' uc vc huc hvc hcu hcv hsv hsuQ hsvQ hsu
    c W hW hsupp hconst
  exact aux_thm_prop_form_eq_zero_of_bilinear E G hE u v hu.1 hv.1 hbi

def aux_thm_prop_lowerSet {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω) : Set ℝ :=
  {a : ℝ | ∀ i : ℕ, ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
    u ∈ limitFormDomain (GE i omega) →
      a * (limitFormEnergy (GE i omega) u).toReal ≤
        (limitFormEnergy (GF i omega) u).toReal}

def aux_thm_prop_upperSet {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω) : Set ℝ :=
  {a : ℝ | ∀ i : ℕ, ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
    u ∈ limitFormDomain (GE i omega) →
      (limitFormEnergy (GF i omega) u).toReal ≤
        a * (limitFormEnergy (GE i omega) u).toReal}

def aux_thm_prop_compare {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (omega : Ω) : Prop :=
  ∀ i : ℕ, limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
    ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
      u ∈ limitFormDomain (GE i omega) →
      C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
          (limitFormEnergy (GF i omega) u).toReal ∧
        (limitFormEnergy (GF i omega) u).toReal ≤
          C0 * (limitFormEnergy (GE i omega) u).toReal

def aux_thm_prop_nonzero {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω) : Prop :=
  ∃ i : ℕ, ∃ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
    u ∈ limitFormDomain (GE i omega) ∧ 0 < (limitFormEnergy (GE i omega) u).toReal

theorem aux_thm_prop_endpoints_at {d : ℕ} (hd : 2 ≤ d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (hC0 : 1 ≤ C0) (omega : Ω)
    (hcomp : aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : aux_thm_prop_nonzero z r hr GE omega) :
    IsLUB (aux_thm_prop_lowerSet z r hr GE GF omega)
        (sSup (aux_thm_prop_lowerSet z r hr GE GF omega)) ∧
      IsGLB (aux_thm_prop_upperSet z r hr GE GF omega)
        (sInf (aux_thm_prop_upperSet z r hr GE GF omega)) ∧
      (C0⁻¹ ≤ sSup (aux_thm_prop_lowerSet z r hr GE GF omega) ∧
        sSup (aux_thm_prop_lowerSet z r hr GE GF omega) ≤
          sInf (aux_thm_prop_upperSet z r hr GE GF omega) ∧
        sInf (aux_thm_prop_upperSet z r hr GE GF omega) ≤ C0) ∧
      (sSup (aux_thm_prop_lowerSet z r hr GE GF omega) ∈
          aux_thm_prop_lowerSet z r hr GE GF omega ∧
        sInf (aux_thm_prop_upperSet z r hr GE GF omega) ∈
          aux_thm_prop_upperSet z r hr GE GF omega) :=
  optimal_endpoints d hd (fun n => centeredCube (z n) (r n) (hr n))
    (fun n => ⟨z n, r n, hr n, rfl⟩) (fun n => GE n omega) (fun n => GF n omega) C0 hC0
    (fun n => (hcomp n).1) (fun n u hu => (hcomp n).2 u hu) hnz

theorem aux_thm_prop_gap_zero {d : ℕ} (hd : 2 ≤ d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega)
    (cL cU : ℝ)
    (hcLU : ∀ᵐ omega ∂P, sSup (aux_thm_prop_lowerSet z r hr GE GF omega) = cL ∧
      sInf (aux_thm_prop_upperSet z r hr GE GF omega) = cU)
    (himp : cL < cU → ∃ k1 : ℝ, 0 < k1 ∧
      ((∀ᵐ omega ∂P, cU - k1 * (cU - cL) ∈ aux_thm_prop_upperSet z r hr GE GF omega) ∨
        (∀ᵐ omega ∂P, cL + k1 * (cU - cL) ∈ aux_thm_prop_lowerSet z r hr GE GF omega))) :
    cL = cU := by
  haveI : (ae P).NeBot := IsProbabilityMeasure.ae_neBot
  have hEnd := (hcomp.and hnz).mono fun omega h =>
    aux_thm_prop_endpoints_at hd z r hr GE GF C0 hC0 omega h.1 h.2
  have hle : cL ≤ cU := by
    obtain ⟨omega, h1, h2⟩ := (hEnd.and hcLU).exists
    have h3 := h1.2.2.1.2.1
    rw [h2.1, h2.2] at h3
    exact h3
  by_contra hne
  obtain ⟨k1, hk1, hcase⟩ := himp (lt_of_le_of_ne hle hne)
  have hpos : 0 < k1 * (cU - cL) := mul_pos hk1 (sub_pos.mpr (lt_of_le_of_ne hle hne))
  rcases hcase with h | h
  · obtain ⟨omega, ⟨h1, h2⟩, h3⟩ := ((hEnd.and hcLU).and h).exists
    have h4 := h1.2.1.1 h3
    rw [h2.2] at h4
    linarith
  · obtain ⟨omega, ⟨h1, h2⟩, h3⟩ := ((hEnd.and hcLU).and h).exists
    have h4 := h1.1.1 h3
    rw [h2.1] at h4
    linarith

theorem aux_thm_prop_assembly {d : ℕ} (hd : 2 ≤ d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega)
    (hdet : ∃ cL cU : ℝ, ∀ᵐ omega ∂P,
      sSup (aux_thm_prop_lowerSet z r hr GE GF omega) = cL ∧
        sInf (aux_thm_prop_upperSet z r hr GE GF omega) = cU)
    (himp : ∀ cL cU : ℝ,
      (∀ᵐ omega ∂P, sSup (aux_thm_prop_lowerSet z r hr GE GF omega) = cL ∧
        sInf (aux_thm_prop_upperSet z r hr GE GF omega) = cU) →
      cL < cU → ∃ k1 : ℝ, 0 < k1 ∧
        ((∀ᵐ omega ∂P, cU - k1 * (cU - cL) ∈ aux_thm_prop_upperSet z r hr GE GF omega) ∨
          (∀ᵐ omega ∂P, cL + k1 * (cU - cL) ∈ aux_thm_prop_lowerSet z r hr GE GF omega))) :
    ∃ c : ℝ, C0⁻¹ ≤ c ∧ c ≤ C0 ∧
      ∀ᵐ omega ∂P,
        (∀ i : ℕ,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            (limitFormEnergy (GF i omega) u).toReal =
              c * (limitFormEnergy (GE i omega) u).toReal) ∧
        sInf (aux_thm_prop_upperSet z r hr GE GF omega) -
            sSup (aux_thm_prop_lowerSet z r hr GE GF omega) = 0 ∧
        sSup (aux_thm_prop_lowerSet z r hr GE GF omega) = c ∧
        sInf (aux_thm_prop_upperSet z r hr GE GF omega) = c := by
  obtain ⟨cL, cU, hcLU⟩ := hdet
  have hLU : cL = cU :=
    aux_thm_prop_gap_zero hd z r hr P GE GF C0 hC0 hcomp hnz cL cU hcLU (himp cL cU hcLU)
  have hEnd := (hcomp.and hnz).mono fun omega h =>
    aux_thm_prop_endpoints_at hd z r hr GE GF C0 hC0 omega h.1 h.2
  have hbounds : ∀ᵐ omega ∂P,
      C0⁻¹ ≤ sSup (aux_thm_prop_lowerSet z r hr GE GF omega) ∧
        sSup (aux_thm_prop_lowerSet z r hr GE GF omega) ≤
          sInf (aux_thm_prop_upperSet z r hr GE GF omega) ∧
        sInf (aux_thm_prop_upperSet z r hr GE GF omega) ≤ C0 :=
    hEnd.mono fun _ h => h.2.2.1
  have horders : ∀ᵐ omega ∂P, ∀ n,
      limitFormDomain (GE n omega) = limitFormDomain (GF n omega) ∧
      (∀ u : DomainL2 (centeredCube (z n) (r n) (hr n)), u ∈ limitFormDomain (GE n omega) →
        (sSup (aux_thm_prop_lowerSet z r hr GE GF omega) *
            (limitFormEnergy (GE n omega) u).toReal ≤
          (limitFormEnergy (GF n omega) u).toReal ∧
        (limitFormEnergy (GF n omega) u).toReal ≤
          sInf (aux_thm_prop_upperSet z r hr GE GF omega) *
            (limitFormEnergy (GE n omega) u).toReal)) := by
    filter_upwards [hEnd, hcomp] with omega h hc n
    exact ⟨(hc n).1, fun u hu => ⟨h.2.2.2.1 n u hu, h.2.2.2.2 n u hu⟩⟩
  have hzero : ∀ᵐ omega ∂P, sInf (aux_thm_prop_upperSet z r hr GE GF omega) -
      sSup (aux_thm_prop_lowerSet z r hr GE GF omega) = 0 := by
    filter_upwards [hcLU] with omega h
    rw [h.1, h.2, hLU, sub_self]
  obtain ⟨c, hc1, hc2, hc3⟩ := zero_endpoint_gap d hd Ω P
    (fun n => centeredCube (z n) (r n) (hr n)) (fun n => ⟨z n, r n, hr n, rfl⟩) GE GF
    (fun omega => sSup (aux_thm_prop_lowerSet z r hr GE GF omega))
    (fun omega => sInf (aux_thm_prop_upperSet z r hr GE GF omega)) C0 hC0
    hbounds horders ⟨cL, hcLU.mono fun _ h => h.1⟩ hzero
  refine ⟨c, hc1, hc2, ?_⟩
  filter_upwards [hc3, hcLU, hzero] with omega h h' hz
  refine ⟨h.2, hz, h.1, ?_⟩
  rw [h'.2, ← hLU, ← h'.1]
  exact h.1

def aux_thm_prop_catalogue (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta beta t : ℝ) : Prop :=
  ∃ (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (root : ℕ)
    (hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
    (Dcat : ∀ i, Submodule ℚ
      (DomainL2 (centeredCube (z i) (r i) (hr i))))
    (hDcat : ∀ i, Countable (Dcat i))
    (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
    (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (traceH1 : ∀ i, ℕ → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
    (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (I : Paper.in_J d)
    (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
    (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
    (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
    letI : ∀ i, Countable (Dcat i) := hDcat
    conv_represented_estimates d hd model H Ω P NE (fun _ omega => field omega)
      ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I
      ℕ (fun i n omega => catalogResponse i (NE n) (field omega)) responseE
      (fun i n omega => catalogConstant i (NE n) (field omega)) eventE
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
    conv_represented_estimates d hd model H Ω P NF (fun _ omega => field omega)
      ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I
      ℕ (fun i n omega => catalogResponse i (NF n) (field omega)) responseF
      (fun i n omega => catalogConstant i (NF n) (field omega)) eventF
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey

/-- The catalogue with explicit `beta t` gives the catalogue of `lem_endpoints_support_2` (which quantifies `beta t`). -/
theorem aux_thm_prop_catalogue_to_endpoints (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) {beta t : ℝ}
    (h : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t) :
    aux_lem_endpoints_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta := by
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF, root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, I,
    coercivityKey, extensionKey, lambdaKey, sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hEF⟩ := h
  exact ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF, root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, beta, t, I,
    coercivityKey, extensionKey, lambdaKey, sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hEF⟩

theorem aux_thm_prop_comparison_of_catalogue (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ddet : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha)
    (hResp :
      ∃ delta0 C : ℝ, 0 < delta0 ∧
        ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
          (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization model H →
        ∀ (S : ResponseSpace (centeredCube (0 : SpatialCoordinates d) 1 one_pos)),
          S.space = killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) →
        ∃ f0 : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
          ∀ N : ℕ,
            (∀ om : BilateralField d, 0 < inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL)) ∧
            MemLp (fun om : BilateralField d => inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ∧
            eLpNorm (fun om : BilateralField d => inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ≤
              ENNReal.ofReal C ∧
            MemLp (fun om : BilateralField d => (inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ∧
            eLpNorm (fun om : BilateralField d => (inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ≤
              ENNReal.ofReal C)
    (hLlarge : 2 * Cd ^ (eta0 / 3) ≤ ((3 : ℝ) ^ H1) ^ (eta0 / 3 - eta0 / 8))
    (hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      (Nat.card {i : OddGridIndex d (Lane3.subdivisionHalfWidth H1) //
        ¬ Metric.closedBall (oddGridCenter zP R (Lane3.subdivisionHalfWidth H1) i)
            (3 * (R / (3 : ℝ) ^ H1) / 2) ⊆
          (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
        Cd * ((3 : ℝ) ^ H1) ^ ((d : ℝ) - 1)) :
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        ∀ (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF
          NE NF),
        Paper.aux_thm_prop_bounds_pointwise d hd model H z r hr Sspace NE NF →
        @aux_thm_prop_catalogue d hd _ _ model H Ω _ P hJoint.1 field z r hr Sspace NE NF
          alpha eta beta t →
        ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega := by
  obtain ⟨δ, C0, hδ, hC0, h⟩ := thm_C0 d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp eta0 heta0 heta03 D theta alpha eta hD htheta
    htheta8 halpha halpha1 heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
  refine ⟨δ, C0, hδ, hC0, ?_⟩
  intro _ _ model hmodel Rm Sreg It H Ω _ P field z r hr Sspace GN GE GF NE NF hJoint hBounds hCat
  haveI : IsProbabilityMeasure P := hJoint.1
  have hprob := hJoint.1
  have hmeas := hJoint.2.1
  have hmap := hJoint.2.2.1
  have hIR := hJoint.2.2.2.1
  have hNE := hJoint.2.2.2.2.1.1
  have hNF := hJoint.2.2.2.2.1.2
  have hS := hJoint.2.2.2.2.2.1
  have hGN := hJoint.2.2.2.2.2.2.1
  have hconv := hJoint.2.2.2.2.2.2.2
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF, hrest⟩ := hCat
  have hmp : MeasurePreserving field P (chaosSampleLaw model).toMeasure := ⟨hmeas, hmap⟩
  have hBnd : aux_conv_represented_env_interface_bounds d hd model H Ω P (fun _ omega => field omega)
      (fun _ omega => field omega) z r hr Sspace GE GF NE NF :=
    aux_thm_prop_bounds_pointwise_ae hd hJoint hmeas hmap hBounds
  obtain ⟨G, -, hGfull, -, hG⟩ := h model hmodel Rm Sreg It H Ω P field (fun _ => field) (fun _ => field)
    catalogResponse catalogConstant responseE responseF eventE eventF z r hr Sspace
    (fun i n omega => GN i (NE n) omega) (fun i n omega => GN i (NF n) omega) GE GF NE NF
    Set.univ MeasurableSet.univ (by simp)
    ⟨hprob, hmeas, hmap, hIR, hNE, hNF, fun _ => ⟨hmp, hmp⟩,
      ae_of_all _ (fun _ => ⟨tendsto_const_nhds, tendsto_const_nhds⟩), hS,
      ae_of_all _ (fun omega i n f => ⟨hGN i (NE n) omega f, hGN i (NF n) omega f⟩),
      hconv, hrest⟩ hBnd
  have hae : ∀ᵐ omega ∂P, omega ∈ G := by
    rw [ae_iff]
    simpa only [Set.compl_def, Set.mem_setOf_eq] using hGfull
  filter_upwards [hae] with omega homega i
  exact ⟨(hG omega homega i).2.2.1, (hG omega homega i).2.2.2⟩

theorem aux_thm_prop_pad_inner {d : ℕ} (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (i : OddGridIndex d m) (hi : ∀ j, 2 ≤ (i j).val ∧ (i j).val + 2 ≤ 2 * m) :
    Metric.closedBall (oddGridCenter zP R m i) (3 * (R / (2 * (m : ℝ) + 1)) / 2) ⊆
      (centeredCube zP R hR : Set (SpatialCoordinates d)) := by
  change _ ⊆ Metric.ball zP (R / 2)
  rcases Nat.eq_zero_or_pos d with hd0 | hpos
  · subst hd0
    intro x _
    rw [Metric.mem_ball]
    have hxz : x = zP := funext (fun j => j.elim0)
    rw [hxz, dist_self]
    exact half_pos hR
  · have hm2 : 2 ≤ m := by
      obtain ⟨h1, h2⟩ := hi ⟨0, hpos⟩
      omega
    have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have ht : 0 < R / (2 * (m : ℝ) + 1) := div_pos hR (by positivity)
    have h0t : 0 ≤ (m : ℝ) - 2 := by linarith
    apply Metric.closedBall_subset_ball'
    have hdist : dist (oddGridCenter zP R m i) zP
        ≤ ((m : ℝ) - 2) * (R / (2 * (m : ℝ) + 1)) := by
      rw [dist_pi_le_iff (mul_nonneg h0t ht.le)]
      intro j
      rw [Real.dist_eq]
      have hinner : (oddGridCenter zP R m i) j - zP j
          = ((i j).val - (m : ℝ)) * (R / (2 * (m : ℝ) + 1)) := by
        simp only [oddGridCenter]
        ring
      rw [hinner, abs_mul, abs_of_pos ht]
      have hv : |((i j).val : ℝ) - (m : ℝ)| ≤ (m : ℝ) - 2 := by
        rw [abs_le]
        constructor
        · have h2 : (2 : ℝ) ≤ ((i j).val : ℝ) := by exact_mod_cast (hi j).1
          linarith
        · have h3 : ((i j).val : ℝ) + 2 ≤ 2 * (m : ℝ) := by exact_mod_cast (hi j).2
          linarith
      exact mul_le_mul_of_nonneg_right hv ht.le
    have hfinal : 3 * (R / (2 * (m : ℝ) + 1)) / 2
        + ((m : ℝ) - 2) * (R / (2 * (m : ℝ) + 1)) < R / 2 := by
      have ht_eq : (2 * (m : ℝ) + 1) * (R / (2 * (m : ℝ) + 1)) = R :=
        mul_div_cancel₀ _ (by positivity)
      nlinarith [ht_eq, ht]
    linarith [hdist, hfinal]

theorem aux_thm_prop_bad_count (d L : ℕ) :
    (Finset.univ.filter (fun i : Fin d → Fin L =>
      ∃ j, (i j).val < 2 ∨ L < (i j).val + 3)).card ≤ d * 4 * L ^ (d - 1) := by
  have hcard_bad : (Finset.univ.filter (fun a : Fin L => a.val < 2 ∨ L < a.val + 3)).card ≤ 4 := by
    rw [Finset.filter_or]
    have h1 : (Finset.univ.filter (fun a : Fin L => a.val < 2)).card ≤ 2 := by
      have key : (Finset.univ.filter (fun a : Fin L => a.val < 2)).card ≤ (Finset.range 2).card := by
        apply Finset.card_le_card_of_injOn (f := fun a : Fin L => a.val)
        · rintro a ha
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          simpa using ha
        · rintro a _ b _ hab
          exact Fin.ext hab
      simpa using key
    have h2 : (Finset.univ.filter (fun a : Fin L => L < a.val + 3)).card ≤ 2 := by
      have key : (Finset.univ.filter (fun a : Fin L => L < a.val + 3)).card ≤ (Finset.range 2).card := by
        apply Finset.card_le_card_of_injOn (f := fun a : Fin L => L - 1 - a.val)
        · rintro a ha
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [Finset.mem_coe, Finset.mem_range]
          change L - 1 - a.val < 2
          have := a.isLt
          omega
        · rintro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          have ha' := a.isLt
          have hb' := b.isLt
          dsimp only at hab
          apply Fin.ext
          omega
      simpa using key
    calc ((Finset.univ.filter (fun a : Fin L => a.val < 2)) ∪ (Finset.univ.filter (fun a : Fin L => L < a.val + 3))).card
        ≤ (Finset.univ.filter (fun a : Fin L => a.val < 2)).card + (Finset.univ.filter (fun a : Fin L => L < a.val + 3)).card := Finset.card_union_le _ _
      _ ≤ 2 + 2 := add_le_add h1 h2
      _ = 4 := by norm_num
  have hsub : (Finset.univ.filter (fun i : Fin d → Fin L => ∃ j, (i j).val < 2 ∨ L < (i j).val + 3))
      ⊆ Finset.univ.biUnion (fun j : Fin d =>
          Finset.univ.filter (fun i : Fin d → Fin L => (i j).val < 2 ∨ L < (i j).val + 3)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hj⟩ := hi
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hj⟩⟩
  have hper : ∀ j : Fin d, (Finset.univ.filter (fun i : Fin d → Fin L => (i j).val < 2 ∨ L < (i j).val + 3)).card
      ≤ 4 * L ^ (d - 1) := by
    intro j
    have hfiber : ∀ a : Fin L, (Finset.univ.filter (fun i : Fin d → Fin L => i j = a)).card = L ^ (d - 1) := by
      intro a
      have h := Fintype.card_filter_piFinset_eq (fun _ : Fin d => (Finset.univ : Finset (Fin L))) j a
      rw [Fintype.piFinset_univ] at h
      rw [if_pos (Finset.mem_univ a)] at h
      simp only [Finset.card_univ, Fintype.card_fin] at h
      rw [h, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    have hsub2 : (Finset.univ.filter (fun i : Fin d → Fin L => (i j).val < 2 ∨ L < (i j).val + 3))
        ⊆ (Finset.univ.filter (fun a : Fin L => a.val < 2 ∨ L < a.val + 3)).biUnion
            (fun a => Finset.univ.filter (fun i : Fin d → Fin L => i j = a)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_biUnion.mpr ⟨i j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    calc (Finset.univ.filter (fun i : Fin d → Fin L => (i j).val < 2 ∨ L < (i j).val + 3)).card
        ≤ ((Finset.univ.filter (fun a : Fin L => a.val < 2 ∨ L < a.val + 3)).biUnion
            (fun a => Finset.univ.filter (fun i : Fin d → Fin L => i j = a))).card := Finset.card_le_card hsub2
      _ ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin L => a.val < 2 ∨ L < a.val + 3),
            (Finset.univ.filter (fun i : Fin d → Fin L => i j = a)).card := Finset.card_biUnion_le
      _ = ∑ a ∈ Finset.univ.filter (fun a : Fin L => a.val < 2 ∨ L < a.val + 3), L ^ (d - 1) :=
            Finset.sum_congr rfl (fun a _ => hfiber a)
      _ = (Finset.univ.filter (fun a : Fin L => a.val < 2 ∨ L < a.val + 3)).card * L ^ (d - 1) := by
            rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 4 * L ^ (d - 1) := Nat.mul_le_mul_right _ hcard_bad
  calc (Finset.univ.filter (fun i : Fin d → Fin L => ∃ j, (i j).val < 2 ∨ L < (i j).val + 3)).card
      ≤ (Finset.univ.biUnion (fun j : Fin d =>
          Finset.univ.filter (fun i : Fin d → Fin L => (i j).val < 2 ∨ L < (i j).val + 3))).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.univ, (Finset.univ.filter (fun i : Fin d → Fin L => (i j).val < 2 ∨ L < (i j).val + 3)).card := Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.univ, 4 * L ^ (d - 1) := Finset.sum_le_sum (fun j _ => hper j)
    _ = d * 4 * L ^ (d - 1) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
          ring

theorem aux_thm_prop_Llarge (Cd eta0 : ℝ) (hCd : 1 ≤ Cd) (heta0 : 0 < eta0) :
    ∃ H0 : ℕ, ∀ H1 : ℕ, H0 ≤ H1 →
      2 * Cd ^ (eta0 / 3) ≤ ((3 : ℝ) ^ H1) ^ (eta0 / 3 - eta0 / 8) := by
  have he_pos : 0 < eta0 / 3 - eta0 / 8 := by linarith
  set b : ℝ := (3 : ℝ) ^ (eta0 / 3 - eta0 / 8) with hb
  have hb_gt : 1 < b := by
    rw [hb]
    exact Real.one_lt_rpow (by norm_num) he_pos
  have h_eq : ∀ H1 : ℕ,
      ((3 : ℝ) ^ H1) ^ (eta0 / 3 - eta0 / 8) = b ^ H1 := by
    intro H1
    rw [hb]
    rw [← Real.rpow_natCast (3 : ℝ) H1]
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 3 by norm_num)]
    rw [mul_comm ((H1 : ℝ)) (eta0 / 3 - eta0 / 8)]
    rw [Real.rpow_mul (show (0 : ℝ) ≤ 3 by norm_num) (eta0 / 3 - eta0 / 8) (H1 : ℝ)]
    rw [Real.rpow_natCast]
  have htend : Tendsto (fun n : ℕ => b ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hb_gt
  have hev : ∀ᶠ n in atTop, 2 * Cd ^ (eta0 / 3) ≤ b ^ n :=
    htend.eventually_ge_atTop (2 * Cd ^ (eta0 / 3))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨H0, hH0⟩ := hev
  refine ⟨H0, fun H1 hH1 => ?_⟩
  rw [h_eq H1]
  exact hH0 H1 hH1

theorem aux_thm_prop_CdPad (d : ℕ) (hd : 2 ≤ d) (H1 : ℕ) :
    ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      (Nat.card {i : OddGridIndex d (Lane3.subdivisionHalfWidth H1) //
        ¬ Metric.closedBall (oddGridCenter zP R (Lane3.subdivisionHalfWidth H1) i)
            (3 * (R / (3 : ℝ) ^ H1) / 2) ⊆
          (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
        (4 * (d : ℝ)) * ((3 : ℝ) ^ H1) ^ ((d : ℝ) - 1) := by
  classical
  intro zP R hR
  have hL : 2 * Lane3.subdivisionHalfWidth H1 + 1 = 3 ^ H1 :=
    Lane3.two_mul_subdivisionHalfWidth_add_one H1
  have hLR : (2 * (Lane3.subdivisionHalfWidth H1 : ℝ) + 1) = (3 : ℝ) ^ H1 := by
    exact_mod_cast hL
  have hsub : ∀ i : OddGridIndex d (Lane3.subdivisionHalfWidth H1),
      ¬ Metric.closedBall (oddGridCenter zP R (Lane3.subdivisionHalfWidth H1) i)
          (3 * (R / (3 : ℝ) ^ H1) / 2) ⊆
        (centeredCube zP R hR : Set (SpatialCoordinates d)) →
      ∃ j, (i j).val < 2 ∨ 2 * Lane3.subdivisionHalfWidth H1 + 1 < (i j).val + 3 := by
    intro i hi
    by_contra hcon
    push_neg at hcon
    apply hi
    rw [← hLR]
    exact aux_thm_prop_pad_inner zP R hR _ i
      (fun j => ⟨(hcon j).1, by have := (hcon j).2; omega⟩)
  have hcard : Nat.card {i : OddGridIndex d (Lane3.subdivisionHalfWidth H1) //
      ¬ Metric.closedBall (oddGridCenter zP R (Lane3.subdivisionHalfWidth H1) i)
          (3 * (R / (3 : ℝ) ^ H1) / 2) ⊆
        (centeredCube zP R hR : Set (SpatialCoordinates d))} ≤
      (Finset.univ.filter (fun i : Fin d → Fin (2 * Lane3.subdivisionHalfWidth H1 + 1) =>
        ∃ j, (i j).val < 2 ∨ 2 * Lane3.subdivisionHalfWidth H1 + 1 < (i j).val + 3)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact Finset.card_le_card fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hsub i hi
  have hbc := aux_thm_prop_bad_count d (2 * Lane3.subdivisionHalfWidth H1 + 1)
  have hdpos : 1 ≤ d := by omega
  have he : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hdpos, Nat.cast_one]
  have hnat := hcard.trans hbc
  calc (Nat.card {i : OddGridIndex d (Lane3.subdivisionHalfWidth H1) //
        ¬ Metric.closedBall (oddGridCenter zP R (Lane3.subdivisionHalfWidth H1) i)
            (3 * (R / (3 : ℝ) ^ H1) / 2) ⊆
          (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ)
      ≤ ((d * 4 * (2 * Lane3.subdivisionHalfWidth H1 + 1) ^ (d - 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
    _ = (4 * (d : ℝ)) * ((3 : ℝ) ^ H1) ^ ((d : ℝ) - 1) := by
        rw [← he, Real.rpow_natCast]
        push_cast
        rw [hLR]
        ring

theorem aux_thm_prop_C0_params (d : ℕ) (hd : 2 ≤ d) :
    ∃ H1 : ℕ, 0 < H1 ∧
      2 * (6 * (d : ℝ)) ^ ((1 / 4 : ℝ) / 3) ≤
        ((3 : ℝ) ^ H1) ^ ((1 / 4 : ℝ) / 3 - (1 / 4 : ℝ) / 8) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨H0, hH0⟩ := aux_thm_prop_Llarge (6 * (d : ℝ)) (1 / 4) (by linarith) (by norm_num)
  exact ⟨H0 + 1, Nat.succ_pos _, hH0 _ (Nat.le_succ _)⟩

theorem aux_thm_prop_comparison_of_catalogue_fixed (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ddet : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < aux_thm_prop_alpha d hd)
    (hResp :
      ∃ delta0 C : ℝ, 0 < delta0 ∧
        ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
          (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization model H →
        ∀ (S : ResponseSpace (centeredCube (0 : SpatialCoordinates d) 1 one_pos)),
          S.space = killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) →
        ∃ f0 : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
          ∀ N : ℕ,
            (∀ om : BilateralField d, 0 < inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL)) ∧
            MemLp (fun om : BilateralField d => inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ∧
            eLpNorm (fun om : BilateralField d => inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ≤
              ENNReal.ofReal C ∧
            MemLp (fun om : BilateralField d => (inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ∧
            eLpNorm (fun om : BilateralField d => (inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ≤
              ENNReal.ofReal C) :
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        ∀ (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF
          NE NF),
        Paper.aux_thm_prop_bounds_pointwise d hd model H z r hr Sspace NE NF →
        @aux_thm_prop_catalogue d hd _ _ model H Ω _ P hJoint.1 field z r hr Sspace NE NF
          (aux_thm_prop_alpha d hd) (1 / 128) beta t →
        ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega := by
  obtain ⟨H1, hH1, hLl⟩ := aux_thm_prop_C0_params d hd
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact aux_thm_prop_comparison_of_catalogue d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp (1 / 4) (by norm_num) (by norm_num)
    (32 * d) (1 / 32) (aux_thm_prop_alpha d hd) (1 / 128) (le_of_eq (by ring)) (by norm_num) (by norm_num)
    (aux_thm_prop_alpha_bounds d hd).1 (aux_thm_prop_alpha_bounds d hd).2.1 (by norm_num) (by norm_num)
    (aux_thm_prop_alpha_bounds d hd).2.2.2 H1 hH1 (6 * d)
    le_rfl t beta ht htd hbeta hbetaAlpha hResp hLl
    (fun zP R hR => (aux_thm_prop_CdPad d hd H1 zP R hR).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity)))

theorem aux_thm_prop_symm_nonneg_of_tendsto
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q) (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hlim : Tendsto GN atTop (𝓝 G))
    (hsym : ∀ n (x y : DomainL2 Q), inner ℝ (GN n x) y = inner ℝ x (GN n y))
    (hpos : ∀ n (x : DomainL2 Q), 0 ≤ inner ℝ x (GN n x)) :
    (∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) := by
  have happ (x : DomainL2 Q) : Tendsto (fun n => GN n x) atTop (𝓝 (G x)) :=
    ((ContinuousLinearMap.apply ℝ (DomainL2 Q) x).continuous.tendsto G).comp hlim
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have hL : Tendsto (fun n => inner ℝ (GN n x) y) atTop (𝓝 (inner ℝ (G x) y)) :=
      ((continuous_inner (𝕜 := ℝ) (E := DomainL2 Q)).tendsto _).comp
        ((happ x).prodMk_nhds tendsto_const_nhds)
    have hR : Tendsto (fun n => inner ℝ x (GN n y)) atTop (𝓝 (inner ℝ x (G y))) :=
      ((continuous_inner (𝕜 := ℝ) (E := DomainL2 Q)).tendsto _).comp
        ((tendsto_const_nhds (x := x)).prodMk_nhds (happ y))
    have hEq : (fun n => inner ℝ (GN n x) y) = (fun n => inner ℝ x (GN n y)) :=
      funext fun n => hsym n x y
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR
  · have hT : Tendsto (fun n => inner ℝ x (GN n x)) atTop (𝓝 (inner ℝ x (G x))) :=
      ((continuous_inner (𝕜 := ℝ) (E := DomainL2 Q)).tendsto _).comp
        ((tendsto_const_nhds (x := x)).prodMk_nhds (happ x))
    exact ge_of_tendsto hT (Eventually.of_forall fun n => hpos n x)

theorem aux_thm_prop_candidates_symm_nonneg (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) :
    ∀ᵐ omega ∂P, ∀ i : ℕ,
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GE i omega x))) ∧
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GF i omega x) y = inner ℝ x (GF i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GF i omega x))) := by
  obtain ⟨-, -, -, -, -, -, hGN, hconv⟩ := hJoint
  filter_upwards [hconv] with omega hconvomega i
  have hsym : ∀ N (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GN i N omega x) y = inner ℝ x (GN i N omega y) := by
    intro N x y
    rw [hGN i N omega x, hGN i N omega y, real_inner_comm]
    exact volumeResponse_pairing_symm _ _ y x
  have hpos : ∀ N (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      0 ≤ inner ℝ x (GN i N omega x) := by
    intro N x
    rw [hGN i N omega x]
    exact volumeResponse_pairing_nonneg _ _ x
  exact ⟨aux_thm_prop_symm_nonneg_of_tendsto _ _ (hconvomega i).1 (fun n => hsym (NE n))
      (fun n => hpos (NE n)),
    aux_thm_prop_symm_nonneg_of_tendsto _ _ (hconvomega i).2 (fun n => hsym (NF n))
      (fun n => hpos (NF n))⟩

theorem aux_thm_prop_energy_range {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) (f : DomainL2 Q) :
    limitFormEnergy G (G f) = ((inner ℝ f (G f) : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun g => EReal.coe_le_coe_iff.mpr ?_
    have h := hpos (g - f)
    have h1 : inner ℝ (g - f) (G (g - f)) =
        inner ℝ g (G g) - 2 * inner ℝ g (G f) + inner ℝ f (G f) := by
      have hgf : inner ℝ f (G g) = inner ℝ g (G f) := by
        rw [← hsym f g, real_inner_comm]
      simp only [map_sub, inner_sub_left, inner_sub_right, hgf]
      ring
    linarith
  · refine le_iSup_of_le f (EReal.coe_le_coe_iff.mpr (le_of_eq ?_))
    ring

theorem aux_thm_prop_nonzero_of_response {d : ℕ}
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω)
    (hsym : ∀ i (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y))
    (hpos : ∀ i (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      0 ≤ inner ℝ x (GE i omega x))
    (hresp : ∃ i : ℕ, ∃ f : DomainL2 (centeredCube (z i) (r i) (hr i)),
      0 < inner ℝ f (GE i omega f)) :
    aux_thm_prop_nonzero z r hr GE omega := by
  obtain ⟨i, f, hf⟩ := hresp
  have he := aux_thm_prop_energy_range (GE i omega) (hsym i) (hpos i) f
  refine ⟨i, GE i omega f, ?_, ?_⟩
  · change limitFormEnergy (GE i omega) (GE i omega f) < ⊤
    rw [he]
    exact EReal.coe_lt_top _
  · rw [he, EReal.toReal_coe]
    exact hf



theorem aux_thm_prop_comparison (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ddet : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < aux_thm_prop_alpha d hd)
    (hResp :
      ∃ delta0 C : ℝ, 0 < delta0 ∧
        ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
          (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization model H →
        ∀ (S : ResponseSpace (centeredCube (0 : SpatialCoordinates d) 1 one_pos)),
          S.space = killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) →
        ∃ f0 : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
          ∀ N : ℕ,
            (∀ om : BilateralField d, 0 < inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL)) ∧
            MemLp (fun om : BilateralField d => inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ∧
            eLpNorm (fun om : BilateralField d => inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ≤
              ENNReal.ofReal C ∧
            MemLp (fun om : BilateralField d => (inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ∧
            eLpNorm (fun om : BilateralField d => (inverseResponse S
              (Lane4.cutoffPositiveCoefficient model H om N 0 one_pos)
              ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ≤
              ENNReal.ofReal C) :
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        ∀ (hJoint :
          in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF),
        Paper.aux_thm_prop_bounds_pointwise d hd model H z r hr Sspace NE NF →
        @aux_thm_prop_catalogue d hd _ _ model H Ω _ P hJoint.1 field z r hr Sspace NE NF
          (aux_thm_prop_alpha d hd) (1 / 128) beta t →
        ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega := by
  exact aux_thm_prop_comparison_of_catalogue_fixed d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp t beta ht htd hbeta hbetaAlpha hResp

theorem aux_thm_prop_nonzero_ae (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        (hJoint :
          in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) →
        (∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega) →
        ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega := by
  refine ⟨1, one_pos, ?_⟩
  intro _ _ model _hmodel H Ω _ P field z r hr Sspace GN GE GF NE NF _hJoint hNonzero
  exact hNonzero

theorem aux_thm_prop_dual_shift {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (u f h : DomainL2 Q) :
    2 * inner ℝ (h + f) u - inner ℝ (h + f) (G (h + f)) =
      (2 * inner ℝ h (u - G f) - inner ℝ h (G h)) +
        (2 * inner ℝ f u - inner ℝ f (G f)) := by
  have hfh : inner ℝ f (G h) = inner ℝ h (G f) := by
    rw [← hsym f h, real_inner_comm]
  simp only [map_add, inner_add_left, inner_add_right, inner_sub_right, hfh]
  ring

theorem aux_thm_prop_core_closure {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (GE x) y = inner ℝ x (GE y))
    (S : Set (DomainL2 Q)) (hS : Dense S) (K : ℝ) (hK : 0 ≤ K)
    (hcore : ∀ f ∈ S,
      limitFormEnergy GF (GE f) ≤ ((K * inner ℝ f (GE f) : ℝ) : EReal)) :
    ∀ u ∈ limitFormDomain GE,
      limitFormEnergy GF u ≤ ((K * (limitFormEnergy GE u).toReal : ℝ) : EReal) := by
  intro u hu
  have hu' : limitFormEnergy GE u < ⊤ := hu
  have hE0 := limitFormEnergy_nonneg GE u
  obtain ⟨e, hEu⟩ : ∃ e : ℝ, limitFormEnergy GE u = (e : EReal) :=
    ⟨_, (EReal.coe_toReal (ne_of_lt hu')
      (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hE0))).symm⟩
  rw [hEu, EReal.toReal_coe]
  have he0 : 0 ≤ e := by
    rw [hEu] at hE0
    exact EReal.coe_nonneg.mp hE0
  have hφ : ∀ g : DomainL2 Q, 2 * inner ℝ g u - inner ℝ g (GE g) ≤ e := by
    intro g
    have h1 : ((2 * inner ℝ g u - inner ℝ g (GE g) : ℝ) : EReal) ≤ limitFormEnergy GE u :=
      le_iSup (fun g : DomainL2 Q => ((2 * inner ℝ g u - inner ℝ g (GE g) : ℝ) : EReal)) g
    rw [hEu] at h1
    exact EReal.coe_le_coe_iff.mp h1
  have hdist : ∀ f : DomainL2 Q, ‖u - GE f‖ ^ 2 ≤
      (‖GE‖ + 1) * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) := by
    intro f
    have hn : 0 < ‖GE‖ + 1 := by positivity
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = (‖GE‖ + 1)⁻¹ := ⟨_, rfl⟩
    have ht : 0 < t := by rw [ht_def]; exact inv_pos.mpr hn
    have h1 := hφ (t • (u - GE f) + f)
    rw [aux_thm_prop_dual_shift GE hsym u f (t • (u - GE f))] at h1
    simp only [real_inner_smul_left, map_smul, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at h1
    have hGv : inner ℝ (u - GE f) (GE (u - GE f)) ≤ ‖GE‖ * ‖u - GE f‖ ^ 2 := by
      calc inner ℝ (u - GE f) (GE (u - GE f)) ≤ ‖u - GE f‖ * ‖GE (u - GE f)‖ :=
            real_inner_le_norm _ _
        _ ≤ ‖u - GE f‖ * (‖GE‖ * ‖u - GE f‖) := by
            gcongr
            exact GE.le_opNorm _
        _ = ‖GE‖ * ‖u - GE f‖ ^ 2 := by ring
    have htG : t * ‖GE‖ ≤ 1 := by
      rw [ht_def, inv_mul_le_iff₀ hn]
      linarith
    have h2 : t * inner ℝ (u - GE f) (GE (u - GE f)) ≤ ‖u - GE f‖ ^ 2 := by
      calc t * inner ℝ (u - GE f) (GE (u - GE f)) ≤ t * (‖GE‖ * ‖u - GE f‖ ^ 2) := by
            gcongr
        _ = (t * ‖GE‖) * ‖u - GE f‖ ^ 2 := by ring
        _ ≤ 1 * ‖u - GE f‖ ^ 2 := by gcongr
        _ = ‖u - GE f‖ ^ 2 := one_mul _
    have h3 : t * (t * inner ℝ (u - GE f) (GE (u - GE f))) ≤ t * ‖u - GE f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h2 ht.le
    have key : t * ‖u - GE f‖ ^ 2 ≤ e - (2 * inner ℝ f u - inner ℝ f (GE f)) := by
      linarith
    calc ‖u - GE f‖ ^ 2 = (‖GE‖ + 1) * (t * ‖u - GE f‖ ^ 2) := by
          rw [ht_def, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
      _ ≤ (‖GE‖ + 1) * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) :=
          mul_le_mul_of_nonneg_left key hn.le
  refine iSup_le fun g => ?_
  rw [EReal.coe_le_coe_iff]
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  have hKe : 0 ≤ K * e := mul_nonneg hK he0
  obtain ⟨τ, hτpos, hτhalf, hτδ⟩ : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ 2 * (K * e) * τ ≤ δ / 3 := by
    refine ⟨min (1 / 2) (δ / (6 * (K * e + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    calc 2 * (K * e) * min (1 / 2) (δ / (6 * (K * e + 1)))
        ≤ 2 * (K * e) * (δ / (6 * (K * e + 1))) := by gcongr; exact min_le_right _ _
      _ = δ / 3 * ((K * e) / (K * e + 1)) := by field_simp; ring
      _ ≤ δ / 3 * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith
      _ = δ / 3 := mul_one _
  obtain ⟨ρ0, hρ0pos, hρ0⟩ : ∃ ρ0 : ℝ, 0 < ρ0 ∧ 2 * (‖g‖ * ρ0) < δ / 3 := by
    refine ⟨δ / (6 * (‖g‖ + 1)), by positivity, ?_⟩
    have hx : 2 * (‖g‖ * (δ / (6 * (‖g‖ + 1)))) = δ / 3 * (‖g‖ / (‖g‖ + 1)) := by
      field_simp; ring
    rw [hx]
    have hlt : ‖g‖ / (‖g‖ + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hδ3 : 0 < δ / 3 := by positivity
    calc δ / 3 * (‖g‖ / (‖g‖ + 1)) < δ / 3 * 1 := by gcongr
      _ = δ / 3 := mul_one _
  obtain ⟨η0, hη0pos, hη0K, hη0ρ⟩ : ∃ η0 : ℝ, 0 < η0 ∧ K * η0 ≤ τ * (δ / 3) ∧
      (‖GE‖ + 1) * η0 ≤ ρ0 ^ 2 := by
    refine ⟨min (τ * (δ / 3) / (K + 1)) (ρ0 ^ 2 / (‖GE‖ + 1)),
      lt_min (by positivity) (by positivity), ?_, ?_⟩
    · calc K * min (τ * (δ / 3) / (K + 1)) (ρ0 ^ 2 / (‖GE‖ + 1))
          ≤ K * (τ * (δ / 3) / (K + 1)) := by gcongr; exact min_le_left _ _
        _ = τ * (δ / 3) * (K / (K + 1)) := by field_simp
        _ ≤ τ * (δ / 3) * 1 := by
            gcongr
            rw [div_le_one (by positivity)]
            linarith
        _ = τ * (δ / 3) := mul_one _
    · calc (‖GE‖ + 1) * min (τ * (δ / 3) / (K + 1)) (ρ0 ^ 2 / (‖GE‖ + 1))
          ≤ (‖GE‖ + 1) * (ρ0 ^ 2 / (‖GE‖ + 1)) := by gcongr; exact min_le_right _ _
        _ = ρ0 ^ 2 := by field_simp
  -- a source in `S` whose dual value is within `η0` of `E(u)`
  obtain ⟨f, hfS, hfU⟩ : ∃ f ∈ S, e - η0 < 2 * inner ℝ f u - inner ℝ f (GE f) := by
    have hlt : ((e - η0 / 2 : ℝ) : EReal) <
        ⨆ g : DomainL2 Q, ((2 * inner ℝ g u - inner ℝ g (GE g) : ℝ) : EReal) := by
      change _ < limitFormEnergy GE u
      rw [hEu]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨g0, hg0⟩ := lt_iSup_iff.mp hlt
    have hg0' : e - η0 / 2 < 2 * inner ℝ g0 u - inner ℝ g0 (GE g0) :=
      EReal.coe_lt_coe_iff.mp hg0
    have hcont : Continuous fun f : DomainL2 Q => 2 * inner ℝ f u - inner ℝ f (GE f) :=
      (continuous_const.mul (continuous_id.inner continuous_const)).sub
        (continuous_id.inner GE.continuous)
    have hopen : IsOpen {f : DomainL2 Q | e - η0 < 2 * inner ℝ f u - inner ℝ f (GE f)} :=
      isOpen_lt continuous_const hcont
    obtain ⟨f, hfS, hfU⟩ := hS.exists_mem_open hopen ⟨g0, by
      show e - η0 < 2 * inner ℝ g0 u - inner ℝ g0 (GE g0)
      linarith⟩
    exact ⟨f, hfS, hfU⟩
  have hφf := hφ f
  -- the distance `‖u - G_E f‖ < ρ0`
  have hv : ‖u - GE f‖ < ρ0 := by
    have h1 := hdist f
    have h2 : (‖GE‖ + 1) * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) < ρ0 ^ 2 := by
      have hn : 0 < ‖GE‖ + 1 := by positivity
      calc (‖GE‖ + 1) * (e - (2 * inner ℝ f u - inner ℝ f (GE f)))
          < (‖GE‖ + 1) * η0 := by gcongr; linarith
        _ ≤ ρ0 ^ 2 := hη0ρ
    exact lt_of_pow_lt_pow_left₀ 2 hρ0pos.le (lt_of_le_of_lt h1 h2)
  -- the energy `⟨f, G_E f⟩ ≤ e + 2 e τ + η / τ`
  have ha_bd : τ * (1 - τ) * inner ℝ f (GE f) ≤
      τ * e + (1 - τ) * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) := by
    have h := hφ ((1 - τ) • f)
    simp only [real_inner_smul_left, map_smul, real_inner_smul_right] at h
    nlinarith [h]
  have hτ1 : 0 < 1 - τ := by linarith
  have ha : K * inner ℝ f (GE f) ≤ K * e + δ / 3 + δ / 3 := by
    have hpp : 0 < τ * (1 - τ) := mul_pos hτpos hτ1
    have hRHS : (e + 2 * e * τ + (e - (2 * inner ℝ f u - inner ℝ f (GE f))) / τ) *
        (τ * (1 - τ)) = τ * e + (1 - τ) * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) +
          e * τ ^ 2 * (1 - 2 * τ) := by
      field_simp
      ring
    have hnn : 0 ≤ e * τ ^ 2 * (1 - 2 * τ) := by
      have : 0 ≤ 1 - 2 * τ := by linarith
      positivity
    have hA : inner ℝ f (GE f) ≤
        e + 2 * e * τ + (e - (2 * inner ℝ f u - inner ℝ f (GE f))) / τ := by
      refine le_of_mul_le_mul_right ?_ hpp
      rw [hRHS]
      nlinarith [ha_bd]
    have hη : K * ((e - (2 * inner ℝ f u - inner ℝ f (GE f))) / τ) ≤ δ / 3 := by
      rw [mul_div_assoc', div_le_iff₀ hτpos]
      have : K * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) ≤ K * η0 :=
        mul_le_mul_of_nonneg_left (by linarith) hK
      linarith
    calc K * inner ℝ f (GE f)
        ≤ K * (e + 2 * e * τ + (e - (2 * inner ℝ f u - inner ℝ f (GE f))) / τ) :=
          mul_le_mul_of_nonneg_left hA hK
      _ = K * e + 2 * (K * e) * τ +
          K * ((e - (2 * inner ℝ f u - inner ℝ f (GE f))) / τ) := by ring
      _ ≤ K * e + δ / 3 + δ / 3 := by linarith
  -- `ψ_g(G_E f) ≤ F(G_E f) ≤ K ⟨f, G_E f⟩`
  have hF : 2 * inner ℝ g (GE f) - inner ℝ g (GF g) ≤ K * inner ℝ f (GE f) := by
    have h1 : ((2 * inner ℝ g (GE f) - inner ℝ g (GF g) : ℝ) : EReal) ≤
        limitFormEnergy GF (GE f) :=
      le_iSup (fun g : DomainL2 Q =>
        ((2 * inner ℝ g (GE f) - inner ℝ g (GF g) : ℝ) : EReal)) g
    exact EReal.coe_le_coe_iff.mp (h1.trans (hcore f hfS))
  have hsplit : 2 * inner ℝ g u - inner ℝ g (GF g) =
      (2 * inner ℝ g (GE f) - inner ℝ g (GF g)) + 2 * inner ℝ g (u - GE f) := by
    rw [inner_sub_right]
    ring
  have hcs : inner ℝ g (u - GE f) ≤ ‖g‖ * ‖u - GE f‖ := real_inner_le_norm _ _
  have hgv : 2 * (‖g‖ * ‖u - GE f‖) ≤ 2 * (‖g‖ * ρ0) := by
    gcongr
  rw [hsplit]
  linarith

def aux_thm_prop_smoothSources {d : ℕ} (Q : Opens (SpatialCoordinates d)) :
    Set (DomainL2 Q) :=
  {f | ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
    tsupport fc ⊆ (Q : Set (SpatialCoordinates d)) ∧
    (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fc}

theorem aux_thm_prop_smoothSources_dense {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (hQ : volume (Q : Set (SpatialCoordinates d)) ≠ ⊤) :
    Dense (aux_thm_prop_smoothSources Q) := by
  refine (Homogenization.dense_smoothCompactSupportScalarL2_tsupport_subset Q.isOpen hQ).mono ?_
  rintro f ⟨g, hgL2, rfl, hg, hgc, hgs⟩
  exact ⟨g, hg, hgc, hgs, hgL2.coeFn_toLp⟩

theorem aux_thm_prop_energy_lsc {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) : LowerSemicontinuous (limitFormEnergy G) := by
  show LowerSemicontinuous fun u : DomainL2 Q =>
    ⨆ f : DomainL2 Q, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)
  refine lowerSemicontinuous_iSup fun f => Continuous.lowerSemicontinuous ?_
  exact continuous_coe_real_ereal.comp
    ((continuous_const.mul (continuous_const.inner continuous_id)).sub continuous_const)

theorem aux_thm_prop_saving_sum {ι : Type} (G : Finset ι) (T Γ vol B : ι → ℝ)
    (Δ a κ ϱ c E volQ ε : ℝ) (hΔ : 0 ≤ Δ) (ha : 0 < a) (hκ : 0 ≤ κ)
    (hϱ : 0 ≤ ϱ) (hϱa : ϱ ≤ a * κ / 16) (hc : 0 ≤ c) (hE : 0 ≤ E) (hvolQ : 0 ≤ volQ)
    (hsave : ∀ q ∈ G, Δ * (a / 2 * T q - 4 * ϱ * (Γ q + c * vol q)) ≤ B q)
    (hrep : ∑ q ∈ G, (Γ q - T q) ≤ ε)
    (hmass : κ * (E + c * volQ) ≤ ∑ q ∈ G, (Γ q + c * vol q))
    (htot : ∑ q ∈ G, (Γ q + c * vol q) ≤ E + c * volQ)
    (hvol : ∑ q ∈ G, vol q ≤ volQ) :
    Δ * (a * κ / 4 * E - a * c * volQ - a / 2 * ε) ≤ ∑ q ∈ G, B q := by
  have h1 : ∑ q ∈ G, Δ * (a / 2 * T q - 4 * ϱ * (Γ q + c * vol q)) ≤ ∑ q ∈ G, B q :=
    Finset.sum_le_sum hsave
  have h2 : ∑ q ∈ G, Δ * (a / 2 * T q - 4 * ϱ * (Γ q + c * vol q)) =
      Δ * (a / 2 * ∑ q ∈ G, T q - 4 * ϱ * ∑ q ∈ G, (Γ q + c * vol q)) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h3 : ∑ q ∈ G, (Γ q - T q) = ∑ q ∈ G, Γ q - ∑ q ∈ G, T q := Finset.sum_sub_distrib ..
  have h4 : ∑ q ∈ G, (Γ q + c * vol q) = ∑ q ∈ G, Γ q + c * ∑ q ∈ G, vol q := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hcv : c * ∑ q ∈ G, vol q ≤ c * volQ := mul_le_mul_of_nonneg_left hvol hc
  have hX : 0 ≤ E + c * volQ := by positivity
  have s1 : ∑ q ∈ G, Γ q - ε ≤ ∑ q ∈ G, T q := by linarith
  have s2 := mul_le_mul_of_nonneg_left s1 (by positivity : (0 : ℝ) ≤ a / 2)
  have s3 := mul_le_mul_of_nonneg_left htot (by positivity : (0 : ℝ) ≤ 4 * ϱ)
  have s4 : κ * (E + c * volQ) - c * volQ ≤ ∑ q ∈ G, Γ q := by linarith
  have s5 := mul_le_mul_of_nonneg_left s4 (by positivity : (0 : ℝ) ≤ a / 2)
  have s6 := mul_le_mul_of_nonneg_right hϱa hX
  have s7 : 0 ≤ a * κ * c * volQ := by positivity
  have s8 : 0 ≤ a * c * volQ := by positivity
  have hinner : a * κ / 4 * E - a * c * volQ - a / 2 * ε ≤
      a / 2 * ∑ q ∈ G, T q - 4 * ϱ * ∑ q ∈ G, (Γ q + c * vol q) := by
    linarith [s2, s3, s5, s6, s7, s8]
  calc Δ * (a * κ / 4 * E - a * c * volQ - a / 2 * ε)
      ≤ Δ * (a / 2 * ∑ q ∈ G, T q - 4 * ϱ * ∑ q ∈ G, (Γ q + c * vol q)) :=
        mul_le_mul_of_nonneg_left hinner hΔ
    _ = ∑ q ∈ G, Δ * (a / 2 * T q - 4 * ϱ * (Γ q + c * vol q)) := h2.symm
    _ ≤ ∑ q ∈ G, B q := h1

theorem aux_thm_prop_limit_step (Fu E M Δ k1 C : ℝ) (hΔ : 0 ≤ Δ) (hC : 0 ≤ C)
    (h : ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → Fu ≤ (M - k1 * Δ) * E + Δ * (C * c) + ε) :
    Fu ≤ (M - k1 * Δ) * E := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  have hc : 0 < δ / (2 * (Δ * C + 1)) := by
    have : 0 ≤ Δ * C := mul_nonneg hΔ hC
    positivity
  have h1 := h _ hc (δ / 4) (by positivity)
  have h2 : Δ * (C * (δ / (2 * (Δ * C + 1)))) ≤ δ / 2 := by
    have hpos : 0 < 2 * (Δ * C + 1) := by
      have : 0 ≤ Δ * C := mul_nonneg hΔ hC
      positivity
    rw [← mul_assoc, mul_div_assoc', div_le_iff₀ hpos]
    nlinarith [mul_nonneg hΔ hC]
  linarith

theorem aux_thm_prop_swap_algebra (cL cU k1 : ℝ) (hcL : 0 < cL) (hlt : cL < cU)
    (hk1 : 0 < k1) (hk11 : k1 ≤ 1) :
    0 < cL⁻¹ - k1 * (cL⁻¹ - cU⁻¹) ∧
      (cL + k1 * cL / cU * (cU - cL)) * (cL⁻¹ - k1 * (cL⁻¹ - cU⁻¹)) ≤ 1 := by
  have hcU : 0 < cU := hcL.trans hlt
  have hK' : cL⁻¹ - k1 * (cL⁻¹ - cU⁻¹) = ((1 - k1) * cU + k1 * cL) / (cL * cU) := by
    field_simp
    ring
  have hden : 0 < (1 - k1) * cU + k1 * cL := by
    have : 0 ≤ (1 - k1) * cU := mul_nonneg (by linarith) hcU.le
    have : 0 < k1 * cL := mul_pos hk1 hcL
    linarith
  refine ⟨by rw [hK']; positivity, ?_⟩
  have hid : (cL + k1 * cL / cU * (cU - cL)) * (cL⁻¹ - k1 * (cL⁻¹ - cU⁻¹)) =
      1 - (k1 * (cU - cL) / cU) ^ 2 := by
    field_simp
    ring
  rw [hid]
  nlinarith [sq_nonneg (k1 * (cU - cL) / cU)]

theorem aux_thm_prop_toReal_le {X : EReal} {y : ℝ} (hX : 0 ≤ X) (h : X ≤ (y : EReal)) :
    X.toReal ≤ y := by
  have := EReal.toReal_le_toReal h (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hX))
    (EReal.coe_ne_top y)
  simpa using this

def aux_thm_prop_localSaving (M Δ E Fu volQ c ε : ℝ) : Prop :=
  ∃ (n : ℕ) (T Γ vol B : Fin n → ℝ) (Fv : ℝ),
    (∀ q, Δ * ((3 / 8 : ℝ) / 2 * T q -
      4 * ((3 / 8 : ℝ) * (1 / 8) / 16) * (Γ q + c * vol q)) ≤ B q) ∧
    ∑ q, (Γ q - T q) ≤ ε ∧
    (1 / 8 : ℝ) * (E + c * volQ) ≤ ∑ q, (Γ q + c * vol q) ∧
    ∑ q, (Γ q + c * vol q) ≤ E + c * volQ ∧
    ∑ q, vol q ≤ volQ ∧
    Fv ≤ M * E - ∑ q, B q ∧
    Fu ≤ Fv + ε

theorem aux_thm_prop_local_to_improve (M Δ E Fu volQ : ℝ) (hΔ : 0 ≤ Δ) (hE : 0 ≤ E)
    (hvolQ : 0 ≤ volQ)
    (h : ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → aux_thm_prop_localSaving M Δ E Fu volQ c ε) :
    Fu ≤ (M - 3 / 256 * Δ) * E := by
  refine aux_thm_prop_limit_step Fu E M Δ (3 / 256) (3 / 8 * volQ) hΔ (by positivity) ?_
  intro c hc ε hε
  have hε' : 0 < ε / (Δ + 1) := by positivity
  obtain ⟨n, T, Γ, vol, B, Fv, hsave, hrep, hmass, htot, hvol, hcomp, hlsc⟩ :=
    h c hc (ε / (Δ + 1)) hε'
  have hsum := aux_thm_prop_saving_sum Finset.univ T Γ vol B Δ (3 / 8) (1 / 8)
    ((3 / 8 : ℝ) * (1 / 8) / 16) c E volQ (ε / (Δ + 1)) hΔ (by norm_num) (by norm_num)
    (by norm_num) (le_refl _) hc.le hE hvolQ (fun q _ => hsave q) hrep hmass htot hvol
  have hkey : Δ * (3 / 8 / 2 * (ε / (Δ + 1))) + ε / (Δ + 1) ≤ ε := by
    have h1 : Δ * (3 / 8 / 2 * (ε / (Δ + 1))) + ε / (Δ + 1) ≤ (Δ + 1) * (ε / (Δ + 1)) := by
      have : 0 ≤ Δ * (ε / (Δ + 1)) := by positivity
      nlinarith
    have h2 : (Δ + 1) * (ε / (Δ + 1)) = ε := by field_simp
    linarith
  nlinarith [hsum, hkey]

theorem aux_thm_prop_half_density (Pgood : ℕ → Prop) :
    (1 / 2 : ℝ) ≤ Lane3.upperDensity Pgood ∨
      (1 / 2 : ℝ) ≤ Lane3.upperDensity (fun n => ¬ Pgood n) := by
  classical
  by_cases hU : (1 / 2 : ℝ) ≤ Lane3.upperDensity Pgood
  · exact Or.inl hU
  · right
    by_contra hV
    have hU_lt : Lane3.upperDensity Pgood < (1 / 2 : ℝ) := lt_of_not_ge hU
    have hV_lt : Lane3.upperDensity (fun n => ¬ Pgood n) < (1 / 2 : ℝ) := lt_of_not_ge hV
    have hU_ev : ∀ᶠ J : ℕ in atTop,
        (Lane3.levelCount Pgood J : ℝ) / (J : ℝ) < (1 / 2 : ℝ) :=
      eventually_lt_of_limsup_lt hU_lt (Lane3.upperDensity_bddUnder Pgood)
    have hV_ev : ∀ᶠ J : ℕ in atTop,
        (Lane3.levelCount (fun n => ¬ Pgood n) J : ℝ) / (J : ℝ) < (1 / 2 : ℝ) :=
      eventually_lt_of_limsup_lt hV_lt
        (Lane3.upperDensity_bddUnder (fun n => ¬ Pgood n))
    have hJ_ev : ∀ᶠ J : ℕ in atTop, 1 ≤ J :=
      eventually_atTop.2 ⟨1, fun J hJ => hJ⟩
    rcases eventually_atTop.1 hU_ev with ⟨JU, hU_ev'⟩
    rcases eventually_atTop.1 hV_ev with ⟨JV, hV_ev'⟩
    rcases eventually_atTop.1 hJ_ev with ⟨J1, hJ_ev'⟩
    let J := max JU (max JV J1)
    have hJUJ : JU ≤ J := le_max_left _ _
    have hJVJ : JV ≤ J := (le_max_left _ _).trans (le_max_right _ _)
    have hJ1J : J1 ≤ J := (le_max_right _ _).trans (le_max_right _ _)
    have hUJ := hU_ev' J hJUJ
    have hVJ := hV_ev' J hJVJ
    have hJ1 := hJ_ev' J hJ1J
    have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ1
    have hcovNat : J ≤ Lane3.levelCount Pgood J +
        Lane3.levelCount (fun n => ¬ Pgood n) J := by
      have hcover := Lane3.levelCount_cover Pgood (fun n => ¬ Pgood n)
        (fun _ : ℕ => False) (by intro n hnU hnV; exact hnV hnU) J
      simpa [Lane3.levelCount] using hcover
    have hcov : (J : ℝ) ≤ (Lane3.levelCount Pgood J : ℝ) +
        (Lane3.levelCount (fun n => ¬ Pgood n) J : ℝ) := by
      exact_mod_cast hcovNat
    have hU_count : (Lane3.levelCount Pgood J : ℝ) <
        (1 / 2 : ℝ) * (J : ℝ) := (div_lt_iff₀ hJpos).mp hUJ
    have hV_count : (Lane3.levelCount (fun n => ¬ Pgood n) J : ℝ) <
        (1 / 2 : ℝ) * (J : ℝ) := (div_lt_iff₀ hJpos).mp hVJ
    nlinarith

theorem aux_thm_prop_F_upper {ι : Type*} (s : Finset ι) (Fv M ME GamEout : ℝ)
    (GamE LamF B : ι → ℝ)
    (hME : ME = GamEout + ∑ q ∈ s, GamE q)
    (hB : ∀ q ∈ s, B q = M * GamE q - LamF q)
    (hFv : Fv ≤ M * GamEout + ∑ q ∈ s, LamF q) :
    Fv ≤ M * ME - ∑ q ∈ s, B q := by
  have hBsum : ∑ q ∈ s, B q = M * ∑ q ∈ s, GamE q - ∑ q ∈ s, LamF q := by
    have h1 : (∑ q ∈ s, B q) = ∑ q ∈ s, (M * GamE q - LamF q) :=
      Finset.sum_congr rfl fun q hq => hB q hq
    rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hME, hBsum]
  nlinarith [hFv]

theorem aux_thm_prop_final_bracket (a κ ϱ E c Qmass GamU eps Bsum : ℝ)
    (ha : 0 < a) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hϱ0 : 0 ≤ ϱ) (hϱ : ϱ ≤ a * κ / 16)
    (hE : 0 ≤ E) (hc : 0 ≤ c) (hQ : 0 ≤ Qmass) (heps : 0 ≤ eps)
    (hGam : κ * E - (1 - κ) * (c * Qmass) ≤ GamU)
    (hB : a / 2 * GamU - eps - 4 * ϱ * (E + c * Qmass) ≤ Bsum) :
    a * κ / 4 * E - (a / 2 * (1 - κ) + 4 * ϱ) * (c * Qmass) - eps ≤ Bsum := by
  have ha2 : 0 ≤ a / 2 := by positivity
  have hkey : 0 ≤ E * (a * κ / 4 - 4 * ϱ) := by
    refine mul_nonneg hE ?_
    have h : a * κ / 4 - 4 * ϱ = 4 * (a * κ / 16 - ϱ) := by ring
    rw [h]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr hϱ)
  nlinarith [hB, mul_le_mul_of_nonneg_left hGam ha2, hkey]

theorem aux_thm_prop_sum_saving {ι : Type*} (s : Finset ι) (B T lam : ι → ℝ) (Delta a rho lamQ : ℝ)
    (hDelta : 0 ≤ Delta) (hrho : 0 ≤ rho)
    (hcell : ∀ q ∈ s, Delta * (a / 2 * T q - 4 * rho * lam q) ≤ B q)
    (hlam : (∑ q ∈ s, lam q) ≤ lamQ) :
    Delta * (a / 2 * (∑ q ∈ s, T q) - 4 * rho * lamQ) ≤ ∑ q ∈ s, B q := by
  have hsplit : ∑ q ∈ s, Delta * (a / 2 * T q - 4 * rho * lam q)
      = Delta * (a / 2 * (∑ q ∈ s, T q) - 4 * rho * (∑ q ∈ s, lam q)) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hle : Delta * (a / 2 * (∑ q ∈ s, T q) - 4 * rho * lamQ)
      ≤ Delta * (a / 2 * (∑ q ∈ s, T q) - 4 * rho * (∑ q ∈ s, lam q)) := by
    apply mul_le_mul_of_nonneg_left _ hDelta
    have h4 : 4 * rho * (∑ q ∈ s, lam q) ≤ 4 * rho * lamQ :=
      mul_le_mul_of_nonneg_left hlam (by linarith)
    linarith
  calc Delta * (a / 2 * (∑ q ∈ s, T q) - 4 * rho * lamQ)
      ≤ Delta * (a / 2 * (∑ q ∈ s, T q) - 4 * rho * (∑ q ∈ s, lam q)) := hle
    _ = ∑ q ∈ s, Delta * (a / 2 * T q - 4 * rho * lam q) := hsplit.symm
    _ ≤ ∑ q ∈ s, B q := Finset.sum_le_sum hcell

theorem aux_thm_prop_dich_pointwise {V : Type} [AddCommGroup V] [Module ℝ V]
    (Q0 Bq : QuadraticForm ℝ V) (hQ : ∀ v, 0 ≤ Q0 v) (hB : ∀ v, 0 ≤ Bq v)
    (Del : ℝ) (hDel : 0 ≤ Del)
    (hdom : ∀ v, Bq v ≤ Del * Q0 v) (b l : V) (lam : ℝ)
    (hsaving : (3 / 8 : ℝ) * Del * Q0 l ≤ Bq l)
    (haffine : Q0 (b - l) ≤ (3 / 8 : ℝ) * (1 / 8) / 16 * lam) :
    Del * ((3 / 8 : ℝ) / 2 * Q0 b - 4 * ((3 / 8 : ℝ) * (1 / 8) / 16) * lam) ≤ Bq b := by
  have hkey := lem_saving Q0 Bq hQ hB Del (3 / 8) (by norm_num) (by norm_num) hdom b l hsaving
  have hgap : 0 ≤ Del * (4 * ((3 / 8 : ℝ) * (1 / 8) / 16 * lam - Q0 (b - l))) :=
    mul_nonneg hDel (by nlinarith [haffine])
  nlinarith [hkey, hgap]

theorem aux_thm_prop_dich_massMono {d : ℕ} {ι : Type} [Fintype ι]
    (Q : Opens (SpatialCoordinates d))
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (q : ι → Set (SpatialCoordinates d))
    (hmeas : ∀ i, MeasurableSet (q i)) (hsub : ∀ i, q i ⊆ (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise (fun i j => Disjoint (q i) (q j))) :
    ∑ i, (nu (q i)).toReal ≤ (nu (Q : Set (SpatialCoordinates d))).toReal := by
  have hne : ∀ i, nu (q i) ≠ ⊤ := fun i => measure_ne_top nu _
  have hadd : nu (⋃ i, q i) = ∑ i, nu (q i) := by
    rw [measure_iUnion (fun i j hij => hdisj hij) hmeas, tsum_fintype]
  have hUsub : (⋃ i, q i) ⊆ (Q : Set (SpatialCoordinates d)) := Set.iUnion_subset hsub
  have hsum_eq : ∑ i, (nu (q i)).toReal = (∑ i, nu (q i)).toReal :=
    (ENNReal.toReal_sum (fun i _ => hne i)).symm
  rw [hsum_eq, ← hadd]
  exact ENNReal.toReal_mono (measure_ne_top nu _) (measure_mono hUsub)

theorem aux_thm_prop_dich_massLower {d : ℕ} {ι : Type} [Fintype ι]
    (Q : Opens (SpatialCoordinates d))
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (q : ι → Set (SpatialCoordinates d))
    (hraw : (nu (Q : Set (SpatialCoordinates d))).toReal / 8 ≤
      (nu (⋃ i, q i)).toReal)
    (hadd : nu (⋃ i, q i) = ∑ i, nu (q i)) :
    (1 / 8 : ℝ) * (nu (Q : Set (SpatialCoordinates d))).toReal ≤ ∑ i, (nu (q i)).toReal := by
  have hsum_eq : ∑ i, (nu (q i)).toReal = (∑ i, nu (q i)).toReal :=
    (ENNReal.toReal_sum (fun i _ => measure_ne_top nu _)).symm
  rw [hsum_eq, ← hadd]
  linarith [hraw]

theorem aux_thm_prop_dich_mesh {d : ℕ} (hd : 2 ≤ d)
    (I : Paper.in_J d) (Pin : Paper.in_poincare d hd I) (Sob : Lane4.SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
    ∀ (Rm : Paper.in_responses d model)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (field : Ω → BilateralField d)
      (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
      (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
      (GN : (i : ℕ) → ℕ → Ω →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)))
      (GE : (i : ℕ) → Ω →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)))
      (NE : ℕ → ℕ),
    in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GE NE NE →
    ∀ᵐ omega ∂P, ∀ root : ℕ,
      ∀ (E : DirichletForm.ClosedForm
          (volume.restrict (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d))))
        (hEdom : E.domain = limitFormDomain (GE root omega))
        (hEenergy : ∀ u ∈ E.domain, E.form u u = (limitFormEnergy (GE root omega) u).toReal)
        (Gamma : DirichletForm.EnergyMeasure E)
        (hsupport : ∀ u ∈ E.domain,
          Gamma.measure u (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d))ᶜ = 0)
        (f : DomainL2 (centeredCube (z root) (r root) (hr root))) (ε : ℝ) (hε : 0 < ε),
      let u := GE root omega f
      ∃ h0 : ℝ, 0 < h0 ∧
        ∀ (n : ℕ) (zc : Fin n → SpatialCoordinates d) (rc : Fin n → ℝ) (hrc : ∀ i, 0 < rc i)
          (h : ℝ), 0 < h → h ≤ h0 →
          (∀ i, rc i ≤ h) →
          (∀ i, (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d)) ⊆
            (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d))) →
          Pairwise (fun i j =>
            Disjoint (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d))
              (centeredCube (zc j) (rc j) (hrc j) : Set (SpatialCoordinates d))) →
          ∀ (Vi : Fin n → Submodule ℝ (DomainL2 (centeredCube (z root) (r root) (hr root))))
            (hVi : ∀ i, DirichletForm.IsKilledDomain E
              (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d)) (Vi i)),
          let Lambda : Fin n → ℝ := fun i =>
            sInf {t : ℝ | ∃ v : DomainL2 (centeredCube (z root) (r root) (hr root)), v ∈ Vi i ∧
              t = (Gamma.measure (u + v)
                (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d))).toReal}
          (∑ i : Fin n, ((Gamma.measure u
            (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d))).toReal - Lambda i)) < ε := by
  obtain ⟨delta0, hdelta0, hAll⟩ := lem_replace d hd I Pin Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel Rm H Ω _ P field z r hr Sspace GN GE NE hJoint
  filter_upwards [hAll model hmodel Rm H Ω P field z r hr Sspace GN GE NE hJoint]
    with omega hOmega root E hEdom hEenergy Gamma hsupport f ε hε
  obtain ⟨K, _hK, _hB, _hC, hClauseF⟩ := hOmega root E hEdom hEenergy Gamma hsupport
  obtain ⟨h0fun, hh0pos, hClause⟩ := hClauseF f
  refine ⟨h0fun ε, hh0pos ε hε, ?_⟩
  intro n zc rc hrc h hh hhle hside hinside hdisjoint Vi hVi
  obtain ⟨uC, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    hClause n zc rc hrc h hh hside hinside hdisjoint Vi hVi
  exact c9 ε hε hhle

theorem aux_thm_prop_dich_locality {n : ℕ} (Eu M Foff Fv : ℝ) (hM : 0 ≤ M)
    (T Gam Fq Bq : Fin n → ℝ)
    (hloc : Fv ≤ M * Foff + ∑ q, Fq q)
    (hBeq : ∀ q, Fq q = M * T q - Bq q)
    (hTG : ∀ q, T q ≤ Gam q)
    (hEadd : Eu = Foff + ∑ q, Gam q) :
    Fv ≤ M * Eu - ∑ q, Bq q := by
  have hsum : ∑ q, Fq q = M * ∑ q, T q - ∑ q, Bq q := by
    simp_rw [hBeq]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have hTsum : ∑ q, T q ≤ ∑ q, Gam q := Finset.sum_le_sum (fun q _ => hTG q)
  have hMTsum : M * ∑ q, T q ≤ M * ∑ q, Gam q := mul_le_mul_of_nonneg_left hTsum hM
  calc Fv ≤ M * Foff + ∑ q, Fq q := hloc
    _ = M * Foff + (M * ∑ q, T q - ∑ q, Bq q) := by rw [hsum]
    _ ≤ M * Foff + (M * ∑ q, Gam q - ∑ q, Bq q) := by linarith
    _ = M * Eu - ∑ q, Bq q := by rw [hEadd]; ring

theorem aux_thm_prop_dich_limit (Fu L : ℝ) (Fv : ℝ → ℝ) (hFu : Fu ≤ L)
    (hlsc : Filter.Tendsto Fv (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ Fu ≤ Fv h + ε := by
  intro ε hε
  have hev : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), Fv h ∈ Set.Ioo (L - ε) (L + ε) :=
    hlsc.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨h, hh1, hh2⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨h, hh2, by linarith [hh1.1]⟩

theorem aux_thm_prop_dich_locality_concrete {d : ℕ} {n : ℕ}
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (i : ℕ)
    {Ω : Type} (GE : Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω) (M : ℝ) (hM : 0 ≤ M)
    (E : DirichletForm.ClosedForm
      (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E)
    (f : DomainL2 (centeredCube (z i) (r i) (hr i)))
    (zc : Fin n → SpatialCoordinates d) (rc : Fin n → ℝ) (hrc : ∀ q, 0 < rc q)
    (Fv Foff : ℝ)
    (T Gam Fq Bq : Fin n → ℝ)
    (hT : ∀ q, T q ≤ Gam q)
    (hGam : ∀ q, Gam q = (GammaE.measure (GE omega f)
      (centeredCube (zc q) (rc q) (hrc q) : Set (SpatialCoordinates d))).toReal)
    (hEadd : (limitFormEnergy (GE omega) (GE omega f)).toReal = Foff + ∑ q, Gam q)
    (hBeq : ∀ q, Fq q = M * T q - Bq q)
    (hloc : Fv ≤ M * Foff + ∑ q, Fq q) :
    Fv ≤ M * (limitFormEnergy (GE omega) (GE omega f)).toReal - ∑ q, Bq q :=
  aux_thm_prop_dich_locality (limitFormEnergy (GE omega) (GE omega f)).toReal M Foff Fv hM
    T Gam Fq Bq hloc hBeq hT hEadd

theorem aux_thm_prop_dich_limit_concrete {d : ℕ}
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (i : ℕ)
    {Ω : Type} (GE GF : Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω)
    (F : DirichletForm.ClosedForm
      (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))))
    (f : DomainL2 (centeredCube (z i) (r i) (hr i)))
    (v : ℝ → DomainL2 (centeredCube (z i) (r i) (hr i)))
    (L : ℝ) (hFu : (limitFormEnergy (GF omega) (GE omega f)).toReal ≤ L)
    (hlsc : Filter.Tendsto (fun h => F.form (v h) (v h))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧
      (limitFormEnergy (GF omega) (GE omega f)).toReal ≤ F.form (v h) (v h) + ε :=
  aux_thm_prop_dich_limit (limitFormEnergy (GF omega) (GE omega f)).toReal L
    (fun h => F.form (v h) (v h)) hFu hlsc

theorem aux_thm_prop_dich_hloc_derive {d : ℕ} {n : ℕ}
    (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hEloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (hFreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hFloc : DirichletForm.IsStronglyLocal F.toClosedForm)
    (m M : ℝ) (hm : 0 < m)
    (hform : ∀ w ∈ E.domain, m * E.form w w ≤ F.form w w ∧ F.form w w ≤ M * E.form w w)
    (u v : DomainL2 Q) (hu : u ∈ E.domain) (hvF : v ∈ F.domain)
    (off : Set (SpatialCoordinates d)) (hoffOpen : IsOpen off) (hoffMeas : MeasurableSet off)
    (huv_off : (v : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict
      (Q : Set (SpatialCoordinates d))).restrict off] (u : SpatialCoordinates d → ℝ))
    (cell : Fin n → Set (SpatialCoordinates d)) (hcell_meas : ∀ i, MeasurableSet (cell i))
    (hcell_disj : Pairwise (fun i j => Disjoint (cell i) (cell j)))
    (hoff_disj : Disjoint off (⋃ i, cell i))
    (hoff_cover : off ∪ (⋃ i, cell i) = (Q : Set (SpatialCoordinates d)))
    (hsuppF : GammaF.measure v (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (Fq : Fin n → ℝ) (hFq : ∀ i, Fq i = (GammaF.measure v (cell i)).toReal) :
    F.form v v ≤ M * (GammaE.measure u off).toReal + ∑ i, Fq i := by
  have hu' : u ∈ E.domain := hu
  have hordE := energy_order_of_form_order Q E F hEreg hEloc hFreg hFloc hdom GammaE GammaF
    m M hm hform u hu' off hoffMeas
  have hlocA : GammaF.measure v off = GammaF.measure u off :=
    GammaF.locality_apply hvF (hdom ▸ hu) hoffOpen huv_off
  have hUnivFin : GammaF.measure v Set.univ ≠ ⊤ := (GammaF.measure_univ_lt_top v hvF).ne
  have hcellne : ∀ i, GammaF.measure v (cell i) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top hUnivFin (measure_mono (Set.subset_univ _))
  have hoffne : GammaF.measure v off ≠ ⊤ :=
    ne_top_of_le_ne_top hUnivFin (measure_mono (Set.subset_univ _))
  have hUnionMeas : MeasurableSet (⋃ i, cell i) := MeasurableSet.iUnion hcell_meas
  have hcellsum : GammaF.measure v (⋃ i, cell i) = ∑ i, GammaF.measure v (cell i) := by
    rw [measure_iUnion (fun i j hij => hcell_disj hij) hcell_meas, tsum_fintype]
  have hQeq : GammaF.measure v (Q : Set (SpatialCoordinates d)) =
      GammaF.measure v off + ∑ i, GammaF.measure v (cell i) := by
    have hunion : GammaF.measure v (off ∪ ⋃ i, cell i) =
        GammaF.measure v off + ∑ i, GammaF.measure v (cell i) := by
      rw [measure_union hoff_disj hUnionMeas, hcellsum]
    rwa [hoff_cover] at hunion
  have hQne : GammaF.measure v (Q : Set (SpatialCoordinates d)) ≠ ⊤ :=
    ne_top_of_le_ne_top hUnivFin (measure_mono (Set.subset_univ _))
  have hcellsum_ne : (∑ i, GammaF.measure v (cell i)) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr (fun i _ => (hcellne i).lt_top)).ne
  have hQreal : (GammaF.measure v (Q : Set (SpatialCoordinates d))).toReal =
      (GammaF.measure v off).toReal + ∑ i, (GammaF.measure v (cell i)).toReal := by
    rw [hQeq, ENNReal.toReal_add hoffne hcellsum_ne]
    congr 1
    exact ENNReal.toReal_sum (fun i _ => hcellne i)
  have hUnivQ : GammaF.measure v Set.univ = GammaF.measure v (Q : Set (SpatialCoordinates d)) := by
    have hcompl : GammaF.measure v (Q : Set (SpatialCoordinates d))ᶜ = 0 := hsuppF
    have := measure_add_measure_compl (μ := GammaF.measure v)
      Q.isOpen.measurableSet
    rw [hcompl, add_zero] at this
    exact this.symm
  have hFv : F.form v v = (GammaF.measure v Set.univ).toReal := (GammaF.measure_univ v hvF).symm
  rw [hFv, hUnivQ, hQreal, hlocA]
  have hsum_eq : ∑ i, (GammaF.measure v (cell i)).toReal = ∑ i, Fq i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hFq i]
  rw [hsum_eq]
  linarith [hordE.2]

theorem aux_thm_prop_dich_assemble {n : ℕ} (M Del E Fu volQ c ε : ℝ)
    (T Γ vol B : Fin n → ℝ) (Fv : ℝ)
    (h1 : ∀ q, Del * ((3 / 8 : ℝ) / 2 * T q -
      4 * ((3 / 8 : ℝ) * (1 / 8) / 16) * (Γ q + c * vol q)) ≤ B q)
    (h2 : ∑ q, (Γ q - T q) ≤ ε)
    (h3 : (1 / 8 : ℝ) * (E + c * volQ) ≤ ∑ q, (Γ q + c * vol q))
    (h4 : ∑ q, (Γ q + c * vol q) ≤ E + c * volQ)
    (h5 : ∑ q, vol q ≤ volQ)
    (h6 : Fv ≤ M * E - ∑ q, B q)
    (h7 : Fu ≤ Fv + ε) :
    aux_thm_prop_localSaving M Del E Fu volQ c ε :=
  ⟨n, T, Γ, vol, B, Fv, h1, h2, h3, h4, h5, h6, h7⟩

theorem aux_thm_prop_energy_coe {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) (hu : u ∈ limitFormDomain G) :
    limitFormEnergy G u = ((limitFormEnergy G u).toReal : EReal) := by
  have hu' : limitFormEnergy G u < ⊤ := hu
  exact (EReal.coe_toReal (ne_of_lt hu')
    (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg G u)))).symm

theorem aux_thm_prop_energy_lsc_eventually
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (u : DomainL2 Q) (hu : u ∈ limitFormDomain G)
    (v : ℕ → DomainL2 Q) (hv : ∀ n, v n ∈ limitFormDomain G)
    (hconv : Tendsto v atTop (𝓝 u)) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n in atTop, (limitFormEnergy G u).toReal ≤ (limitFormEnergy G (v n)).toReal + eps := by
  have hlt : (((limitFormEnergy G u).toReal - eps : ℝ) : EReal) < limitFormEnergy G u := by
    rw [aux_thm_prop_energy_coe G u hu]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ heps)
  have hev := hconv.eventually ((aux_thm_prop_energy_lsc G) u _ hlt)
  filter_upwards [hev] with n hn
  rw [aux_thm_prop_energy_coe G (v n) (hv n)] at hn
  have hh := EReal.coe_lt_coe_iff.mp hn
  linarith
















section Resample

variable {d : ℕ} (S : Finset ℤ) (om1 om2 : BilateralField d)













end Resample

section Measure

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)




end Measure

































end Paper

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

theorem aux_thm_prop_isRegular_of_core
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hcore : ∃ C, DirichletForm.IsCoreOn F (Q : Set (SpatialCoordinates d)) C) :
    DirichletForm.IsRegular F := by
  refine ⟨Q, Q.isOpen, ?_, hcore⟩
  rw [Measure.restrict_apply Q.isOpen.measurableSet.compl]
  simp only [compl_inter_self, measure_empty]

theorem aux_thm_prop_energy_measure_of_locality
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (F : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (EM : DirichletForm.HasEnergyMeasure F)
    (hcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hloc : DirichletForm.IsStronglyLocal F.toClosedForm) :
    ∃ Gamma : DirichletForm.EnergyMeasure F.toClosedForm,
      ∀ u ∈ F.domain,
        Gamma.measure u (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
  obtain ⟨Gamma⟩ := EM.exists_energyMeasure
    (aux_thm_prop_isRegular_of_core (centeredCube z r hr) F.toClosedForm hcore) hloc
  obtain ⟨C, hC⟩ := hcore
  exact ⟨Gamma, fun u hu => aux_thm_prop_energy_measure_support Gamma
    (centeredCube z r hr).isOpen.measurableSet hC hu⟩





end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Coefficient comparison is needed only on the support of the gradient. -/
theorem aux_thm_prop_responseForm_le_local
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a b : PositiveCoefficient Q) (K : ℝ) (q : Set (SpatialCoordinates d))
    (u : S.space)
    (hcoeff : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ q → b.val x ≤ K * a.val x)
    (hgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ q → u.val.2 i x = 0) :
    responseForm S b u u ≤ K * responseForm S a u u := by
  rw [aux_prop_locality_recovery_responseForm_eq_sum,
    aux_prop_locality_recovery_responseForm_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [weightedL2Form_apply, weightedL2Form_apply, ← integral_const_mul]
  apply integral_mono_ae (integrable_weighted_inner b.val _ _)
    ((integrable_weighted_inner a.val _ _).const_mul K)
  filter_upwards [hcoeff, hgrad i] with x hx hg
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hxq : x ∈ q
  · simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hx hxq) (mul_self_nonneg (u.val.2 i x))
  · rw [hg hxq]
    simp only [mul_zero, le_refl]

theorem aux_thm_prop_modV_recovery {d : ℕ} (hd : 2 ≤ d) (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n) (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (cut : ℕ → S.space) (B : ℝ) (hB : 0 ≤ B)
    (hcutE : ∀ n, responseForm S (a n) (cut n) (cut n) ≤ B)
    (hgrowth : ∀ n, ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((cut n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))
    (w : DomainL2 (centeredCube z r hr)) (hw : limitFormEnergy G w < ⊤)
    (Φ : ℕ → S.space) (hΦ1 : Tendsto (fun n => (Φ n).val.1) atTop (𝓝 w))
    (hΦE : Tendsto (fun n => responseForm S (a n) (Φ n) (Φ n)) atTop
      (𝓝 (limitFormEnergy G w).toReal))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (phi : ℕ → TestFunction (centeredCube z r hr) ℝ ⊤)
    (hPhi : ∀ n, (Φ n).val = smoothSobolevData (phi n))
    (hinner : ∀ n,
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        0 ≤ (cut n).val.1 x ∧ (cut n).val.1 x ≤ 1) ∧
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        w x ≠ 0 → (cut n).val.1 x = 1) ∧
      (∀ i, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (cut n).val.2 i x ≠ 0 → w x = 0)) :
    Tendsto (fun n =>
      ((aux_prop_locality_recovery_modV S hS (phi n) (cut n)).val.1,
       (responseForm S (a n)
         (aux_prop_locality_recovery_modV S hS (phi n) (cut n))
         (aux_prop_locality_recovery_modV S hS (phi n) (cut n)) : EReal)))
      atTop (𝓝 (w, limitFormEnergy G w)) := by
  have hp := fun n => aux_prop_locality_recovery_modV_props S hS
    (phi n) (Φ n) (hPhi n) (cut n) w
    (hinner n).1 (hinner n).2.1 (hinner n).2.2
  exact aux_prop_locality_recovery_side hd hInterp z r hr t ht S a G
    hLower KN hKN Kstar hKstar hfrac hcoercive cut B hB hcutE hgrowth
    w hw Φ hΦ1 hΦE (fun n => aux_prop_locality_recovery_modV S hS (phi n) (cut n))
    (fun n i => aux_prop_locality_recovery_mulL
      (aux_prop_locality_recovery_testPartialLinf (phi n) i) (cut n).val.1)
    (fun n i => aux_prop_locality_recovery_mulL
      (aux_prop_locality_recovery_testLinf (phi n)) ((cut n).val.2 i))
    (fun n i => aux_prop_locality_recovery_modV_grad S hS (phi n) (cut n) i)
    (fun n => (hp n).1) (fun n => (hp n).2.1) (fun n => (hp n).2.2)

theorem aux_thm_prop_modV_grad_zero
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (phi : TestFunction Q ℝ ⊤) (chi : S.space) (chic : SpatialCoordinates d → ℝ)
    (hchi : (chi.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic)
    (O q : Set (SpatialCoordinates d)) (hOq : closure O ⊆ q)
    (hzero : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic x = 0) :
    ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ q → (aux_prop_locality_recovery_modV S hS phi chi).val.2 i x = 0 := by
  let Y := aux_prop_locality_recovery_modV S hS phi chi
  have hz : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ (closure O)ᶜ → Y.val.1 x = 0 := by
    filter_upwards [aux_prop_locality_recovery_modV_fst_ae S hS phi chi,
      hchi, ae_restrict_mem Q.isOpen.measurableSet] with x hx hcx hxQ hxO
    change (aux_prop_locality_recovery_modV S hS phi chi).val.1 x = 0
    rw [hx, hcx, hzero x hxQ (fun h => hxO (subset_closure h)), mul_zero]
  intro i
  have hg := aux_prop_locality_recovery_grad_ae_zero_of_const Y.val
    (S.le_weak Y.2) (closure O)ᶜ isClosed_closure.isOpen_compl 0 hz i
  filter_upwards [hg] with x hx hxq
  exact hx (fun hxO => hxq (hOq hxO))

/-- A core function supported in an open subregion admits a recovery sequence
whose gradients vanish outside that subregion. The cutoff error tends to zero
by the represented trace bounds. -/
theorem aux_thm_prop_localized_recovery_base
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    let Q := centeredCube z r hr
    let H := DomainL2 Q
    ∀ (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : ℕ → PositiveCoefficient Q)
    (G : H →L[ℝ] H)
    (hLower : ∀ (wN : ℕ → S.space) (w : H),
      (∀ f : H, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (hRecovery : ∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
      Tendsto (fun n => ((wN n).val.1,
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
        (𝓝 (w, limitFormEnergy G w)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (Q : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (u : DomainL2 (centeredCube z r hr)) (hu : u ∈ limitFormDomain G)
    (uc : SpatialCoordinates d → ℝ) (huc : Continuous uc)
    (hucs : HasCompactSupport uc) (hucq : tsupport uc ⊆ q)
    (huae : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc),
    ∃ Y : ℕ → S.space,
      Tendsto (fun n => ((Y n).val.1,
        (responseForm S (a n)
          (Y n) (Y n) : EReal))) atTop (𝓝 (u, limitFormEnergy G u)) ∧
      ∀ n (i : Fin d), ∀ᵐ x ∂volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d)),
        x ∉ q → (Y n).val.2 i x = 0 := by
  intro Q H S hS a G hLower hRecovery KN hKN Kstar hKstar hfrac hcoercive
    hInterp t ht _htd hcutoffs q hq hqQ u hu uc huc hucs hucq huae
  have hb1 := exists_open_between_and_isCompact_closure hucs.isCompact hq hucq
  obtain ⟨O, hO, hKO, hOq, _hOc⟩ := hb1
  have hb2 := hcutoffs (tsupport uc) O hucs.isCompact hO hKO (hOq.trans hqQ)
  obtain ⟨V, chi, chic, B, hV, hKV, _hVO, hB, hchi⟩ := hb2
  have hb3 := hRecovery u hu
  obtain ⟨vN, hvN⟩ := hb3
  have hb4 := aux_prop_locality_recovery_recovery_parts
    (fun n => (vN n).val.1) (fun n => responseForm S (a n) (vN n) (vN n))
    u (limitFormEnergy G u) (limitFormEnergy_nonneg G u) hu hvN
  obtain ⟨hvN1, hvNE⟩ := hb4
  have hb5 := aux_prop_locality_recovery_smooth_seq S hS a vN u _ hvN1 hvNE
  obtain ⟨phi, Phi, hPhi, hPhi1, hPhiE⟩ := hb5
  let Y := fun n => aux_prop_locality_recovery_modV S hS (phi n) (chi n)
  have hin := fun n => aux_prop_locality_recovery_inner_ae
    (chi n).val (S.le_weak (chi n).2) (chic n)
    (hchi n).2.1 (hchi n).2.2.1 V hV (hchi n).2.2.2.1
    u uc huae hKV
  have hrec := aux_thm_prop_modV_recovery hd hInterp z r hr t ht S a G
    hLower KN hKN Kstar hKstar hfrac hcoercive chi B hB
    (fun n => (hchi n).2.2.2.2.2.1) (fun n => (hchi n).2.2.2.2.2.2)
    u hu Phi hPhi1 hPhiE hS phi hPhi hin
  refine ⟨Y, hrec, ?_⟩
  intro n
  exact aux_thm_prop_modV_grad_zero S hS (phi n) (chi n) (chic n)
    (hchi n).2.1 O q hOq (hchi n).2.2.2.2.1


/-- Eventual coefficient order, along an actual recovery sequence, passes to
the finite limit energy. -/
theorem aux_thm_prop_energy_order_of_recovery
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a b : ℕ → PositiveCoefficient Q)
    (GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hlower : ∀ (vN : ℕ → S.space) (v : DomainL2 Q),
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      limitFormEnergy GF v ≤
        liminf (fun n => (responseForm S (b n) (vN n) (vN n) : EReal)) atTop)
    (u : DomainL2 Q) (Eu K : ℝ) (Y : ℕ → S.space)
    (hY : Tendsto (fun n => ((Y n).val.1,
      (responseForm S (a n) (Y n) (Y n) : EReal))) atTop (𝓝 (u, (Eu : EReal))))
    (horder : ∀ᶠ n in atTop,
      responseForm S (b n) (Y n) (Y n) ≤ K * responseForm S (a n) (Y n) (Y n)) :
    limitFormEnergy GF u ≤ ((K * Eu : ℝ) : EReal) := by
  have he : Tendsto (fun n => responseForm S (a n) (Y n) (Y n)) atTop (𝓝 Eu) :=
    EReal.tendsto_coe.mp hY.snd_nhds
  have hbound : Tendsto (fun n => ((K * responseForm S (a n) (Y n) (Y n) : ℝ) : EReal))
      atTop (𝓝 ((K * Eu : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr (tendsto_const_nhds.mul he)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun n => (responseForm S (b n) (Y n) (Y n) : EReal)) := by
    change ∃ bound : EReal, ∀ᶠ n : ℕ in atTop,
      (responseForm S (b n) (Y n) (Y n) : EReal) ≥ bound
    refine ⟨0, Eventually.of_forall ?_⟩
    intro n
    exact EReal.coe_nonneg.mpr (responseForm_nonneg S (b n) (Y n))
  have hlim := Filter.liminf_le_liminf
    (horder.mono (fun n hn => EReal.coe_le_coe_iff.mpr hn)) hbdd hbound.isCoboundedUnder_ge
  rw [hbound.liminf_eq] at hlim
  exact (hlower Y u (fun f => tendsto_const_nhds.inner hY.fst_nhds)).trans hlim

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- The actual form and energy measure attached to one represented operator limit. -/
structure aux_thm_prop_limit_side
    (d : ℕ) (hd : 2 ≤ d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (N : ℕ → ℕ) where
  response : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)
  response_eq : ∀ n f, response n f =
    (responseSolution S (Lane4.cutoffPositiveCoefficient model H om (N n) z hr)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1
  response_tendsto : Tendsto response atTop (𝓝 G)
  bounds : aux_in_represented_bounds_side d hd model H om z r hr S G N
  form : _root_.DirichletForm
    (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
  energy_eq : ∀ u, form.toClosedForm.energy u = limitFormEnergy G u
  core : ∃ C, DirichletForm.IsCoreOn form.toClosedForm
    (centeredCube z r hr : Set (SpatialCoordinates d)) C
  gamma : DirichletForm.EnergyMeasure form.toClosedForm



theorem aux_thm_prop_domain_mem_of_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hE : ∀ u, E.energy u = limitFormEnergy G u)
    {u : DomainL2 Q} (hu : u ∈ limitFormDomain G) : u ∈ E.domain := by
  apply E.mem_domain_of_energy_lt_top
  rw [hE]
  exact hu



theorem aux_thm_prop_core_dense_of_isCoreOn
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E (Q : Set (SpatialCoordinates d)) C) :
    ∀ u ∈ limitFormDomain G, ∀ eps : ℝ, 0 < eps →
      ∃ p : DomainL2 Q, MemFormCore G p ∧ ‖p - u‖ ≤ eps ∧
        limitFormEnergy G (p - u) ≤ ((eps : ℝ) : EReal) := by
  obtain ⟨C, hC⟩ := hcore
  intro u hu eps heps
  have huE : u ∈ E.domain := E.mem_domain_of_energy_lt_top (by rw [hE]; exact hu)
  obtain ⟨p, hpC, hsmall⟩ := hC.denseEnergy u huE (min (eps ^ 2) eps)
    (lt_min (sq_pos_of_pos heps) heps)
  have hp := hC.memCoreOn p hpC
  have hpu := E.domain.sub_mem hp.mem_domain huE
  rw [E.energyNormSq_sub_comm huE hp.mem_domain] at hsmall
  have hnormsq := (E.sq_norm_le_energyNormSq hpu).trans
    (hsmall.le.trans (min_le_left _ _))
  have hform := E.form_le_energyNormSq.trans (hsmall.le.trans (min_le_right _ _))
  refine ⟨p, ⟨?_, hp.2⟩, ?_, ?_⟩
  · show limitFormEnergy G p < ⊤
    rw [← hE]
    exact (E.energy_lt_top_iff p).mpr hp.mem_domain
  · nlinarith [norm_nonneg (p - u)]
  · rw [← hE, E.energy_of_mem hpu]
    exact EReal.coe_le_coe_iff.mpr hform




theorem aux_thm_prop_local_measure_bounds
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEreg : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hFreg : ∃ C, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q) (hqQ : q ⊆ Q)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hup : ∀ v, E.toClosedForm.MemCoreOn q v → F.form v v ≤ hi * E.form v v)
    (hlow : ∀ v, F.toClosedForm.MemCoreOn q v → E.form v v ≤ lo⁻¹ * F.form v v)
    (u : DomainL2 Q) (hu : E.toClosedForm.MemCore u)
    (B : Set (SpatialCoordinates d)) (hBq : B ⊆ q) :
    lo * (GammaE.measure u B).toReal ≤ (GammaF.measure u B).toReal ∧
      (GammaF.measure u B).toReal ≤ hi * (GammaE.measure u B).toReal := by
  have huF : F.toClosedForm.MemCore u := ⟨hdom ▸ hu.mem_domain, hu.2⟩
  have hupper := aux_lem_sincos_of_mul_comp E F hEreg hdom GammaE GammaF q hq hqQ
    (DirichletForm.mul_comp_mem E q) hi.toNNReal
    (by simpa only [Real.coe_toNNReal hi hhi] using hup) u hu B hBq
  have hlower := aux_lem_sincos_of_mul_comp F E hFreg hdom.symm GammaF GammaE q hq hqQ
    (DirichletForm.mul_comp_mem F q) (lo⁻¹).toNNReal
    (by simpa only [Real.coe_toNNReal _ (inv_nonneg.mpr hlo.le)] using hlow) u huF B hBq
  have hiReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (GammaE.measure_ne_top hu.mem_domain B)) hupper
  have loReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (GammaF.measure_ne_top huF.mem_domain B)) hlower
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal hi hhi] at hiReal
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
    Real.coe_toNNReal _ (inv_nonneg.mpr hlo.le)] at loReal
  exact ⟨(le_inv_mul_iff₀ hlo).mp loReal, hiReal⟩

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper


theorem aux_thm_prop_coefficient_weight_upper
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (a b : PositiveCoefficient Q)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x)
    (q : Set (SpatialCoordinates d)) (K : ℝ) (hK : ∀ x ∈ q, rho x ≤ K) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ q → b.val x ≤ K * a.val x := by
  filter_upwards [hweight, aux_prop_locality_recovery_coeff_nonneg a] with x hx hax hxq
  rw [hx]
  exact mul_le_mul_of_nonneg_right (hK x hxq) hax

theorem aux_thm_prop_coefficient_weight_lower
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (a b : PositiveCoefficient Q)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x)
    (q : Set (SpatialCoordinates d)) (K : ℝ) (hK : 0 < K)
    (hlow : ∀ x ∈ q, K ≤ rho x) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ q → a.val x ≤ K⁻¹ * b.val x := by
  filter_upwards [hweight, aux_prop_locality_recovery_coeff_nonneg a] with x hx hax hxq
  apply (le_inv_mul_iff₀ hK).mpr
  rw [hx]
  exact mul_le_mul_of_nonneg_right (hlow x hxq) hax

section Weight

variable {d : ℕ} {hd : 2 ≤ d} {model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
  {H : BilateralField d → C(SpatialCoordinates d, ℝ)} {om om' : BilateralField d}
  {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
  {S : ResponseSpace (centeredCube z r hr)}
  {G G' : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
  {N : ℕ → ℕ}





end Weight
end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper



section Order

variable {d : ℕ} (Q : Opens (SpatialCoordinates d))
  (E F Ew Fw : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
  (hdom : E.domain = F.domain)
  (hEwdom : Ew.domain = E.domain) (hFwdom : Fw.domain = F.domain)
  (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
  (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
  (rho : SpatialCoordinates d → ℝ)
  (hEw : ∀ u ∈ E.domain, Ew.form u u = ∫ x, rho x ∂(GammaE.measure u))
  (hFw : ∀ u ∈ F.domain, Fw.form u u = ∫ x, rho x ∂(GammaF.measure u))

include hdom hEwdom hFwdom GammaE GammaF hEw hFw



end Order






end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

theorem aux_thm_prop_side_supply
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (hSspace0 : Sspace0.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (hcontract0 : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : Sspace0.space,
        ∃ v : Sspace0.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) v v ≤
            responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) u u)
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N0 : ℕ → ℕ)
    (GN0 : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGN0 : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), GN0 n f =
      (responseSolution Sspace0
          (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0)
          ((sobolevVolumeLoad f).comp Sspace0.space.subtypeL)).val.1)
    (hGN0tendsto : Tendsto GN0 atTop (𝓝 G0))
    (hbundle0 : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 Sspace0 G0 N0)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasEnergyMeasure F) :
    Nonempty (aux_thm_prop_limit_side d hd model H om z0 r0 hr0 Sspace0 G0 N0) := by
  obtain ⟨F, _hFdom, hF, hcore⟩ := aux_thm_prop_hregularity_side hd model H om z0 r0 hr0
    Sspace0 hSspace0 hcontract0 G0 N0 GN0 hGN0 hGN0tendsto hbundle0
  have hlocal := aux_thm_prop_form_core_locality d hd model H om z0 r0 hr0
    Sspace0 hSspace0 G0 N0 GN0 hGN0 hGN0tendsto hbundle0 F.toClosedForm hF
  have hstrong := (BD z0 r0 hr0 F).isStronglyLocal_of_onCore
    (aux_thm_prop_isRegular_of_core (centeredCube z0 r0 hr0) F.toClosedForm hcore)
    (BDQ z0 r0 hr0 F hcore hlocal)
  obtain ⟨Gamma, _hSupport⟩ := aux_thm_prop_energy_measure_of_locality z0 r0 hr0 F
    (EM z0 r0 hr0 F) hcore hstrong
  exact ⟨⟨GN0, hGN0, hGN0tendsto, hbundle0, F, hF, hcore, Gamma⟩⟩

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper


end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper


end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper
noncomputable section

/-- Coercivity makes the harmonic projection unique. -/
theorem aux_thm_prop_projection_unique
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (D : Submodule ℝ (DomainL2 Q)) (hD : D ≤ E.domain)
    (hcoercive : ∃ K : ℝ, 0 < K ∧ ∀ v ∈ D, ‖v‖ ^ 2 ≤ K * E.form v v)
    (u p p' : DomainL2 Q) (hu : u ∈ E.domain) (hp : p ∈ D) (hp' : p' ∈ D)
    (ho : ∀ v ∈ D, E.form (u - p) v = 0)
    (ho' : ∀ v ∈ D, E.form (u - p') v = 0) : p = p' := by
  have hw : p - p' ∈ D := D.sub_mem hp hp'
  have h0 : E.form (p - p') (p - p') = 0 := by
    have h1 := ho (p - p') hw
    have h2 := ho' (p - p') hw
    rw [E.form_sub_left hu (hD hp) (hD hw)] at h1
    rw [E.form_sub_left hu (hD hp') (hD hw)] at h2
    rw [E.form_sub_left (hD hp) (hD hp') (hD hw)]
    linarith
  obtain ⟨K, _hK, hbound⟩ := hcoercive
  have hn := hbound (p - p') hw
  rw [h0, mul_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (p - p')]))

/-- The killed projection is linear on the actual form domain. -/
theorem aux_thm_prop_projection_linear
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (U : Set (SpatialCoordinates d)) (D : Submodule ℝ (DomainL2 Q))
    (hD : DirichletForm.IsKilledDomain E U D)
    (hcoercive : ∃ K : ℝ, 0 < K ∧ ∀ v ∈ D, ‖v‖ ^ 2 ≤ K * E.form v v) :
    ∃ P : E.domain →ₗ[ℝ] E.domain,
      (∀ u, (P u).val ∈ D) ∧
      ∀ u (v : DomainL2 Q), v ∈ D → E.form (u.val - (P u).val) v = 0 := by
  classical
  choose p hp ho using fun u : E.domain =>
    aux_lem_replace_projection_exists E hD hcoercive u.val u.property
  let P : E.domain →ₗ[ℝ] E.domain := {
    toFun := fun u => ⟨p u, hD.le_domain (hp u)⟩
    map_add' := by
      intro u v
      apply Subtype.ext
      change p (u + v) = p u + p v
      apply aux_thm_prop_projection_unique E D hD.le_domain hcoercive
        (u.val + v.val) _ _ (E.domain.add_mem u.property v.property)
        (hp (u + v)) (D.add_mem (hp u) (hp v)) (ho (u + v))
      intro w hw
      rw [show u.val + v.val - (p u + p v) = (u.val - p u) + (v.val - p v) by abel]
      rw [E.form_add_left _ (E.domain.sub_mem u.property (hD.le_domain (hp u)))
        _ (E.domain.sub_mem v.property (hD.le_domain (hp v))) _ (hD.le_domain hw),
        ho u w hw, ho v w hw, add_zero]
    map_smul' := by
      intro c u
      apply Subtype.ext
      change p (c • u) = c • p u
      apply aux_thm_prop_projection_unique E D hD.le_domain hcoercive
        (c • u.val) _ _ (E.domain.smul_mem c u.property)
        (hp (c • u)) (D.smul_mem c (hp u)) (ho (c • u))
      intro v hv
      rw [← smul_sub, E.form_smul_left c _
        (E.domain.sub_mem u.property (hD.le_domain (hp u))) _ (hD.le_domain hv),
        ho u v hv, mul_zero] }
  exact ⟨P, hp, ho⟩

/-- The cross energy is linear in its second domain argument. -/
def aux_thm_prop_measure_linear
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) (U : Set (SpatialCoordinates d))
    (u : E.domain) : E.domain →ₗ[ℝ] ℝ where
  toFun v := Gamma.cross u.val v.val U
  map_add' v w := by
    change Gamma.cross u.val (v.val + w.val) U = _
    rw [Gamma.cross_add_right u.val u.property v.val v.property w.val w.property,
      VectorMeasure.add_apply]
  map_smul' c v := by
    change Gamma.cross u.val (c • v.val) U = _
    rw [Gamma.cross_smul_right c u.val u.property v.val v.property,
      VectorMeasure.smul_apply]
    rfl

/-- Restricting the cross energy measure to a set gives a bilinear form. -/
def aux_thm_prop_measure_bilin
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) (U : Set (SpatialCoordinates d)) :
    E.domain →ₗ[ℝ] E.domain →ₗ[ℝ] ℝ where
  toFun := aux_thm_prop_measure_linear E Gamma U
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change Gamma.cross (u.val + v.val) w.val U = _
    rw [Gamma.cross_add_left u.property v.property w.property, VectorMeasure.add_apply]
    rfl
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    change Gamma.cross (c • u.val) v.val U = _
    rw [Gamma.cross_smul_left c u.property v.property, VectorMeasure.smul_apply]
    rfl

/-- The local energy of the harmonic representative is a genuine quadratic form. -/
def aux_thm_prop_trace_quadratic
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) (U : Set (SpatialCoordinates d))
    (P : E.domain →ₗ[ℝ] E.domain) : QuadraticForm ℝ E.domain :=
  (LinearMap.BilinMap.toQuadraticMap
    (aux_thm_prop_measure_bilin E Gamma U)).comp (LinearMap.id - P)

theorem aux_thm_prop_trace_quadratic_apply
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) (U : Set (SpatialCoordinates d))
    (hU : MeasurableSet U) (P : E.domain →ₗ[ℝ] E.domain) (u : E.domain) :
    aux_thm_prop_trace_quadratic E Gamma U P u =
      (Gamma.measure (u.val - (P u).val) U).toReal := by
  change Gamma.cross (u.val - (P u).val) (u.val - (P u).val) U = _
  exact Gamma.cross_self _ (E.domain.sub_mem u.property (P u).property) U hU

theorem aux_thm_prop_trace_isLeast
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (D : Submodule ℝ (DomainL2 Q)) (hD : DirichletForm.IsKilledDomain E U D)
    (P : E.domain →ₗ[ℝ] E.domain)
    (hP : ∀ u, (P u).val ∈ D)
    (ho : ∀ u (v : DomainL2 Q), v ∈ D → E.form (u.val - (P u).val) v = 0)
    (u : E.domain) :
    IsLeast {t : ℝ | ∃ v : DomainL2 Q, v ∈ D ∧
      t = (Gamma.measure (u.val + v) U).toReal}
      (aux_thm_prop_trace_quadratic E Gamma U P u) := by
  rw [aux_thm_prop_trace_quadratic_apply E Gamma U hU.measurableSet P u]
  constructor
  · exact ⟨-(P u).val, D.neg_mem (hP u), by simp only [sub_eq_add_neg]⟩
  · rintro t ⟨v, hv, rfl⟩
    have hpv : (P u).val + v ∈ D := D.add_mem (hP u) hv
    have hs := aux_lem_replace_cell_energy_split E Gamma hU hD
      (E.domain.sub_mem u.property (P u).property) hpv (ho u _ hpv)
    rw [show (u.val - (P u).val) + ((P u).val + v) = u.val + v by abel] at hs
    rw [hs]
    exact le_add_of_nonneg_right (E.form_nonneg _ (hD.le_domain hpv))

theorem aux_thm_prop_trace_eq_sInf
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (D : Submodule ℝ (DomainL2 Q)) (hD : DirichletForm.IsKilledDomain E U D)
    (P : E.domain →ₗ[ℝ] E.domain)
    (hP : ∀ u, (P u).val ∈ D)
    (ho : ∀ u (v : DomainL2 Q), v ∈ D → E.form (u.val - (P u).val) v = 0)
    (u : E.domain) :
    aux_thm_prop_trace_quadratic E Gamma U P u =
      sInf {t : ℝ | ∃ v : DomainL2 Q, v ∈ D ∧
        t = (Gamma.measure (u.val + v) U).toReal} := by
  exact (aux_thm_prop_trace_isLeast E Gamma U hU D hD P hP ho u).csInf_eq.symm

/-- The local trace infimum is represented by a nonnegative quadratic form on
all ambient domain functions. -/
theorem aux_thm_prop_trace_quadratic_exists
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (D : Submodule ℝ (DomainL2 Q)) (hD : DirichletForm.IsKilledDomain E U D)
    (hcoercive : ∃ K : ℝ, 0 < K ∧ ∀ v ∈ D, ‖v‖ ^ 2 ≤ K * E.form v v) :
    ∃ T : QuadraticForm ℝ E.domain, (∀ u, 0 ≤ T u) ∧ ∀ u : E.domain,
      IsLeast {t : ℝ | ∃ v : DomainL2 Q, v ∈ D ∧
        t = (Gamma.measure (u.val + v) U).toReal} (T u) := by
  obtain ⟨P, hP, ho⟩ := aux_thm_prop_projection_linear E U D hD hcoercive
  refine ⟨aux_thm_prop_trace_quadratic E Gamma U P, ?_, ?_⟩
  · intro u
    rw [aux_thm_prop_trace_quadratic_apply E Gamma U hU.measurableSet P u]
    exact ENNReal.toReal_nonneg
  · exact aux_thm_prop_trace_isLeast E Gamma U hU D hD P hP ho

/-- Measure order transfers to the two actual trace minima in the same killed
variation space. -/
theorem aux_thm_prop_trace_order
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E) (GammaF : DirichletForm.EnergyMeasure F)
    (U : Set (SpatialCoordinates d))
    (D : Submodule ℝ (DomainL2 Q)) (hD : D ≤ E.domain)
    (QE QF : QuadraticForm ℝ E.domain)
    (hQE : ∀ u : E.domain, IsLeast {t : ℝ | ∃ v : DomainL2 Q, v ∈ D ∧
      t = (GammaE.measure (u.val + v) U).toReal} (QE u))
    (hQF : ∀ u : E.domain, IsLeast {t : ℝ | ∃ v : DomainL2 Q, v ∈ D ∧
      t = (GammaF.measure (u.val + v) U).toReal} (QF u))
    (m M : ℝ) (hm : 0 ≤ m) (hM : 0 ≤ M)
    (horder : ∀ u ∈ E.domain,
      m * (GammaE.measure u U).toReal ≤ (GammaF.measure u U).toReal ∧
        (GammaF.measure u U).toReal ≤ M * (GammaE.measure u U).toReal) :
    ∀ u, m * QE u ≤ QF u ∧ QF u ≤ M * QE u := by
  intro u
  obtain ⟨vE, hvE, hvalE⟩ := (hQE u).1
  obtain ⟨vF, hvF, hvalF⟩ := (hQF u).1
  constructor
  · have hmin := (hQE u).2 ⟨vF, hvF, rfl⟩
    have hmul := mul_le_mul_of_nonneg_left hmin hm
    rw [hvalF]
    exact hmul.trans (horder (u.val + vF) (E.domain.add_mem u.property (hD hvF))).1
  · have hmin := (hQF u).2 ⟨vE, hvE, rfl⟩
    rw [hvalE]
    exact hmin.trans (horder (u.val + vE) (E.domain.add_mem u.property (hD hvE))).2

/-- The quadratic saving lemma applies to the genuine difference of trace
quadratic forms. -/
theorem aux_thm_prop_trace_saving
    {V : Type} [AddCommGroup V] [Module ℝ V]
    (QE QF : QuadraticForm ℝ V) (hQE : ∀ u, 0 ≤ QE u)
    (m M : ℝ) (hmM : m ≤ M)
    (horder : ∀ u, m * QE u ≤ QF u ∧ QF u ≤ M * QE u)
    (u ell : V) (lam : ℝ)
    (haffineSaving : (3 / 8 : ℝ) * (M - m) * QE ell ≤ M * QE ell - QF ell)
    (haffineApprox : QE (u - ell) ≤ (3 / 8 : ℝ) * (1 / 8) / 16 * lam) :
    (M - m) * ((3 / 8 : ℝ) / 2 * QE u -
      4 * ((3 / 8 : ℝ) * (1 / 8) / 16) * lam) ≤ M * QE u - QF u := by
  let B : QuadraticForm ℝ V := M • QE - QF
  have hB (v : V) : B v = M * QE v - QF v := rfl
  apply aux_thm_prop_dich_pointwise QE B hQE
    (fun v => by rw [hB]; exact sub_nonneg.mpr (horder v).2)
    (M - m) (sub_nonneg.mpr hmM)
    (fun v => by rw [hB]; nlinarith [(horder v).1]) u ell lam
    haffineSaving haffineApprox


end
end Paper



end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Decompose the total mass into disjoint measurable cells and their exact
complement. No openness of the complement is required. -/
theorem aux_thm_prop_measure_partition
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (Q : Set X) (hQ : MeasurableSet Q) (hsupport : mu Qᶜ = 0)
    {n : ℕ} (cell : Fin n → Set X)
    (hcell : ∀ i, MeasurableSet (cell i)) (hsub : ∀ i, cell i ⊆ Q)
    (hdisj : Pairwise (fun i j => Disjoint (cell i) (cell j))) :
    (mu univ).toReal = (mu (Q \ ⋃ i, cell i)).toReal + ∑ i, (mu (cell i)).toReal := by
  have hUnion : MeasurableSet (⋃ i, cell i) := MeasurableSet.iUnion hcell
  have hUnionSub : (⋃ i, cell i) ⊆ Q := iUnion_subset hsub
  have hsum : mu (⋃ i, cell i) = ∑ i, mu (cell i) := by
    rw [measure_iUnion (fun i j hij => hdisj hij) hcell, tsum_fintype]
  have hwhole : mu Q = mu univ := by
    simpa only [hsupport, add_zero] using measure_add_measure_compl (μ := mu) hQ
  have h := measure_diff_add_inter (μ := mu) Q hUnion
  rw [inter_eq_right.mpr hUnionSub, hwhole, hsum] at h
  have hsumfin : (∑ i : Fin n, mu (cell i)) ≠ ⊤ := by
    exact (ENNReal.sum_lt_top.mpr (fun i _ => measure_lt_top mu _)).ne
  have hreal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (measure_ne_top mu _) hsumfin,
    ENNReal.toReal_sum (fun i _ => measure_ne_top mu _)] at hreal
  exact hreal.symm

/-- The replacement energy estimate uses the projection's exact energy drop
and measure order on the measurable complement of the cells. -/
theorem aux_thm_prop_replacement_energy_upper
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (M : ℝ) (hM : 0 < M)
    (horder : ∀ u ∈ E.domain, F.form u u ≤ M * E.form u u)
    (u v : DomainL2 Q) (hu : u ∈ E.domain) (hv : v ∈ F.domain)
    (hsupportE : GammaE.measure u (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (hsupportF : GammaF.measure u (Q : Set (SpatialCoordinates d))ᶜ = 0)
    {n : ℕ} (cell : Fin n → Set (SpatialCoordinates d))
    (hcell : ∀ i, MeasurableSet (cell i))
    (hsub : ∀ i, cell i ⊆ (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise (fun i j => Disjoint (cell i) (cell j)))
    (TE TF : Fin n → ℝ)
    (hTE : ∀ i, TE i ≤ (GammaE.measure u (cell i)).toReal)
    (hpyth : F.form u u = F.form v v + F.form (u - v) (u - v))
    (hgap : ∑ i, ((GammaF.measure u (cell i)).toReal - TF i) =
      F.form (u - v) (u - v)) :
    F.form v v ≤ M * E.form u u - ∑ i, (M * TE i - TF i) := by
  have huF : u ∈ F.domain := hdom ▸ hu
  haveI : IsFiniteMeasure (GammaE.measure u) := ⟨GammaE.measure_univ_lt_top u hu⟩
  haveI : IsFiniteMeasure (GammaF.measure u) := ⟨GammaF.measure_univ_lt_top u huF⟩
  let off := (Q : Set (SpatialCoordinates d)) \ ⋃ i, cell i
  have hoff : MeasurableSet off := Q.isOpen.measurableSet.diff (MeasurableSet.iUnion hcell)
  have hEpart := aux_thm_prop_measure_partition (GammaE.measure u)
    (Q : Set (SpatialCoordinates d)) Q.isOpen.measurableSet hsupportE cell hcell hsub hdisj
  have hFpart := aux_thm_prop_measure_partition (GammaF.measure u)
    (Q : Set (SpatialCoordinates d)) Q.isOpen.measurableSet hsupportF cell hcell hsub hdisj
  rw [GammaE.measure_univ u hu] at hEpart
  rw [GammaF.measure_univ u huF] at hFpart
  have hreverse : ∀ w ∈ F.domain, M⁻¹ * F.form w w ≤ E.form w w := by
    intro w hw
    exact (inv_mul_le_iff₀ hM).mpr (horder w (hdom ▸ hw))
  have hmeasure := aux_thm_prop_endpoint_invariance_energy_order_one_sided_light
    Q F E hEcore hdom.symm GammaF GammaE M⁻¹ (inv_pos.mpr hM) hreverse u huF off hoff
  have hoffle : (GammaF.measure u off).toReal ≤ M * (GammaE.measure u off).toReal :=
    (inv_mul_le_iff₀ hM).mp hmeasure
  have hsum : ∑ i, TE i ≤ ∑ i, (GammaE.measure u (cell i)).toReal :=
    Finset.sum_le_sum (fun i _ => hTE i)
  have hmul := mul_le_mul_of_nonneg_left hsum hM.le
  rw [Finset.sum_sub_distrib] at hgap
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  change E.form u u = (GammaE.measure u off).toReal + _ at hEpart
  change F.form u u = (GammaF.measure u off).toReal + _ at hFpart
  nlinarith

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Pythagoras and the uniform small-cell coercivity bound imply that
harmonic replacements converge in the ambient L² space as the mesh vanishes. -/
theorem aux_thm_prop_replacement_tendsto
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (u : DomainL2 Q) (v : ℕ → DomainL2 Q) (hv : ∀ n, v n ∈ E.domain)
    (mesh : ℕ → ℝ) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hmesh0 : ∀ n, 0 ≤ mesh n) (K : ℝ) (hK : 0 ≤ K) (s : ℝ) (hs : 0 < s)
    (hpyth : ∀ n, E.form u u = E.form (v n) (v n) + E.form (u - v n) (u - v n))
    (hcoer : ∀ n, ‖u - v n‖ ^ 2 ≤ K * mesh n ^ (2 * s) *
      E.form (u - v n) (u - v n)) :
    Tendsto v atTop (𝓝 u) := by
  have ht : 0 < 2 * s := mul_pos two_pos hs
  have hp : Tendsto (fun n => mesh n ^ (2 * s)) atTop (𝓝 0) := by
    have h : Tendsto (fun n => mesh n ^ (2 * s)) atTop (𝓝 ((0 : ℝ) ^ (2 * s))) :=
      ((Real.continuous_rpow_const ht.le).tendsto 0).comp hmesh
    simpa only [Real.zero_rpow ht.ne'] using h
  have hb : Tendsto (fun n => K * mesh n ^ (2 * s) * E.form u u) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hp).mul_const (E.form u u)
  have hsq : Tendsto (fun n => ‖u - v n‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hb
    have hle : E.form (u - v n) (u - v n) ≤ E.form u u := by
      linarith [hpyth n, E.form_nonneg (v n) (hv n)]
    exact (hcoer n).trans (mul_le_mul_of_nonneg_left hle
      (mul_nonneg hK (Real.rpow_nonneg (hmesh0 n) _)))
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using hn

/-- The lower-semicontinuity estimate needed for the replacement term of
D.1.L follows from the checked small-cell coercivity estimate. -/
theorem aux_thm_prop_replacement_lsc_eventually
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hE : ∀ w, E.energy w = limitFormEnergy G w)
    (u : DomainL2 Q) (hu : u ∈ E.domain)
    (v : ℕ → DomainL2 Q) (hv : ∀ n, v n ∈ E.domain)
    (mesh : ℕ → ℝ) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hmesh0 : ∀ n, 0 ≤ mesh n) (K : ℝ) (hK : 0 ≤ K) (s : ℝ) (hs : 0 < s)
    (hpyth : ∀ n, E.form u u = E.form (v n) (v n) + E.form (u - v n) (u - v n))
    (hcoer : ∀ n, ‖u - v n‖ ^ 2 ≤ K * mesh n ^ (2 * s) *
      E.form (u - v n) (u - v n))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n in atTop, E.form u u ≤ E.form (v n) (v n) + eps := by
  have hconv := aux_thm_prop_replacement_tendsto E u v hv mesh hmesh hmesh0 K hK s hs
    hpyth hcoer
  have hdomain : ∀ w ∈ E.domain, w ∈ limitFormDomain G := by
    intro w hw
    change limitFormEnergy G w < ⊤
    rw [← hE]
    exact (E.energy_lt_top_iff w).mpr hw
  have heq : ∀ w ∈ E.domain, (limitFormEnergy G w).toReal = E.form w w := by
    intro w hw
    rw [← hE, E.energy_of_mem hw, EReal.toReal_coe]
  filter_upwards [aux_thm_prop_energy_lsc_eventually G u (hdomain u hu) v
    (fun n => hdomain (v n) (hv n)) hconv eps heps] with n hn
  simpa only [heq u hu, heq (v n) (hv n)] using hn

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

section Killed
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}

theorem aux_thm_prop_energyNormSq_add_le
    (E : DirichletForm.ClosedForm mu) {u v : Lp ℝ 2 mu}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.energyNormSq (u + v) ≤ 2 * E.energyNormSq u + 2 * E.energyNormSq v := by
  have hp := E.energyNormSq_add_smul_self 1 hu hv
  have hm := E.energyNormSq_add_smul_self (-1) hu hv
  have hn := E.energyNormSq_nonneg (E.domain.sub_mem hu hv)
  simp only [one_smul, mul_one, one_pow, one_mul] at hp
  simp only [neg_smul, one_smul, neg_one_sq, one_mul, ← sub_eq_add_neg] at hm
  linarith

theorem aux_thm_prop_energyNormSq_smul
    (E : DirichletForm.ClosedForm mu) (c : ℝ) {u : Lp ℝ 2 mu} (hu : u ∈ E.domain) :
    E.energyNormSq (c • u) = c ^ 2 * E.energyNormSq u := by
  unfold DirichletForm.ClosedForm.energyNormSq
  rw [E.form_smul_left c u hu (c • u) (E.domain.smul_mem c hu),
    E.form_smul_right c hu hu, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The actual energy closure of the core supported in U, inside E.domain. -/
def aux_thm_prop_killed_domain (E : DirichletForm.ClosedForm mu) (U : Set X) :
    Submodule ℝ (Lp ℝ 2 mu) where
  carrier := {u | u ∈ E.domain ∧ ∀ eps : ℝ, 0 < eps →
    ∃ w : Lp ℝ 2 mu, E.MemCoreOn U w ∧ E.energyNormSq (u - w) < eps}
  zero_mem' := by
    refine ⟨E.domain.zero_mem, fun eps heps => ⟨0, DirichletForm.ClosedForm.memCoreOn_zero E U, ?_⟩⟩
    simpa [DirichletForm.ClosedForm.energyNormSq, E.form_zero_left E.domain.zero_mem] using heps
  add_mem' := by
    rintro u v ⟨hu, hau⟩ ⟨hv, hav⟩
    refine ⟨E.domain.add_mem hu hv, fun eps heps => ?_⟩
    obtain ⟨w, hw, hwu⟩ := hau (eps / 4) (by positivity)
    obtain ⟨z, hz, hzv⟩ := hav (eps / 4) (by positivity)
    refine ⟨w + z, hw.add hz, ?_⟩
    have heq : u + v - (w + z) = (u - w) + (v - z) := by abel
    rw [heq]
    have hbound := aux_thm_prop_energyNormSq_add_le E
      (E.domain.sub_mem hu hw.1) (E.domain.sub_mem hv hz.1)
    linarith
  smul_mem' := by
    rintro c u ⟨hu, hau⟩
    refine ⟨E.domain.smul_mem c hu, fun eps heps => ?_⟩
    obtain ⟨w, hw, hwu⟩ := hau (eps / (c ^ 2 + 1)) (by positivity)
    refine ⟨c • w, hw.smul c, ?_⟩
    rw [← smul_sub, aux_thm_prop_energyNormSq_smul E c (E.domain.sub_mem hu hw.1)]
    have hh := (lt_div_iff₀ (by positivity : 0 < c ^ 2 + 1)).mp hwu
    have hn := E.energyNormSq_nonneg (E.domain.sub_mem hu hw.1)
    nlinarith

theorem aux_thm_prop_isKilledDomain
    (E : DirichletForm.ClosedForm mu) (U : Set X) :
    DirichletForm.IsKilledDomain E U (aux_thm_prop_killed_domain E U) := by
  refine ⟨fun _ hu => hu.1, ?_, fun _ hu => hu.2, ?_⟩
  · intro u hu
    refine ⟨hu.1, fun eps heps => ⟨u, hu, ?_⟩⟩
    simpa [DirichletForm.ClosedForm.energyNormSq, E.form_zero_left E.domain.zero_mem] using heps
  · intro u w hu hw hlim
    refine ⟨hw, fun eps heps => ?_⟩
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by positivity : 0 < eps / 4))).exists
    obtain ⟨z, hz, hzn⟩ := (hu n).2 (eps / 4) (by positivity)
    refine ⟨z, hz, ?_⟩
    have heq : w - z = (w - u n) + (u n - z) := by abel
    have hbound := aux_thm_prop_energyNormSq_add_le E
      (E.domain.sub_mem hw (hu n).1) (E.domain.sub_mem (hu n).1 hz.1)
    rw [← heq, E.energyNormSq_sub_comm hw (hu n).1] at hbound
    linarith

/-- Global form comparison controls the energy norm, including its L² term. -/
theorem aux_thm_prop_energyNormSq_compare
    (E F : DirichletForm.ClosedForm mu) (C : ℝ) (hC : 0 ≤ C)
    (hdom : E.domain = F.domain)
    (horder : ∀ u ∈ E.domain, F.form u u ≤ C * E.form u u)
    {u : Lp ℝ 2 mu} (hu : u ∈ E.domain) :
    F.energyNormSq u ≤ (C + 1) * E.energyNormSq u := by
  have ho := horder u hu
  have he := E.form_nonneg u hu
  have hn := sq_nonneg ‖u‖
  unfold DirichletForm.ClosedForm.energyNormSq
  nlinarith [mul_nonneg hC hn]

/-- Two globally comparable forms have the same killed variation space. -/
theorem aux_thm_prop_killed_domain_mono
    (E F : DirichletForm.ClosedForm mu) (C : ℝ) (hC : 0 ≤ C)
    (hdom : E.domain = F.domain)
    (horder : ∀ u ∈ E.domain, F.form u u ≤ C * E.form u u)
    (U : Set X) :
    aux_thm_prop_killed_domain E U ≤ aux_thm_prop_killed_domain F U := by
  intro u hu
  refine ⟨hdom ▸ hu.1, fun eps heps => ?_⟩
  obtain ⟨w, hw, hwu⟩ := hu.2 (eps / (C + 1)) (div_pos heps (by positivity))
  refine ⟨w, ⟨hdom ▸ hw.1, hw.2⟩, ?_⟩
  have hbound := aux_thm_prop_energyNormSq_compare E F C hC hdom horder
    (E.domain.sub_mem hu.1 hw.1)
  have hh := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hwu
  linarith

theorem aux_thm_prop_common_killed_domain
    (E F : DirichletForm.ClosedForm mu) (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hdom : E.domain = F.domain)
    (horder : ∀ u ∈ E.domain, m * E.form u u ≤ F.form u u ∧ F.form u u ≤ M * E.form u u)
    (U : Set X) :
    DirichletForm.IsKilledDomain E U (aux_thm_prop_killed_domain E U) ∧
      DirichletForm.IsKilledDomain F U (aux_thm_prop_killed_domain E U) := by
  have heq : aux_thm_prop_killed_domain E U = aux_thm_prop_killed_domain F U := by
    apply le_antisymm
    · exact aux_thm_prop_killed_domain_mono E F M hM hdom (fun u hu => (horder u hu).2) U
    · apply aux_thm_prop_killed_domain_mono F E m⁻¹ (inv_pos.mpr hm).le hdom.symm
      intro u hu
      apply (le_inv_mul_iff₀ hm).mpr
      exact (horder u (hdom.symm ▸ hu)).1
  refine ⟨aux_thm_prop_isKilledDomain E U, ?_⟩
  rw [heq]
  exact aux_thm_prop_isKilledDomain F U

end Killed
end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Comparable actual limit forms supply common killed domains, both trace
quadratic forms, and the same optimal comparison constants on every open cell. -/
theorem aux_thm_prop_trace_pair
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hdom : E.domain = F.domain)
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEdom : E.domain = limitFormDomain GE) (hFdom : F.domain = limitFormDomain GF)
    (hEenergy : ∀ u ∈ E.domain, E.form u u = (limitFormEnergy GE u).toReal)
    (hFenergy : ∀ u ∈ F.domain, F.form u u = (limitFormEnergy GF u).toReal)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (horder : ∀ u ∈ E.domain, m * E.form u u ≤ F.form u u ∧ F.form u u ≤ M * E.form u u)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) :
    ∃ (D : Submodule ℝ (DomainL2 Q)) (QE QF : QuadraticForm ℝ E.domain),
      DirichletForm.IsKilledDomain E.toClosedForm U D ∧
      DirichletForm.IsKilledDomain F.toClosedForm U D ∧
      (∀ u, 0 ≤ QE u) ∧ (∀ u, 0 ≤ QF u) ∧
      (∀ u : E.domain, IsLeast {t : ℝ | ∃ v : DomainL2 Q, v ∈ D ∧
        t = (GammaE.measure (u.val + v) U).toReal} (QE u)) ∧
      (∀ u : E.domain, IsLeast {t : ℝ | ∃ v : DomainL2 Q, v ∈ D ∧
        t = (GammaF.measure (u.val + v) U).toReal} (QF u)) ∧
      (∀ u, m * QE u ≤ QF u ∧ QF u ≤ M * QE u) := by
  let D := aux_thm_prop_killed_domain E.toClosedForm U
  obtain ⟨hDE, hDF⟩ := aux_thm_prop_common_killed_domain
    E.toClosedForm F.toClosedForm m M hm hM.le hdom horder U
  obtain ⟨KE, hKE, hcoerE⟩ := aux_lem_replace_limit_form_coercivity
    GE E.toClosedForm hEdom hEenergy
  obtain ⟨KF, hKF, hcoerF⟩ := aux_lem_replace_limit_form_coercivity
    GF F.toClosedForm hFdom hFenergy
  obtain ⟨QE, hQE0, hQE⟩ := aux_thm_prop_trace_quadratic_exists
    E.toClosedForm GammaE U hU D hDE ⟨KE, hKE, fun u hu => hcoerE u (hDE.le_domain hu)⟩
  obtain ⟨TF, hTF0, hTF⟩ := aux_thm_prop_trace_quadratic_exists
    F.toClosedForm GammaF U hU D hDF ⟨KF, hKF, fun u hu => hcoerF u (hDF.le_domain hu)⟩
  let incl : E.domain →ₗ[ℝ] F.domain := {
    toFun u := ⟨u.val, hdom ▸ u.property⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let QF : QuadraticForm ℝ E.domain := TF.comp incl
  have hQF : ∀ u : E.domain, IsLeast {t : ℝ | ∃ v : DomainL2 Q, v ∈ D ∧
        t = (GammaF.measure (u.val + v) U).toReal} (QF u) := fun u => hTF (incl u)
  refine ⟨D, QE, QF, hDE, hDF, hQE0, fun u => hTF0 (incl u), hQE, hQF, ?_⟩
  apply aux_thm_prop_trace_order E.toClosedForm F.toClosedForm GammaE GammaF U D
    hDE.le_domain QE QF hQE hQF m M hm.le hM.le
  intro u hu
  refine ⟨aux_thm_prop_endpoint_invariance_energy_order_one_sided_light Q E F hFcore hdom
    GammaE GammaF m hm (fun u hu => (horder u hu).1) u hu U hU.measurableSet, ?_⟩
  have hrev : ∀ w ∈ F.domain, M⁻¹ * F.form w w ≤ E.form w w := by
    intro w hw
    exact (inv_mul_le_iff₀ hM).mpr ((horder w (hdom.symm ▸ hw)).2)
  have hh := aux_thm_prop_endpoint_invariance_energy_order_one_sided_light Q F E hEcore
    hdom.symm GammaF GammaE M⁻¹ (inv_pos.mpr hM) hrev u (hdom ▸ hu) U hU.measurableSet
  exact (inv_mul_le_iff₀ hM).mp hh

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- The positive floor is Lebesgue mass and is kept separate from energy. -/
theorem aux_thm_prop_floor_measure_apply
    {X : Type*} [MeasurableSpace X] (mu nu : Measure X)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] (c : ℝ) (hc : 0 ≤ c) (A : Set X) :
    ((mu + ENNReal.ofReal c • nu) A).toReal = (mu A).toReal + c * (nu A).toReal := by
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_add (measure_ne_top mu A)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top nu A)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- Every actual fine-cell family with the affine trace saving and a positive
floor mass produces the seven local-saving estimates. The harmonic functions
need only the proved Pythagoras and small-cell coercivity bounds. -/
theorem aux_thm_prop_localSaving_of_cells
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (hQfin : volume (Q : Set (SpatialCoordinates d)) ≠ ⊤)
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hdom : E.domain = F.domain)
    (GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hF : ∀ w, F.energy w = limitFormEnergy GF w)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (M Delta : ℝ) (hM : 0 < M)
    (horder : ∀ w ∈ E.domain, F.form w w ≤ M * E.form w w)
    (u : DomainL2 Q) (hu : u ∈ E.domain)
    (hsupportE : GammaE.measure u (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (hsupportF : GammaF.measure u (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (c : ℝ) (hc : 0 < c)
    (count : ℕ → ℕ) (cell : (j : ℕ) → Fin (count j) → Set (SpatialCoordinates d))
    (hcell : ∀ j i, MeasurableSet (cell j i))
    (hsub : ∀ j i, cell j i ⊆ (Q : Set (SpatialCoordinates d)))
    (hdisj : ∀ j, Pairwise (fun i k => Disjoint (cell j i) (cell j k)))
    (TE TF : (j : ℕ) → Fin (count j) → ℝ)
    (hTE : ∀ j i, TE j i ≤ (GammaE.measure u (cell j i)).toReal)
    (hsaving : ∀ j i,
      Delta * ((3 / 8 : ℝ) / 2 * TE j i - 4 * ((3 / 8 : ℝ) * (1 / 8) / 16) *
        ((GammaE.measure u (cell j i)).toReal + c * (volume (cell j i)).toReal)) ≤
      M * TE j i - TF j i)
    (hgapE : Tendsto (fun j => ∑ i, ((GammaE.measure u (cell j i)).toReal - TE j i))
      atTop (𝓝 0))
    (hmass : ∀ j,
      ((GammaE.measure u + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d)))
        (Q : Set (SpatialCoordinates d))).toReal / 8 ≤
      ((GammaE.measure u + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d)))
        (⋃ i, cell j i)).toReal)
    (mesh : ℕ → ℝ) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hmesh0 : ∀ j, 0 ≤ mesh j) (K : ℝ) (hK : 0 ≤ K) (s : ℝ) (hs : 0 < s)
    (hreplacement : ∀ j, ∃ v : DomainL2 Q, v ∈ F.domain ∧
      F.form u u = F.form v v + F.form (u - v) (u - v) ∧
      (∑ i, ((GammaF.measure u (cell j i)).toReal - TF j i)) = F.form (u - v) (u - v) ∧
      ‖u - v‖ ^ 2 ≤ K * mesh j ^ (2 * s) * F.form (u - v) (u - v)) :
    ∀ eps : ℝ, 0 < eps → aux_thm_prop_localSaving M Delta (E.form u u) (F.form u u)
      (volume (Q : Set (SpatialCoordinates d))).toReal c eps := by
  classical
  haveI : IsFiniteMeasure (GammaE.measure u) := ⟨GammaE.measure_univ_lt_top u hu⟩
  haveI : IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hQfin⟩
  let nu := GammaE.measure u + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d))
  haveI : IsFiniteMeasure nu := by
    refine ⟨lt_top_iff_ne_top.mpr ?_⟩
    dsimp only [nu]
    rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)⟩
  have hnu (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A)
      (hAQ : A ⊆ (Q : Set (SpatialCoordinates d))) :
      (nu A).toReal = (GammaE.measure u A).toReal + c * (volume A).toReal := by
    rw [aux_thm_prop_floor_measure_apply _ _ c hc.le,
      Measure.restrict_apply hA, inter_eq_left.mpr hAQ]
  have hEwhole : (GammaE.measure u (Q : Set (SpatialCoordinates d))).toReal = E.form u u := by
    have h := measure_add_measure_compl (μ := GammaE.measure u) Q.isOpen.measurableSet
    rw [hsupportE, add_zero] at h
    rw [h, GammaE.measure_univ u hu]
  have hnuQ : (nu (Q : Set (SpatialCoordinates d))).toReal =
      E.form u u + c * (volume (Q : Set (SpatialCoordinates d))).toReal := by
    rw [hnu _ Q.isOpen.measurableSet (Subset.refl _), hEwhole]
  have hnuCell j i : (nu (cell j i)).toReal =
      (GammaE.measure u (cell j i)).toReal + c * (volume (cell j i)).toReal :=
    hnu _ (hcell j i) (hsub j i)
  have hvolCell j i : ((volume.restrict (Q : Set (SpatialCoordinates d))) (cell j i)).toReal =
      (volume (cell j i)).toReal := by
    rw [Measure.restrict_apply (hcell j i), inter_eq_left.mpr (hsub j i)]
  choose v hv hpyth hgapF hcoer using hreplacement
  have hlsc := aux_thm_prop_replacement_lsc_eventually GF F.toClosedForm hF
    u (hdom ▸ hu) v hv mesh hmesh hmesh0 K hK s hs hpyth hcoer
  intro eps heps
  have hgapEv : ∀ᶠ j in atTop,
      (∑ i, ((GammaE.measure u (cell j i)).toReal - TE j i)) < eps :=
    hgapE.eventually (gt_mem_nhds heps)
  obtain ⟨j, hgj, hlj⟩ := (hgapEv.and (hlsc eps heps)).exists
  refine ⟨count j, TE j, (fun i => (GammaE.measure u (cell j i)).toReal),
    (fun i => (volume (cell j i)).toReal), (fun i => M * TE j i - TF j i),
    F.form (v j) (v j), hsaving j, hgj.le, ?_, ?_, ?_, ?_, hlj⟩
  · have hadd : nu (⋃ i, cell j i) = ∑ i, nu (cell j i) := by
      rw [measure_iUnion (fun i k hik => hdisj j hik) (hcell j), tsum_fintype]
    have h := aux_thm_prop_dich_massLower Q nu (cell j) (hmass j) hadd
    simpa only [hnuQ, hnuCell] using h
  · have h := aux_thm_prop_dich_massMono Q nu (cell j) (hcell j) (hsub j) (hdisj j)
    simpa only [hnuQ, hnuCell] using h
  · have h := aux_thm_prop_dich_massMono Q
      (volume.restrict (Q : Set (SpatialCoordinates d))) (cell j) (hcell j) (hsub j) (hdisj j)
    simpa only [hvolCell, Measure.restrict_apply Q.isOpen.measurableSet, inter_self] using h
  · exact aux_thm_prop_replacement_energy_upper Q E F hdom GammaE GammaF hEcore M hM horder
      u (v j) hu (hv j) hsupportE hsupportF (cell j) (hcell j) (hsub j) (hdisj j)
      (TE j) (TF j) (hTE j) (hpyth j) (hgapF j)

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Corollary 32 with epsilon = 1/8 gives the U-branch affine saving. -/
theorem aux_thm_prop_affine_saving_U (m M ck E F : ℝ)
    (hE : 0 ≤ E) (hck : ck ≤ (m + M) / 2)
    (hconc : |F - ck * E| ≤ (1 / 8 : ℝ) * (M - m) * E) :
    (3 / 8 : ℝ) * (M - m) * E ≤ M * E - F := by
  have h := (abs_le.mp hconc).2
  have hc := mul_le_mul_of_nonneg_right hck hE
  nlinarith

/-- Corollary 32 gives the lower affine improvement on V. -/
theorem aux_thm_prop_affine_lower_V (m M ck E F : ℝ)
    (hE : 0 ≤ E) (hck : (m + M) / 2 ≤ ck)
    (hconc : |F - ck * E| ≤ (1 / 8 : ℝ) * (M - m) * E) :
    (m + (3 / 8 : ℝ) * (M - m)) * E ≤ F := by
  have h := (abs_le.mp hconc).1
  have hc := mul_le_mul_of_nonneg_right hck hE
  nlinarith

/-- The reciprocal endpoint gap retains the same absolute saving constant. -/
theorem aux_thm_prop_reciprocal_saving (m M a E F : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hF : 0 ≤ F) (hlower : (m + a * (M - m)) * E ≤ F) :
    a * (m⁻¹ - M⁻¹) * F ≤ m⁻¹ * F - E := by
  have hM : 0 < M := hm.trans_le hmM
  let k := m + a * (M - m)
  have hk : 0 < k := by dsimp [k]; nlinarith [mul_nonneg ha (sub_nonneg.mpr hmM)]
  have hkM : k ≤ M := by
    dsimp [k]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hmM)]
  have hgap : a * (m⁻¹ - M⁻¹) ≤ m⁻¹ - k⁻¹ := by
    have hid : m⁻¹ - k⁻¹ - a * (m⁻¹ - M⁻¹) =
        a * (M - m) * (M - k) / (m * k * M) := by
      field_simp [hm.ne', hM.ne', hk.ne']
      dsimp [k]
      ring
    have hnn : 0 ≤ a * (M - m) * (M - k) / (m * k * M) :=
      div_nonneg (mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hmM))
        (sub_nonneg.mpr hkM)) (by positivity)
    linarith
  have hE : E ≤ k⁻¹ * F := (le_inv_mul_iff₀ hk).mpr hlower
  have hmul := mul_le_mul_of_nonneg_right hgap hF
  nlinarith

/-- U uses E as the first trace form. -/
theorem aux_thm_prop_trace_saving_U
    {V : Type} [AddCommGroup V] [Module ℝ V]
    (QE QF : QuadraticForm ℝ V) (hQE : ∀ u, 0 ≤ QE u)
    (m M ck : ℝ) (hmM : m ≤ M)
    (horder : ∀ u, m * QE u ≤ QF u ∧ QF u ≤ M * QE u)
    (u ell : V) (lam : ℝ) (hck : ck ≤ (m + M) / 2)
    (hconc : |QF ell - ck * QE ell| ≤ (1 / 8 : ℝ) * (M - m) * QE ell)
    (haffineApprox : QE (u - ell) ≤ (3 / 8 : ℝ) * (1 / 8) / 16 * lam) :
    (M - m) * ((3 / 8 : ℝ) / 2 * QE u -
      4 * ((3 / 8 : ℝ) * (1 / 8) / 16) * lam) ≤ M * QE u - QF u := by
  exact aux_thm_prop_trace_saving QE QF hQE m M hmM horder u ell lam
    (aux_thm_prop_affine_saving_U m M ck (QE ell) (QF ell) (hQE ell) hck hconc)
    haffineApprox

/-- V uses F as the first trace form and both reciprocal endpoints. -/
theorem aux_thm_prop_trace_saving_V
    {V : Type} [AddCommGroup V] [Module ℝ V]
    (QE QF : QuadraticForm ℝ V) (hQE : ∀ u, 0 ≤ QE u) (hQF : ∀ u, 0 ≤ QF u)
    (m M ck : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (horder : ∀ u, m * QE u ≤ QF u ∧ QF u ≤ M * QE u)
    (u ell : V) (lam : ℝ) (hck : (m + M) / 2 ≤ ck)
    (hconc : |QF ell - ck * QE ell| ≤ (1 / 8 : ℝ) * (M - m) * QE ell)
    (haffineApprox : QF (u - ell) ≤ (3 / 8 : ℝ) * (1 / 8) / 16 * lam) :
    (m⁻¹ - M⁻¹) * ((3 / 8 : ℝ) / 2 * QF u -
      4 * ((3 / 8 : ℝ) * (1 / 8) / 16) * lam) ≤ m⁻¹ * QF u - QE u := by
  have hM : 0 < M := hm.trans_le hmM
  have hswap : ∀ v, M⁻¹ * QF v ≤ QE v ∧ QE v ≤ m⁻¹ * QF v := by
    intro v
    exact ⟨(inv_mul_le_iff₀ hM).mpr (horder v).2,
      (le_inv_mul_iff₀ hm).mpr (horder v).1⟩
  apply aux_thm_prop_trace_saving QF QE hQF M⁻¹ m⁻¹ (inv_anti₀ hm hmM)
    hswap u ell lam
  · exact aux_thm_prop_reciprocal_saving m M (3 / 8) (QE ell) (QF ell)
      hm hmM (by norm_num) (by norm_num) (hQF ell)
      (aux_thm_prop_affine_lower_V m M ck (QE ell) (QF ell) (hQE ell) hck hconc)
  · exact haffineApprox

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- The open cube with the same endpoints as a half-open grid cell. -/
theorem aux_thm_prop_grid_open_eq {d : ℕ}
    (lo : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) :
    (centeredCube (fun i => lo i + s / 2) s hs : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun i => Set.Ioo (lo i) (lo i + s)) := by
  rw [centeredCube_eq_pi]
  congr 1
  funext i
  congr 1 <;> ring

theorem aux_thm_prop_grid_open_subset {d : ℕ}
    (lo : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) :
    (centeredCube (fun i => lo i + s / 2) s hs : Set (SpatialCoordinates d)) ⊆
      Set.pi Set.univ (fun i => Set.Ico (lo i) (lo i + s)) := by
  rw [aux_thm_prop_grid_open_eq]
  intro x hx i hi
  exact ⟨(hx i hi).1.le, (hx i hi).2⟩

/-- Removing the lower faces from a half-open cell preserves its measure.
The upper faces were already excluded. -/
theorem aux_thm_prop_grid_open_ae {d : ℕ}
    (mu : Measure (SpatialCoordinates d))
    (lo : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (hfaces : ∀ i : Fin d, mu {x : SpatialCoordinates d | x i = lo i} = 0) :
    (centeredCube (fun i => lo i + s / 2) s hs : Set (SpatialCoordinates d))
      =ᵐ[mu] Set.pi Set.univ (fun i => Set.Ico (lo i) (lo i + s)) := by
  have havoid : ∀ᵐ x ∂mu, ∀ i : Fin d, x i ≠ lo i := by
    apply ae_all_iff.mpr
    intro i
    apply ae_iff.mpr
    simpa only [not_not] using hfaces i
  filter_upwards [havoid] with x hx
  rw [aux_thm_prop_grid_open_eq]
  apply propext
  constructor
  · intro h i hi
    exact ⟨(h i hi).1.le, (h i hi).2⟩
  · intro h i hi
    exact ⟨lt_of_le_of_ne (h i hi).1 (Ne.symm (hx i)), (h i hi).2⟩

/-- Equal-scale half-open cells in one translated grid are disjoint. -/
theorem aux_thm_prop_grid_halfOpen_disjoint {d : ℕ}
    (a : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) :
    Pairwise (fun k l : Fin d → ℤ => Disjoint
      (Set.pi Set.univ (fun i => Set.Ico (a i + s * (k i : ℝ))
        (a i + s * (k i : ℝ) + s)))
      (Set.pi Set.univ (fun i => Set.Ico (a i + s * (l i : ℝ))
        (a i + s * (l i : ℝ) + s)))) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hkl
  funext i
  have hk := (aux_lem_mass_grid_partition_interval_floor hs).mp (hx i (mem_univ i))
  have hl := (aux_lem_mass_grid_partition_interval_floor hs).mp (hy i (mem_univ i))
  exact hk.trans hl.symm

/-- Convert a finite collection selected by `lem_mass` to disjoint open
cubes, preserving every cell predicate and the exact mass of their union. -/
theorem aux_thm_prop_grid_open_family {d : ℕ}
    (mu : Measure (SpatialCoordinates d)) (Q : Set (SpatialCoordinates d))
    (a : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (hfaces : ∀ (i : Fin d) (k : ℤ),
      mu {x : SpatialCoordinates d | x i = a i + s * (k : ℝ)} = 0)
    (G : Finset (Fin d → ℤ))
    (hsub : ∀ k ∈ G, Set.pi Set.univ (fun i =>
      Set.Ico (a i + s * (k i : ℝ)) (a i + s * (k i : ℝ) + s)) ⊆ Q) :
    ∃ idx : Fin G.card → (Fin d → ℤ),
      Function.Injective idx ∧ (∀ j, idx j ∈ G) ∧
      (∀ k ∈ G, ∃ j, idx j = k) ∧
      let zc : Fin G.card → SpatialCoordinates d :=
        fun j i => a i + s * (idx j i : ℝ) + s / 2
      (∀ j, (centeredCube (zc j) s hs : Set (SpatialCoordinates d)) ⊆ Q) ∧
      Pairwise (fun i j => Disjoint
        (centeredCube (zc i) s hs : Set (SpatialCoordinates d))
        (centeredCube (zc j) s hs : Set (SpatialCoordinates d))) ∧
      mu (⋃ j, (centeredCube (zc j) s hs : Set (SpatialCoordinates d))) =
        mu (⋃ k ∈ G, Set.pi Set.univ (fun i =>
          Set.Ico (a i + s * (k i : ℝ)) (a i + s * (k i : ℝ) + s))) := by
  classical
  let e : Fin G.card ≃ G := G.equivFin.symm
  let idx : Fin G.card → (Fin d → ℤ) := fun j => (e j).val
  have hinj : Function.Injective idx := Subtype.val_injective.comp e.injective
  have hmem : ∀ j, idx j ∈ G := fun j => (e j).property
  have hsurj : ∀ k ∈ G, ∃ j, idx j = k := by
    intro k hk
    obtain ⟨j, hj⟩ := e.surjective ⟨k, hk⟩
    exact ⟨j, congrArg Subtype.val hj⟩
  refine ⟨idx, hinj, hmem, hsurj, ?_, ?_, ?_⟩
  · intro j
    exact (aux_thm_prop_grid_open_subset _ s hs).trans (hsub (idx j) (hmem j))
  · intro i j hij
    exact (aux_thm_prop_grid_halfOpen_disjoint a s hs (hinj.ne hij)).mono
      (aux_thm_prop_grid_open_subset _ s hs) (aux_thm_prop_grid_open_subset _ s hs)
  · have hae : (⋃ j, (centeredCube
          (fun i => a i + s * (idx j i : ℝ) + s / 2) s hs : Set (SpatialCoordinates d)))
        =ᵐ[mu] ⋃ j, Set.pi Set.univ (fun i =>
          Set.Ico (a i + s * (idx j i : ℝ)) (a i + s * (idx j i : ℝ) + s)) := by
      exact EventuallyEq.countable_iUnion (fun j =>
        aux_thm_prop_grid_open_ae mu _ s hs (fun i => hfaces i (idx j i)))
    rw [measure_congr hae]
    congr 1
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨idx j, hmem j, hj⟩
    · rintro ⟨k, hk, hx⟩
      obtain ⟨j, rfl⟩ := hsurj k hk
      exact ⟨j, hx⟩

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

theorem aux_thm_prop_grid_side_pos (H1 n : ℕ) :
    0 < ((3 : ℝ) ^ H1) ^ (-(n : ℝ)) := by positivity

noncomputable def aux_thm_prop_mass_side (H1 n : ℕ) : ℝ :=
  ((3 : ℝ) ^ H1) ^ (-(n : ℝ))

noncomputable def aux_thm_prop_mass_shift {d : ℕ} (Mm : ℕ)
    (sigma : Fin d → Fin Mm) : SpatialCoordinates d :=
  fun i => ((sigma i).val : ℝ) / (Mm : ℝ)

noncomputable def aux_thm_prop_mass_lo {d : ℕ} (H1 Mm : ℕ)
    (sigma : Fin d → Fin Mm) (n : ℕ) (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => aux_thm_prop_mass_shift Mm sigma i + aux_thm_prop_mass_side H1 n * (k i : ℝ)

noncomputable def aux_thm_prop_mass_cell {d : ℕ} (H1 Mm : ℕ)
    (sigma : Fin d → Fin Mm) (n : ℕ) (k : Fin d → ℤ) : Set (SpatialCoordinates d) :=
  Set.pi Set.univ (fun i => Set.Ico (aux_thm_prop_mass_lo H1 Mm sigma n k i)
    (aux_thm_prop_mass_lo H1 Mm sigma n k i + aux_thm_prop_mass_side H1 n))

noncomputable def aux_thm_prop_mass_parent_idx {d : ℕ} (H1 : ℕ)
    (k : Fin d → ℤ) : Fin d → ℤ := fun i => Int.floor ((k i : ℝ) / (3 : ℝ) ^ H1)

noncomputable def aux_thm_prop_mass_parent {d : ℕ} (H1 Mm : ℕ)
    (sigma : Fin d → Fin Mm) (n : ℕ) (k : Fin d → ℤ) : Set (SpatialCoordinates d) :=
  aux_thm_prop_mass_cell H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k)

noncomputable def aux_thm_prop_mass_point_idx {d : ℕ} (H1 Mm : ℕ)
    (sigma : Fin d → Fin Mm) (n : ℕ) (x : SpatialCoordinates d) : Fin d → ℤ :=
  fun i => Int.floor ((x i - aux_thm_prop_mass_shift Mm sigma i) / aux_thm_prop_mass_side H1 n)

def aux_thm_prop_mass_padded {d : ℕ} (H1 Mm : ℕ) (Cwidth gamma : ℝ)
    (sigma : Fin d → Fin Mm) (n : ℕ) (k : Fin d → ℤ) : Prop :=
  ∀ i : Fin d,
    Cwidth * ((3 : ℝ) ^ H1) ^ gamma * aux_thm_prop_mass_side H1 n <
      aux_thm_prop_mass_lo H1 Mm sigma n k i -
        aux_thm_prop_mass_lo H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k) i ∧
    Cwidth * ((3 : ℝ) ^ H1) ^ gamma * aux_thm_prop_mass_side H1 n <
      aux_thm_prop_mass_lo H1 Mm sigma (n - 1) (aux_thm_prop_mass_parent_idx H1 k) i +
        aux_thm_prop_mass_side H1 (n - 1) -
          (aux_thm_prop_mass_lo H1 Mm sigma n k i + aux_thm_prop_mass_side H1 n)

/-- Mass selection with disjoint open cells and the same captured mass. -/
theorem aux_thm_prop_mass_open_cells
    (d : ℕ) (hd : 2 ≤ d)
    (H1 : ℕ) (hH1 : 1 ≤ H1)
    (Mm : ℕ) (hMm : 2 ≤ Mm)
    (gamma : ℝ) (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (zeta : ℝ) (hzeta : 0 < zeta)
    (Cwidth : ℝ) (hCwidth : 0 < Cwidth) :
    (hcop : Nat.Coprime Mm (3 ^ H1)) →
    (hMgam : (Mm : ℝ) ^ (-1 : ℝ) ≤ ((3 : ℝ) ^ H1) ^ (gamma - 1)) →
    (zQ : SpatialCoordinates d) →
    (rQ : ℝ) →
    (hrQ : 0 < rQ) →
    (mu : Measure (SpatialCoordinates d)) →
    [IsFiniteMeasure mu] →
    (hsupp : mu (((centeredCube zQ rQ hrQ) : Set (SpatialCoordinates d))ᶜ) = 0) →
    (hQpositive : 0 < mu ((centeredCube zQ rQ hrQ) : Set (SpatialCoordinates d))) →
    (hfaces : ∀ (sigma : (Fin d → Fin Mm)) (n : ℕ) (i : Fin d) (k : Int),
      mu {x : SpatialCoordinates d |
        x i = (aux_thm_prop_mass_shift Mm) sigma i + (aux_thm_prop_mass_side H1) n * (k : ℝ)} = 0) →
    (Uset : ℕ → Prop) →
    ((1 / 2 : ℝ) ≤ SubdiffusiveProcess.Lane3.upperDensity Uset) →
    (Good : (Fin d → Fin Mm) → ℕ → (Fin d → Int) → Prop) →
    (theta : ℝ) →
    (htheta : 0 ≤ theta) →
    (epscoll : ℝ) →
    (hepscoll : 0 < epscoll) →
    (hloss : theta + ((3 : ℝ) ^ H1) ^ (-zeta) + (2 * (d : ℝ) * (Cwidth + 2)) * ((3 : ℝ) ^ H1) ^ (gamma - 1) + epscoll ≤
      1 / 8) →
    (B : (Fin d → Fin Mm) → ℝ) →
    (hB : ∀ sigma : (Fin d → Fin Mm), 0 ≤ B sigma) →
    (hbad : ∀ (sigma : (Fin d → Fin Mm)) (x : SpatialCoordinates d),
      x ∈ ((centeredCube zQ rQ hrQ) : Set (SpatialCoordinates d)) →
      ∀ J : ℕ,
        (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧
          ¬ Good sigma n ((aux_thm_prop_mass_point_idx H1 Mm) sigma n x)} : ℝ) ≤
          theta * (J : ℝ) + B sigma) →
    ∀ n0 : ℕ, ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧ Uset n ∧
      ∃ sigma : (Fin d → Fin Mm), ∃ G : Finset (Fin d → Int),
      ∃ idx : Fin G.card → (Fin d → Int),
        Function.Injective idx ∧ (∀ j, idx j ∈ G) ∧
        (∀ j, Good sigma n (idx j) ∧ (aux_thm_prop_mass_padded H1 Mm Cwidth gamma) sigma n (idx j) ∧
          closure ((aux_thm_prop_mass_parent H1 Mm) sigma n (idx j)) ⊆ ((centeredCube zQ rQ hrQ) : Set (SpatialCoordinates d)) ∧
          (mu ((aux_thm_prop_mass_parent H1 Mm) sigma n (idx j))).toReal ≤
            ((3 : ℝ) ^ H1) ^ ((d : ℝ) + zeta) * (mu ((aux_thm_prop_mass_cell H1 Mm) sigma n (idx j))).toReal) ∧
        let zc : Fin G.card → SpatialCoordinates d :=
          fun j i => (aux_thm_prop_mass_lo H1 Mm) sigma n (idx j) i + (aux_thm_prop_mass_side H1) n / 2
        let hside : 0 < (aux_thm_prop_mass_side H1) n := aux_thm_prop_grid_side_pos H1 n
        (∀ j, (centeredCube (zc j) ((aux_thm_prop_mass_side H1) n) hside : Set (SpatialCoordinates d)) ⊆
          ((centeredCube zQ rQ hrQ) : Set (SpatialCoordinates d))) ∧
        Pairwise (fun i j => Disjoint
          (centeredCube (zc i) ((aux_thm_prop_mass_side H1) n) hside : Set (SpatialCoordinates d))
          (centeredCube (zc j) ((aux_thm_prop_mass_side H1) n) hside : Set (SpatialCoordinates d))) ∧
        (mu ((centeredCube zQ rQ hrQ) : Set (SpatialCoordinates d))).toReal / 8 ≤
          (mu (⋃ j, (centeredCube (zc j) ((aux_thm_prop_mass_side H1) n) hside :
            Set (SpatialCoordinates d)))).toReal := by
  dsimp only
  intro hcop hMgam zQ rQ hrQ mu instFinite hsupp hQpositive hfaces Uset hU Good theta
    htheta epscoll hepscoll hloss B hB hbad n0
  have hsel := lem_mass d hd H1 hH1 Mm hMm gamma hgamma zeta hzeta Cwidth hCwidth
    hcop hMgam zQ rQ hrQ mu hsupp hQpositive hfaces Uset hU Good theta htheta
    epscoll hepscoll hloss B hB hbad n0
  obtain ⟨n, hnn0, hn1, hnU, sigma, G, hprops, hmass⟩ := hsel
  let L : ℝ := (3 : ℝ) ^ H1
  let a : SpatialCoordinates d := fun i => ((sigma i).val : ℝ) / (Mm : ℝ)
  let side : ℝ := L ^ (-(n : ℝ))
  have hside : 0 < side := Real.rpow_pos_of_pos (by dsimp [L]; positivity) _
  have hgrid := lem_mass_grid_partition d H1 Mm hd hH1 hMm
  have hsub : ∀ k ∈ G, Set.pi Set.univ (fun i =>
      Set.Ico (a i + side * (k i : ℝ)) (a i + side * (k i : ℝ) + side)) ⊆
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) := by
    intro k hk
    exact ((hgrid.2.2.1 sigma n hn1 k).1.trans subset_closure).trans (hprops k hk).2.2.1
  obtain ⟨idx, hinj, hmem, _, hsubOpen, hdisj, hmassEq⟩ :=
    aux_thm_prop_grid_open_family mu (centeredCube zQ rQ hrQ) a side hside
      (fun i k => hfaces sigma n i k) G hsub
  refine ⟨n, hnn0, hn1, hnU, sigma, G, idx, hinj, hmem,
    (fun j => hprops (idx j) (hmem j)), hsubOpen, hdisj, ?_⟩
  exact hmass.trans_eq (congrArg ENNReal.toReal hmassEq).symm

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- The mass-selection losses can be made small at one fixed grid scale.
The shift denominator is explicit and coprime to the subdivision factor;
none of these choices depends on the endpoint gap. -/
theorem aux_thm_prop_mass_parameters
    (d H0 : ℕ) (gamma zeta Cwidth : ℝ)
    (hgamma : 0 < gamma) (hgamma1 : gamma < 1) (hzeta : 0 < zeta) :
    ∃ H1 Mm : ℕ,
      H0 ≤ H1 ∧ 1 ≤ H1 ∧ 2 ≤ Mm ∧ Nat.Coprime Mm (3 ^ H1) ∧
      (Mm : ℝ) ^ (-1 : ℝ) ≤ ((3 : ℝ) ^ H1) ^ (gamma - 1) ∧
      (1 / 32 : ℝ) + ((3 : ℝ) ^ H1) ^ (-zeta) +
        (2 * (d : ℝ) * (Cwidth + 2)) * ((3 : ℝ) ^ H1) ^ (gamma - 1) +
        (1 / 32 : ℝ) ≤ 1 / 8 := by
  have hpow : Tendsto (fun n : ℕ => (3 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => ((3 : ℝ) ^ n) ^ (-zeta)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hzeta).comp hpow
  have hg : Tendsto (fun n : ℕ => ((3 : ℝ) ^ n) ^ (gamma - 1)) atTop (𝓝 0) := by
    rw [show gamma - 1 = -(1 - gamma) by ring]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hgamma1)).comp hpow
  have hgc : Tendsto (fun n : ℕ =>
      (2 * (d : ℝ) * (Cwidth + 2)) * ((3 : ℝ) ^ n) ^ (gamma - 1)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hg.const_mul (2 * (d : ℝ) * (Cwidth + 2))
  obtain ⟨H1, hlarge, hpositive, hze, hge⟩ :=
    ((eventually_ge_atTop H0).and ((eventually_ge_atTop 1).and
      ((hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32))).and
        (hgc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32)))))).exists
  have hLpos : 0 < (3 : ℝ) ^ H1 := pow_pos (by norm_num) _
  have hLone : 1 ≤ (3 : ℝ) ^ H1 := one_le_pow₀ (by norm_num)
  refine ⟨H1, 3 ^ H1 + 1, hlarge, hpositive, ?_, ?_, ?_, ?_⟩
  · have hnat : 0 < (3 : ℕ) ^ H1 := pow_pos (by norm_num) _
    omega
  · exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  · have hden : (3 : ℝ) ^ H1 ≤ ((3 ^ H1 + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    calc
      ((3 ^ H1 + 1 : ℕ) : ℝ) ^ (-1 : ℝ) = (((3 ^ H1 + 1 : ℕ) : ℝ))⁻¹ :=
        Real.rpow_neg_one _
      _ ≤ ((3 : ℝ) ^ H1)⁻¹ := inv_anti₀ hLpos hden
      _ = ((3 : ℝ) ^ H1) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
      _ ≤ ((3 : ℝ) ^ H1) ^ (gamma - 1) :=
        Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
  · linarith

/-- Arbitrarily late selected levels give a sequence whose physical mesh
tends to zero. Monotonicity of the chosen levels is unnecessary. -/
theorem aux_thm_prop_fine_levels
    (L : ℝ) (hL : 1 < L) (P : ℕ → Prop)
    (hP : ∀ n0 : ℕ, ∃ n : ℕ, n0 ≤ n ∧ P n) :
    ∃ N : ℕ → ℕ, (∀ j, j ≤ N j ∧ P (N j)) ∧
      Tendsto N atTop atTop ∧
      Tendsto (fun j => L ^ (-(N j : ℝ))) atTop (𝓝 0) := by
  choose N hN hgood using hP
  have hNt : Tendsto N atTop atTop := tendsto_atTop_mono hN tendsto_id
  have hreal : Tendsto (fun j => (N j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNt
  exact ⟨N, fun j => ⟨hN j, hgood j⟩, hNt,
    (tendsto_rpow_atBot_of_base_gt_one L hL).comp
      (tendsto_neg_atTop_atBot.comp hreal)⟩

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Assemble the actual cell projections, identifying their energies with
the chosen trace minima. This supplies the replacement data used by D.1.L. -/
theorem aux_thm_prop_replacement_trace_data
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEdom : E.domain = limitFormDomain G)
    (hEenergy : ∀ w ∈ E.domain, E.form w w = (limitFormEnergy G w).toReal)
    (Gamma : DirichletForm.EnergyMeasure E)
    {n : ℕ} (q : Fin n → Opens (SpatialCoordinates d))
    (hdisj : Pairwise (fun i j => Disjoint (q i : Set (SpatialCoordinates d))
      (q j : Set (SpatialCoordinates d))))
    (Vi : Fin n → Submodule ℝ (DomainL2 Q))
    (hVi : ∀ i, DirichletForm.IsKilledDomain E (q i : Set (SpatialCoordinates d)) (Vi i))
    (u : DomainL2 Q) (hu : u ∈ E.domain)
    (T : Fin n → ℝ)
    (hT : ∀ i, IsLeast {e : ℝ | ∃ w : DomainL2 Q, w ∈ Vi i ∧
      e = (Gamma.measure (u + w) (q i : Set (SpatialCoordinates d))).toReal} (T i))
    (s K h : ℝ)
    (hcoer : ∀ w ∈ (⨆ i, Vi i), ‖w‖ ^ 2 ≤ K * h ^ (2 * s) * E.form w w) :
    ∃ v : DomainL2 Q,
      v ∈ E.domain ∧ u - v ∈ (⨆ i, Vi i) ∧
      (∀ w ∈ (⨆ i, Vi i), E.form v w = 0) ∧
      E.form u u = E.form v v + E.form (u - v) (u - v) ∧
      (∑ i, ((Gamma.measure u (q i : Set (SpatialCoordinates d))).toReal - T i)) =
        E.form (u - v) (u - v) ∧
      ‖u - v‖ ^ 2 ≤ K * h ^ (2 * s) * E.form (u - v) (u - v) := by
  classical
  choose p hp ho using fun i => aux_lem_replace_gap_projection_exists
    G E hEdom hEenergy (q i).isOpen (hVi i) u hu
  obtain ⟨hv, herr, horth, hpyth, _, _, hgap⟩ :=
    aux_lem_replace_projection_assembly E Gamma q hdisj Vi hVi u hu p hp ho
  refine ⟨u - ∑ i, p i, hv, herr, horth, hpyth, ?_, hcoer _ herr⟩
  simpa only [(hT _).csInf_eq] using hgap

/-- The source equation gives the vanishing trace error with the actual
small-cell coercivity exponent and no energy-convergence hypothesis. -/
theorem aux_thm_prop_source_trace_gap_bound
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEdom : E.domain = limitFormDomain G)
    (hEenergy : ∀ w ∈ E.domain, E.form w w = (limitFormEnergy G w).toReal)
    (Gamma : DirichletForm.EnergyMeasure E)
    {n : ℕ} (q : Fin n → Opens (SpatialCoordinates d))
    (hdisj : Pairwise (fun i j => Disjoint (q i : Set (SpatialCoordinates d))
      (q j : Set (SpatialCoordinates d))))
    (Vi : Fin n → Submodule ℝ (DomainL2 Q))
    (hVi : ∀ i, DirichletForm.IsKilledDomain E (q i : Set (SpatialCoordinates d)) (Vi i))
    (f u : DomainL2 Q) (hu : u ∈ E.domain)
    (hweak : ∀ w ∈ E.domain, E.form u w = inner ℝ f w)
    (T : Fin n → ℝ)
    (hT : ∀ i, IsLeast {e : ℝ | ∃ w : DomainL2 Q, w ∈ Vi i ∧
      e = (Gamma.measure (u + w) (q i : Set (SpatialCoordinates d))).toReal} (T i))
    (s K h : ℝ) (hK : 0 < K) (hh : 0 < h)
    (hcoer : ∀ w ∈ (⨆ i, Vi i), ‖w‖ ^ 2 ≤ K * h ^ (2 * s) * E.form w w) :
    0 ≤ (∑ i, ((Gamma.measure u (q i : Set (SpatialCoordinates d))).toReal - T i)) ∧
    (∑ i, ((Gamma.measure u (q i : Set (SpatialCoordinates d))).toReal - T i)) ≤
      K * h ^ (2 * s) * ‖f‖ ^ 2 := by
  obtain ⟨v, hv, herr, horth, _, hgap, _⟩ := aux_thm_prop_replacement_trace_data
    G E hEdom hEenergy Gamma q hdisj Vi hVi u hu T hT s K h hcoer
  rw [hgap]
  exact ⟨E.form_nonneg _ (E.domain.sub_mem hu hv),
    aux_lem_replace_gap_source_bound E s K hK (⨆ i, Vi i) f u v hu hv hweak
      (horth _ herr) herr (E.domain.sub_mem hu hv) h hh hcoer⟩

theorem aux_thm_prop_source_trace_gap_tendsto
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEdom : E.domain = limitFormDomain G)
    (hEenergy : ∀ w ∈ E.domain, E.form w w = (limitFormEnergy G w).toReal)
    (Gamma : DirichletForm.EnergyMeasure E)
    (count : ℕ → ℕ) (q : (j : ℕ) → Fin (count j) → Opens (SpatialCoordinates d))
    (hdisj : ∀ j, Pairwise (fun i k => Disjoint (q j i : Set (SpatialCoordinates d))
      (q j k : Set (SpatialCoordinates d))))
    (Vi : (j : ℕ) → Fin (count j) → Submodule ℝ (DomainL2 Q))
    (hVi : ∀ j i, DirichletForm.IsKilledDomain E (q j i : Set (SpatialCoordinates d)) (Vi j i))
    (f u : DomainL2 Q) (hu : u ∈ E.domain)
    (hweak : ∀ w ∈ E.domain, E.form u w = inner ℝ f w)
    (T : (j : ℕ) → Fin (count j) → ℝ)
    (hT : ∀ j i, IsLeast {e : ℝ | ∃ w : DomainL2 Q, w ∈ Vi j i ∧
      e = (Gamma.measure (u + w) (q j i : Set (SpatialCoordinates d))).toReal} (T j i))
    (s K : ℝ) (hs : 0 < s) (hK : 0 < K)
    (mesh : ℕ → ℝ) (hmesh : Tendsto mesh atTop (𝓝 0)) (hmesh0 : ∀ j, 0 < mesh j)
    (hcoer : ∀ j, ∀ w ∈ (⨆ i, Vi j i),
      ‖w‖ ^ 2 ≤ K * mesh j ^ (2 * s) * E.form w w) :
    Tendsto (fun j => ∑ i, ((Gamma.measure u (q j i : Set (SpatialCoordinates d))).toReal - T j i))
      atTop (𝓝 0) := by
  have ht : 0 < 2 * s := mul_pos two_pos hs
  have hp : Tendsto (fun j => mesh j ^ (2 * s)) atTop (𝓝 0) := by
    have h : Tendsto (fun n => mesh n ^ (2 * s)) atTop (𝓝 ((0 : ℝ) ^ (2 * s))) :=
      ((Real.continuous_rpow_const ht.le).tendsto 0).comp hmesh
    simpa only [Real.zero_rpow ht.ne'] using h
  have hbound : Tendsto (fun j => K * mesh j ^ (2 * s) * ‖f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hp).mul_const (‖f‖ ^ 2)
  have hb := fun j => aux_thm_prop_source_trace_gap_bound
    G E hEdom hEenergy Gamma (q j) (hdisj j) (Vi j) (hVi j) f u hu hweak
    (T j) (hT j) s K (mesh j) hK (hmesh0 j) (hcoer j)
  exact squeeze_zero (fun j => (hb j).1) (fun j => (hb j).2) hbound

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- The deterministic part of D.1.L. Actual trace minima, the source
equation and killed-cell coercivity supply all replacement and limit steps. -/
theorem aux_thm_prop_localSaving_of_trace_cells
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (hQfin : volume (Q : Set (SpatialCoordinates d)) ≠ ⊤)
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hdom : E.domain = F.domain)
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEdom : E.domain = limitFormDomain GE) (hFdom : F.domain = limitFormDomain GF)
    (hEenergy : ∀ w ∈ E.domain, E.form w w = (limitFormEnergy GE w).toReal)
    (hFenergy : ∀ w ∈ F.domain, F.form w w = (limitFormEnergy GF w).toReal)
    (hF : ∀ w, F.energy w = limitFormEnergy GF w)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (M Delta : ℝ) (hM : 0 < M)
    (horder : ∀ w ∈ E.domain, F.form w w ≤ M * E.form w w)
    (f u : DomainL2 Q) (hu : u ∈ E.domain)
    (hweak : ∀ w ∈ E.domain, E.form u w = inner ℝ f w)
    (hsupportE : GammaE.measure u (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (hsupportF : GammaF.measure u (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (c : ℝ) (hc : 0 < c)
    (count : ℕ → ℕ) (q : (j : ℕ) → Fin (count j) → Opens (SpatialCoordinates d))
    (hsub : ∀ j i, (q j i : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (hdisj : ∀ j, Pairwise (fun i k => Disjoint (q j i : Set (SpatialCoordinates d))
      (q j k : Set (SpatialCoordinates d))))
    (Vi : (j : ℕ) → Fin (count j) → Submodule ℝ (DomainL2 Q))
    (hViE : ∀ j i, DirichletForm.IsKilledDomain E.toClosedForm
      (q j i : Set (SpatialCoordinates d)) (Vi j i))
    (hViF : ∀ j i, DirichletForm.IsKilledDomain F.toClosedForm
      (q j i : Set (SpatialCoordinates d)) (Vi j i))
    (TE TF : (j : ℕ) → Fin (count j) → ℝ)
    (hTE : ∀ j i, IsLeast {e : ℝ | ∃ w : DomainL2 Q, w ∈ Vi j i ∧
      e = (GammaE.measure (u + w) (q j i : Set (SpatialCoordinates d))).toReal} (TE j i))
    (hTF : ∀ j i, IsLeast {e : ℝ | ∃ w : DomainL2 Q, w ∈ Vi j i ∧
      e = (GammaF.measure (u + w) (q j i : Set (SpatialCoordinates d))).toReal} (TF j i))
    (hsaving : ∀ j i,
      Delta * ((3 / 8 : ℝ) / 2 * TE j i - 4 * ((3 / 8 : ℝ) * (1 / 8) / 16) *
        ((GammaE.measure u (q j i : Set (SpatialCoordinates d))).toReal +
          c * (volume (q j i : Set (SpatialCoordinates d))).toReal)) ≤
        M * TE j i - TF j i)
    (hmass : ∀ j,
      ((GammaE.measure u + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d)))
        (Q : Set (SpatialCoordinates d))).toReal / 8 ≤
      ((GammaE.measure u + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d)))
        (⋃ i, (q j i : Set (SpatialCoordinates d)))).toReal)
    (mesh : ℕ → ℝ) (hmesh : Tendsto mesh atTop (𝓝 0)) (hmesh0 : ∀ j, 0 < mesh j)
    (sE KE sF KF : ℝ) (hsE : 0 < sE) (hKE : 0 < KE) (hsF : 0 < sF) (hKF : 0 < KF)
    (hcoerE : ∀ j, ∀ w ∈ (⨆ i, Vi j i),
      ‖w‖ ^ 2 ≤ KE * mesh j ^ (2 * sE) * E.form w w)
    (hcoerF : ∀ j, ∀ w ∈ (⨆ i, Vi j i),
      ‖w‖ ^ 2 ≤ KF * mesh j ^ (2 * sF) * F.form w w) :
    ∀ eps : ℝ, 0 < eps → aux_thm_prop_localSaving M Delta (E.form u u) (F.form u u)
      (volume (Q : Set (SpatialCoordinates d))).toReal c eps := by
  have hTEle : ∀ j i, TE j i ≤ (GammaE.measure u (q j i : Set (SpatialCoordinates d))).toReal := by
    intro j i
    exact (hTE j i).2 ⟨0, (Vi j i).zero_mem, by rw [add_zero]⟩
  have hgap := aux_thm_prop_source_trace_gap_tendsto GE E.toClosedForm
    hEdom hEenergy GammaE count q hdisj Vi hViE f u hu hweak TE hTE
    sE KE hsE hKE mesh hmesh hmesh0 hcoerE
  have hrep : ∀ j, ∃ v : DomainL2 Q, v ∈ F.domain ∧
      F.form u u = F.form v v + F.form (u - v) (u - v) ∧
      (∑ i, ((GammaF.measure u (q j i : Set (SpatialCoordinates d))).toReal - TF j i)) =
        F.form (u - v) (u - v) ∧
      ‖u - v‖ ^ 2 ≤ KF * mesh j ^ (2 * sF) * F.form (u - v) (u - v) := by
    intro j
    obtain ⟨v, hv, _, _, hpyth, hsum, hcoer⟩ := aux_thm_prop_replacement_trace_data
      GF F.toClosedForm hFdom hFenergy GammaF (q j) (hdisj j) (Vi j) (hViF j)
      u (hdom ▸ hu) (TF j) (hTF j) sF KF (mesh j) (hcoerF j)
    exact ⟨v, hv, hpyth, hsum, hcoer⟩
  exact aux_thm_prop_localSaving_of_cells Q hQfin E F hdom GF hF GammaE GammaF
    hEcore M Delta hM horder u hu hsupportE hsupportF c hc count
    (fun j i => (q j i : Set (SpatialCoordinates d)))
    (fun j i => (q j i).isOpen.measurableSet) hsub hdisj TE TF hTEle hsaving hgap hmass
    mesh hmesh (fun j => (hmesh0 j).le) KF hKF.le sF hsF hrep

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- The algebra clauses are the proved FOT product calculus for the actual form. -/
theorem aux_thm_prop_core_algebra
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (Q : Set (SpatialCoordinates d)) C) :
    DirichletForm.IsCoreAlgebra E.toClosedForm :=
  ⟨aux_thm_prop_isRegular_of_core Q E.toClosedForm hcore,
    DirichletForm.mul_mem E, DirichletForm.comp_mem E,
    DirichletForm.mul_comp_mem E, DirichletForm.mul_mem_of_bounded E⟩

/-- A closure-continuous representative can be extended continuously without
changing either its volume class or its values almost everywhere for its energy
measure. The second assertion uses support, not absolute continuity. -/
theorem aux_thm_prop_continuous_energy_representative
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z R hR : Set (SpatialCoordinates d)) C)
    (v : DomainL2 (centeredCube z R hR)) (hv : v ∈ E.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvc : ContinuousOn vc (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hrep : ⇑v =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] vc) :
    ∃ V : SpatialCoordinates d → ℝ, Continuous V ∧
      (⇑v =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] V) ∧
      (V =ᵐ[Gamma.measure v] vc) := by
  let Qs : Set (SpatialCoordinates d) := centeredCube z R hR
  have hQc : IsCompact (closure Qs) := lane2_isCompact_closure_centeredCube z hR
  letI : CompactSpace (closure Qs) := isCompact_iff_compactSpace.mp hQc
  let fQ : C(closure Qs, ℝ) := ⟨fun x => vc x, hvc.restrict⟩
  let fQb : BoundedContinuousFunction (closure Qs) ℝ :=
    BoundedContinuousFunction.mkOfCompact fQ
  obtain ⟨V, _hVnorm, hVeq⟩ :=
    BoundedContinuousFunction.exists_norm_eq_restrict_eq_of_closed fQb isClosed_closure
  have heq : ∀ x ∈ closure Qs, V x = vc x := by
    intro x hx
    have hx' := congrArg
      (fun f : BoundedContinuousFunction (closure Qs) ℝ => f ⟨x, hx⟩) hVeq
    exact hx'
  have hQmeas : MeasurableSet Qs := (centeredCube z R hR).isOpen.measurableSet
  refine ⟨V, V.continuous, ?_, ?_⟩
  · filter_upwards [hrep, ae_restrict_mem hQmeas] with x hx hxQ
    exact hx.trans (heq x (subset_closure hxQ)).symm
  · obtain ⟨C, hC⟩ := hcore
    have hsupp : Gamma.measure v Qsᶜ = 0 :=
      aux_thm_prop_energy_measure_support Gamma hQmeas hC hv
    have hmem : ∀ᵐ x ∂Gamma.measure v, x ∈ Qs := by
      exact ae_iff.mpr hsupp
    filter_upwards [hmem] with x hx
    exact heq x (subset_closure hx)

/-- The proved continuous-representative Bouleau--Hirsch lemmas supply the exact
two inputs consumed by zero-trace truncation on a cube. -/
theorem aux_thm_prop_boundary_BH
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z R hR : Set (SpatialCoordinates d)) C)
    (v : DomainL2 (centeredCube z R hR)) (hv : v ∈ E.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvc : ContinuousOn vc (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hrep : ⇑v =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] vc) :
    (∀ N : Set ℝ, MeasurableSet N → volume N = 0 →
      Gamma.measure v (vc ⁻¹' N) = 0) ∧
    (∀ T : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K T) → T 0 = 0 →
      ∀ Tderiv : ℝ → ℝ, Measurable Tderiv →
      (∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) →
      ∀ w : DomainL2 (centeredCube z R hR), w ∈ E.domain →
        (⇑w =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          fun x => T (vc x)) →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        (Gamma.measure w B).toReal =
          ∫ x in B, (Tderiv (vc x)) ^ 2 ∂(Gamma.measure v)) := by
  obtain ⟨V, hV, hVrep, hVenergy⟩ :=
    aux_thm_prop_continuous_energy_representative z R hR E Gamma hcore v hv vc hvc hrep
  have halg := aux_thm_prop_core_algebra (centeredCube z R hR) E hcore
  have hnc := DirichletForm.hasNormalContractions E
  constructor
  · intro N hN hN0
    have heq : (vc ⁻¹' N) =ᵐ[Gamma.measure v] (V ⁻¹' N) := by
      filter_upwards [hVenergy] with x hx
      change (vc x ∈ N) = (V x ∈ N)
      rw [hx]
    rw [measure_congr heq]
    exact obl_BH_compact_preimage_nullity E Gamma halg hnc v hv V hV hVrep N hN hN0
  · intro T hLip hT0 Tderiv hdm hdv w hw hwrep B hB
    have hwrepV : ⇑w =ᵐ[volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))] fun x => T (V x) := by
      filter_upwards [hwrep, hrep, hVrep] with x hwx hvx hVx
      exact hwx.trans (congrArg T (hvx.symm.trans hVx))
    have hchain := obl_BH_energy_measure_convergence E Gamma halg hnc v hv V hV hVrep
      T hLip hT0 Tderiv hdm hdv w hw hwrepV B hB
    rw [hchain]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hVenergy] with x hx
    rw [hx]

/-- Zero-trace restriction belongs to the actual killed space. No Bouleau--Hirsch
premises are left to the consumer. -/
theorem aux_thm_prop_boundary_truncation
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hkilled : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) Dq)
    (v : DomainL2 (centeredCube zQ R hR)) (hv : v ∈ E.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvc : ContinuousOn vc (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hrep : ⇑v =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] vc)
    (hvanish : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), vc x = 0)
    (vq : DomainL2 (centeredCube zQ R hR))
    (hvq : ⇑vq =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))]
      (closure (centeredCube zq r hr : Set (SpatialCoordinates d))).indicator vc) :
    vq ∈ Dq ∧ E.form vq vq =
      (Gamma.measure v (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal := by
  obtain ⟨hnull, hchain⟩ := aux_thm_prop_boundary_BH zQ R hR E Gamma hcore v hv vc hvc hrep
  have h := lem_truncation d hd zQ zq R r hR hr hqQ E Gamma
    (DirichletForm.hasNormalContractions E)
    (aux_thm_prop_core_algebra (centeredCube zQ R hR) E hcore)
    hcore Dq hkilled v hv vc hvc hrep hvanish hnull hchain vq hvq
  exact ⟨h.1, h.2.1⟩

/-- The killed-variation minimum is below the continuous boundary-extension
infimum used by `lem_affine`. Only the needed direction is asserted. -/
theorem aux_thm_prop_trace_le_boundary_glb
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hkilled : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) Dq)
    (u : DomainL2 (centeredCube zQ R hR)) (hu : u ∈ E.domain)
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hurep : ⇑u =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U)
    (b : SpatialCoordinates d → ℝ)
    (hUb : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), U x = b x)
    (T : ℝ)
    (hT : IsLeast {t : ℝ | ∃ w : DomainL2 (centeredCube zQ R hR), w ∈ Dq ∧
      t = (Gamma.measure (u + w) (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal} T)
    (Lambda : ℝ)
    (hLambda : IsGLB {e : ℝ |
      ∃ (v : DomainL2 (centeredCube zQ R hR)) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧
        ContinuousOn V (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))) ∧
        (⇑v =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), V x = b x) ∧
        e = (Gamma.measure v (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal} Lambda) :
    T ≤ Lambda := by
  apply hLambda.2
  intro e he
  obtain ⟨v, V, hv, hV, hvrep, hboundary, rfl⟩ := he
  have hw : v - u ∈ E.domain := E.domain.sub_mem hv hu
  have hwrep : ⇑(v - u) =ᵐ[volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))] fun x => V x - U x := by
    filter_upwards [Lp.coeFn_sub v u, hvrep, hurep] with x hsub hvx hux
    rw [hsub, Pi.sub_apply, hvx, hux]
  have hwLp := (Lp.memLp (v - u)).ae_eq hwrep
  have hqbar : MeasurableSet (closure (centeredCube zq r hr : Set (SpatialCoordinates d))) :=
    isClosed_closure.measurableSet
  let wq := (hwLp.indicator hqbar).toLp _
  have hwqrep : ⇑wq =ᵐ[volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))]
      (closure (centeredCube zq r hr : Set (SpatialCoordinates d))).indicator
        (fun x => V x - U x) := MemLp.coeFn_toLp _
  have hwq := aux_thm_prop_boundary_truncation d hd zQ zq R r hR hr hqQ E Gamma hcore
    Dq hkilled (v - u) hw (fun x => V x - U x) (hV.sub hU) hwrep
    (fun x hx => sub_eq_zero.mpr ((hboundary x hx).trans (hUb x hx).symm)) wq hwqrep
  have huadd : u + wq ∈ E.domain := E.domain.add_mem hu (hkilled.le_domain hwq.1)
  have hqopen := (centeredCube zq r hr).isOpen
  have hlocaleq : ⇑v =ᵐ[(volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))).restrict
        (centeredCube zq r hr : Set (SpatialCoordinates d))] ⇑(u + wq) := by
    filter_upwards [ae_restrict_mem hqopen.measurableSet,
      ae_restrict_of_ae hvrep, ae_restrict_of_ae hurep,
      ae_restrict_of_ae hwqrep, ae_restrict_of_ae (Lp.coeFn_add u wq)]
      with x hxq hvx hux hwqx hadd
    rw [Set.indicator_of_mem (subset_closure hxq)] at hwqx
    rw [hvx, hadd, Pi.add_apply, hux, hwqx]
    ring
  rw [Gamma.locality_apply hv huadd hqopen hlocaleq]
  exact hT.2 ⟨wq, hwq.1, rfl⟩

/-- `lem_affine`'s nonempty boundary-error class supplies an actual domain
element with affine boundary values. Smooth affine functions need not themselves
belong to the singular form domain. -/
theorem aux_thm_prop_affine_trace_approximation
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hkilled : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) Dq)
    (T : QuadraticForm ℝ E.domain)
    (hT : ∀ u : E.domain, IsLeast
      {t : ℝ | ∃ w : DomainL2 (centeredCube zQ R hR), w ∈ Dq ∧
        t = (Gamma.measure (u.val + w)
          (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal} (T u))
    (u : E.domain) (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hurep : ⇑u.val =ᵐ[volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))] U)
    (ell : SpatialCoordinates d → ℝ) (rho lam : ℝ)
    (herror : let eSet : Set ℝ := {e : ℝ |
      ∃ (v : DomainL2 (centeredCube zQ R hR)) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧
        ContinuousOn V (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))) ∧
        (⇑v =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)),
          V x = U x - ell x) ∧
        e = (Gamma.measure v (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal}
      ∃ Lambda : ℝ, IsGLB eSet Lambda ∧ eSet.Nonempty ∧ Lambda ≤ rho * lam) :
    ∃ ellD : E.domain, ∃ L : SpatialCoordinates d → ℝ,
      ContinuousOn L (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))) ∧
      (⇑ellD.val =ᵐ[volume.restrict
        (centeredCube zQ R hR : Set (SpatialCoordinates d))] L) ∧
      (∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), L x = ell x) ∧
      T (u - ellD) ≤ rho * lam := by
  obtain ⟨Lambda, hLambda, ⟨e, v, V, hv, hV, hvrep, hVb, _he⟩, hbound⟩ := herror
  let vD : E.domain := ⟨v, hv⟩
  have hmin : T vD ≤ Lambda :=
    aux_thm_prop_trace_le_boundary_glb d hd zQ zq R r hR hr hqQ E Gamma hcore Dq hkilled
      v hv V hV hvrep (fun x => U x - ell x) hVb (T vD) (hT vD) Lambda hLambda
  refine ⟨u - vD, fun x => U x - V x, hU.sub hV, ?_, ?_, ?_⟩
  · change ⇑(u.val - v) =ᵐ[_] _
    filter_upwards [Lp.coeFn_sub u.val v, hurep, hvrep] with x hsub hux hvx
    rw [hsub, Pi.sub_apply, hux, hvx]
  · intro x hx
    change U x - V x = ell x
    rw [hVb x hx]
    ring
  · simpa only [sub_sub_cancel] using hmin.trans hbound

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Equal continuous boundary values give the same local killed coset. -/
theorem aux_thm_prop_boundary_local_coset
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hkilled : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) Dq)
    (u v : DomainL2 (centeredCube zQ R hR)) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (U V : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hV : ContinuousOn V (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hurep : ⇑u =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U)
    (hvrep : ⇑v =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] V)
    (hboundary : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), V x = U x) :
    ∃ w ∈ Dq, ⇑v =ᵐ[(volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))).restrict
        (centeredCube zq r hr : Set (SpatialCoordinates d))] ⇑(u + w) := by
  have hw : v - u ∈ E.domain := E.domain.sub_mem hv hu
  have hwrep : ⇑(v - u) =ᵐ[volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))] fun x => V x - U x := by
    filter_upwards [Lp.coeFn_sub v u, hvrep, hurep] with x hsub hvx hux
    rw [hsub, Pi.sub_apply, hvx, hux]
  have hwLp := (Lp.memLp (v - u)).ae_eq hwrep
  have hqbar : MeasurableSet (closure (centeredCube zq r hr : Set (SpatialCoordinates d))) :=
    isClosed_closure.measurableSet
  let wq := (hwLp.indicator hqbar).toLp _
  have hwqrep : ⇑wq =ᵐ[volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))]
      (closure (centeredCube zq r hr : Set (SpatialCoordinates d))).indicator
        (fun x => V x - U x) := MemLp.coeFn_toLp _
  have hwq := aux_thm_prop_boundary_truncation d hd zQ zq R r hR hr hqQ E Gamma hcore
    Dq hkilled (v - u) hw (fun x => V x - U x) (hV.sub hU) hwrep
    (fun x hx => sub_eq_zero.mpr (hboundary x hx)) wq hwqrep
  refine ⟨wq, hwq.1, ?_⟩
  filter_upwards [ae_restrict_mem (centeredCube zq r hr).isOpen.measurableSet,
    ae_restrict_of_ae hvrep, ae_restrict_of_ae hurep,
    ae_restrict_of_ae hwqrep, ae_restrict_of_ae (Lp.coeFn_add u wq)]
    with x hxq hvx hux hwqx hadd
  rw [Set.indicator_of_mem (subset_closure hxq)] at hwqx
  rw [hvx, hadd, Pi.add_apply, hux, hwqx]
  ring

/-- A local killed-coset relation transfers the actual energy minimum. -/
theorem aux_thm_prop_trace_le_of_local_coset
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (D : Submodule ℝ (DomainL2 Q)) (hD : D ≤ E.domain)
    (u v : DomainL2 Q) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (Tu Tv : ℝ)
    (hTu : IsLeast {t : ℝ | ∃ w : DomainL2 Q, w ∈ D ∧
      t = (Gamma.measure (u + w) q).toReal} Tu)
    (hTv : IsLeast {t : ℝ | ∃ w : DomainL2 Q, w ∈ D ∧
      t = (Gamma.measure (v + w) q).toReal} Tv)
    (w : DomainL2 Q) (hw : w ∈ D)
    (hae : ⇑v =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d))).restrict q] ⇑(u + w)) :
    Tu ≤ Tv := by
  obtain ⟨p, hp, hTvval⟩ := hTv.1
  have hwp : w + p ∈ D := D.add_mem hw hp
  have heq : ⇑(v + p) =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d))).restrict q]
      ⇑(u + (w + p)) := by
    filter_upwards [hae, ae_restrict_of_ae (Lp.coeFn_add v p),
      ae_restrict_of_ae (Lp.coeFn_add u w), ae_restrict_of_ae (Lp.coeFn_add w p),
      ae_restrict_of_ae (Lp.coeFn_add u (w + p))] with x hx h1 h2 h3 h4
    rw [h1, Pi.add_apply, hx, h2, Pi.add_apply, h4, Pi.add_apply, h3, Pi.add_apply]
    ring
  have hmeasure := Gamma.locality_apply (E.domain.add_mem hv (hD hp))
    (E.domain.add_mem hu (hD hwp)) hq heq
  rw [hTvval, hmeasure]
  exact hTu.2 ⟨w + p, hwp, rfl⟩

/-- The trace quadratic form depends only on the actual continuous boundary
values, so a constructed affine-boundary representative can replace any other. -/
theorem aux_thm_prop_trace_eq_of_boundary
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hkilled : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) Dq)
    (u v : DomainL2 (centeredCube zQ R hR)) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (U V : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hV : ContinuousOn V (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hurep : ⇑u =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U)
    (hvrep : ⇑v =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] V)
    (hboundary : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), V x = U x)
    (Tu Tv : ℝ)
    (hTu : IsLeast {t : ℝ | ∃ w : DomainL2 (centeredCube zQ R hR), w ∈ Dq ∧
      t = (Gamma.measure (u + w) (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal} Tu)
    (hTv : IsLeast {t : ℝ | ∃ w : DomainL2 (centeredCube zQ R hR), w ∈ Dq ∧
      t = (Gamma.measure (v + w) (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal} Tv) :
    Tu = Tv := by
  obtain ⟨w, hw, hae⟩ := aux_thm_prop_boundary_local_coset d hd zQ zq R r hR hr hqQ
    E Gamma hcore Dq hkilled u v hu hv U V hU hV hurep hvrep hboundary
  obtain ⟨w', hw', hae'⟩ := aux_thm_prop_boundary_local_coset d hd zQ zq R r hR hr hqQ
    E Gamma hcore Dq hkilled v u hv hu V U hV hU hvrep hurep
      (fun x hx => (hboundary x hx).symm)
  exact le_antisymm
    (aux_thm_prop_trace_le_of_local_coset _ E.toClosedForm Gamma _ (centeredCube zq r hr).isOpen
      Dq hkilled.le_domain u v hu hv Tu Tv hTu hTv w hw hae)
    (aux_thm_prop_trace_le_of_local_coset _ E.toClosedForm Gamma _ (centeredCube zq r hr).isOpen
      Dq hkilled.le_domain v u hv hu Tv Tu hTv hTu w' hw' hae')

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

section Joint

variable {d : ℕ}
  [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
  {model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
  {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {field : Ω → BilateralField d}
  {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ i, 0 < r i}
  {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
  {GN : (i : ℕ) → ℕ → Ω →
    DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
  {GE GF : (i : ℕ) → Ω →
    DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
  {NE NF : ℕ → ℕ}

theorem aux_thm_prop_joint_self_left
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) :
    in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GE NE NE := by
  obtain ⟨hP, hfield, hmap, hIR, ⟨hNE, _hNF⟩, hS, hGN, hconv⟩ := hJoint
  refine ⟨hP, hfield, hmap, hIR, ⟨hNE, hNE⟩, hS, hGN, ?_⟩
  filter_upwards [hconv] with om hom i
  exact ⟨(hom i).1, (hom i).1⟩

theorem aux_thm_prop_joint_self_right
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) :
    in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GF GF NF NF := by
  obtain ⟨hP, hfield, hmap, hIR, ⟨_hNE, hNF⟩, hS, hGN, hconv⟩ := hJoint
  refine ⟨hP, hfield, hmap, hIR, ⟨hNF, hNF⟩, hS, hGN, ?_⟩
  filter_upwards [hconv] with om hom i
  exact ⟨(hom i).2, (hom i).2⟩

/-- The actual source equation follows from joint operator convergence, by the
proved weak-solution supplier in `lem_replace`. -/
theorem aux_thm_prop_source_of_joint (hd : 2 ≤ d)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) :
    ∀ᵐ om ∂P, ∀ i : ℕ,
      ∀ E : DirichletForm.ClosedForm
        (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
      (∀ u, E.energy u = limitFormEnergy (GE i om) u) →
      ∀ Gamma : DirichletForm.EnergyMeasure E,
      (∃ C, DirichletForm.IsCoreOn E
        (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) →
      DirichletForm.IsResolvent E 0 (GE i om) := by
  have hSelf := aux_thm_prop_joint_self_left hJoint
  filter_upwards [hJoint.2.2.2.2.2.2.2] with om hconv
  intro i E hE Gamma hcore
  have hdom : (E.domain : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))) =
      limitFormDomain (GE i om) := by
    ext u
    change u ∈ E.domain ↔ limitFormEnergy (GE i om) u < ⊤
    rw [← hE u]
    exact (E.energy_lt_top_iff u).symm
  have hdiag : ∀ u ∈ E.domain, E.form u u = (limitFormEnergy (GE i om) u).toReal := by
    intro u hu
    rw [← hE u, E.energy_of_mem hu, EReal.toReal_coe]
  obtain ⟨C, hC⟩ := hcore
  have hsupp : ∀ u ∈ E.domain,
      Gamma.measure u (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))ᶜ = 0 := by
    intro u hu
    exact aux_thm_prop_energy_measure_support Gamma
      (centeredCube (z i) (r i) (hr i)).isOpen.measurableSet hC hu
  intro f
  have hweak := aux_lem_replace_gap_weak_solution_needs d hd model H Ω P field z r hr
    Sspace GN GE NE hSelf om i (hconv i).1 E hdom hdiag Gamma hsupp f
  simpa only [zero_mul, zero_add] using hweak

end Joint

end Paper


end

namespace Paper

theorem aux_thm_prop_side_supply_actual
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (hSspace0 : Sspace0.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (hcontract0 : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : Sspace0.space,
        ∃ v : Sspace0.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) v v ≤
            responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) u u)
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N0 : ℕ → ℕ)
    (GN0 : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGN0 : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), GN0 n f =
      (responseSolution Sspace0
          (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0)
          ((sobolevVolumeLoad f).comp Sspace0.space.subtypeL)).val.1)
    (hGN0tendsto : Tendsto GN0 atTop (𝓝 G0))
    (hbundle0 : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 Sspace0 G0 N0)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasEnergyMeasure F) :
    Nonempty (aux_thm_prop_limit_side d hd model H om z0 r0 hr0 Sspace0 G0 N0) := by
  obtain ⟨F, _hFdom, hF, hcore⟩ := aux_thm_prop_hregularity_side hd model H om z0 r0 hr0
    Sspace0 hSspace0 hcontract0 G0 N0 GN0 hGN0 hGN0tendsto hbundle0
  have hlocal := aux_thm_prop_form_core_locality d hd model H om z0 r0 hr0
    Sspace0 hSspace0 G0 N0 GN0 hGN0 hGN0tendsto hbundle0 F.toClosedForm hF
  have hstrong := (BD z0 r0 hr0 F).isStronglyLocal_of_onCore
    (aux_thm_prop_isRegular_of_core (centeredCube z0 r0 hr0) F.toClosedForm hcore)
    (BDQ z0 r0 hr0 F hcore hlocal)
  obtain ⟨Gamma, _hSupport⟩ := aux_thm_prop_energy_measure_of_locality z0 r0 hr0 F
    (EM z0 r0 hr0 F) hcore hstrong
  exact ⟨⟨GN0, hGN0, hGN0tendsto, hbundle0, F, hF, hcore, Gamma⟩⟩




end Paper
section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

section Joint

variable {d : ℕ}
  [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
  {model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
  {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {field : Ω → BilateralField d}
  {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ i, 0 < r i}
  {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
  {GN : (i : ℕ) → ℕ → Ω →
    DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
  {GE GF : (i : ℕ) → Ω →
    DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
  {NE NF : ℕ → ℕ}

/-- Both actual represented forms and their energy measures exist on the same
full-measure event, using only the approved standing inputs. -/
theorem aux_thm_prop_sides_of_joint (hd : 2 ≤ d)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (hBounds : aux_thm_prop_bounds_pointwise d hd model H z r hr Sspace NE NF) :
    ∀ᵐ om ∂P, ∀ i,
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z i) (r i) (hr i)
        (Sspace i) (GE i om) NE) ∧
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z i) (r i) (hr i)
        (Sspace i) (GF i om) NF) := by
  have hb := aux_thm_prop_bounds_pointwise_ae hd hJoint hJoint.2.1 hJoint.2.2.1 hBounds
  filter_upwards [hb, hJoint.2.2.2.2.2.2.2] with om hbo hc i
  have hSi := hJoint.2.2.2.2.2.1 i
  have hcontract0 := fun n => hcontract (z i) (r i) (hr i) (Sspace i) hSi
    (Lane4.cutoffPositiveCoefficient model H (field om) n (z i) (hr i))
  exact ⟨aux_thm_prop_side_supply_actual hd model H (field om) (z i) (r i) (hr i)
    (Sspace i) hSi hcontract0 (GE i om) NE (fun n => GN i (NE n) om)
    (fun n f => hJoint.2.2.2.2.2.2.1 i (NE n) om f) (hc i).1 (hbo i).1 BD BDQ EM,
    aux_thm_prop_side_supply_actual hd model H (field om) (z i) (r i) (hr i)
    (Sspace i) hSi hcontract0 (GF i om) NF (fun n => GN i (NF n) om)
    (fun n f => hJoint.2.2.2.2.2.2.1 i (NF n) om f) (hc i).2 (hbo i).2 BD BDQ EM⟩

/-- The deterministic optimal endpoints are actual form-order bounds. -/
theorem aux_thm_prop_endpoint_order (hd : 2 ≤ d)
    (C0 : ℝ) (hC0 : 1 ≤ C0) (m M : ℝ)
    (hcomp : ∀ᵐ om ∂P, aux_thm_prop_compare z r hr GE GF C0 om)
    (hnz : ∀ᵐ om ∂P, aux_thm_prop_nonzero z r hr GE om)
    (hdet : ∀ᵐ om ∂P, sSup (aux_thm_prop_lowerSet z r hr GE GF om) = m ∧
      sInf (aux_thm_prop_upperSet z r hr GE GF om) = M) :
    ∀ᵐ om ∂P, C0⁻¹ ≤ m ∧ m ≤ M ∧ M ≤ C0 ∧
      ∀ i, limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
        ∀ u ∈ limitFormDomain (GE i om),
          m * (limitFormEnergy (GE i om) u).toReal ≤
            (limitFormEnergy (GF i om) u).toReal ∧
          (limitFormEnergy (GF i om) u).toReal ≤
            M * (limitFormEnergy (GE i om) u).toReal := by
  filter_upwards [hcomp, hnz, hdet] with om hc hn he
  have h := aux_thm_prop_endpoints_at hd z r hr GE GF C0 hC0 om hc hn
  rw [he.1, he.2] at h
  refine ⟨h.2.2.1.1, h.2.2.1.2.1, h.2.2.1.2.2, fun i => ⟨(hc i).1, ?_⟩⟩
  intro u hu
  exact ⟨h.2.2.2.1 i u hu, h.2.2.2.2 i u hu⟩

end Joint

/-- The uniform small-cell coercivity consumed by harmonic replacement. -/
def aux_thm_prop_cell_coercivity {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (s K : ℝ) : Prop :=
  ∀ (n : ℕ) (zc : Fin n → SpatialCoordinates d)
    (rc : Fin n → ℝ) (hrc : ∀ i, 0 < rc i),
    let q : Fin n → Opens (SpatialCoordinates d) := fun i => centeredCube (zc i) (rc i) (hrc i)
    ∀ (h : ℝ), 0 < h → (∀ i, rc i ≤ h) →
      (∀ i, (q i : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d))) →
      Pairwise (fun i j => Disjoint (q i : Set (SpatialCoordinates d))
        (q j : Set (SpatialCoordinates d))) →
      ∀ (Vi : Fin n → Submodule ℝ (DomainL2 Q)),
      (∀ i, DirichletForm.IsKilledDomain E (q i : Set (SpatialCoordinates d)) (Vi i)) →
      ∀ v ∈ (⨆ i, Vi i), ‖v‖ ^ 2 ≤ K * h ^ (2 * s) * E.form v v

/-- `lem_replace` supplies the uniform cell coercivity for both actual limits
on one common event. No extra coercivity premise is added to proportionality. -/
theorem aux_thm_prop_coercivity_pair
    (d : ℕ) (hd : 2 ≤ d) (I : Paper.in_J d) (Pin : Paper.in_poincare d hd I)
    (Sob : Lane4.SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i))) (NE NF : ℕ → ℕ),
      in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF →
      ∀ᵐ om ∂P, ∀ i,
        (∀ (E : DirichletForm.ClosedForm
          (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))),
          (∀ u, E.energy u = limitFormEnergy (GE i om) u) →
          ∀ Gamma : DirichletForm.EnergyMeasure E,
          ∃ s K : ℝ, 1 / 2 < s ∧ s < 1 ∧ 0 < K ∧
            aux_thm_prop_cell_coercivity (centeredCube (z i) (r i) (hr i)) E s K) ∧
        (∀ (F : DirichletForm.ClosedForm
          (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))),
          (∀ u, F.energy u = limitFormEnergy (GF i om) u) →
          ∀ Gamma : DirichletForm.EnergyMeasure F,
          ∃ s K : ℝ, 1 / 2 < s ∧ s < 1 ∧ 0 < K ∧
            aux_thm_prop_cell_coercivity (centeredCube (z i) (r i) (hr i)) F s K) := by
  obtain ⟨delta0, hdelta0, hc⟩ := aux_lem_replace_gap_coercivity d hd I Pin Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel Rm H Ω _ P field z r hr Sspace GN GE GF NE NF hJoint
  have he := hc model hmodel Rm H Ω P field z r hr Sspace GN GE NE
    (aux_thm_prop_joint_self_left hJoint)
  have hf := hc model hmodel Rm H Ω P field z r hr Sspace GN GF NF
    (aux_thm_prop_joint_self_right hJoint)
  filter_upwards [he, hf] with om home homf i
  constructor
  · intro E hE Gamma
    obtain ⟨s, K, hsK, hcoer⟩ := home i E
      (aux_thm_prop_domain_eq_of_energy E (GE i om) hE)
      (aux_thm_prop_form_eq_toReal_energy E (GE i om) hE) Gamma
    exact ⟨s, K, hsK.1, hsK.2.1, hsK.2.2, hcoer⟩
  · intro F hF Gamma
    obtain ⟨s, K, hsK, hcoer⟩ := homf i F
      (aux_thm_prop_domain_eq_of_energy F (GF i om) hF)
      (aux_thm_prop_form_eq_toReal_energy F (GF i om) hF) Gamma
    exact ⟨s, K, hsK.1, hsK.2.1, hsK.2.2, hcoer⟩

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- The geometric and affine data used in one directed branch of D.1.L.
The quadratic forms are actual killed trace minima, and the mass includes the
positive volume floor. The affine saving remains scaled by the endpoint gap. -/
structure aux_thm_prop_fine_cells
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m M : ℝ) (u : E.domain) (c : ℝ) where
  count : ℕ → ℕ
  center : (j : ℕ) → Fin (count j) → SpatialCoordinates d
  radius : (j : ℕ) → Fin (count j) → ℝ
  radius_pos : ∀ j i, 0 < radius j i
  mesh : ℕ → ℝ
  mesh_pos : ∀ j, 0 < mesh j
  mesh_tendsto : Tendsto mesh atTop (𝓝 0)
  radius_le_mesh : ∀ j i, radius j i ≤ mesh j
  inside : ∀ j i, (centeredCube (center j i) (radius j i) (radius_pos j i) :
    Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d))
  disjoint : ∀ j, Pairwise (fun i k => Disjoint
    (centeredCube (center j i) (radius j i) (radius_pos j i) : Set (SpatialCoordinates d))
    (centeredCube (center j k) (radius j k) (radius_pos j k) : Set (SpatialCoordinates d)))
  variation : (j : ℕ) → Fin (count j) → Submodule ℝ (DomainL2 Q)
  killedE : ∀ j i, DirichletForm.IsKilledDomain E.toClosedForm
    (centeredCube (center j i) (radius j i) (radius_pos j i) : Set (SpatialCoordinates d))
    (variation j i)
  killedF : ∀ j i, DirichletForm.IsKilledDomain F.toClosedForm
    (centeredCube (center j i) (radius j i) (radius_pos j i) : Set (SpatialCoordinates d))
    (variation j i)
  QE : (j : ℕ) → Fin (count j) → QuadraticForm ℝ E.domain
  QF : (j : ℕ) → Fin (count j) → QuadraticForm ℝ E.domain
  QE_nonneg : ∀ j i w, 0 ≤ QE j i w
  QF_nonneg : ∀ j i w, 0 ≤ QF j i w
  minimalE : ∀ j i (w : E.domain), IsLeast {e : ℝ | ∃ v : DomainL2 Q,
    v ∈ variation j i ∧ e = (GammaE.measure (w.val + v)
      (centeredCube (center j i) (radius j i) (radius_pos j i) : Set (SpatialCoordinates d))).toReal}
    (QE j i w)
  minimalF : ∀ j i (w : E.domain), IsLeast {e : ℝ | ∃ v : DomainL2 Q,
    v ∈ variation j i ∧ e = (GammaF.measure (w.val + v)
      (centeredCube (center j i) (radius j i) (radius_pos j i) : Set (SpatialCoordinates d))).toReal}
    (QF j i w)
  order : ∀ j i w, m * QE j i w ≤ QF j i w ∧ QF j i w ≤ M * QE j i w
  ell : (j : ℕ) → Fin (count j) → E.domain
  affine_saving : ∀ j i,
    (3 / 8 : ℝ) * (M - m) * QE j i (ell j i) ≤
      M * QE j i (ell j i) - QF j i (ell j i)
  affine_error : ∀ j i, QE j i (u - ell j i) ≤
    ((3 / 8 : ℝ) * (1 / 8) / 16) *
      ((GammaE.measure u.val (centeredCube (center j i) (radius j i) (radius_pos j i) :
        Set (SpatialCoordinates d))).toReal +
        c * (volume (centeredCube (center j i) (radius j i) (radius_pos j i) :
          Set (SpatialCoordinates d))).toReal)
  mass : ∀ j,
    ((GammaE.measure u.val + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d)))
      (Q : Set (SpatialCoordinates d))).toReal / 8 ≤
    ((GammaE.measure u.val + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d)))
      (⋃ i, (centeredCube (center j i) (radius j i) (radius_pos j i) :
        Set (SpatialCoordinates d)))).toReal

/-- Fine affine cells imply all seven local-saving clauses. This consumes the
actual source equation and the root-derived uniform coercivity for both forms. -/
theorem aux_thm_prop_localSaving_of_fine_cells
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (hQfin : volume (Q : Set (SpatialCoordinates d)) ≠ ⊤)
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hE : ∀ w, E.energy w = limitFormEnergy GE w)
    (hF : ∀ w, F.energy w = limitFormEnergy GF w)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (m M : ℝ) (hmM : m ≤ M) (hM : 0 < M)
    (horder : ∀ w ∈ E.domain, F.form w w ≤ M * E.form w w)
    (f : DomainL2 Q) (u : E.domain)
    (hweak : ∀ w ∈ E.domain, E.form u.val w = inner ℝ f w)
    (sE KE sF KF : ℝ) (hsE : 0 < sE) (hKE : 0 < KE) (hsF : 0 < sF) (hKF : 0 < KF)
    (hcoerE : aux_thm_prop_cell_coercivity Q E.toClosedForm sE KE)
    (hcoerF : aux_thm_prop_cell_coercivity Q F.toClosedForm sF KF)
    (c : ℝ) (hc : 0 < c)
    (cells : aux_thm_prop_fine_cells Q E F GammaE GammaF m M u c) :
    ∀ eps : ℝ, 0 < eps →
      aux_thm_prop_localSaving M (M - m) (E.form u.val u.val) (F.form u.val u.val)
        (volume (Q : Set (SpatialCoordinates d))).toReal c eps := by
  have hEdom := aux_thm_prop_domain_eq_of_energy E.toClosedForm GE hE
  have hFdom := aux_thm_prop_domain_eq_of_energy F.toClosedForm GF hF
  have hEe := aux_thm_prop_form_eq_toReal_energy E.toClosedForm GE hE
  have hFe := aux_thm_prop_form_eq_toReal_energy F.toClosedForm GF hF
  obtain ⟨CE, hCE⟩ := hEcore
  obtain ⟨CF, hCF⟩ := hFcore
  have hsuppE := aux_thm_prop_energy_measure_support GammaE Q.isOpen.measurableSet hCE u.property
  have huF : u.val ∈ F.domain := hdom ▸ u.property
  have hsuppF : GammaF.measure u.val (Q : Set (SpatialCoordinates d))ᶜ = 0 := aux_thm_prop_energy_measure_support GammaF Q.isOpen.measurableSet hCF huF
  refine aux_thm_prop_localSaving_of_trace_cells Q hQfin E F hdom GE GF hEdom hFdom
    hEe hFe hF GammaE GammaF ⟨CE, hCE⟩ M (M - m) hM horder f u.val u.property hweak
    hsuppE hsuppF c hc cells.count
    (fun j i => centeredCube (cells.center j i) (cells.radius j i) (cells.radius_pos j i))
    cells.inside cells.disjoint cells.variation cells.killedE cells.killedF
    (fun j i => cells.QE j i u) (fun j i => cells.QF j i u)
    (fun j i => cells.minimalE j i u) (fun j i => cells.minimalF j i u)
    ?_ cells.mass cells.mesh cells.mesh_tendsto cells.mesh_pos
    sE KE sF KF hsE hKE hsF hKF ?_ ?_
  · intro j i
    exact aux_thm_prop_trace_saving (cells.QE j i) (cells.QF j i)
      (cells.QE_nonneg j i) m M hmM (cells.order j i) u (cells.ell j i) _
      (cells.affine_saving j i) (cells.affine_error j i)
  · intro j
    exact hcoerE (cells.count j) (cells.center j) (cells.radius j) (cells.radius_pos j)
      (cells.mesh j) (cells.mesh_pos j) (cells.radius_le_mesh j) (cells.inside j)
      (cells.disjoint j) (cells.variation j) (cells.killedE j)
  · intro j
    exact hcoerF (cells.count j) (cells.center j) (cells.radius j) (cells.radius_pos j)
      (cells.mesh j) (cells.mesh_pos j) (cells.radius_le_mesh j) (cells.inside j)
      (cells.disjoint j) (cells.variation j) (cells.killedF j)

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Uniform small-cell coercivity for an actual represented form. -/
def aux_thm_prop_coercive_candidate {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) : Prop :=
  ∀ E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))),
    (∀ u, E.energy u = limitFormEnergy G u) →
    ∀ Gamma : DirichletForm.EnergyMeasure E,
    ∃ s K : ℝ, 1 / 2 < s ∧ s < 1 ∧ 0 < K ∧ aux_thm_prop_cell_coercivity Q E s K

section Joint

variable {d : ℕ}
  [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
  {model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
  {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {field : Ω → BilateralField d}
  {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ i, 0 < r i}
  {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
  {GN : (i : ℕ) → ℕ → Ω →
    DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
  {GE GF : (i : ℕ) → Ω →
    DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
  {NE NF : ℕ → ℕ}


/-- The remaining cell-selection content of a directed D.1.L branch. All
forms and trace minima refer to the represented operators. -/
def aux_thm_prop_fine_candidates (hd : 2 ≤ d) (m M : ℝ) : Prop :=
  ∀ᵐ om ∂P, ∀ i,
    ∀ (E : aux_thm_prop_limit_side d hd model H (field om) (z i) (r i) (hr i)
      (Sspace i) (GE i om) NE)
      (F : aux_thm_prop_limit_side d hd model H (field om) (z i) (r i) (hr i)
        (Sspace i) (GF i om) NF),
    ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z i) (r i) (hr i)),
    ∀ hu : GE i om f ∈ E.form.domain,
    ∀ c : ℝ, 0 < c → Nonempty (aux_thm_prop_fine_cells
      (centeredCube (z i) (r i) (hr i)) E.form F.form E.gamma F.gamma m M
      ⟨GE i om f, hu⟩ c)

/-- Close the directed replacement argument once the genuine fine affine
cells have been selected. This constructs the source and both coercivity inputs. -/
theorem aux_thm_prop_directed_dichotomy (hd : 2 ≤ d)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (hside : ∀ᵐ om ∂P, ∀ i,
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z i) (r i) (hr i)
        (Sspace i) (GE i om) NE) ∧
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z i) (r i) (hr i)
        (Sspace i) (GF i om) NF))
    (m M : ℝ) (hmM : m ≤ M) (hM : 0 < M)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (hcoer : ∀ᵐ om ∂P, ∀ i,
      aux_thm_prop_coercive_candidate (centeredCube (z i) (r i) (hr i)) (GE i om) ∧
      aux_thm_prop_coercive_candidate (centeredCube (z i) (r i) (hr i)) (GF i om))
    (hfine : aux_thm_prop_fine_candidates (model := model) (H := H) (P := P)
      (field := field) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
      (GE := GE) (GF := GF) (NE := NE) (NF := NF) hd m M) :
    ∀ᵐ om ∂P, ∀ i,
      ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z i) (r i) (hr i)),
      ∀ c : ℝ, 0 < c → ∀ eps : ℝ, 0 < eps →
        aux_thm_prop_localSaving M (M - m)
          (limitFormEnergy (GE i om) (GE i om f)).toReal
          (limitFormEnergy (GF i om) (GE i om f)).toReal
          (volume (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))).toReal
          c eps := by
  have hsource := aux_thm_prop_source_of_joint hd hJoint
  filter_upwards [hside, horder, hcoer, hfine, hsource] with om hs ho hc hf hsrc i f hfs c hcpos
  obtain ⟨E⟩ := (hs i).1
  obtain ⟨F⟩ := (hs i).2
  have hEdom := aux_thm_prop_domain_eq_of_energy E.form.toClosedForm (GE i om) E.energy_eq
  have hFdom := aux_thm_prop_domain_eq_of_energy F.form.toClosedForm (GF i om) F.energy_eq
  have hdom : E.form.domain = F.form.domain := by
    apply SetLike.coe_injective
    exact hEdom.trans ((ho i).1.trans hFdom.symm)
  have hres := hsrc i E.form.toClosedForm E.energy_eq E.gamma E.core f
  have hu : GE i om f ∈ E.form.domain := hres.1
  have hweak : ∀ w ∈ E.form.domain, E.form.form (GE i om f) w = inner ℝ f w := by
    simpa only [zero_mul, zero_add] using hres.2
  obtain ⟨sE, KE, hsE, _hsE1, hKE, hcoerE⟩ :=
    (hc i).1 E.form.toClosedForm E.energy_eq E.gamma
  obtain ⟨sF, KF, hsF, _hsF1, hKF, hcoerF⟩ :=
    (hc i).2 F.form.toClosedForm F.energy_eq F.gamma
  have hEe := aux_thm_prop_form_eq_toReal_energy E.form.toClosedForm (GE i om) E.energy_eq
  have hFe := aux_thm_prop_form_eq_toReal_energy F.form.toClosedForm (GF i om) F.energy_eq
  have hforms : ∀ w ∈ E.form.domain, F.form.form w w ≤ M * E.form.form w w := by
    intro w hw
    have hwF : w ∈ F.form.domain := hdom ▸ hw
    rw [hEe w hw, hFe w hwF]
    exact ((ho i).2 w (hEdom ▸ hw)).2
  obtain ⟨cells⟩ := hf i E F f hfs hu c hcpos
  have hsaving := aux_thm_prop_localSaving_of_fine_cells
    (centeredCube (z i) (r i) (hr i))
    (centeredCube_isBounded (z i) (hr i)).measure_lt_top.ne
    E.form F.form (GE i om) (GF i om) E.energy_eq F.energy_eq hdom E.gamma F.gamma
    E.core F.core m M hmM hM hforms f ⟨GE i om f, hu⟩ hweak sE KE sF KF
    (by linarith) hKE (by linarith) hKF hcoerE hcoerF c hcpos cells
  have huF : GE i om f ∈ F.form.domain := hdom ▸ hu
  simpa only [hEe _ hu, hFe _ huF] using hsaving

/-- Swap the represented subsequences without changing the probability law. -/
theorem aux_thm_prop_joint_swap
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) :
    in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GF GE NF NE := by
  obtain ⟨hP, hfield, hmap, hIR, hN, hS, hGN, hconv⟩ := hJoint
  refine ⟨hP, hfield, hmap, hIR, hN.symm, hS, hGN, ?_⟩
  filter_upwards [hconv] with om hom i
  exact (hom i).symm

/-- Reciprocal endpoint order for the distinct V branch. -/
theorem aux_thm_prop_order_swap
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal) :
    ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GF i om) = limitFormDomain (GE i om) ∧
      ∀ u ∈ limitFormDomain (GF i om),
        M⁻¹ * (limitFormEnergy (GF i om) u).toReal ≤ (limitFormEnergy (GE i om) u).toReal ∧
        (limitFormEnergy (GE i om) u).toReal ≤ m⁻¹ * (limitFormEnergy (GF i om) u).toReal := by
  filter_upwards [horder] with om ho i
  refine ⟨(ho i).1.symm, ?_⟩
  intro u hu
  have h := (ho i).2 u ((ho i).1.symm ▸ hu)
  exact ⟨(inv_mul_le_iff₀ hM).mpr h.2, (le_inv_mul_iff₀ hm).mpr h.1⟩

end Joint

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper

/-- The actual relative matrix concentration conclusion of `prop_conc`,
including its band approximation and the common deterministic coefficients. -/
def aux_thm_prop_concentration
    (d : ℕ) (I : Paper.in_J d) (C0 p delta0 Cp aexp : ℝ) : Prop :=
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ)
        (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr
          Sspace GN GE GF NE NF)
        (m M : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
        (horder : ∀ᵐ omega ∂P, ∀ i,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GE i omega) →
                m * (limitFormEnergy (GE i omega) u).toReal ≤
                    (limitFormEnergy (GF i omega) u).toReal ∧
                  (limitFormEnergy (GF i omega) u).toReal ≤
                    M * (limitFormEnergy (GE i omega) u).toReal)
        (zcell : SpatialCoordinates d)
        (cellIdx : ℕ → ℕ)
        (hcell : ∀ k, z (cellIdx k) = zcell ∧
          r (cellIdx k) = (3 : ℝ) ^ (-(k : ℝ)))
        (paddedIdx : ℕ → ℕ)
        (hpaddedIdx : ∀ k,
          z (paddedIdx k) = zcell ∧
          r (paddedIdx k) = 3 * ((3 : ℝ) ^ (-(k : ℝ))))
        (hPk : ∀ k : ℕ, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
        (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
        (hsymAE : ∀ k omega, (AE k omega).transpose = AE k omega)
        (hsymAF : ∀ k omega, (AF k omega).transpose = AF k omega)
        (hAE : ∀ᵐ omega ∂P, ∀ k : ℕ, ∀ pvec : Fin d → ℝ,
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity))
                (hPk k)
                (Lane4.cutoffPositiveCoefficient model H (field omega)
                  (NE j) zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity)) pvec /
                (volume
                  (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (by positivity) : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AE k omega).mulVec pvec)))
        (hAF : ∀ᵐ omega ∂P, ∀ k : ℕ, ∀ pvec : Fin d → ℝ,
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity))
                (hPk k)
                (Lane4.cutoffPositiveCoefficient model H (field omega)
                  (NF j) zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity)) pvec /
                (volume
                  (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (by positivity) : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AF k omega).mulVec pvec))),
      let ck : ℕ → ℝ := fun k =>
        ∫ omega, Matrix.trace (AF k omega) / Matrix.trace (AE k omega) ∂P
      let Bk : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ := fun k omega =>
        (Matrix.trace (AE k omega))⁻¹ •
          (AF k omega - ck k • AE k omega)
      let Band : ℕ → ℕ → MeasurableSpace Ω := fun k H =>
        ⨆ (j : ℤ) (_h : |j + (k : ℤ)| ≤ (H : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun omega : Ω => field omega j)
      (∀ k : ℕ, ck k ∈ Icc m M) ∧
      (∀ (k : ℕ) (i j : Fin d),
        ∫ omega, Bk k omega i j ∂P = 0) ∧
      (∀ k : ℕ,
        eLpNorm
            (fun omega => ∑ i : Fin d, ∑ j : Fin d, |Bk k omega i j|)
            (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cp * model.delta * (M - m))) ∧
      (∀ (k H : ℕ),
        eLpNorm
            (fun omega =>
              ∑ i : Fin d, ∑ j : Fin d,
                |Bk k omega i j -
                  ((P[fun omega => Bk k omega i j | Band k H]) omega)|)
            (ENNReal.ofReal p) P ≤
          ENNReal.ofReal
            (Cp * model.delta * (M - m) *
              (3 : ℝ) ^ (-aexp * (H : ℝ))))

/-- Choose the moment order after the spatial subdivision, so the concentration
exponent beats the all-chain entropy. The choice is independent of the endpoint
gap and of the sample. Interpolation is recovered from the existing represented
bounds at application time. Classical implication/existential distribution chooses
constants before that proof, since interpolation is a proposition of the dimension.
`prop_conc` is an upstream supplier. -/
theorem aux_thm_prop_concentration_parameters
    (d : ℕ) (hd : 2 ≤ d)
    (I : Paper.in_J d) (X : Paper.in_extension d hd I)
    (Sob : Lane4.SobolevFoundationalInput d hd)
    (MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I) (Ccamp : Lane4.CampanatoInput d)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (C0 : ℝ) (hC0 : 1 ≤ C0) (H1 : ℕ) (theta : ℝ) :
    ∃ p aexp Cp delta0 : ℝ,
      0 < p ∧ 0 < aexp ∧ 0 < Cp ∧ 0 < delta0 ∧
      2 * (2 * Real.log 2 + 1 + (48 / theta) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3 ∧
      (CubeFractionalInterpolationInput d hd →
        aux_thm_prop_concentration d I C0 p delta0 Cp aexp) := by
  classical
  have hprovider : ∃ aexp : ℝ, 0 < aexp ∧
      ∀ (_hInterp : CubeFractionalInterpolationInput d hd) (C0 : ℝ), 1 ≤ C0 →
      ∀ p : ℝ, 0 < p → ∃ delta0 Cp : ℝ, 0 < delta0 ∧ 0 < Cp ∧
        aux_thm_prop_concentration d I C0 p delta0 Cp aexp := by
    by_cases hInterp : CubeFractionalInterpolationInput d hd
    · obtain ⟨aexp, haexp, hsupplier⟩ := prop_conc d hd I X Sob MeyersMorrey Pin Ccamp hInterp hES
      exact ⟨aexp, haexp, fun _ => hsupplier⟩
    · exact ⟨1, one_pos, fun h => (hInterp h).elim⟩
  obtain ⟨aexp, haexp, hsupplier⟩ := hprovider
  let A : ℝ := 2 * Real.log 2 + 1 + (48 / theta) *
    (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)
  let p : ℝ := max 1 (2 * A / (aexp * Real.log 3))
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ha : 0 < aexp * Real.log 3 := mul_pos haexp (Real.log_pos (by norm_num))
  have hrate : 2 * A ≤ p * aexp * Real.log 3 := by
    have h := (div_le_iff₀ ha).mp (le_max_right 1 (2 * A / (aexp * Real.log 3)))
    exact h.trans_eq (mul_assoc p aexp (Real.log 3)).symm
  by_cases hInterp : CubeFractionalInterpolationInput d hd
  · obtain ⟨delta0, Cp, hdelta0, hCp, hconc⟩ := hsupplier hInterp C0 hC0 p hp
    exact ⟨p, aexp, Cp, delta0, hp, haexp, hCp, hdelta0, hrate, fun _ => hconc⟩
  · exact ⟨p, aexp, 1, 1, hp, haexp, one_pos, one_pos, hrate, fun h => (hInterp h).elim⟩

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper

/-- The actual trace-minimum and affine data on a single selected open cell. -/
structure aux_thm_prop_affine_cell
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m M : ℝ) (u : E.domain) (c : ℝ) (q : Opens (SpatialCoordinates d)) where
  variation : Submodule ℝ (DomainL2 Q)
  killedE : DirichletForm.IsKilledDomain E.toClosedForm
    (q : Set (SpatialCoordinates d))
    (variation)
  killedF : DirichletForm.IsKilledDomain F.toClosedForm
    (q : Set (SpatialCoordinates d))
    (variation)
  QE : QuadraticForm ℝ E.domain
  QF : QuadraticForm ℝ E.domain
  QE_nonneg : ∀ w, 0 ≤ QE w
  QF_nonneg : ∀ w, 0 ≤ QF w
  minimalE : ∀ (w : E.domain), IsLeast {e : ℝ | ∃ v : DomainL2 Q,
    v ∈ variation ∧ e = (GammaE.measure (w.val + v)
      (q : Set (SpatialCoordinates d))).toReal}
    (QE w)
  minimalF : ∀ (w : E.domain), IsLeast {e : ℝ | ∃ v : DomainL2 Q,
    v ∈ variation ∧ e = (GammaF.measure (w.val + v)
      (q : Set (SpatialCoordinates d))).toReal}
    (QF w)
  order : ∀ w, m * QE w ≤ QF w ∧ QF w ≤ M * QE w
  ell : E.domain
  affine_saving :
    (3 / 8 : ℝ) * (M - m) * QE (ell) ≤
      M * QE (ell) - QF (ell)
  affine_error : QE (u - ell) ≤
    ((3 / 8 : ℝ) * (1 / 8) / 16) *
      ((GammaE.measure u.val (q :
        Set (SpatialCoordinates d))).toReal +
        c * (volume (q :
          Set (SpatialCoordinates d))).toReal)

/-- Apply the mass theorem at arbitrarily late levels and attach the actual
per-cell affine data. The mesh converges to zero and the mass remains the true
energy-plus-volume measure. -/
theorem aux_thm_prop_fine_cells_of_mass
    (d : ℕ) (hd : 2 ≤ d)
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
    (E F : _root_.DirichletForm
      (volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m M : ℝ) (u : E.domain) (c : ℝ)
    (mu : Measure (SpatialCoordinates d)) [IsFiniteMeasure mu]
    (hmu : mu = GammaE.measure u.val +
      ENNReal.ofReal c • volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)))
    (hsupp : mu (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))ᶜ = 0)
    (hpositive : 0 < mu (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)))
    (H1 Mm : ℕ) (hH1 : 1 ≤ H1) (hMm : 2 ≤ Mm)
    (gamma zeta Cwidth : ℝ) (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (hzeta : 0 < zeta) (hCwidth : 0 < Cwidth)
    (hcop : Nat.Coprime Mm (3 ^ H1))
    (hMgam : (Mm : ℝ) ^ (-1 : ℝ) ≤ ((3 : ℝ) ^ H1) ^ (gamma - 1))
    (hfaces : ∀ (sigma : Fin d → Fin Mm) (n : ℕ) (i : Fin d) (k : ℤ),
      mu {x : SpatialCoordinates d | x i = aux_thm_prop_mass_shift Mm sigma i +
        aux_thm_prop_mass_side H1 n * (k : ℝ)} = 0)
    (Uset : ℕ → Prop) (hU : (1 / 2 : ℝ) ≤ Lane3.upperDensity Uset)
    (Good : (Fin d → Fin Mm) → ℕ → (Fin d → ℤ) → Prop)
    (theta epscoll : ℝ) (htheta : 0 ≤ theta) (hepscoll : 0 < epscoll)
    (hloss : theta + ((3 : ℝ) ^ H1) ^ (-zeta) +
      (2 * (d : ℝ) * (Cwidth + 2)) * ((3 : ℝ) ^ H1) ^ (gamma - 1) + epscoll ≤ 1 / 8)
    (B : (Fin d → Fin Mm) → ℝ) (hB : ∀ sigma, 0 ≤ B sigma)
    (hbad : ∀ sigma x, x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) →
      ∀ J : ℕ,
        (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧
          ¬ Good sigma n (aux_thm_prop_mass_point_idx H1 Mm sigma n x)} : ℝ) ≤
          theta * (J : ℝ) + B sigma)
    (baseMesh : ℝ) (hbase : 0 < baseMesh)
    (hlocal : ∀ (n : ℕ), 1 ≤ n → Uset n → aux_thm_prop_mass_side H1 n ≤ baseMesh →
      ∀ (sigma : Fin d → Fin Mm) (k : Fin d → ℤ),
      Good sigma n k → aux_thm_prop_mass_padded H1 Mm Cwidth gamma sigma n k →
      closure (aux_thm_prop_mass_parent H1 Mm sigma n k) ⊆
        (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) →
      (mu (aux_thm_prop_mass_parent H1 Mm sigma n k)).toReal ≤
        ((3 : ℝ) ^ H1) ^ ((d : ℝ) + zeta) * (mu (aux_thm_prop_mass_cell H1 Mm sigma n k)).toReal →
      Nonempty (aux_thm_prop_affine_cell (centeredCube zQ rQ hrQ) E F GammaE GammaF m M u c
        (centeredCube (fun i => aux_thm_prop_mass_lo H1 Mm sigma n k i +
          aux_thm_prop_mass_side H1 n / 2) (aux_thm_prop_mass_side H1 n)
          (aux_thm_prop_grid_side_pos H1 n)))) :
    Nonempty (aux_thm_prop_fine_cells (centeredCube zQ rQ hrQ) E F GammaE GammaF m M u c) := by
  classical
  have hL : 1 < (3 : ℝ) ^ H1 := one_lt_pow₀ (by norm_num) (by omega)
  have ht : Tendsto (aux_thm_prop_mass_side H1) atTop (𝓝 0) := by
    exact (tendsto_rpow_atBot_of_base_gt_one ((3 : ℝ) ^ H1) hL).comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hbase))
  have hselect (j : ℕ) := aux_thm_prop_mass_open_cells d hd H1 hH1 Mm hMm gamma hgamma
    zeta hzeta Cwidth hCwidth hcop hMgam zQ rQ hrQ mu hsupp hpositive hfaces Uset hU
    Good theta htheta epscoll hepscoll hloss B hB hbad (max j n0)
  dsimp only at hselect
  choose N hNj hN1 hNU sigma G idx hidx hmem hprops hinside hdisjoint hmass using hselect
  have hNt : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun j => (le_max_left j n0).trans (hNj j)) tendsto_id
  let cellData (j : ℕ) (i : Fin (G j).card) := Classical.choice
    (hlocal (N j) (hN1 j) (hNU j) (hn0 (N j) ((le_max_right j n0).trans (hNj j))).le
      (sigma j) (idx j i) (hprops j i).1 (hprops j i).2.1
      (hprops j i).2.2.1 (hprops j i).2.2.2)
  refine ⟨{
    count := fun j => (G j).card
    center := fun j i k => aux_thm_prop_mass_lo H1 Mm (sigma j) (N j) (idx j i) k +
      aux_thm_prop_mass_side H1 (N j) / 2
    radius := fun j _ => aux_thm_prop_mass_side H1 (N j)
    radius_pos := fun j _ => aux_thm_prop_grid_side_pos H1 (N j)
    mesh := fun j => aux_thm_prop_mass_side H1 (N j)
    mesh_pos := fun j => aux_thm_prop_grid_side_pos H1 (N j)
    mesh_tendsto := ht.comp hNt
    radius_le_mesh := fun _ _ => le_rfl
    inside := hinside
    disjoint := hdisjoint
    variation := fun j i => (cellData j i).variation
    killedE := fun j i => (cellData j i).killedE
    killedF := fun j i => (cellData j i).killedF
    QE := fun j i => (cellData j i).QE
    QF := fun j i => (cellData j i).QF
    QE_nonneg := fun j i => (cellData j i).QE_nonneg
    QF_nonneg := fun j i => (cellData j i).QF_nonneg
    minimalE := fun j i => (cellData j i).minimalE
    minimalF := fun j i => (cellData j i).minimalF
    order := fun j i => (cellData j i).order
    ell := fun j i => (cellData j i).ell
    affine_saving := fun j i => (cellData j i).affine_saving
    affine_error := fun j i => (cellData j i).affine_error
    mass := ?_ }⟩
  intro j
  simpa only [hmu] using hmass j

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Approximate the actual harmonic projection by core variations. This keeps
exact continuous boundary values while approaching the killed trace minimum. -/
theorem aux_thm_prop_trace_continuous_competitor
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (Dq : Submodule ℝ (DomainL2 Q)) (hD : DirichletForm.IsKilledDomain E q Dq)
    (hcoercive : ∃ K : ℝ, 0 < K ∧ ∀ v ∈ Dq, ‖v‖ ^ 2 ≤ K * E.form v v)
    (u : DomainL2 Q) (hu : u ∈ E.domain)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
    (hurep : ⇑u =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U)
    (T : ℝ)
    (hT : IsLeast {t : ℝ | ∃ w : DomainL2 Q, w ∈ Dq ∧
      t = (Gamma.measure (u + w) q).toReal} T)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
      (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
      (∀ x ∈ frontier q, V x = U x) ∧ (Gamma.measure v q).toReal < T + eps := by
  obtain ⟨p, hp, ho⟩ := aux_lem_replace_projection_exists E hD hcoercive u hu
  have hup : u - p ∈ E.domain := E.domain.sub_mem hu (hD.le_domain hp)
  have hmin : IsLeast {t : ℝ | ∃ w : DomainL2 Q, w ∈ Dq ∧
      t = (Gamma.measure (u + w) q).toReal}
      (Gamma.measure (u - p) q).toReal := by
    refine ⟨⟨-p, Dq.neg_mem hp, by simp [sub_eq_add_neg]⟩, ?_⟩
    rintro e ⟨w, hw, rfl⟩
    have hpw : p + w ∈ Dq := Dq.add_mem hp hw
    have hsplit := aux_lem_replace_cell_energy_split E Gamma hq hD hup hpw (ho _ hpw)
    rw [show (u - p) + (p + w) = u + w by abel] at hsplit
    rw [hsplit]
    exact le_add_of_nonneg_right (E.form_nonneg _ (hD.le_domain hpw))
  have hval : (Gamma.measure (u - p) q).toReal = T := hmin.unique hT
  obtain ⟨w, hw, hnear⟩ := hD.approx p hp eps heps
  obtain ⟨W, hW, _hcW, hsW, hwrep⟩ := hw.2
  have hpw : p - w ∈ Dq := Dq.sub_mem hp (hD.memCoreOn_mem w hw)
  have hsplit := aux_lem_replace_cell_energy_split E Gamma hq hD hup hpw (ho _ hpw)
  rw [show (u - p) + (p - w) = u - w by abel, hval] at hsplit
  refine ⟨u - w, fun x => U x - W x, E.domain.sub_mem hu hw.1,
    hU.sub hW.continuousOn, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub u w, hurep, hwrep] with x hsub hux hwx
    rw [hsub, Pi.sub_apply, hux, hwx]
  · intro x hx
    have hxq : x ∉ q := by
      simpa only [hq.interior_eq] using hx.2
    have hxW : x ∉ tsupport W := fun hh => hxq (hsW hh)
    change U x - W x = U x
    rw [image_eq_zero_of_notMem_tsupport hxW, sub_zero]
  · rw [hsplit]
    have hnorm := sq_nonneg ‖p - w‖
    unfold DirichletForm.ClosedForm.energyNormSq at hnear
    linarith

/-- The killed trace minimum equals the GLB over continuous boundary
extensions. The reverse inequality uses actual core approximation of the
harmonic projection, so no continuity of an arbitrary minimizer is assumed. -/
theorem aux_thm_prop_trace_eq_boundary_glb
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hkilled : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) Dq)
    (hcoercive : ∃ K : ℝ, 0 < K ∧ ∀ v ∈ Dq, ‖v‖ ^ 2 ≤ K * E.form v v)
    (u : DomainL2 (centeredCube zQ R hR)) (hu : u ∈ E.domain)
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hurep : ⇑u =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U)
    (b : SpatialCoordinates d → ℝ)
    (hUb : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), U x = b x)
    (T : ℝ)
    (hT : IsLeast {t : ℝ | ∃ w : DomainL2 (centeredCube zQ R hR), w ∈ Dq ∧
      t = (Gamma.measure (u + w) (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal} T)
    (Lambda : ℝ)
    (hLambda : IsGLB {e : ℝ |
      ∃ (v : DomainL2 (centeredCube zQ R hR)) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧
        ContinuousOn V (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))) ∧
        (⇑v =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), V x = b x) ∧
        e = (Gamma.measure v (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal} Lambda) :
    T = Lambda := by
  apply le_antisymm
  · exact aux_thm_prop_trace_le_boundary_glb d hd zQ zq R r hR hr hqQ E Gamma hcore Dq
      hkilled u hu U hU hurep b hUb T hT Lambda hLambda
  · apply le_of_forall_pos_le_add
    intro eps heps
    obtain ⟨v, V, hv, hV, hvrep, hVb, hbound⟩ :=
      aux_thm_prop_trace_continuous_competitor (centeredCube zQ R hR) E.toClosedForm
        Gamma _ (centeredCube zq r hr).isOpen Dq hkilled hcoercive u hu U hU hurep T hT eps heps
    exact (hLambda.1 ⟨v, V, hv, hV, hvrep,
      fun x hx => (hVb x hx).trans (hUb x hx), rfl⟩).trans hbound.le

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper



/-- Populate a selected cell from the literal boundary GLBs and affine response
saving. Both killed domains, both quadratic minima, their comparison, and the
affine-boundary domain element are constructed inside this proof. -/
theorem aux_thm_prop_affine_cell_of_boundary_estimates
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E F : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (GE GF : DomainL2 (centeredCube zQ R hR) →L[ℝ] DomainL2 (centeredCube zQ R hR))
    (hdom : E.domain = F.domain)
    (hEdom : E.domain = limitFormDomain GE) (hFdom : F.domain = limitFormDomain GF)
    (hEenergy : ∀ v ∈ E.domain, E.form v v = (limitFormEnergy GE v).toReal)
    (hFenergy : ∀ v ∈ F.domain, F.form v v = (limitFormEnergy GF v).toReal)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (horder : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v ∧ F.form v v ≤ M * E.form v v)
    (u : E.domain) (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hurep : ⇑u.val =ᵐ[volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))] U)
    (c : ℝ) (AE AF : Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ (p : Fin d → ℝ) (b : ℝ),
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube zQ R hR) E.toClosedForm GammaE
        (centeredCube zq r hr : Set (SpatialCoordinates d)) (fun x => (∑ i, p i * x i) + b))
        ((volume (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ AE.mulVec p)))
    (hAF : ∀ (p : Fin d → ℝ) (b : ℝ),
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube zQ R hR) F.toClosedForm GammaF
        (centeredCube zq r hr : Set (SpatialCoordinates d)) (fun x => (∑ i, p i * x i) + b))
        ((volume (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ AF.mulVec p)))
    (hsaving : ∀ p : Fin d → ℝ,
      (3 / 8 : ℝ) * (M - m) *
          ((volume (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal * (p ⬝ᵥ AE.mulVec p)) ≤
        M * ((volume (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ AE.mulVec p)) -
        (volume (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal * (p ⬝ᵥ AF.mulVec p))
    (happrox : ∃ pc : (Fin d → ℝ) × ℝ,
      let b := fun x => U x - ((∑ i, pc.1 i * x i) + pc.2)
      let eSet := aux_thm_prop_boundary_energy_set (centeredCube zQ R hR) E.toClosedForm GammaE
        (centeredCube zq r hr : Set (SpatialCoordinates d)) b
      ∃ Lambda : ℝ, IsGLB eSet Lambda ∧ eSet.Nonempty ∧
        Lambda ≤ ((3 / 8 : ℝ) * (1 / 8) / 16) *
          ((GammaE.measure u.val (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal +
            c * (volume (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal)) :
    Nonempty (aux_thm_prop_affine_cell (centeredCube zQ R hR) E F GammaE GammaF m M u c
      (centeredCube zq r hr)) := by
  obtain ⟨Dq, QE, QF, hDE, hDF, hQE0, hQF0, hQE, hQF, hQorder⟩ :=
    aux_thm_prop_trace_pair E F hdom GE GF hEdom hFdom hEenergy hFenergy hEcore hFcore
      GammaE GammaF m M hm hM horder _ (centeredCube zq r hr).isOpen
  obtain ⟨pc, herror⟩ := happrox
  obtain ⟨ell, L, hL, hellRep, hLb, hellError⟩ :=
    aux_thm_prop_affine_trace_approximation d hd zQ zq R r hR hr hqQ E GammaE hEcore
      Dq hDE QE hQE u U hU hurep (fun x => (∑ i, pc.1 i * x i) + pc.2)
      ((3 / 8 : ℝ) * (1 / 8) / 16)
      ((GammaE.measure u.val (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal +
        c * (volume (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal) herror
  obtain ⟨KE, hKE, hcoerE⟩ := aux_lem_replace_limit_form_coercivity GE E.toClosedForm hEdom hEenergy
  obtain ⟨KF, hKF, hcoerF⟩ := aux_lem_replace_limit_form_coercivity GF F.toClosedForm hFdom hFenergy
  have hTE := aux_thm_prop_trace_eq_boundary_glb d hd zQ zq R r hR hr hqQ E GammaE hEcore
    Dq hDE ⟨KE, hKE, fun v hv => hcoerE v (hDE.le_domain hv)⟩ ell.val ell.property
    L hL hellRep (fun x => (∑ i, pc.1 i * x i) + pc.2) hLb (QE ell) (hQE ell)
    _ (hAE pc.1 pc.2)
  have hTF := aux_thm_prop_trace_eq_boundary_glb d hd zQ zq R r hR hr hqQ F GammaF hFcore
    Dq hDF ⟨KF, hKF, fun v hv => hcoerF v (hDF.le_domain hv)⟩ ell.val (hdom ▸ ell.property)
    L hL hellRep (fun x => (∑ i, pc.1 i * x i) + pc.2) hLb (QF ell) (hQF ell)
    _ (hAF pc.1 pc.2)
  refine ⟨{
    variation := Dq
    killedE := hDE
    killedF := hDF
    QE := QE
    QF := QF
    QE_nonneg := hQE0
    QF_nonneg := hQF0
    minimalE := hQE
    minimalF := hQF
    order := hQorder
    ell := ell
    affine_saving := ?_
    affine_error := hellError }⟩
  rw [hTE, hTF]
  exact hsaving pc.1

end Paper


end


section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

theorem aux_thm_prop_biUnion_finset_image
    {J K X : Type*} [DecidableEq J] (s : Finset K) (f : K → J) (A : J → Set X) :
    (⋃ j ∈ s.image f, A j) = ⋃ k ∈ s, A (f k) := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_image]
  constructor
  · rintro ⟨j, ⟨k, hk, rfl⟩, hx⟩
    exact ⟨k, hk, hx⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨f k, ⟨k, hk, rfl⟩, hx⟩

/-- A represented root catalogue restricts to all its cells lying in any one
of its cubes; the countable grids restrict with their roots. Actual responses,
constants, trace closure and plateau coverage are retained. -/
theorem aux_thm_prop_catalogue_restrict
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (qroot : J) :
    let J' := {j : J // (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z qroot) (r qroot) (hr qroot) : Set (SpatialCoordinates d))}
    let Grid' := {g : Grid //
      (centeredCube (z (gridRoot g)) (r (gridRoot g)) (hr (gridRoot g)) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z qroot) (r qroot) (hr qroot) : Set (SpatialCoordinates d))}
    letI : DecidableEq J' := Classical.decEq J'
    conv_represented_estimates d hd M H Ω P cutoff env J' ⟨qroot, subset_rfl⟩
      (fun j => z j.val) (fun j => r j.val) (fun j => hr j.val)
      (fun j => S j.val) (fun j => D j.val) (fun j => f j.val)
      (fun j => T j.val) (fun j => theta j.val) (fun j => thetaH1 j.val)
      (fun j => usrc j.val) (fun j => srcRep j.val) (fun j => ucell j.val)
      Cext beta alpha eta t orders E Index resp respLim constants G
      (fun j => coercivityKey j.val) (fun j => extensionKey j.val) (fun j => lambdaKey j.val)
      (fun j => sourceResponseKey j.val) (fun j => sourceGrowthKey j.val)
      (fun j => sourceHolderKey j.val) (fun j => cellResponseKey j.val)
      (fun j => cellGrowthKey j.val) (fun j => cellHolderKey j.val)
      Grid' (fun g => origin g.val) (fun g => ⟨gridRoot g.val, g.property⟩) (fun g => gridKey g.val) := by
  classical
  dsimp only
  rcases hRep with ⟨hA, hAlpha, hBeta, hC, hOrders, hN, hIR, hMeas, hLaw, hSeq,
    hcontain, hrat, htri, hcomplete, hgrat, hcover, hS, hDense, hSrc, hSrcDense,
    hTrace, hSt, hParent, hTDense, hPlateau, hMeasc, hMom, hNonneg, hSol, hCoeff,
    hCoerc, hExt, hGrid, hSrcEst, hCellEst⟩
  refine ⟨hA, hAlpha, hBeta, hC, hOrders, hN, hIR, hMeas, hLaw, hSeq,
    (fun j => j.property), (fun j => hrat j.val), (fun j => htri j.val), ?_,
    (fun g => hgrat g.val), ?_, (fun j => hS j.val), (fun j => hDense j.val),
    (fun j => hSrc j.val), (fun j => hSrcDense j.val), (fun j => hTrace j.val),
    (fun j => hSt j.val), (fun j k => hParent j.val k.val), (fun j => hTDense j.val), ?_,
    hMeasc, hMom, hNonneg, (fun j => hSol j.val), (fun j => hCoeff j.val),
    (fun j => hCoerc j.val), (fun j => hExt j.val), (fun g n k j => hGrid g.val n k j.val),
    (fun j => hSrcEst j.val), (fun j => hCellEst j.val)⟩
  · intro z' r' hr' hrat' htri' hsub
    obtain ⟨j, hz, hrj⟩ := hcomplete z' r' hr' hrat' htri' (hsub.trans (hcontain qroot))
    refine ⟨⟨j, ?_⟩, hz, hrj⟩
    simpa only [hz, hrj] using hsub
  · intro j
    obtain ⟨g, hroot, horigin⟩ := hcover j.val
    refine ⟨⟨g, ?_⟩, Subtype.ext hroot, horigin⟩
    simpa only [hroot] using j.property
  · intro j s o hso ho m
    have hclosure :
        (⋃ k ∈ s.image Subtype.val,
          closure (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) =
        ⋃ k ∈ s, closure (centeredCube (z k.val) (r k.val) (hr k.val) :
          Set (SpatialCoordinates d)) :=
      aux_thm_prop_biUnion_finset_image s Subtype.val _
    have hopen :
        (⋃ k ∈ o.image Subtype.val,
          (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) =
        ⋃ k ∈ o, (centeredCube (z k.val) (r k.val) (hr k.val) :
          Set (SpatialCoordinates d)) :=
      aux_thm_prop_biUnion_finset_image o Subtype.val _
    have hso' :
        (⋃ k ∈ s.image Subtype.val,
          closure (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆
        ⋃ k ∈ o.image Subtype.val,
          (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d)) := by
      simpa only [hclosure, hopen] using hso
    have ho' : closure (⋃ k ∈ o.image Subtype.val,
        (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆
        (centeredCube (z j.val) (r j.val) (hr j.val) : Set (SpatialCoordinates d)) := by
      simpa only [hopen] using ho
    simpa only [hclosure, hopen] using hPlateau j.val (s.image Subtype.val)
      (o.image Subtype.val) hso' ho' m

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators

namespace Paper
noncomputable section

/-- The centered open cube underlying the half-open mass grid. -/
def aux_thm_prop_mass_center {d : ℕ} (H1 Mm : ℕ)
    (sigma : Fin d → Fin Mm) (n : ℕ) (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => aux_thm_prop_mass_lo H1 Mm sigma n k i + aux_thm_prop_mass_side H1 n / 2

/-- Euclidean remainder is the actual label of a child in the odd subdivision. -/
def aux_thm_prop_mass_digit {d : ℕ} (H1 : ℕ) (k : Fin d → ℤ) :
    OddGridIndex d (subdivisionHalfWidth H1) := fun i =>
  ⟨(k i % (3 ^ H1 : ℤ)).toNat, by
    rw [two_mul_subdivisionHalfWidth_add_one]
    apply (Int.toNat_lt_of_ne_zero (by positivity : (3 : ℕ) ^ H1 ≠ 0)).mpr
    exact_mod_cast Int.emod_lt_of_pos (k i) (by positivity : (0 : ℤ) < 3 ^ H1)⟩

theorem aux_thm_prop_mass_side_descendant (H1 n : ℕ) :
    descendantSide (subdivisionHalfWidth H1) n 1 = aux_thm_prop_mass_side H1 n := by
  have hL : (2 * (subdivisionHalfWidth H1 : ℝ) + 1) = (3 : ℝ) ^ H1 := by
    exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
  rw [descendantSide, hL, aux_thm_prop_mass_side, Real.rpow_neg, Real.rpow_natCast, one_div]
  positivity

theorem aux_thm_prop_mass_parent_point
    (d H1 Mm : ℕ) (hd : 2 ≤ d) (hH1 : 1 ≤ H1) (hMm : 2 ≤ Mm)
    (sigma : Fin d → Fin Mm) (n : ℕ) (x : SpatialCoordinates d) :
    aux_thm_prop_mass_point_idx H1 Mm sigma n x =
      aux_thm_prop_mass_parent_idx H1 (aux_thm_prop_mass_point_idx H1 Mm sigma (n + 1) x) := by
  have hg := lem_mass_grid_partition d H1 Mm hd hH1 hMm
  have hx := (hg.2.1 sigma (n + 1) x (aux_thm_prop_mass_point_idx H1 Mm sigma (n + 1) x)).mpr rfl
  have h := (hg.2.2.1 sigma (n + 1) (by omega) _).2 x hx
  simp only [Nat.add_sub_cancel] at h
  exact h

/-- The mass-grid parent and its Euclidean digit reproduce the exact odd-grid
center, including the fixed shift. -/
theorem aux_thm_prop_mass_child_center
    {d : ℕ} (H1 Mm n : ℕ) (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) :
    oddGridCenter
      (aux_thm_prop_mass_center H1 Mm sigma n (aux_thm_prop_mass_parent_idx H1 k))
      (aux_thm_prop_mass_side H1 n) (subdivisionHalfWidth H1) (aux_thm_prop_mass_digit H1 k) =
    aux_thm_prop_mass_center H1 Mm sigma (n + 1) k := by
  have hL : (2 * (subdivisionHalfWidth H1 : ℝ) + 1) = (3 : ℝ) ^ H1 := by
    exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
  have hLpos : 0 < (3 : ℝ) ^ H1 := by positivity
  have hs : aux_thm_prop_mass_side H1 n = (3 : ℝ) ^ H1 * aux_thm_prop_mass_side H1 (n + 1) := by
    have h := aux_lem_mass_grid_partition_side_parent ((3 : ℝ) ^ H1) hLpos (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    exact h
  have hdigit (i : Fin d) : ((aux_thm_prop_mass_digit H1 k i).val : ℤ) = k i % (3 ^ H1 : ℤ) := by
    simp only [aux_thm_prop_mass_digit, Int.toNat_of_nonneg
      (Int.emod_nonneg _ (by positivity : (3 ^ H1 : ℤ) ≠ 0))]
  have hparent (i : Fin d) : aux_thm_prop_mass_parent_idx H1 k i = k i / (3 ^ H1 : ℤ) := by
    dsimp [aux_thm_prop_mass_parent_idx]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Int.floor_intCast, Int.natCast_pow]
      using Int.floor_div_natCast (k i : ℝ) (3 ^ H1)
  have hsum (i : Fin d) : (3 : ℝ) ^ H1 * (aux_thm_prop_mass_parent_idx H1 k i : ℝ) +
      ((aux_thm_prop_mass_digit H1 k i).val : ℝ) = (k i : ℝ) := by
    have hi : (3 ^ H1 : ℤ) * aux_thm_prop_mass_parent_idx H1 k i +
        ((aux_thm_prop_mass_digit H1 k i).val : ℤ) = k i := by
      rw [hdigit, hparent]
      exact Int.mul_ediv_add_emod (k i) (3 ^ H1)
    exact_mod_cast hi
  funext i
  simp only [oddGridCenter, aux_thm_prop_mass_center, aux_thm_prop_mass_lo, hL, hs]
  rw [mul_div_cancel_left₀ _ hLpos.ne']
  have hrel := congrArg (fun y : ℝ => aux_thm_prop_mass_side H1 (n + 1) * y) (hsum i)
  have hwidth := congrArg (fun y : ℝ => aux_thm_prop_mass_side H1 (n + 1) * y) hL
  nlinarith [hwidth]

/-- Every point's nested half-open cells are one exact odd-grid branch, even
when the point lies on a grid face. -/
theorem aux_thm_prop_mass_point_branch
    (d H1 Mm : ℕ) (hd : 2 ≤ d) (hH1 : 1 ≤ H1) (hMm : 2 ≤ Mm)
    (sigma : Fin d → Fin Mm) (x : SpatialCoordinates d) (n : ℕ) :
    descendantCenter (subdivisionHalfWidth H1)
      (aux_thm_prop_mass_center H1 Mm sigma 0 (aux_thm_prop_mass_point_idx H1 Mm sigma 0 x)) 1 n
      (fun j => aux_thm_prop_mass_digit H1 (aux_thm_prop_mass_point_idx H1 Mm sigma (j.val + 1) x)) =
    aux_thm_prop_mass_center H1 Mm sigma n (aux_thm_prop_mass_point_idx H1 Mm sigma n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change oddGridCenter (descendantCenter _ _ _ n _) _ _ _ = _
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, aux_thm_prop_mass_side_descendant,
      aux_thm_prop_mass_parent_point d H1 Mm hd hH1 hMm sigma n x]
    exact aux_thm_prop_mass_child_center H1 Mm n sigma _

/-- The two index conventions used by cor_32 and lem_mass count the same bad
levels; the zero level is omitted on both sides. -/
theorem aux_thm_prop_bad_nat_eq_fin (J : ℕ) (Bad : ℕ → Prop) :
    Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧ Bad n} =
      Nat.card {j : Fin J // Bad (j.val + 1)} := by
  apply Nat.card_congr
  refine {
    toFun := fun n => ⟨⟨n.val - 1, by omega⟩, ?_⟩
    invFun := fun j => ⟨j.val.val + 1, by omega, by omega, j.property⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa only [Nat.sub_add_cancel (show 1 ≤ n.val from n.property.1)] using n.property.2.2
  · intro n
    apply Subtype.ext
    dsimp only
    omega
  · intro j
    apply Subtype.ext
    apply Fin.ext
    simp

end
end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- A chain estimate on every rooted odd tree supplies the pointwise estimate
required by mass selection. Only finitely many level-zero roots meet the target
cube, so their nonnegative allowances have one finite sum for each shift. -/
theorem aux_thm_prop_mass_bad_of_tree
    (d H1 Mm : ℕ) (hd : 2 ≤ d) (hH1 : 1 ≤ H1) (hMm : 2 ≤ Mm)
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
    (Good : ℕ → SpatialCoordinates d → Prop) (theta : ℝ)
    (hchain : ∀ (sigma : Fin d → Fin Mm) (k : Fin d → ℤ),
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ (J : ℕ) (pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1)),
          (Nat.card {j : Fin J // ¬ Good (j.val + 1)
            (descendantCenter (subdivisionHalfWidth H1)
              (aux_thm_prop_mass_center H1 Mm sigma 0 k) 1 (j.val + 1)
              (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
            theta * (J : ℝ) + B) :
    ∃ B : (Fin d → Fin Mm) → ℝ, (∀ sigma, 0 ≤ B sigma) ∧
      ∀ (sigma : Fin d → Fin Mm) (x : SpatialCoordinates d),
        x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) → ∀ J : ℕ,
        (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧
          ¬ Good n (aux_thm_prop_mass_center H1 Mm sigma n
            (aux_thm_prop_mass_point_idx H1 Mm sigma n x))} : ℝ) ≤
          theta * (J : ℝ) + B sigma := by
  classical
  choose allowance hallowance hcount using hchain
  have hgrid := lem_mass_grid_partition d H1 Mm hd hH1 hMm
  let roots (sigma : Fin d → Fin Mm) : Set (Fin d → ℤ) :=
    {k | (aux_thm_prop_mass_cell H1 Mm sigma 0 k ∩
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))).Nonempty}
  have hfinite (sigma : Fin d → Fin Mm) : (roots sigma).Finite :=
    hgrid.2.2.2.2 sigma 0 zQ rQ hrQ
  let B (sigma : Fin d → Fin Mm) : ℝ :=
    ∑ k ∈ (hfinite sigma).toFinset, allowance sigma k
  refine ⟨B, fun sigma => Finset.sum_nonneg (fun k _ => hallowance sigma k), ?_⟩
  intro sigma x hx J
  let k : Fin d → ℤ := aux_thm_prop_mass_point_idx H1 Mm sigma 0 x
  have hk : k ∈ (hfinite sigma).toFinset := by
    apply (hfinite sigma).mem_toFinset.mpr
    exact ⟨x, (hgrid.2.1 sigma 0 x k).mpr rfl, hx⟩
  have hB : allowance sigma k ≤ B sigma :=
    Finset.single_le_sum (fun k _ => hallowance sigma k) hk
  let pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1) :=
    fun j => aux_thm_prop_mass_digit H1
      (aux_thm_prop_mass_point_idx H1 Mm sigma (j.val + 1) x)
  have heq (j : Fin J) :
      descendantCenter (subdivisionHalfWidth H1)
        (aux_thm_prop_mass_center H1 Mm sigma 0 k) 1 (j.val + 1)
        (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩) =
      aux_thm_prop_mass_center H1 Mm sigma (j.val + 1)
        (aux_thm_prop_mass_point_idx H1 Mm sigma (j.val + 1) x) :=
    aux_thm_prop_mass_point_branch d H1 Mm hd hH1 hMm sigma x (j.val + 1)
  have hbound := hcount sigma k J pi
  simp only [heq] at hbound
  rw [aux_thm_prop_bad_nat_eq_fin]
  exact hbound.trans (add_le_add_right hB _)

/-- Countably many rootwise almost-sure chain statements may be used on one
common event before choosing the mass grids. The allowances remain samplewise. -/
theorem aux_thm_prop_mass_bad_of_tree_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (d H1 Mm : ℕ) (hd : 2 ≤ d) (hH1 : 1 ≤ H1) (hMm : 2 ≤ Mm)
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
    (Good : ℕ → SpatialCoordinates d → Set Ω) (theta : ℝ)
    (hchain : ∀ (sigma : Fin d → Fin Mm) (k : Fin d → ℤ),
      ∀ᵐ om ∂P, ∃ B : ℝ, 0 ≤ B ∧
        ∀ (J : ℕ) (pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1)),
          (Nat.card {j : Fin J // ¬ om ∈ Good (j.val + 1)
            (descendantCenter (subdivisionHalfWidth H1)
              (aux_thm_prop_mass_center H1 Mm sigma 0 k) 1 (j.val + 1)
              (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
            theta * (J : ℝ) + B) :
    ∀ᵐ om ∂P, ∃ B : (Fin d → Fin Mm) → ℝ, (∀ sigma, 0 ≤ B sigma) ∧
      ∀ (sigma : Fin d → Fin Mm) (x : SpatialCoordinates d),
        x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) → ∀ J : ℕ,
        (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧
          ¬ om ∈ Good n (aux_thm_prop_mass_center H1 Mm sigma n
            (aux_thm_prop_mass_point_idx H1 Mm sigma n x))} : ℝ) ≤
          theta * (J : ℝ) + B sigma := by
  have hall := ae_all_iff.mpr (fun sigma => ae_all_iff.mpr (hchain sigma))
  filter_upwards [hall] with om hom
  exact aux_thm_prop_mass_bad_of_tree d H1 Mm hd hH1 hMm zQ rQ hrQ
    (fun n z => om ∈ Good n z) theta hom

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Nullity of all cube boundaries implies nullity of the entire coordinate
planes, by a countable exhaustion of each plane by faces. -/
theorem aux_thm_prop_planes_null_of_frontiers {d : ℕ}
    (mu : Measure (SpatialCoordinates d))
    (hfront : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      mu (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0) :
    ∀ (i : Fin d) (c : ℝ), mu {x : SpatialCoordinates d | x i = c} = 0 := by
  classical
  intro i c
  letI : Nonempty (Fin d) := ⟨i⟩
  let z (n : ℕ) : SpatialCoordinates d := fun j => if j = i then c + (n + 1) else 0
  have hpos (n : ℕ) : 0 < 2 * (n + 1 : ℝ) := by positivity
  have hsub : {x : SpatialCoordinates d | x i = c} ⊆
      ⋃ n : ℕ, frontier (centeredCube (z n) (2 * (n + 1)) (hpos n) :
        Set (SpatialCoordinates d)) := by
    intro x hx
    change x i = c at hx
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change x ∈ frontier (Metric.ball (z n) (2 * (n + 1 : ℝ) / 2))
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      frontier_ball _ (by positivity : (n + 1 : ℝ) ≠ 0)]
    apply (dist_pi_eq_iff (by positivity : (0 : ℝ) < n + 1)).mpr
    have hi : dist (x i) (z n i) = (n + 1 : ℝ) := by
      simp only [z, if_pos rfl, Real.dist_eq, hx]
      rw [show c - (c + (n + 1 : ℝ)) = -(n + 1) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    refine ⟨⟨i, hi⟩, fun j => ?_⟩
    by_cases hj : j = i
    · subst j
      exact hi.le
    · simp only [z, hj, if_false, dist_zero_right, Real.norm_eq_abs]
      have hcoord : |x j| ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
      linarith
  exact measure_mono_null hsub (measure_iUnion_null (fun n => hfront (z n) _ (hpos n)))

/-- The positive volume floor preserves coordinate-face nullity. -/
theorem aux_thm_prop_floor_planes_null {d : ℕ}
    (mu : Measure (SpatialCoordinates d)) (Q : Set (SpatialCoordinates d)) (c : ℝ)
    (hplanes : ∀ (i : Fin d) (a : ℝ), mu {x : SpatialCoordinates d | x i = a} = 0) :
    ∀ (i : Fin d) (a : ℝ),
      (mu + ENNReal.ofReal c • volume.restrict Q)
        {x : SpatialCoordinates d | x i = a} = 0 := by
  intro i a
  have hvolume : (volume : Measure (SpatialCoordinates d)) {x | x i = a} = 0 :=
    Measure.pi_eval_preimage_null (μ := fun _ : Fin d => (volume : Measure ℝ))
      (measure_singleton a)
  have hrestrict : (volume.restrict Q) {x : SpatialCoordinates d | x i = a} = 0 :=
    ((Measure.restrict_apply_le _ _).trans_eq hvolume).antisymm (zero_le)
  simp only [Measure.add_apply, Measure.smul_apply, hplanes, hrestrict, smul_zero, add_zero]

/-- A bounded finite-cutoff energy family with growth exponent greater than
d-1 and the genuine energy-measure lower-cluster clause supplies all faces
needed for shifted mass selection. -/
theorem aux_thm_prop_planes_null_of_energy_clusters {d : ℕ} (hd : 2 ≤ d)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (muN : ℕ → Measure (SpatialCoordinates d)) (E0 Kg t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ)) (hKg : 0 ≤ Kg)
    (hmass : ∀ n, muN n Set.univ ≤ ENNReal.ofReal E0)
    (hsupp : ∀ n, muN n Kᶜ = 0)
    (hgrowth : ∀ n (x : SpatialCoordinates d) (s : ℝ), 0 < s → s ≤ 1 / 2 →
      muN n (Metric.ball x s) ≤ ENNReal.ofReal (Kg * s ^ t))
    (Gamma : Measure (SpatialCoordinates d))
    (hclause : ∀ (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
      nu Set.univ < ⊤ → nu Kᶜ = 0 → StrictMono sigma →
      (∀ phi : SpatialCoordinates d → ℝ, ContinuousOn phi K →
        Tendsto (fun n => ∫ x, phi x ∂(muN (sigma n))) atTop (𝓝 (∫ x, phi x ∂nu))) →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B → Gamma B ≤ nu B) :
    ∀ (i : Fin d) (a : ℝ), Gamma {x : SpatialCoordinates d | x i = a} = 0 := by
  obtain ⟨nu, sigma, _hSigma, _hFinite, _hSupp, _hConv, hdom, hfront⟩ :=
    aux_prop_boundary_cluster_generic hd K hK muN E0 Kg t ht htd hKg hmass hsupp
      hgrowth Gamma hclause id strictMono_id
  have hplanes := aux_thm_prop_planes_null_of_frontiers nu hfront
  intro i a
  apply le_antisymm _ (zero_le)
  exact (hdom _ (isClosed_eq (continuous_apply i) continuous_const).measurableSet).trans_eq
    (hplanes i a)

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- The finite-cutoff energy measures of a represented catalogue source have
uniform finite mass and the actual spatial growth exponent in the catalogue.
This uses its convergent response and bounded growth constant on the same event. -/
theorem aux_thm_prop_represented_source_measure_data
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (om : Ω) (hom : om ∈ G) (j : J) (g : D j) :
    let muN : ℕ → Measure (SpatialCoordinates d) := fun n =>
      (volume.restrict (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal
          ((Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)).val y *
            ∑ i : Fin d, ((usrc j g n om).val.2 i y) ^ 2))
    ∃ E0 Kg : ℝ, 0 ≤ E0 ∧ 0 ≤ Kg ∧
      (∀ n, muN n Set.univ ≤ ENNReal.ofReal E0) ∧
      (∀ n, muN n (closure
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))ᶜ = 0) ∧
      (∀ n (x : SpatialCoordinates d) (s : ℝ), 0 < s → s ≤ 1 / 2 →
        muN n (Metric.ball x s) ≤ ENNReal.ofReal (Kg * s ^ t)) := by
  dsimp only
  rcases hRep with ⟨hA, hAlpha, hBeta, hC, hOrders, hN, hIR, hMeas, hLaw, hSeq,
    hcontain, hrat, htri, hcomplete, hgrat, hcover, hS, hDense, hSrc, hSrcDense,
    hTrace, hSt, hParent, hTDense, hPlateau, hMeasc, hMom, hNonneg, hSol, hCoeff,
    hCoerc, hExt, hGrid, hSrcEst, hCellEst⟩
  obtain ⟨Bmass, hBmass⟩ := (hSeq.2.2.2.1 (sourceResponseKey j g) om hom).bddAbove_range
  obtain ⟨Bgrow, hBgrow⟩ := hSeq.2.2.2.2 (sourceGrowthKey j g) om hom
  let fmax : ℝ := sSup {v : ℝ | ∃ x ∈ closure
    (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)), v = |f j g x|}
  let B : ℝ := max Bgrow 0 * fmax ^ 2
  have hB : 0 ≤ B := mul_nonneg (le_max_right _ _) (sq_nonneg _)
  refine ⟨max Bmass 0, (2 : ℝ) ^ t * B, le_max_right _ _,
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hB, ?_, ?_, ?_⟩
  · intro n
    rw [aux_prop_boundary_mass_univ]
    apply ENNReal.ofReal_le_ofReal
    have hactual := (hSol j n om hom).1 g
    rw [hactual.1]
    change inverseResponse (S j) _ _ ≤ max Bmass 0
    rw [← hactual.2.2]
    exact (hBmass (Set.mem_range_self n)).trans (le_max_left _ _)
  · intro n
    exact aux_prop_boundary_supp _ _
  · intro n x s hs hs2
    have hlocal : ∀ y ∈ closure
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
        ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube (z j) (r j) (hr j) :
          Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal
            ((Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)).val y *
              ∑ i : Fin d, ((usrc j g n om).val.2 i y) ^ 2)))
          (Metric.ball y rr) ≤ ENNReal.ofReal (B * rr ^ t) := by
      intro y hy rr hrr hrr1
      refine ((hSrcEst j g n om hom).1 y hy rr hrr hrr1).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hconst : constants (sourceGrowthKey j g) n om ≤ max Bgrow 0 :=
        (le_abs_self _).trans ((hBgrow n).trans (le_max_left _ _))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconst (sq_nonneg _)) (Real.rpow_nonneg hrr.le _)
    have hglobal := aux_prop_boundary_cell_small_growth _
      (centeredCube (z j) (r j) (hr j)).isOpen _ B t hlocal x s hs (by linarith)
    convert hglobal using 1
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hs.le]
    congr 1
    ring

/-- A null-set property of energy measures is closed in the form norm.
The estimate uses the genuine cross measure and its Cauchy--Schwarz inequality. -/
theorem aux_thm_prop_energy_null_of_dense
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {mu : Measure X} (E : DirichletForm.ClosedForm mu)
    (Gamma : DirichletForm.EnergyMeasure E)
    (B : Set X) (hB : MeasurableSet B)
    (u : Lp ℝ 2 mu) (hu : u ∈ E.domain)
    (happrox : ∀ eps : ℝ, 0 < eps → ∃ v : Lp ℝ 2 mu,
      v ∈ E.domain ∧ Gamma.measure v B = 0 ∧ E.form (u - v) (u - v) < eps) :
    Gamma.measure u B = 0 := by
  apply (ENNReal.toReal_eq_toReal_iff' (Gamma.measure_ne_top hu B) ENNReal.zero_ne_top).mp
  change (Gamma.measure u B).toReal = 0
  apply le_antisymm _ ENNReal.toReal_nonneg
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨v, hv, hvnull, hsmall⟩ := happrox eps heps
  have hc : Gamma.cross u v B = 0 := by
    have hb := Gamma.abs_cross_le u hu v hv B hB
    rw [hvnull, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero] at hb
    exact abs_nonpos_iff.mp hb
  have hexp := Gamma.cross_sub_self_apply hu hv B
  rw [Gamma.cross_self (u - v) (E.domain.sub_mem hu hv) B hB,
    Gamma.cross_self u hu B hB, Gamma.cross_self v hv B hB,
    hc, hvnull, ENNReal.toReal_zero, mul_zero, sub_zero, add_zero] at hexp
  have hle := Gamma.toReal_measure_le_form (E.domain.sub_mem hu hv) B
  rw [hexp] at hle
  simpa only [zero_add] using (hle.trans hsmall.le)

/-- It suffices to prove source-measure nullity for one dense source catalogue.
No continuous representative, inverse map identity, or absolute continuity of
energy measures with respect to volume is assumed by this transport. -/
theorem aux_thm_prop_source_null_to_domain
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hGmem : ∀ f, G f ∈ E.domain)
    (hRange : ∀ v ∈ E.domain, ∀ eps : ℝ, 0 < eps →
      ∃ f0, E.energyNormSq (v - G f0) < eps)
    (hGbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ f, E.energyNormSq (G f) ≤ C * ‖f‖ ^ 2)
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (hDense : Dense (D : Set (DomainL2 (centeredCube z r hr))))
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (hnull : ∀ f : D, Gamma.measure (G f.val) B = 0) :
    ∀ u ∈ E.domain, Gamma.measure u B = 0 := by
  intro u hu
  apply aux_thm_prop_energy_null_of_dense E.toClosedForm Gamma B hB u hu
  intro eps heps
  obtain ⟨f, hf⟩ := aux_thm_prop_regularity_instance_killed_gdense d z r hr G E
    hGmem hRange hGbound D hDense u hu eps heps
  exact ⟨G f.val, hGmem _, hnull f, E.form_le_energyNormSq.trans_lt hf⟩

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- A countable diagonal extraction of actual quadratic responses supplies an
operator-norm cluster for a collectively compact symmetric positive sequence. -/
theorem aux_thm_prop_operator_cluster
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [Module ℚ V]
    (T : ℕ → V →L[ℝ] V) (D : Submodule ℚ V)
    (hDcount : (D : Set V).Countable) (hDense : Dense (D : Set V))
    (hSym : ∀ n x y, inner ℝ (T n x) y = inner ℝ x (T n y))
    (hPos : ∀ n x, 0 ≤ inner ℝ x (T n x))
    (hCompact : IsCompact (closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : V) 1))) :
    ∃ (sigma : ℕ → ℕ) (G : V →L[ℝ] V), StrictMono sigma ∧
      Tendsto (fun n => T (sigma n)) atTop (𝓝 G) ∧ IsCompactOperator G ∧
      (∀ x y, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x, 0 ≤ inner ℝ x (G x)) := by
  classical
  letI : Countable D := Set.countable_coe_iff.mpr hDcount
  obtain ⟨C, hC, hBound⟩ := exists_operatorNorm_bound_of_collectively_compact hCompact
  let q : ℕ → D → ℝ := fun n f => inner ℝ f.val (T n f.val)
  have hqbound (n : ℕ) (f : D) : q n f ∈ Icc (0 : ℝ) (C * ‖f.val‖ ^ 2) := by
    refine ⟨hPos n f.val, ?_⟩
    calc
      q n f ≤ |inner ℝ f.val (T n f.val)| := le_abs_self _
      _ ≤ ‖f.val‖ * ‖T n f.val‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖f.val‖ * (C * ‖f.val‖) :=
        mul_le_mul_of_nonneg_left
          ((T n).le_opNorm f.val |>.trans
            (mul_le_mul_of_nonneg_right (hBound n) (norm_nonneg _))) (norm_nonneg _)
      _ = C * ‖f.val‖ ^ 2 := by ring
  have hProd : IsCompact {p : D → ℝ | ∀ f, p f ∈ Icc (0 : ℝ) (C * ‖f.val‖ ^ 2)} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  obtain ⟨qlim, _hqlim, sigma, hsigma, hq⟩ := hProd.tendsto_subseq hqbound
  have hqCauchy : ∀ f ∈ (D : Set V),
      CauchySeq (fun n => inner ℝ f (T (sigma n) f)) := by
    intro f hf
    exact (((continuous_apply (⟨f, hf⟩ : D)).tendsto qlim).comp hq).cauchySeq
  have hsub : closure (⋃ n : ℕ, (T (sigma n)) '' Metric.closedBall (0 : V) 1) ⊆
      closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : V) 1) := by
    apply closure_mono
    intro y hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨sigma n, hn⟩
  obtain ⟨G, hG, _hUnique⟩ := existsUnique_limit_of_collectively_compact_quadratic_responses
    hDense (fun x hx y hy => D.add_mem hx hy)
    (fun n => hSym (sigma n)) (fun n => hPos (sigma n))
    (hCompact.of_isClosed_subset isClosed_closure hsub) hqCauchy
  exact ⟨sigma, G, hsigma, hG⟩

/-- Coercivity and the dense source catalogue produce an actual operator cluster;
no convergence or Cauchy premise is imposed on the new weighted responses. -/
theorem aux_thm_prop_response_cluster
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hInterp : CubeFractionalInterpolationInput d hd)
    (K : ℝ) (hK : 0 < K)
    (hCoercive : ∀ n (v : S.space),
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤ K * responseForm S (a n) v v)
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (hDcount : (D : Set (DomainL2 (centeredCube z r hr))).Countable)
    (hDense : Dense (D : Set (DomainL2 (centeredCube z r hr)))) :
    ∃ (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
      (sigma : ℕ → ℕ)
      (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)),
      (∀ n f, GN n f =
        (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) ∧
      StrictMono sigma ∧ Tendsto (fun n => GN (sigma n)) atTop (𝓝 G) ∧
      IsCompactOperator G ∧
      (∀ x y, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x, 0 ≤ inner ℝ x (G x)) := by
  choose GN hGN using fun n => (existsUnique_volumeResponseOperator S (a n)).exists
  have hCompact := aux_killed_inverse_mosco_compact d hd z r hr S a GN hGN
    hInterp K hK hCoercive
  have hSym : ∀ n x y, inner ℝ (GN n x) y = inner ℝ x (GN n y) := by
    intro n x y
    rw [hGN, hGN, real_inner_comm]
    exact volumeResponse_pairing_symm S (a n) y x
  have hPos : ∀ n x, 0 ≤ inner ℝ x (GN n x) := by
    intro n x
    rw [hGN]
    exact volumeResponse_pairing_nonneg S (a n) x
  obtain ⟨sigma, G, hsigma, hG⟩ := aux_thm_prop_operator_cluster GN D hDcount hDense
    hSym hPos hCompact
  exact ⟨GN, sigma, G, hGN, hsigma, hG⟩

end Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace Paper

/-- The concrete compactness, cutoff and mesh data stable under bounded positive
changes of the coefficient. These are extracted from the represented bounds. -/
structure aux_thm_prop_analytic_controls
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr)) where
  K : ℝ
  K_pos : 0 < K
  coercive : ∀ n (v : S.space),
    cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
      (fun _ : Fin 1 => v.val.1) < ⊤ ∧
    ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
      ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤ K * responseForm S (a n) v v
  interpolation : CubeFractionalInterpolationInput d hd
  sources : Submodule ℚ (DomainL2 (centeredCube z r hr))
  sources_countable : (sources : Set (DomainL2 (centeredCube z r hr))).Countable
  sources_dense : Dense (sources : Set (DomainL2 (centeredCube z r hr)))
  sources_smooth : ∀ f : sources,
    ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
      tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (f.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc
  mesh : ∀ phi : DomainL2 (centeredCube z r hr),
    (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
      tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (phi : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
    ∀ eps : ℝ, 0 < eps → ∃ w : ℕ → S.space, ∃ C : ℝ,
      (∀ n, responseForm S (a n) (w n) (w n) ≤ C) ∧
      (∀ n, ‖(w n).val.1 - phi‖ ≤ eps)
  t : ℝ
  t_lower : (d : ℝ) - 1 < t
  t_upper : t < (d : ℝ)
  cutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))


/-- Actual represented bounds supply the analytic package without strengthening
its exponent or adding a regularity premise. -/
theorem aux_thm_prop_controls_of_bounds
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (N : ℕ → ℕ)
    (hBounds : aux_in_represented_bounds_side d hd model H om z r hr S G N) :
    Nonempty (aux_thm_prop_analytic_controls d hd z r hr S
      (fun n => Lane4.cutoffPositiveCoefficient model H om (N n) z hr)) := by
  obtain ⟨K, hK, hCoerc, D, hDcount, hDense, hSmooth, hInterp⟩ :=
    aux_thm_prop_hregularity_supply hd model H om z r hr S G N hBounds
  have hmesh := aux_thm_prop_endpoint_invariance_hmesh_of_bounds_side hd model H om z r hr
    S G N hBounds
  obtain ⟨_KN, _hKN, _Kstar, _hKstar, _hfrac, _hcoer, _hInterp, t, ht, htd,
    hCutoffs, _⟩ := hBounds
  exact ⟨{
    K := K, K_pos := hK, coercive := hCoerc, interpolation := hInterp
    sources := D, sources_countable := hDcount, sources_dense := hDense
    sources_smooth := hSmooth
    mesh := hmesh
    t := t, t_lower := ht, t_upper := htd, cutoffs := hCutoffs }⟩

/-- Positive two-sided coefficient comparison transports every analytic
control, including its source-independent cutoff growth and finite meshes. -/
noncomputable def aux_thm_prop_analytic_controls_reindex_weight
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (b : ℕ → PositiveCoefficient (centeredCube z r hr)) (iota : ℕ → ℕ)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hLower : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo * (a (iota n)).val x ≤ (b n).val x)
    (hUpper : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (b n).val x ≤ hi * (a (iota n)).val x) :
    aux_thm_prop_analytic_controls d hd z r hr S b where
  K := A.K / lo
  K_pos := div_pos A.K_pos hlo
  coercive := by
    intro n v
    refine ⟨(A.coercive (iota n) v).1, ?_⟩
    exact aux_lem_weighted_cluster_weighted_coercive S (a (iota n)) (b n) lo A.K
      hlo A.K_pos.le (fun u => ‖u‖ ^ 2 +
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
            (fun _ : Fin 1 => u)).toReal) ^ 2) v
      (A.coercive (iota n) v).2
      (weightedGradientForm_mul_le _ _ hlo (hLower n) (subspaceGradient S.space v))
  interpolation := A.interpolation
  sources := A.sources
  sources_countable := A.sources_countable
  sources_dense := A.sources_dense
  sources_smooth := A.sources_smooth
  mesh := by
    intro phi hphi eps heps
    obtain ⟨w, C, hEnergy, hClose⟩ := A.mesh phi hphi eps heps
    refine ⟨fun n => w (iota n), hi * C, ?_, fun n => hClose (iota n)⟩
    intro n
    exact (aux_lem_weighted_cluster_responseForm_le_mul S (b n) (a (iota n)) hi
      (hUpper n) (w (iota n))).trans
        (mul_le_mul_of_nonneg_left (hEnergy (iota n)) hhi)
  t := A.t
  t_lower := A.t_lower
  t_upper := A.t_upper
  cutoffs := aux_lem_weighted_cluster_weighted_cutoffs z r hr A.t S a b iota hi hhi
    hUpper A.cutoffs

/-- Data supplied by the actual norm limit of a coefficient sequence. -/
structure aux_thm_prop_form_cluster
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q) where
  operatorN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q
  operatorN_eq : ∀ n f, operatorN n f =
    (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1
  sigma : ℕ → ℕ
  sigma_strict : StrictMono sigma
  operator : DomainL2 Q →L[ℝ] DomainL2 Q
  operator_tendsto : Tendsto (fun n => operatorN (sigma n)) atTop (𝓝 operator)
  symmetric : ∀ x y, inner ℝ (operator x) y = inner ℝ x (operator y)
  positive : ∀ x, 0 ≤ inner ℝ x (operator x)
  form : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))
  energy_eq : ∀ u, form.energy u = limitFormEnergy operator u
  lower : ∀ (uN : ℕ → S.space) (u : DomainL2 Q),
    (∀ f, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
    limitFormEnergy operator u ≤
      liminf (fun n => (responseForm S (a (sigma n)) (uN n) (uN n) : EReal)) atTop
  recovery : ∀ u ∈ limitFormDomain operator, ∃ w : ℕ → S.space,
    Tendsto (fun n => ((w n).val.1,
      (responseForm S (a (sigma n)) (w n) (w n) : EReal))) atTop
      (𝓝 (u, limitFormEnergy operator u))

/-- Compactness, meshes and the approved contraction rule construct a genuine
Dirichlet cluster with the weak lower bound and recovery sequences. -/
theorem aux_thm_prop_form_cluster_exists
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (hcontract : ∀ n (T : ℝ → ℝ), DirichletForm.IsNormalContraction T →
      ∀ u : S.space, ∃ v : S.space,
        ((v.val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
            (fun x => T (u.val.1 x))) ∧ responseForm S (a n) v v ≤ responseForm S (a n) u u) :
    Nonempty (aux_thm_prop_form_cluster (centeredCube z r hr) S a) := by
  obtain ⟨GN, sigma, G, hGN, hsigma, hConv, _hComp, hSym, hPos⟩ :=
    aux_thm_prop_response_cluster d hd z r hr S a A.interpolation A.K A.K_pos A.coercive
      A.sources A.sources_countable A.sources_dense
  let EN : ℕ → DomainL2 (centeredCube z r hr) → EReal := fun n u =>
    sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧
      e = (responseForm S (a (sigma n)) w w : EReal)}
  have hmesh : ∀ phi : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (phi : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∀ eps : ℝ, 0 < eps → ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n, responseForm S (a (sigma n)) (w n) (w n) ≤ C) ∧
        (∀ n, ‖(w n).val.1 - phi‖ ≤ eps) := by
    intro phi hphi eps heps
    obtain ⟨w, C, hE, hClose⟩ := A.mesh phi hphi eps heps
    exact ⟨fun n => w (sigma n), C, fun n => hE (sigma n), fun n => hClose (sigma n)⟩
  have hResult := prop_killed_inverse d hd z r hr S hS (fun n => a (sigma n))
    (fun n => hcontract (sigma n)) (fun n => GN (sigma n)) (fun n => hGN (sigma n))
    A.interpolation A.K A.K_pos (fun n => A.coercive (sigma n))
    A.sources A.sources_countable A.sources_dense A.sources_smooth
    (fun f => aux_thm_prop_response_cauchy _ G hConv f.val) EN (fun _ _ => rfl) hmesh
  have hG := aux_thm_prop_property_of_limit (fun n => GN (sigma n)) G hConv _
    (fun _ h => h.1.1) hResult
  obtain ⟨E, hE, _hNC⟩ := hG.2.2.1
  exact ⟨{
    operatorN := GN, operatorN_eq := hGN, sigma := sigma, sigma_strict := hsigma
    operator := G, operator_tendsto := hConv, symmetric := hSym, positive := hPos
    form := E, energy_eq := hE
    lower := aux_prop_killed_inverse_moscoS S (fun n => a (sigma n)) G EN
      (fun _ _ => rfl) hG.2.2.2.1.1
    recovery := hG.2.2.2.1.2 }⟩

end Paper


end

