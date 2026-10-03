module

public import SubdiffusiveProcess.Paper.lem_common_identity_step
public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.lem_borel_weights
public import SubdiffusiveProcess.Paper.lem_diff
public import SubdiffusiveProcess.Paper.thm_C0
public import SubdiffusiveProcess.Paper.optimal_endpoints
public import SubdiffusiveProcess.Paper.lem_sincos
public import SubdiffusiveProcess.Paper.common_trace_class
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane3.RelativeVariation
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

lemma aux_lem_common_energy_estimate_min_orthogonal
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    (K : DirichletForm.ClosedForm m) (D : Submodule ℝ (Lp ℝ 2 m))
    (u : Lp ℝ 2 m) (hu : u ∈ K.domain)
    (hmin : ∀ v ∈ D, K.form u u ≤ K.form (u + v) (u + v))
    (hD : D ≤ K.domain) {v : Lp ℝ 2 m} (hv : v ∈ D) :
    K.form u v = 0 := by
  have hpos := hmin v hv
  have hneg := hmin (-v) (D.neg_mem hv)
  have hcross : K.form u (-v) = -K.form u v := K.form_neg_right hu (hD hv)
  have hself : K.form (-v) (-v) = K.form v v := by
    have h := K.form_smul_left (-1 : ℝ) v (hD hv) ((-1 : ℝ) • v)
      (hD (D.smul_mem (-1 : ℝ) hv))
    rw [K.form_smul_right (-1 : ℝ) (hD hv) (hD hv)] at h
    simpa [neg_one_smul] using h
  have hnonneg : 0 ≤ K.form v v := K.form_nonneg v (hD hv)
  have htest := hmin ((-(K.form u v) / (K.form v v + 1)) • v)
    (D.smul_mem _ hv)
  rw [K.form_add_self hu (hD hv)] at hpos
  rw [K.form_add_self hu (hD (D.neg_mem hv)), hcross, hself] at hneg
  rw [K.form_add_smul_self _ hu (hD hv)] at htest
  have hden : 0 < K.form v v + 1 := by linarith
  field_simp [ne_of_gt hden] at htest
  nlinarith [htest, sq_nonneg (K.form u v)]

lemma aux_lem_common_energy_estimate_square_lower
    (x : ℝ) (hx : 1 ≤ x) : 4 ≤ (x + 1) ^ 2 := by
  nlinarith [sq_nonneg (x - 1)]

lemma aux_lem_common_energy_estimate_scale_lower
    (x y : ℝ) (hx : 1 ≤ x) (hy : 0 ≤ y) :
    2 * y ≤ (4 * (x + 1) ^ 2) * y := by
  have hfour : 4 ≤ (x + 1) ^ 2 :=
    aux_lem_common_energy_estimate_square_lower x hx
  have hc : 2 ≤ 4 * (x + 1) ^ 2 := by
    have hmul' :=
      mul_le_mul_of_nonneg_left hfour (show (0 : ℝ) ≤ 4 by norm_num)
    have hmul : 16 ≤ 4 * (x + 1) ^ 2 := by
      calc
        16 = 4 * 4 := by norm_num
        _ ≤ 4 * (x + 1) ^ 2 := hmul'
    exact le_trans (by norm_num) hmul
  simpa [add_mul] using mul_le_mul_of_nonneg_right hc hy

lemma aux_lem_common_energy_estimate_upper_square
    (x : ℝ) (hx : 1 ≤ x) : x ≤ (x + 1) ^ 2 := by
  nlinarith [sq_nonneg x]

lemma aux_lem_common_energy_estimate_le_double
    (y : ℝ) (hy : 0 ≤ y) : y ≤ 2 * y := by
  nlinarith

lemma aux_lem_common_energy_estimate_nonneg_add_one
    (x : ℝ) (hx : 1 ≤ x) : 0 ≤ x + 1 := by
  exact add_nonneg (le_trans zero_le_one hx) zero_le_one

lemma aux_lem_common_energy_estimate_sqrt_exp_le
    (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (Real.exp x) ≤ Real.exp x := by
  apply (Real.sqrt_le_iff).2
  refine ⟨Real.exp_nonneg _, ?_⟩
  have he : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  simpa [sq] using (le_mul_of_one_le_right (Real.exp_nonneg x) he)

lemma aux_lem_common_energy_estimate_power_gap
  (x : ℝ) (hx : 1 ≤ x) : x ^ 2 ≤ x ^ 10 := by
  have hx2 : 1 ≤ x ^ 2 := by
    have h := mul_self_le_mul_self (show (0 : ℝ) ≤ 1 by norm_num) hx
    simpa [pow_two] using h
  have hpow : 1 ≤ (x ^ 2) ^ 4 := one_le_pow₀ hx2
  calc
    x ^ 2 = x ^ 2 * 1 := by ring
    _ ≤ x ^ 2 * (x ^ 2) ^ 4 :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg x)
    _ = x ^ 10 := by ring

lemma aux_lem_common_energy_estimate_exp_scale_one
    (x y : ℝ) (h4 : 4 ≤ x ^ 2) (h10 : x ^ 2 ≤ x ^ 10) (hy : 0 ≤ y) :
    4 * y + 8 * x ^ 2 * y ≤ 100 * x ^ 10 * y := by
  have hc : 4 + 8 * x ^ 2 ≤ 100 * x ^ 10 := by
    nlinarith
  simpa [add_mul] using mul_le_mul_of_nonneg_right hc hy

lemma aux_lem_common_energy_estimate_exp_scale_ten
    (x y : ℝ) (h4 : 4 ≤ x ^ 2) (h10 : x ^ 2 ≤ x ^ 10) (hy : 0 ≤ y) :
    4 * y + 40 * x ^ 2 * y ≤ 100 * x ^ 10 * y := by
  have hc : 4 + 40 * x ^ 2 ≤ 100 * x ^ 10 := by
    nlinarith
  simpa [add_mul] using mul_le_mul_of_nonneg_right hc hy

lemma aux_lem_common_energy_estimate_exp_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (G : ℝ)
    (hgbound : ∀ x, |g x| ≤ G) :
    Integrable (fun x => Real.exp (g x)) μ := by
  apply Integrable.of_bound hg.exp.aestronglyMeasurable (Real.exp G)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_le_exp).2 (le_trans (le_abs_self _) (hgbound x))

lemma aux_lem_common_energy_estimate_weighted_form_eq
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E Eg : DirichletForm.ClosedForm m}
    (Gamma : DirichletForm.EnergyMeasure E)
    (Gammag : DirichletForm.EnergyMeasure Eg)
    (hdom : Eg.domain = E.domain) (g : X → ℝ) (hg : Measurable g)
    (G : ℝ) (hG : IsLUB (Set.range (fun x => |g x|)) G)
    (hweight : ∀ u ∈ E.domain, ∀ A : Set X, MeasurableSet A →
      Gammag.measure u A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure u))
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    Eg.form u u = ∫ x, Real.exp (g x) ∂(Gamma.measure u) := by
  rw [← Gammag.measure_univ u (hdom ▸ hu)]
  simpa only [Measure.restrict_univ] using
    (aux_cor_14_weighted_mass Gamma Gammag g hg G hG hu hweight
      MeasurableSet.univ)

lemma aux_lem_common_energy_estimate_signed_exp_integrable
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X)
    (g : X → ℝ) (hg : Measurable g) (G : ℝ)
    (hgbound : ∀ x, |g x| ≤ G) :
    Integrable (fun x => Real.exp (g x)) ν.toJordanDecomposition.posPart ∧
      Integrable (fun x => Real.exp (g x)) ν.toJordanDecomposition.negPart := by
  constructor
  · exact aux_lem_common_energy_estimate_exp_integrable g hg G hgbound
  · exact aux_lem_common_energy_estimate_exp_integrable g hg G hgbound

lemma aux_lem_common_energy_estimate_integral_sq_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (B : Set X) (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f)
    (K : ℝ) (hK : 0 ≤ K) (hfb : ∀ x, |f x| ≤ K) :
    Integrable (fun x => f x ^ 2) (μ.restrict B) ∧
      (∫ x in B, f x ^ 2 ∂μ) ≤ K ^ 2 * (μ B).toReal := by
  have hf2 : Integrable (fun x => f x ^ 2) (μ.restrict B) := by
    apply (integrable_const (K ^ 2)).mono (hf.pow_const 2).aestronglyMeasurable
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_pow]
    have hs := (sq_le_sq₀ (abs_nonneg (f x)) hK).2 (hfb x)
    simpa [abs_sq] using hs
  constructor
  · exact hf2
  · have hpoint : (fun x => f x ^ 2) ≤ (fun _ => K ^ 2) := by
      intro x
      have hs := (sq_le_sq₀ (abs_nonneg (f x)) hK).2 (hfb x)
      simpa [abs_sq] using hs
    have hi := integral_mono hf2 (integrable_const _) hpoint
    calc
      (∫ x in B, f x ^ 2 ∂μ) ≤ ∫ _x in B, K ^ 2 ∂μ := hi
      _ = K ^ 2 * (μ B).toReal := by
        rw [integral_const, measureReal_def, smul_eq_mul]
        simp [Measure.restrict_apply, hB, mul_comm]

lemma aux_lem_common_energy_estimate_signedIntegralOn_bounded
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X)
    (B : Set X) (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f)
    (K : ℝ) (hK : 0 ≤ K) (hfb : ∀ x, |f x| ≤ K) :
    |DirichletForm.signedIntegralOn ν B f| ≤ K * (ν.totalVariation B).toReal := by
  let p := ν.toJordanDecomposition.posPart
  let n := ν.toJordanDecomposition.negPart
  have hfp : Integrable f (p.restrict B) := by
    apply (integrable_const K).mono hf.aestronglyMeasurable
    filter_upwards [] with x
    simpa [Real.norm_eq_abs, abs_of_nonneg hK] using hfb x
  have hfn : Integrable f (n.restrict B) := by
    apply (integrable_const K).mono hf.aestronglyMeasurable
    filter_upwards [] with x
    simpa [Real.norm_eq_abs, abs_of_nonneg hK] using hfb x
  have hp : ‖∫ x in B, f x ∂p‖ ≤ K * (p B).toReal := by
    calc
      ‖∫ x in B, f x ∂p‖ ≤ ∫ x in B, ‖f x‖ ∂p :=
        norm_integral_le_integral_norm f
      _ ≤ ∫ _x in B, K ∂p := by
        apply integral_mono hfp.norm (integrable_const _)
        intro x
        simpa [Real.norm_eq_abs, abs_of_nonneg hK] using hfb x
      _ = K * (p B).toReal := by
        rw [integral_const, measureReal_def, smul_eq_mul]
        simp [Measure.restrict_apply, mul_comm]
  have hn : ‖∫ x in B, f x ∂n‖ ≤ K * (n B).toReal := by
    calc
      ‖∫ x in B, f x ∂n‖ ≤ ∫ x in B, ‖f x‖ ∂n :=
        norm_integral_le_integral_norm f
      _ ≤ ∫ _x in B, K ∂n := by
        apply integral_mono hfn.norm (integrable_const _)
        intro x
        simpa [Real.norm_eq_abs, abs_of_nonneg hK] using hfb x
      _ = K * (n B).toReal := by
        rw [integral_const, measureReal_def, smul_eq_mul]
        simp [Measure.restrict_apply, mul_comm]
  have htop_p : p B ≠ ⊤ := measure_ne_top p B
  have htop_n : n B ≠ ⊤ := measure_ne_top n B
  have htv : (ν.totalVariation B).toReal = (p B).toReal + (n B).toReal := by
    rw [SignedMeasure.totalVariation, Measure.add_apply,
      ENNReal.toReal_add htop_p htop_n]
  change |(∫ x in B, f x ∂p) - ∫ x in B, f x ∂n| ≤ _
  calc
    |(∫ x in B, f x ∂p) - ∫ x in B, f x ∂n| ≤
        |∫ x in B, f x ∂p| + |∫ x in B, f x ∂n| := abs_sub _ _
    _ ≤ K * (p B).toReal + K * (n B).toReal :=
      add_le_add (by simpa [Real.norm_eq_abs] using hp) (by simpa [Real.norm_eq_abs] using hn)
    _ = K * (ν.totalVariation B).toReal := by rw [htv]; ring

lemma aux_lem_common_energy_estimate_signedIntegralOn_neg
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) (B : Set X)
    (f : X → ℝ) :
    DirichletForm.signedIntegralOn (-ν) B f =
      -DirichletForm.signedIntegralOn ν B f := by
  simp only [DirichletForm.signedIntegralOn,
    SignedMeasure.toJordanDecomposition_neg,
    MeasureTheory.JordanDecomposition.neg_posPart,
    MeasureTheory.JordanDecomposition.neg_negPart, integral_neg]
  ring

lemma aux_lem_common_energy_estimate_final_bound
    (Ez Dtar Sg Mc m G Del EwB EuB : ℝ)
    (hcommon :
      Ez ≤ 3 * (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2 * EwB +
        (Sg ^ 2 * Real.exp (2 * Sg) +
          10 * Sg ^ 2 * Real.exp (10 * Sg)) * Del ^ 2 * EuB) /
        (m * Real.exp (-2 * G)) ^ 2)
    (hnumA : 3 / (m * Real.exp (-2 * G)) ^ 2 *
        (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2) ≤ Dtar)
    (hnumB : 3 / (m * Real.exp (-2 * G)) ^ 2 *
        (Sg ^ 2 * Real.exp (2 * Sg) +
          10 * Sg ^ 2 * Real.exp (10 * Sg)) ≤ Dtar)
    (hEwB : 0 ≤ EwB) (hEuB : 0 ≤ EuB) (hDel : 0 ≤ Del) :
    Ez ≤ Dtar * (EwB + Del ^ 2 * EuB) := by
  calc
    Ez ≤ 3 * (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2 * EwB +
        (Sg ^ 2 * Real.exp (2 * Sg) +
          10 * Sg ^ 2 * Real.exp (10 * Sg)) * Del ^ 2 * EuB) /
        (m * Real.exp (-2 * G)) ^ 2 := hcommon
    _ = (3 / (m * Real.exp (-2 * G)) ^ 2) *
        (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2 * EwB +
          (Sg ^ 2 * Real.exp (2 * Sg) +
            10 * Sg ^ 2 * Real.exp (10 * Sg)) * Del ^ 2 * EuB) := by ring
    _ ≤ Dtar * EwB + Dtar * (Del ^ 2 * EuB) := by
      have h1 := mul_le_mul_of_nonneg_right hnumA hEwB
      have h2 := mul_le_mul_of_nonneg_right hnumB
        (mul_nonneg (sq_nonneg Del) hEuB)
      have h := add_le_add h1 h2
      convert h using 1 <;> ring
    _ = _ := by ring

lemma aux_lem_common_energy_estimate_finish
    (C0 m M G EwB EuB Ez Ev : ℝ)
    (hC0 : 1 ≤ C0) (hm : 0 < m) (hmLower : C0⁻¹ ≤ m)
    (hmM : m ≤ M) (hM : M ≤ C0)
    (hG : 0 ≤ G) (hDel : 0 ≤ M - m)
    (hEwB : 0 ≤ EwB) (hEuB : 0 ≤ EuB) (hEz : 0 ≤ Ez) (hEv : 0 ≤ Ev)
    (hEuler :
      m * Real.exp (-2 * G) * Ez ≤
        G * Real.exp G * M * Real.sqrt (Real.exp G) * Real.sqrt EwB * Real.sqrt Ez +
          G * Real.exp G * (M - m) * Real.sqrt (Real.exp G) * Real.sqrt EuB * Real.sqrt Ez +
          (M - m) * Real.exp (2 * G) * Real.sqrt Ev * Real.sqrt Ez)
    (hEvE : Ev ≤ 3 * G ^ 2 * Real.exp (4 * G) * EuB) :
    Ez ≤ 100 * (C0 + 1) ^ 10 * G ^ 2 *
      Real.exp (100 * (C0 + 1) ^ 10 * G) * (EwB + (M - m) ^ 2 * EuB) := by
  let Sg : ℝ := 4 * (C0 + 1) ^ 2 * G
  let Mc : ℝ := C0 + 1
  let EvArg : ℝ := Real.exp (4 * G) * Ev
  have hA2 : 0 ≤ (C0 + 1) ^ 2 := sq_nonneg (C0 + 1)
  have hA2four : 4 ≤ (C0 + 1) ^ 2 :=
    aux_lem_common_energy_estimate_square_lower C0 hC0
  have hSg : 0 ≤ Sg := by
    dsimp [Sg]
    exact mul_nonneg (mul_nonneg (by norm_num) hA2) hG
  have hSgG : 2 * G ≤ Sg := by
    dsimp [Sg]
    exact aux_lem_common_energy_estimate_scale_lower C0 G hC0 hG
  have hGSg : G ≤ Sg := le_trans
    (aux_lem_common_energy_estimate_le_double G hG) hSgG
  have hMc : 0 ≤ Mc := by
    change 0 ≤ C0 + 1
    exact aux_lem_common_energy_estimate_nonneg_add_one C0 hC0
  have hM_Mc : M ≤ Mc := by
    dsimp [Mc]
    exact le_trans hM (le_add_of_nonneg_right zero_le_one)
  have hSqrtExp : Real.sqrt (Real.exp G) ≤ Real.exp G :=
    aux_lem_common_energy_estimate_sqrt_exp_le G hG
  have hcoef : G * Real.exp G * Real.sqrt (Real.exp G) ≤ Sg * Real.exp Sg := by
    have he : Real.exp (2 * G) ≤ Real.exp Sg := Real.exp_le_exp.mpr hSgG
    calc
      G * Real.exp G * Real.sqrt (Real.exp G) ≤
          G * Real.exp G * Real.exp G :=
        mul_le_mul_of_nonneg_left hSqrtExp (mul_nonneg hG (Real.exp_nonneg _))
      _ = G * Real.exp (2 * G) := by
        calc
          G * Real.exp G * Real.exp G = G * (Real.exp G * Real.exp G) := by ring
          _ = G * Real.exp (2 * G) := by
            rw [← Real.exp_add]
            congr 1 <;> ring
      _ ≤ Sg * Real.exp (2 * G) :=
        mul_le_mul_of_nonneg_right hGSg (Real.exp_nonneg _)
      _ ≤ Sg * Real.exp Sg := mul_le_mul_of_nonneg_left he hSg
  have hcoefM : G * Real.exp G * M * Real.sqrt (Real.exp G) ≤
      Sg * Real.exp Sg * Mc := by
    calc
      G * Real.exp G * M * Real.sqrt (Real.exp G) =
          (G * Real.exp G * Real.sqrt (Real.exp G)) * M := by ring
      _ ≤ (Sg * Real.exp Sg) * M :=
        mul_le_mul_of_nonneg_right hcoef (le_trans (le_of_lt hm) hmM)
      _ ≤ (Sg * Real.exp Sg) * Mc :=
        mul_le_mul_of_nonneg_left hM_Mc (by positivity)
      _ = Sg * Real.exp Sg * Mc := by ring
  have hcoefDel : G * Real.exp G * (M - m) * Real.sqrt (Real.exp G) ≤
      Sg * Real.exp Sg * (M - m) := by
    calc
      G * Real.exp G * (M - m) * Real.sqrt (Real.exp G) =
          (G * Real.exp G * Real.sqrt (Real.exp G)) * (M - m) := by ring
      _ ≤ (Sg * Real.exp Sg) * (M - m) :=
        mul_le_mul_of_nonneg_right hcoef hDel
      _ = Sg * Real.exp Sg * (M - m) := by ring
  have hSqrtEvArg : Real.sqrt EvArg = Real.exp (2 * G) * Real.sqrt Ev := by
    dsimp [EvArg]
    rw [Real.sqrt_mul (Real.exp_nonneg (4 * G))]
    have he : Real.sqrt (Real.exp (4 * G)) = Real.exp (2 * G) := by
      apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_nonneg (4 * G))
        (Real.exp_nonneg (2 * G))).2
      rw [← Real.exp_add]
      congr 1 <;> ring
    rw [he]
  have hEuler' :
      (m * Real.exp (-2 * G)) * Ez ≤
        (Sg * Real.exp Sg * Mc * Real.sqrt EwB +
          Sg * Real.exp Sg * (M - m) * Real.sqrt EuB +
          (M - m) * Real.sqrt EvArg) * Real.sqrt Ez := by
    calc
      _ ≤ (G * Real.exp G * M * Real.sqrt (Real.exp G) * Real.sqrt EwB) * Real.sqrt Ez +
          (G * Real.exp G * (M - m) * Real.sqrt (Real.exp G) * Real.sqrt EuB) * Real.sqrt Ez +
          ((M - m) * Real.exp (2 * G) * Real.sqrt Ev) * Real.sqrt Ez := by
        simpa [mul_assoc] using hEuler
      _ ≤ (Sg * Real.exp Sg * Mc * Real.sqrt EwB) * Real.sqrt Ez +
          (Sg * Real.exp Sg * (M - m) * Real.sqrt EuB) * Real.sqrt Ez +
          ((M - m) * Real.sqrt EvArg) * Real.sqrt Ez := by
        have h1 :
            (G * Real.exp G * M * Real.sqrt (Real.exp G) * Real.sqrt EwB) *
                Real.sqrt Ez ≤
              (Sg * Real.exp Sg * Mc * Real.sqrt EwB) * Real.sqrt Ez :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoefM (Real.sqrt_nonneg EwB))
            (Real.sqrt_nonneg Ez)
        have h2 :
            (G * Real.exp G * (M - m) * Real.sqrt (Real.exp G) * Real.sqrt EuB) *
                Real.sqrt Ez ≤
              (Sg * Real.exp Sg * (M - m) * Real.sqrt EuB) * Real.sqrt Ez :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoefDel (Real.sqrt_nonneg EuB))
            (Real.sqrt_nonneg Ez)
        have h3 : ((M - m) * Real.exp (2 * G) * Real.sqrt Ev) * Real.sqrt Ez ≤
            ((M - m) * Real.sqrt EvArg) * Real.sqrt Ez := by
          rw [hSqrtEvArg]
          convert le_rfl using 1 <;> ring
        exact add_le_add (add_le_add h1 h2) h3
      _ = _ := by ring
  have hEvArg0 : 0 ≤ EvArg := by
    dsimp [EvArg]
    exact mul_nonneg (Real.exp_nonneg _) hEv
  have hSg_sq : G ^ 2 ≤ Sg ^ 2 := (sq_le_sq₀ hG hSg).2 hGSg
  have hExpEv : EvArg ≤ 3 * G ^ 2 * Real.exp (8 * G) * EuB := by
    dsimp [EvArg]
    calc
      Real.exp (4 * G) * Ev ≤
          Real.exp (4 * G) * (3 * G ^ 2 * Real.exp (4 * G) * EuB) :=
        mul_le_mul_of_nonneg_left hEvE (Real.exp_nonneg _)
      _ = 3 * G ^ 2 * Real.exp (8 * G) * EuB := by
        calc
          Real.exp (4 * G) * (3 * G ^ 2 * Real.exp (4 * G) * EuB) =
              3 * G ^ 2 * (Real.exp (4 * G) * Real.exp (4 * G)) * EuB := by ring
          _ = 3 * G ^ 2 * Real.exp (8 * G) * EuB := by
            rw [← Real.exp_add]
            congr 1 <;> ring
  have hExpEvCoeff : 3 * G ^ 2 * Real.exp (8 * G) ≤
      10 * Sg ^ 2 * Real.exp (10 * Sg) := by
    have he : Real.exp (8 * G) ≤ Real.exp (10 * Sg) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hSgG, hG]
    calc
      3 * G ^ 2 * Real.exp (8 * G) ≤ 3 * Sg ^ 2 * Real.exp (8 * G) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSg_sq (by positivity)) (Real.exp_nonneg _)
      _ ≤ 10 * Sg ^ 2 * Real.exp (8 * G) := by
        calc
          3 * Sg ^ 2 * Real.exp (8 * G) =
              (3 * Sg ^ 2) * Real.exp (8 * G) := by ring
          _ ≤ (10 * Sg ^ 2) * Real.exp (8 * G) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 10) (sq_nonneg Sg))
              (Real.exp_nonneg _)
          _ = _ := by ring
      _ ≤ 10 * Sg ^ 2 * Real.exp (10 * Sg) :=
        mul_le_mul_of_nonneg_left he (by positivity)
  have hEvArg_le : EvArg ≤ 10 * Sg ^ 2 * Real.exp (10 * Sg) * EuB := by
    calc
      EvArg ≤ 3 * G ^ 2 * Real.exp (8 * G) * EuB := hExpEv
      _ ≤ 10 * Sg ^ 2 * Real.exp (10 * Sg) * EuB :=
        mul_le_mul_of_nonneg_right hExpEvCoeff hEuB
  have hcommon := SubdiffusiveProcess.Lane3.common_potential_change_energy_bound
    (10 : ℝ) (m * Real.exp (-2 * G)) Mc (M - m) Sg Ez EwB EuB EvArg
    (mul_pos hm (Real.exp_pos _)) hDel hSg hEz hEwB hEuB hEvArg0
    (by norm_num) hMc hEuler' hEvArg_le
  have hmSq : (C0⁻¹) ^ 2 ≤ m ^ 2 :=
    pow_le_pow_left₀ (by positivity) hmLower 2
  have hinvM : 1 / m ^ 2 ≤ C0 ^ 2 := by
    calc
      1 / m ^ 2 ≤ 1 / (C0⁻¹) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) hmSq
      _ = C0 ^ 2 := by field_simp
  have hinvEff : 1 / (m * Real.exp (-2 * G)) ^ 2 ≤ C0 ^ 2 * Real.exp (4 * G) := by
    have he : 1 / (m * Real.exp (-2 * G)) ^ 2 =
        (1 / m ^ 2) * Real.exp (4 * G) := by
      field_simp
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      have he0 : -(2 * G) + -(2 * G) + G * 4 = 0 := by ring
      rw [he0, Real.exp_zero]
    rw [he]
    exact mul_le_mul_of_nonneg_right hinvM (Real.exp_nonneg _)
  let Ct : ℝ := 100 * (C0 + 1) ^ 10
  let Dtar : ℝ := Ct * G ^ 2 * Real.exp (Ct * G)
  have hA10 : (C0 + 1) ^ 2 ≤ (C0 + 1) ^ 10 := by
    exact aux_lem_common_energy_estimate_power_gap (C0 + 1)
      (le_trans hC0 (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)))
  have hSgCt : 4 * G + 2 * Sg ≤ Ct * G := by
    dsimp [Sg, Ct]
    convert aux_lem_common_energy_estimate_exp_scale_one (C0 + 1) G
      hA2four hA10 hG using 1 <;> ring
  have hSgCt' : 4 * G + 10 * Sg ≤ Ct * G := by
    dsimp [Sg, Ct]
    convert aux_lem_common_energy_estimate_exp_scale_ten (C0 + 1) G
      hA2four hA10 hG using 1 <;> ring
  have hcoefA :
      3 * C0 ^ 2 * Real.exp (4 * G) *
          (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2) ≤ Dtar := by
    have he : Real.exp (4 * G) * Real.exp (2 * Sg) ≤ Real.exp (Ct * G) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hSgCt
    have hc : 3 * C0 ^ 2 * Sg ^ 2 * Mc ^ 2 ≤ Ct * G ^ 2 := by
      have hC0sq : C0 ^ 2 ≤ (C0 + 1) ^ 2 := by
        apply (sq_le_sq₀ (le_trans zero_le_one hC0)
          (aux_lem_common_energy_estimate_nonneg_add_one C0 hC0)).2
        exact le_add_of_nonneg_right zero_le_one
      have hA8 : (C0 + 1) ^ 8 ≤ (C0 + 1) ^ 10 :=
        pow_le_pow_right₀
          (le_trans hC0 (le_add_of_nonneg_right zero_le_one)) (by norm_num)
      have hi : 48 * C0 ^ 2 * (C0 + 1) ^ 6 ≤
          100 * (C0 + 1) ^ 10 := by
        calc
          48 * C0 ^ 2 * (C0 + 1) ^ 6 ≤
              48 * (C0 + 1) ^ 2 * (C0 + 1) ^ 6 := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hC0sq (by norm_num)) (by positivity)
          _ = 48 * (C0 + 1) ^ 8 := by ring
          _ ≤ 100 * (C0 + 1) ^ 8 :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ ≤ 100 * (C0 + 1) ^ 10 :=
            mul_le_mul_of_nonneg_left hA8 (by norm_num)
      dsimp [Sg, Mc, Ct]
      calc
        3 * C0 ^ 2 * (4 * (C0 + 1) ^ 2 * G) ^ 2 * (C0 + 1) ^ 2 =
            (48 * C0 ^ 2 * (C0 + 1) ^ 6) * G ^ 2 := by ring
        _ ≤ (100 * (C0 + 1) ^ 10) * G ^ 2 :=
          mul_le_mul_of_nonneg_right hi (sq_nonneg G)
    calc
      3 * C0 ^ 2 * Real.exp (4 * G) *
          (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2) =
          (3 * C0 ^ 2 * Sg ^ 2 * Mc ^ 2) *
            (Real.exp (4 * G) * Real.exp (2 * Sg)) := by ring
      _ ≤ (Ct * G ^ 2) * Real.exp (Ct * G) :=
        mul_le_mul hc he (by positivity) (by positivity)
      _ = Dtar := by rfl
  have hcoefB :
      3 * C0 ^ 2 * Real.exp (4 * G) *
          (Sg ^ 2 * Real.exp (2 * Sg) +
            10 * Sg ^ 2 * Real.exp (10 * Sg)) ≤ Dtar := by
    have he1 : Real.exp (4 * G) * Real.exp (2 * Sg) ≤ Real.exp (Ct * G) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hSgCt
    have he2 : Real.exp (4 * G) * Real.exp (10 * Sg) ≤ Real.exp (Ct * G) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hSgCt'
    have hC0sq : C0 ^ 2 ≤ (C0 + 1) ^ 2 := by
      apply (sq_le_sq₀ (le_trans zero_le_one hC0)
        (aux_lem_common_energy_estimate_nonneg_add_one C0 hC0)).2
      exact le_add_of_nonneg_right zero_le_one
    have hA4 : 16 ≤ (C0 + 1) ^ 4 := by
      have hh : (4 : ℝ) ^ 2 ≤ ((C0 + 1) ^ 2) ^ 2 :=
        (sq_le_sq₀ (by norm_num) (by positivity)).2 hA2four
      calc
        16 = (4 : ℝ) ^ 2 := by norm_num
        _ ≤ ((C0 + 1) ^ 2) ^ 2 := hh
        _ = (C0 + 1) ^ 4 := by ring
    have hA6 : (C0 + 1) ^ 6 ≤ (C0 + 1) ^ 10 :=
      pow_le_pow_right₀
        (le_trans hC0 (le_add_of_nonneg_right zero_le_one)) (by norm_num)
    have hcB : 3 * C0 ^ 2 * Sg ^ 2 + 30 * C0 ^ 2 * Sg ^ 2 ≤ Ct * G ^ 2 := by
      have hi : 528 * C0 ^ 2 * (C0 + 1) ^ 4 ≤
          100 * (C0 + 1) ^ 10 := by
        have hi' : 528 * (C0 + 1) ^ 6 ≤
            100 * (C0 + 1) ^ 10 := by
          have hc : 528 ≤ 100 * (C0 + 1) ^ 4 := by
            have hh := mul_le_mul_of_nonneg_left hA4 (show (0 : ℝ) ≤ 100 by norm_num)
            exact le_trans (by norm_num) hh
          calc
            528 * (C0 + 1) ^ 6 ≤
                (100 * (C0 + 1) ^ 4) * (C0 + 1) ^ 6 :=
              mul_le_mul_of_nonneg_right hc (by positivity)
            _ = 100 * (C0 + 1) ^ 10 := by ring
        calc
          528 * C0 ^ 2 * (C0 + 1) ^ 4 ≤
              528 * (C0 + 1) ^ 2 * (C0 + 1) ^ 4 := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hC0sq (by norm_num)) (by positivity)
          _ = 528 * (C0 + 1) ^ 6 := by ring
          _ ≤ 100 * (C0 + 1) ^ 10 := hi'
      dsimp [Sg, Ct]
      calc
        3 * C0 ^ 2 * (4 * (C0 + 1) ^ 2 * G) ^ 2 +
            30 * C0 ^ 2 * (4 * (C0 + 1) ^ 2 * G) ^ 2 =
            (528 * C0 ^ 2 * (C0 + 1) ^ 4) * G ^ 2 := by ring
        _ ≤ (100 * (C0 + 1) ^ 10) * G ^ 2 :=
          mul_le_mul_of_nonneg_right hi (sq_nonneg G)
    calc
      3 * C0 ^ 2 * Real.exp (4 * G) *
          (Sg ^ 2 * Real.exp (2 * Sg) +
            10 * Sg ^ 2 * Real.exp (10 * Sg)) =
          (3 * C0 ^ 2 * Sg ^ 2) *
              (Real.exp (4 * G) * Real.exp (2 * Sg)) +
            (30 * C0 ^ 2 * Sg ^ 2) *
              (Real.exp (4 * G) * Real.exp (10 * Sg)) := by ring
      _ ≤ (3 * C0 ^ 2 * Sg ^ 2 + 30 * C0 ^ 2 * Sg ^ 2) *
            Real.exp (Ct * G) := by
        calc
          _ ≤ (3 * C0 ^ 2 * Sg ^ 2) * Real.exp (Ct * G) +
              (30 * C0 ^ 2 * Sg ^ 2) * Real.exp (Ct * G) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left he1 (by positivity))
              (mul_le_mul_of_nonneg_left he2 (by positivity))
          _ = _ := by ring
      _ ≤ Dtar := by
        exact mul_le_mul hcB (le_refl _) (by positivity) (by positivity)
  have hnumA :
      3 / (m * Real.exp (-2 * G)) ^ 2 *
          (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2) ≤ Dtar := by
    calc
      _ = (3 / (m * Real.exp (-2 * G)) ^ 2) *
          (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2) := by rfl
      _ ≤ (3 * C0 ^ 2 * Real.exp (4 * G)) *
          (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2) :=
        by
          have hs : 3 / (m * Real.exp (-2 * G)) ^ 2 ≤
              3 * C0 ^ 2 * Real.exp (4 * G) := by
            calc
              3 / (m * Real.exp (-2 * G)) ^ 2 =
                  3 * (1 / (m * Real.exp (-2 * G)) ^ 2) := by ring
              _ ≤ 3 * (C0 ^ 2 * Real.exp (4 * G)) :=
                mul_le_mul_of_nonneg_left hinvEff (by norm_num)
              _ = _ := by ring
          exact mul_le_mul_of_nonneg_right hs (by positivity)
      _ ≤ Dtar := hcoefA
  have hnumB :
      3 / (m * Real.exp (-2 * G)) ^ 2 *
          (Sg ^ 2 * Real.exp (2 * Sg) +
            10 * Sg ^ 2 * Real.exp (10 * Sg)) ≤ Dtar := by
    calc
      _ = (3 / (m * Real.exp (-2 * G)) ^ 2) *
          (Sg ^ 2 * Real.exp (2 * Sg) +
            10 * Sg ^ 2 * Real.exp (10 * Sg)) := by rfl
      _ ≤ (3 * C0 ^ 2 * Real.exp (4 * G)) *
          (Sg ^ 2 * Real.exp (2 * Sg) +
            10 * Sg ^ 2 * Real.exp (10 * Sg)) :=
        by
          have hs : 3 / (m * Real.exp (-2 * G)) ^ 2 ≤
              3 * C0 ^ 2 * Real.exp (4 * G) := by
            calc
              3 / (m * Real.exp (-2 * G)) ^ 2 =
                  3 * (1 / (m * Real.exp (-2 * G)) ^ 2) := by ring
              _ ≤ 3 * (C0 ^ 2 * Real.exp (4 * G)) :=
                mul_le_mul_of_nonneg_left hinvEff (by norm_num)
              _ = _ := by ring
          exact mul_le_mul_of_nonneg_right hs (by positivity)
      _ ≤ Dtar := hcoefB
  exact aux_lem_common_energy_estimate_final_bound Ez Dtar Sg Mc m G (M - m)
    EwB EuB hcommon hnumA hnumB hEwB hEuB hDel
  /-
  calc
    Ez ≤ 3 * (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2 * EwB +
        (Sg ^ 2 * Real.exp (2 * Sg) +
          10 * Sg ^ 2 * Real.exp (10 * Sg)) * (M - m) ^ 2 * EuB) /
        (m * Real.exp (-2 * G)) ^ 2 := hcommon
    _ = (3 / (m * Real.exp (-2 * G)) ^ 2) *
        (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2 * EwB +
          (Sg ^ 2 * Real.exp (2 * Sg) +
            10 * Sg ^ 2 * Real.exp (10 * Sg)) * (M - m) ^ 2 * EuB) := by ring
    _ ≤ Dtar * EwB + Dtar * ((M - m) ^ 2 * EuB) := by
      have h1 := mul_le_mul_of_nonneg_right hnumA hEwB
      have h2 := mul_le_mul_of_nonneg_right hnumB
        (mul_nonneg (sq_nonneg (M - m)) hEuB)
      nlinarith
    _ = _ := by ring
  -/
lemma aux_lem_common_energy_estimate_weighted_variation_energy
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E Eg : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E) (hdomEg : Eg.domain = E.domain)
    (u v : DomainL2 Q) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (G : ℝ) (hGnonneg : 0 ≤ G) (hgbound : ∀ x, |g x| ≤ G)
    (hlower : Real.exp (-G) * E.form v v ≤ Eg.form v v)
    (hEuler : Eg.form v v = -DirichletForm.signedIntegralOn
      (GammaE.cross u v) B (fun x => Real.exp (g x) - 1)) :
    Eg.form v v ≤ 3 * G ^ 2 * Real.exp (4 * G) *
      (GammaE.measure u B).toReal := by
  letI : IsFiniteMeasure (GammaE.measure u) :=
    ⟨GammaE.measure_univ_lt_top u hu⟩
  letI : IsFiniteMeasure (GammaE.measure v) :=
    ⟨GammaE.measure_univ_lt_top v hv⟩
  let K : ℝ := G * Real.exp G
  have hK : 0 ≤ K := mul_nonneg hGnonneg (Real.exp_nonneg _)
  have hf : Measurable (fun x : SpatialCoordinates d => Real.exp (g x) - 1) :=
    hg.exp.sub measurable_const
  have hfb : ∀ x : SpatialCoordinates d,
      |Real.exp (g x) - 1| ≤ K := by
    intro x
    dsimp [K]
    exact SubdiffusiveProcess.abs_exp_sub_one_le_bound (hgbound x)
  have hsharp := aux_cor_14_form_sharp_energy_weighted_cross
    (GammaE.cross u v) (GammaE.measure u)
    (GammaE.measure v) B hB
    (fun x => Real.exp (g x) - 1) hf K hK hfb
    (fun A hA => GammaE.abs_cross_le u hu v hv A hA)
  have hsq := aux_lem_common_energy_estimate_integral_sq_bound
    (μ := GammaE.measure v) B hB
    (fun x : SpatialCoordinates d => Real.exp (g x) - 1) hf K hK hfb
  have hmassle : (GammaE.measure v B).toReal ≤
      E.form v v := by
    calc
      (GammaE.measure v B).toReal ≤
          (GammaE.measure v Set.univ).toReal :=
        ENNReal.toReal_mono
          (GammaE.measure_univ_lt_top v hv).ne
          (measure_mono (subset_univ B))
      _ = E.form v v :=
        GammaE.measure_univ v hv
  have hEv0 : 0 ≤ Eg.form v v :=
    Eg.form_nonneg v (hdomEg ▸ hv)
  have hE0 : 0 ≤ E.form v v :=
    E.form_nonneg v hv
  have hroot_int : Real.sqrt
      (∫ x in B, (Real.exp (g x) - 1) ^ 2 ∂GammaE.measure v) ≤
      K * Real.sqrt (GammaE.measure v B).toReal := by
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg hK (Real.sqrt_nonneg _), ?_⟩
    calc
      (∫ x in B, (Real.exp (g x) - 1) ^ 2 ∂GammaE.measure v) ≤
          K ^ 2 * (GammaE.measure v B).toReal := hsq.2
      _ = (K * Real.sqrt (GammaE.measure v B).toReal) ^ 2 := by
        dsimp [K]
        have hm : (Real.sqrt (GammaE.measure v B).toReal) ^ 2 =
            (GammaE.measure v B).toReal :=
          Real.sq_sqrt ENNReal.toReal_nonneg
        calc
          (G * Real.exp G) ^ 2 *
              (GammaE.measure v B).toReal =
              (G * Real.exp G) ^ 2 *
              (Real.sqrt (GammaE.measure v B).toReal) ^ 2 := by
                rw [hm]
          _ = (G * Real.exp G *
              Real.sqrt (GammaE.measure v B).toReal) ^ 2 := by ring
  have hroot_mass : Real.sqrt (GammaE.measure v B).toReal ≤
      Real.sqrt (E.form v v) :=
    Real.sqrt_le_sqrt hmassle
  have hroot_form : Real.sqrt (E.form v v) ≤
      Real.exp G * Real.sqrt (Eg.form v v) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _), ?_⟩
    have hlowerE := hlower
    have he1 : 1 ≤ Real.exp G := by
      simpa using (Real.exp_le_exp.mpr hGnonneg)
    have hupperE : E.form v v ≤
        Real.exp G * Eg.form v v := by
      have he : Real.exp G * Real.exp (-G) = 1 := by
        rw [← Real.exp_add]
        simp
      calc
        E.form v v =
            (Real.exp G * Real.exp (-G)) *
              E.form v v := by rw [he]; ring
        _ = Real.exp G * (Real.exp (-G) *
              E.form v v) := by ring
        _ ≤ Real.exp G * Eg.form v v :=
          mul_le_mul_of_nonneg_left hlowerE (Real.exp_nonneg _)
    calc
      E.form v v ≤
          Real.exp G * Eg.form v v := hupperE
      _ ≤ Real.exp G ^ 2 * Eg.form v v := by
        have he : Real.exp G ≤ Real.exp G ^ 2 := by
          have hge : 1 ≤ Real.exp G := by
            simpa using (Real.exp_le_exp.mpr hGnonneg)
          simpa [sq] using
            (le_mul_of_one_le_right (Real.exp_nonneg G) hge)
        exact mul_le_mul_of_nonneg_right he hEv0
      _ = (Real.exp G * Real.sqrt (Eg.form v v)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hEv0]
  have hEv_cs : Eg.form v v ≤
      (K * Real.exp G * Real.sqrt (GammaE.measure u B).toReal) *
        Real.sqrt (Eg.form v v) := by
    calc
      Eg.form v v ≤
          |DirichletForm.signedIntegralOn
            (GammaE.cross u v) B
            (fun x => Real.exp (g x) - 1)| := by
              rw [hEuler]
              simpa [abs_neg] using
                (le_abs_self (-DirichletForm.signedIntegralOn
                  (GammaE.cross u v) B
                    (fun x => Real.exp (g x) - 1)))
      _ ≤ Real.sqrt (GammaE.measure u B).toReal *
            Real.sqrt (∫ x in B, (Real.exp (g x) - 1) ^ 2
              ∂GammaE.measure v) := hsharp
      _ ≤ Real.sqrt (GammaE.measure u B).toReal *
            (K * Real.sqrt (GammaE.measure v B).toReal) := by
              exact mul_le_mul_of_nonneg_left hroot_int (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (GammaE.measure u B).toReal *
            (K * Real.sqrt (E.form v v)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hroot_mass hK)
                (Real.sqrt_nonneg _)
      _ ≤ (K * Real.exp G * Real.sqrt (GammaE.measure u B).toReal) *
            Real.sqrt (Eg.form v v) := by
              calc
                Real.sqrt (GammaE.measure u B).toReal *
                    (K * Real.sqrt (E.form v v)) =
                    (Real.sqrt (GammaE.measure u B).toReal * K) *
                      Real.sqrt (E.form v v) := by ac_rfl
                _ ≤ (Real.sqrt (GammaE.measure u B).toReal * K) *
                      (Real.exp G * Real.sqrt (Eg.form v v)) :=
                  mul_le_mul_of_nonneg_left hroot_form
                    (mul_nonneg (Real.sqrt_nonneg _) hK)
                _ = (K * Real.exp G * Real.sqrt (GammaE.measure u B).toReal) *
                      Real.sqrt (Eg.form v v) := by ac_rfl
  have hweighted := SubdiffusiveProcess.Lane3.weighted_difference_energy_bound
    (1 : ℝ) (Eg.form v v)
    (K * Real.exp G * Real.sqrt (GammaE.measure u B).toReal) 0 0
    zero_lt_one hEv0 (by positivity) (by positivity) (by positivity) (by
      simpa [one_mul, add_zero] using hEv_cs)
  have hexp2 : Real.exp G ^ 2 = Real.exp (2 * G) := by
    rw [sq, ← Real.exp_add]
    congr 1 <;> ring
  have hexp4 : Real.exp G ^ 2 * Real.exp G ^ 2 = Real.exp (4 * G) := by
    rw [hexp2, ← Real.exp_add]
    congr 1 <;> ring
  have hcoeff : G ^ 2 * Real.exp G ^ 2 * Real.exp G ^ 2 =
      G ^ 2 * Real.exp (4 * G) := by
    calc
      G ^ 2 * Real.exp G ^ 2 * Real.exp G ^ 2 =
          G ^ 2 * (Real.exp G ^ 2 * Real.exp G ^ 2) := by ring
      _ = G ^ 2 * Real.exp (4 * G) := by rw [hexp4]
  have hweighted' : Eg.form v v ≤
      3 * (G ^ 2 * Real.exp (4 * G) *
        (GammaE.measure u B).toReal) := by
    simpa [K, mul_pow, hcoeff] using hweighted
  calc
    Eg.form v v ≤
        3 * (G ^ 2 * Real.exp (4 * G) *
          (GammaE.measure u B).toReal) := hweighted'
    _ = 3 * G ^ 2 * Real.exp (4 * G) *
        (GammaE.measure u B).toReal := by ring



theorem lem_common_energy_estimate
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (hd : 2 ≤ d)
      (Q : Opens (SpatialCoordinates d))
      (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
        Q = centeredCube zQ rQ hrQ),
    let q := centeredCube z r hr
    ∀ (hinside : closure (q : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)))
      (E F Eg Fg : DirichletForm.ClosedForm
        (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : DirichletForm.EnergyMeasure E)
      (GammaF : DirichletForm.EnergyMeasure F)
      (GammaEg : DirichletForm.EnergyMeasure Eg)
      (GammaFg : DirichletForm.EnergyMeasure Fg)
      (hdomEF : E.domain = F.domain)
      (hdomEg : Eg.domain = E.domain)
      (hdomFg : Fg.domain = E.domain)
      (V0 : Submodule ℝ (DomainL2 Q))
      (hzero : DirichletForm.IsKilledDomain E
        (q : Set (SpatialCoordinates d)) V0)
      (m M c : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
      (hmc : m ≤ c) (hcM : c ≤ M)
      (horder : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          m * (GammaE.measure u A).toReal ≤ (GammaF.measure u A).toReal ∧
            (GammaF.measure u A).toReal ≤ M * (GammaE.measure u A).toReal)
      (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
      (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
      (hBq : B ⊆ (q : Set (SpatialCoordinates d)))
      (hsupp : ∀ x, x ∉ B → g x = 0)
      (G : ℝ) (hG : IsLUB (Set.range (fun x => |g x|)) G)
      (hbdd : BddAbove (Set.range (fun x => |g x|)))
      (hweightE : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          GammaEg.measure u A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u))
      (hweightF : ∀ u ∈ F.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          GammaFg.measure u A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u))
      (uE uF uEg uFg : DomainL2 Q)
      (huE : uE ∈ E.domain)
      (huF : uF ∈ F.domain)
      (huEg : uEg ∈ Eg.domain)
      (huFg : uFg ∈ Fg.domain)
      (htraceF : uF - uE ∈ V0)
      (htraceEg : uEg - uE ∈ V0)
      (htraceFg : uFg - uE ∈ V0)
      (hminE : ∀ v ∈ V0,
        E.form uE uE ≤ E.form (uE + v) (uE + v))
      (hminF : ∀ v ∈ V0,
        F.form uF uF ≤ F.form (uF + v) (uF + v))
      (hminEg : ∀ v ∈ V0,
        Eg.form uEg uEg ≤ Eg.form (uEg + v) (uEg + v))
      (hminFg : ∀ v ∈ V0,
        Fg.form uFg uFg ≤ Fg.form (uFg + v) (uFg + v))
      (hidentity : ∀ phi ∈ V0,
        Fg.form ((uFg - uF) - (uEg - uE)) phi =
          - DirichletForm.signedIntegralOn
            (GammaF.cross (uF - uE) phi +
              (GammaF.cross uE phi - c • GammaE.cross uE phi))
            B (fun x => Real.exp (g x) - 1) -
          (Fg.form (uEg - uE) phi - c * Eg.form (uEg - uE) phi)),
      Eg.form ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE)) ≤
        C * G ^ 2 * Real.exp (C * G) *
          ((GammaE.measure (uF - uE) B).toReal +
            (M - m) ^ 2 * (GammaE.measure uE B).toReal) := by
  refine ⟨100 * (C0 + 1) ^ 10, by positivity, ?_⟩
  intro d hd Q z r hr hQ
  obtain ⟨zQ, rQ, hrQ, rfl⟩ := hQ
  dsimp only
  intro hinside E F Eg Fg GammaE GammaF GammaEg GammaFg
    hdomEF hdomEg hdomFg V0 hzero m M c hm hmM hM hmc hcM horder
    g hg B hB hBq hsupp G hG hbdd hweightE hweightF
    uE uF uEg uFg huE huF huEg huFg htraceF htraceEg htraceFg
    hminE hminF hminEg hminFg hidentity
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.mpr hC0pos) hm
  have hmnonneg : 0 ≤ m := hmpos.le
  have hMnonneg : 0 ≤ M := le_trans hmnonneg hmM
  have hDel : 0 ≤ M - m := sub_nonneg.mpr hmM
  have hgbound : ∀ x : SpatialCoordinates d, |g x| ≤ G := fun x =>
    hG.1 ⟨x, rfl⟩
  have hGnonneg : 0 ≤ G := by
    let x : SpatialCoordinates d := 0
    exact le_trans (abs_nonneg (g x)) (hgbound x)
  have hV0 : V0 ≤ E.domain := hzero.le_domain
  have hV0F : V0 ≤ F.domain := by
    intro v hv
    rw [← hdomEF]
    exact hV0 hv
  have hV0Eg : V0 ≤ Eg.domain := by
    intro v hv
    rw [hdomEg]
    exact hV0 hv
  have hV0Fg : V0 ≤ Fg.domain := by
    intro v hv
    rw [hdomFg]
    exact hV0 hv
  have huE_Eg : uE ∈ Eg.domain := by rw [hdomEg]; exact huE
  have huF_E : uF ∈ E.domain := hdomEF.symm ▸ huF
  have huF_Eg : uF ∈ Eg.domain := by rw [hdomEg]; exact huF_E
  have huF_Fg : uF ∈ Fg.domain := by rw [hdomFg, hdomEF]; exact huF
  have huE_Fg : uE ∈ Fg.domain := by rw [hdomFg]; exact huE
  have huEg_E : uEg ∈ E.domain := by rw [← hdomEg]; exact huEg
  have huFg_E : uFg ∈ E.domain := by rw [← hdomFg]; exact huFg
  have hwE : uF - uE ∈ E.domain := hV0 htraceF
  have hvE : uEg - uE ∈ E.domain := hV0 htraceEg
  have hvF : uFg - uF ∈ E.domain := by
    have huFgsub : uFg - uE ∈ E.domain := hV0 htraceFg
    rw [show uFg - uF = (uFg - uE) - (uF - uE) by abel]
    exact E.domain.sub_mem huFgsub hwE
  have hzE : (uFg - uF) - (uEg - uE) ∈ E.domain :=
    E.domain.sub_mem hvF hvE
  have hvF0 : uFg - uF ∈ V0 := by
    convert V0.sub_mem htraceFg htraceF using 1 <;> abel
  have hV0z : (uFg - uF) - (uEg - uE) ∈ V0 :=
    V0.sub_mem hvF0 htraceEg
  have horthE : ∀ v ∈ V0, E.form uE v = 0 := by
    intro v hv
    exact aux_lem_common_energy_estimate_min_orthogonal E V0 uE huE hminE hV0 hv
  have horthEg : ∀ v ∈ V0, Eg.form uEg v = 0 := by
    intro v hv
    exact aux_lem_common_energy_estimate_min_orthogonal Eg V0 uEg huEg hminEg hV0Eg hv
  have horthFg : ∀ v ∈ V0, Fg.form uFg v = 0 := by
    intro v hv
    exact aux_lem_common_energy_estimate_min_orthogonal Fg V0 uFg huFg hminFg hV0Fg hv
  have hEulerEg : ∀ phi ∈ V0,
      Eg.form (uEg - uE) phi =
        -DirichletForm.signedIntegralOn (GammaE.cross uE phi) B
          (fun x => Real.exp (g x) - 1) := by
    intro phi hphi
    have hphiE : phi ∈ E.domain := hV0 hphi
    have hphiEg : phi ∈ Eg.domain := by rw [hdomEg]; exact hphiE
    have hweighted := aux_cor_14_weighted_cross_one GammaE GammaEg hdomEg
      g hg G hG hweightE huE hphiE (A := Set.univ) MeasurableSet.univ
    have hform_weight : Eg.form uE phi =
        DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
          (fun x => Real.exp (g x)) := by
      calc
        Eg.form uE phi = GammaEg.cross uE phi Set.univ :=
          (GammaEg.cross_univ uE huE_Eg phi hphiEg).symm
        _ = DirichletForm.signedIntegralOn (GammaEg.cross uE phi) Set.univ
            (fun _ => (1 : ℝ)) := by
          symm
          exact aux_cor_14_signedIntegralOn_one (GammaEg.cross uE phi)
            Set.univ MeasurableSet.univ
        _ = DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
            (fun x => Real.exp (g x)) := hweighted
    have hform_base : E.form uE phi =
        DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
          (fun _ => (1 : ℝ)) := by
      calc
        E.form uE phi = GammaE.cross uE phi Set.univ :=
          (GammaE.cross_univ uE huE phi hphiE).symm
        _ = DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
            (fun _ => (1 : ℝ)) := by
          exact (aux_cor_14_signedIntegralOn_one (GammaE.cross uE phi)
            Set.univ MeasurableSet.univ).symm
    have hbase_zero :
        DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
          (fun _ => (1 : ℝ)) = 0 := by
      rw [← hform_base]
      exact horthE phi hphi
    have hexpint := aux_lem_common_energy_estimate_signed_exp_integrable
      (GammaE.cross uE phi) g hg G hgbound
    have honepos : Integrable (fun _ : SpatialCoordinates d => (1 : ℝ))
        (GammaE.cross uE phi).toJordanDecomposition.posPart := integrable_const _
    have honeneg : Integrable (fun _ : SpatialCoordinates d => (1 : ℝ))
        (GammaE.cross uE phi).toJordanDecomposition.negPart := integrable_const _
    have hsub := aux_cor_14_signedIntegralOn_sub_fun (GammaE.cross uE phi)
      Set.univ (fun x => Real.exp (g x)) (fun _ => (1 : ℝ))
      hexpint.1 hexpint.2 honepos honeneg
    have hsub' :
        DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
            (fun x => Real.exp (g x) - 1) =
          DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
            (fun x => Real.exp (g x)) -
            DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
              (fun _ => (1 : ℝ)) := by
      simpa only [Pi.one_apply] using hsub
    have hset := aux_cor_14_signedIntegralOn_support (GammaE.cross uE phi)
      Set.univ B MeasurableSet.univ hB (Set.subset_univ B)
      (fun x => Real.exp (g x) - 1)
      (fun x hx => by
        change Real.exp (g x) - 1 = 0
        rw [hsupp x hx, Real.exp_zero]
        norm_num)
    have hform_sub : Eg.form (uEg - uE) phi = Eg.form uEg phi - Eg.form uE phi :=
      Eg.form_sub_left huEg huE_Eg hphiEg
    rw [hform_sub, horthEg phi hphi, hform_weight]
    calc
      0 - DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
          (fun x => Real.exp (g x)) =
          -(DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
            (fun x => Real.exp (g x)) -
            DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
              (fun _ => (1 : ℝ))) := by rw [hbase_zero]; ring
      _ = -DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
          (fun x => Real.exp (g x) - 1) := by rw [hsub']
      _ = -DirichletForm.signedIntegralOn (GammaE.cross uE phi) B
          (fun x => Real.exp (g x) - 1) := by rw [hset]
  have hweightedE_bounds : ∀ (u : DomainL2 (centeredCube zQ rQ hrQ)), u ∈ E.domain →
      Real.exp (-G) * E.form u u ≤ Eg.form u u ∧
        Eg.form u u ≤ Real.exp G * E.form u u := by
    intro u hu
    letI : IsFiniteMeasure (GammaE.measure u) :=
      ⟨GammaE.measure_univ_lt_top u hu⟩
    have hI := aux_lem_common_energy_estimate_exp_integrable g hg G hgbound
      (μ := GammaE.measure u)
    have hlow : ∀ x, Real.exp (-G) ≤ Real.exp (g x) := by
      intro x
      exact Real.exp_le_exp.mpr ((abs_le.mp (hgbound x)).1)
    have hupp : ∀ x, Real.exp (g x) ≤ Real.exp G := by
      intro x
      exact Real.exp_le_exp.mpr ((abs_le.mp (hgbound x)).2)
    have hiLow := integral_mono (integrable_const _) hI hlow
    have hiHigh := integral_mono hI (integrable_const _) hupp
    have hform := aux_lem_common_energy_estimate_weighted_form_eq
      GammaE GammaEg hdomEg g hg G hG hweightE hu
    constructor
    · rw [hform]
      calc
        Real.exp (-G) * E.form u u =
            ∫ _x, Real.exp (-G) ∂GammaE.measure u := by
              rw [integral_const, measureReal_def, smul_eq_mul,
                GammaE.measure_univ u hu]
              ring
        _ ≤ ∫ x, Real.exp (g x) ∂GammaE.measure u := hiLow
    · rw [hform]
      calc
        ∫ x, Real.exp (g x) ∂GammaE.measure u ≤
            ∫ _x, Real.exp G ∂GammaE.measure u := hiHigh
        _ = Real.exp G * E.form u u := by
          rw [integral_const, measureReal_def, smul_eq_mul,
            GammaE.measure_univ u hu]
          ring
  have hweightedF_bounds : ∀ (u : DomainL2 (centeredCube zQ rQ hrQ)), u ∈ E.domain →
      Real.exp (-G) * F.form u u ≤ Fg.form u u ∧
        Fg.form u u ≤ Real.exp G * F.form u u := by
    intro u hu
    letI : IsFiniteMeasure (GammaF.measure u) :=
      ⟨GammaF.measure_univ_lt_top u (hdomEF ▸ hu)⟩
    have hI := aux_lem_common_energy_estimate_exp_integrable g hg G hgbound
      (μ := GammaF.measure u)
    have hlow : ∀ x, Real.exp (-G) ≤ Real.exp (g x) := by
      intro x
      exact Real.exp_le_exp.mpr ((abs_le.mp (hgbound x)).1)
    have hupp : ∀ x, Real.exp (g x) ≤ Real.exp G := by
      intro x
      exact Real.exp_le_exp.mpr ((abs_le.mp (hgbound x)).2)
    have hiLow := integral_mono (integrable_const _) hI hlow
    have hiHigh := integral_mono hI (integrable_const _) hupp
    have hform := aux_lem_common_energy_estimate_weighted_form_eq
      GammaF GammaFg (hdomFg.trans hdomEF) g hg G hG hweightF (hdomEF ▸ hu)
    constructor
    · rw [hform]
      calc
        Real.exp (-G) * F.form u u =
            ∫ _x, Real.exp (-G) ∂GammaF.measure u := by
              rw [integral_const, measureReal_def, smul_eq_mul,
                GammaF.measure_univ u (hdomEF ▸ hu)]
              ring
        _ ≤ ∫ x, Real.exp (g x) ∂GammaF.measure u := hiLow
    · rw [hform]
      calc
        ∫ x, Real.exp (g x) ∂GammaF.measure u ≤
            ∫ _x, Real.exp G ∂GammaF.measure u := hiHigh
        _ = Real.exp G * F.form u u := by
          rw [integral_const, measureReal_def, smul_eq_mul,
            GammaF.measure_univ u (hdomEF ▸ hu)]
          ring
  have horder_form : ∀ (u : DomainL2 (centeredCube zQ rQ hrQ)), u ∈ E.domain →
      m * E.form u u ≤ F.form u u ∧ F.form u u ≤ M * E.form u u := by
    intro u hu
    simpa only [GammaE.measure_univ u hu, GammaF.measure_univ u (hdomEF ▸ hu)] using
      horder u hu Set.univ MeasurableSet.univ
  have hcoercive : ∀ (u : DomainL2 (centeredCube zQ rQ hrQ)), u ∈ E.domain →
      m * Real.exp (-2 * G) * Eg.form u u ≤ Fg.form u u := by
    intro u hu
    have h1 := hweightedE_bounds u hu
    have h2 := hweightedF_bounds u hu
    have ho := horder_form u hu
    have hmul1 := mul_le_mul_of_nonneg_left h1.2
      (mul_nonneg hmnonneg (Real.exp_nonneg (-2 * G)))
    have hmul2 := mul_le_mul_of_nonneg_left ho.1 (Real.exp_nonneg (-G))
    calc
      m * Real.exp (-2 * G) * Eg.form u u ≤
          m * Real.exp (-2 * G) * (Real.exp G * E.form u u) := hmul1
      _ = Real.exp (-G) * (m * E.form u u) := by
        have he : Real.exp (-2 * G) * Real.exp G = Real.exp (-G) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
        calc
          m * Real.exp (-2 * G) * (Real.exp G * E.form u u) =
              m * (Real.exp (-2 * G) * Real.exp G) * E.form u u := by ring
          _ = Real.exp (-G) * (m * E.form u u) := by rw [he]; ring
      _ ≤ Real.exp (-G) * F.form u u := hmul2
      _ ≤ Fg.form u u := h2.1
  have hupper : ∀ (u : DomainL2 (centeredCube zQ rQ hrQ)), u ∈ E.domain →
      Fg.form u u ≤ M * Real.exp (2 * G) * Eg.form u u := by
    intro u hu
    have h1 := hweightedE_bounds u hu
    have h2 := hweightedF_bounds u hu
    have ho := horder_form u hu
    have hmul1 := mul_le_mul_of_nonneg_left ho.2 (Real.exp_nonneg G)
    have hmul2 := mul_le_mul_of_nonneg_left h1.1
      (mul_nonneg hMnonneg (Real.exp_nonneg (2 * G)))
    calc
      Fg.form u u ≤ Real.exp G * F.form u u := h2.2
      _ ≤ Real.exp G * (M * E.form u u) := hmul1
      _ = M * Real.exp (2 * G) * (Real.exp (-G) * E.form u u) := by
        have he : Real.exp (2 * G) * Real.exp (-G) = Real.exp G := by
          rw [← Real.exp_add]
          congr 1 <;> ring
        calc
          Real.exp G * (M * E.form u u) =
              M * (Real.exp G * E.form u u) := by ring
          _ = M * (Real.exp (2 * G) * Real.exp (-G)) * E.form u u := by
            rw [he]
            ring
          _ = M * Real.exp (2 * G) * (Real.exp (-G) * E.form u u) := by ring
      _ ≤ M * Real.exp (2 * G) * Eg.form u u := by
        have hp : 0 ≤ M * Real.exp (2 * G) :=
          mul_nonneg hMnonneg (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left h1.1 hp
  have hE_le_Eg : ∀ (u : DomainL2 (centeredCube zQ rQ hrQ)), u ∈ E.domain →
      E.form u u ≤ Real.exp G * Eg.form u u := by
    intro u hu
    have hlower := (hweightedE_bounds u hu).1
    have he : Real.exp G * Real.exp (-G) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      E.form u u = (Real.exp G * Real.exp (-G)) * E.form u u := by
        rw [he, one_mul]
      _ = Real.exp G * (Real.exp (-G) * E.form u u) := by ring
      _ ≤ Real.exp G * Eg.form u u :=
        mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg _)
  have hFmassw : (GammaF.measure (uF - uE) B).toReal ≤
      M * (GammaE.measure (uF - uE) B).toReal :=
    (horder (uF - uE) hwE B hB).2
  have hFmassz : (GammaF.measure ((uFg - uF) - (uEg - uE)) B).toReal ≤
      M * (GammaE.measure ((uFg - uF) - (uEg - uE)) B).toReal :=
    (horder ((uFg - uF) - (uEg - uE)) hzE B hB).2
  have hEmassz : (GammaE.measure ((uFg - uF) - (uEg - uE)) B).toReal ≤
      Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
        ((uFg - uF) - (uEg - uE)) := by
    calc
      (GammaE.measure ((uFg - uF) - (uEg - uE)) B).toReal ≤
          (GammaE.measure ((uFg - uF) - (uEg - uE)) Set.univ).toReal :=
        ENNReal.toReal_mono
          (GammaE.measure_univ_lt_top ((uFg - uF) - (uEg - uE)) hzE).ne
          (measure_mono (subset_univ B))
      _ = E.form ((uFg - uF) - (uEg - uE))
          ((uFg - uF) - (uEg - uE)) :=
        GammaE.measure_univ ((uFg - uF) - (uEg - uE)) hzE
      _ ≤ Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
          ((uFg - uF) - (uEg - uE)) :=
        hE_le_Eg _ hzE
  have hFmassz' : (GammaF.measure ((uFg - uF) - (uEg - uE)) B).toReal ≤
      M * Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
        ((uFg - uF) - (uEg - uE)) := by
    calc
      (GammaF.measure ((uFg - uF) - (uEg - uE)) B).toReal ≤
          M * (GammaE.measure ((uFg - uF) - (uEg - uE)) B).toReal := hFmassz
      _ ≤ M * (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
          ((uFg - uF) - (uEg - uE))) :=
        mul_le_mul_of_nonneg_left hEmassz hMnonneg
      _ = M * Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
          ((uFg - uF) - (uEg - uE)) := by ring
  let K : ℝ := G * Real.exp G
  have hK : 0 ≤ K := mul_nonneg hGnonneg (Real.exp_nonneg _)
  have hf : Measurable (fun x : SpatialCoordinates d => Real.exp (g x) - 1) :=
    hg.exp.sub measurable_const
  have hfb : ∀ x : SpatialCoordinates d,
      |Real.exp (g x) - 1| ≤ K := by
    intro x
    dsimp [K]
    exact SubdiffusiveProcess.abs_exp_sub_one_le_bound (hgbound x)
  letI : IsFiniteMeasure (GammaF.measure (uF - uE)) :=
    ⟨GammaF.measure_univ_lt_top (uF - uE) (hdomEF ▸ hwE)⟩
  letI : IsFiniteMeasure
      (GammaF.measure ((uFg - uF) - (uEg - uE))) :=
    ⟨GammaF.measure_univ_lt_top ((uFg - uF) - (uEg - uE)) (hdomEF ▸ hzE)⟩
  have hsharp1 := aux_cor_14_form_sharp_energy_weighted_cross
    (GammaF.cross (uF - uE) ((uFg - uF) - (uEg - uE)))
    (GammaF.measure (uF - uE))
    (GammaF.measure ((uFg - uF) - (uEg - uE))) B hB
    (fun x => Real.exp (g x) - 1) hf K hK hfb
    (fun A hA => GammaF.abs_cross_le (uF - uE) (hdomEF ▸ hwE)
      ((uFg - uF) - (uEg - uE)) (hdomEF ▸ hzE) A hA)
  have hsq1 := aux_lem_common_energy_estimate_integral_sq_bound
    (μ := GammaF.measure ((uFg - uF) - (uEg - uE))) B hB
    (fun x : SpatialCoordinates d => Real.exp (g x) - 1) hf K hK hfb
  have hroot1 : Real.sqrt
      (∫ x in B, (Real.exp (g x) - 1) ^ 2 ∂GammaF.measure
        ((uFg - uF) - (uEg - uE))) ≤
      K * Real.sqrt (M * Real.exp G *
        Eg.form ((uFg - uF) - (uEg - uE))
          ((uFg - uF) - (uEg - uE))) := by
    have hIle : (∫ x in B, (Real.exp (g x) - 1) ^ 2 ∂GammaF.measure
          ((uFg - uF) - (uEg - uE))) ≤
        K ^ 2 * (M * Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
          ((uFg - uF) - (uEg - uE))) := by
      exact hsq1.2.trans (mul_le_mul_of_nonneg_left hFmassz'
        (sq_nonneg K))
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg hK (Real.sqrt_nonneg _), ?_⟩
    have hEgz0 : 0 ≤ Eg.form ((uFg - uF) - (uEg - uE))
        ((uFg - uF) - (uEg - uE)) := Eg.form_nonneg
          ((uFg - uF) - (uEg - uE)) (hdomEg ▸ hzE)
    have harg : 0 ≤ M * Real.exp G * Eg.form
        ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE)) :=
      mul_nonneg (mul_nonneg hMnonneg (Real.exp_nonneg _)) hEgz0
    have harg_sq : (Real.sqrt (M * Real.exp G * Eg.form
        ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE)))) ^ 2 =
        M * Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
          ((uFg - uF) - (uEg - uE)) := Real.sq_sqrt harg
    calc
      (∫ x in B, (Real.exp (g x) - 1) ^ 2 ∂GammaF.measure
          ((uFg - uF) - (uEg - uE))) ≤
          K ^ 2 * (M * Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE))) := hIle
      _ = (K * Real.sqrt (M * Real.exp G * Eg.form
          ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE)))) ^ 2 := by
        calc
          K ^ 2 * (M * Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
              ((uFg - uF) - (uEg - uE))) =
              K ^ 2 * (Real.sqrt (M * Real.exp G * Eg.form
                ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE)))) ^ 2 := by
                  rw [harg_sq]
          _ = (K * Real.sqrt (M * Real.exp G * Eg.form
              ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE)))) ^ 2 := by ring
  have hI1 :
      |DirichletForm.signedIntegralOn
        (GammaF.cross (uF - uE) ((uFg - uF) - (uEg - uE))) B
        (fun x => Real.exp (g x) - 1)| ≤
      K * M * Real.sqrt (Real.exp G) *
        Real.sqrt (GammaE.measure (uF - uE) B).toReal *
          Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE))) := by
    have hrootw : Real.sqrt (GammaF.measure (uF - uE) B).toReal ≤
        Real.sqrt (M * (GammaE.measure (uF - uE) B).toReal) :=
      Real.sqrt_le_sqrt hFmassw
    have hrootw' : Real.sqrt (M * (GammaE.measure (uF - uE) B).toReal) =
        Real.sqrt M * Real.sqrt (GammaE.measure (uF - uE) B).toReal := by
      rw [Real.sqrt_mul hMnonneg]
    have hroot1' : Real.sqrt (M * Real.exp G * Eg.form
        ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE))) =
        Real.sqrt M * Real.sqrt (Real.exp G) *
          Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE))) := by
      rw [show M * Real.exp G * Eg.form
          ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE)) =
          M * (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE))) by ring,
        Real.sqrt_mul hMnonneg, Real.sqrt_mul (Real.exp_nonneg G)]
      ring
    calc
      |DirichletForm.signedIntegralOn
          (GammaF.cross (uF - uE) ((uFg - uF) - (uEg - uE))) B
          (fun x => Real.exp (g x) - 1)| ≤
          Real.sqrt (GammaF.measure (uF - uE) B).toReal *
            Real.sqrt (∫ x in B, (Real.exp (g x) - 1) ^ 2
              ∂GammaF.measure ((uFg - uF) - (uEg - uE))) := hsharp1
      _ ≤ Real.sqrt (M * (GammaE.measure (uF - uE) B).toReal) *
            Real.sqrt (∫ x in B, (Real.exp (g x) - 1) ^ 2
              ∂GammaF.measure ((uFg - uF) - (uEg - uE))) := by
        exact mul_le_mul hrootw (le_refl _) (Real.sqrt_nonneg _) (by positivity)
      _ ≤ Real.sqrt (M * (GammaE.measure (uF - uE) B).toReal) *
            (K * Real.sqrt (M * Real.exp G * Eg.form
              ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE)))) := by
        exact mul_le_mul_of_nonneg_left hroot1 (by positivity)
      _ = K * M * Real.sqrt (Real.exp G) *
            Real.sqrt (GammaE.measure (uF - uE) B).toReal *
              Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
                ((uFg - uF) - (uEg - uE))) := by
        rw [hrootw', hroot1']
        have hMsq : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hMnonneg
        calc
          Real.sqrt M * Real.sqrt (GammaE.measure (uF - uE) B).toReal *
              (K * (Real.sqrt M * Real.sqrt (Real.exp G) *
                Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
                  ((uFg - uF) - (uEg - uE))))) =
              (Real.sqrt M) ^ 2 * Real.sqrt (GammaE.measure (uF - uE) B).toReal *
                K * Real.sqrt (Real.exp G) *
                Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
                  ((uFg - uF) - (uEg - uE))) := by ring
          _ = _ := by rw [hMsq]; ring
  have hcpos : 0 < c := lt_of_lt_of_le hmpos hmc
  have hTV2 := lem_diff_measure_bound d hd zQ rQ hrQ E F GammaE GammaF hdomEF
    m M c hmpos hmc hcM horder uE ((uFg - uF) - (uEg - uE)) huE hzE B hB
  have hI2 :
      |DirichletForm.signedIntegralOn
        (GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
          c • GammaE.cross uE ((uFg - uF) - (uEg - uE))) B
        (fun x => Real.exp (g x) - 1)| ≤
      K * (M - m) * Real.sqrt (Real.exp G) *
        Real.sqrt (GammaE.measure uE B).toReal *
          Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE))) := by
    have hI2a := aux_lem_common_energy_estimate_signedIntegralOn_bounded
      (GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
        c • GammaE.cross uE ((uFg - uF) - (uEg - uE))) B hB
      (fun x : SpatialCoordinates d => Real.exp (g x) - 1) hf K hK hfb
    have hmassprod :
        (GammaE.measure uE B).toReal *
            (GammaE.measure ((uFg - uF) - (uEg - uE)) B).toReal ≤
          (GammaE.measure uE B).toReal *
            (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
              ((uFg - uF) - (uEg - uE))) := by
      exact mul_le_mul_of_nonneg_left hEmassz ENNReal.toReal_nonneg
    have hrootprod : Real.sqrt
        ((GammaE.measure uE B).toReal *
          (GammaE.measure ((uFg - uF) - (uEg - uE)) B).toReal) ≤
        Real.sqrt ((GammaE.measure uE B).toReal *
          (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE)))) :=
      Real.sqrt_le_sqrt hmassprod
    have hrootprod' : Real.sqrt
        ((GammaE.measure uE B).toReal *
          (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE)))) =
        Real.sqrt (Real.exp G) * Real.sqrt (GammaE.measure uE B).toReal *
          Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE))) := by
      rw [show (GammaE.measure uE B).toReal *
          (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE))) =
          Real.exp G * ((GammaE.measure uE B).toReal *
            Eg.form ((uFg - uF) - (uEg - uE))
              ((uFg - uF) - (uEg - uE))) by ring,
        Real.sqrt_mul (Real.exp_nonneg G), Real.sqrt_mul ENNReal.toReal_nonneg]
      ring
    calc
      |DirichletForm.signedIntegralOn
          (GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
            c • GammaE.cross uE ((uFg - uF) - (uEg - uE))) B
          (fun x => Real.exp (g x) - 1)| ≤
          K * ((GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
            c • GammaE.cross uE ((uFg - uF) - (uEg - uE))).totalVariation B).toReal := hI2a
      _ ≤ K * ((M - m) * Real.sqrt
          ((GammaE.measure uE B).toReal *
            (GammaE.measure ((uFg - uF) - (uEg - uE)) B).toReal)) := by
        exact mul_le_mul_of_nonneg_left hTV2 hK
      _ ≤ K * ((M - m) * Real.sqrt
          ((GammaE.measure uE B).toReal *
            (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
              ((uFg - uF) - (uEg - uE))))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrootprod hDel) hK
      _ = K * (M - m) * Real.sqrt (Real.exp G) *
          Real.sqrt (GammaE.measure uE B).toReal *
            Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
              ((uFg - uF) - (uEg - uE))) := by
        rw [hrootprod']
        ring
  have hformFg : Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) =
      DirichletForm.signedIntegralOn
        (GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
        (fun x => Real.exp (g x)) := by
    calc
      Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) =
          GammaFg.cross (uEg - uE) ((uFg - uF) - (uEg - uE)) Set.univ :=
        (GammaFg.cross_univ (uEg - uE) (hdomFg ▸ hvE)
          ((uFg - uF) - (uEg - uE)) (hdomFg ▸ hzE)).symm
      _ = DirichletForm.signedIntegralOn
          (GammaFg.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
          (fun _ => (1 : ℝ)) := by
        exact (aux_cor_14_signedIntegralOn_one
          (GammaFg.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
          MeasurableSet.univ).symm
      _ = DirichletForm.signedIntegralOn
          (GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
          (fun x => Real.exp (g x)) :=
        aux_cor_14_weighted_cross_one GammaF GammaFg
          (hdomFg.trans hdomEF) g hg G hG hweightF
          (hdomEF ▸ hvE) (hdomEF ▸ hzE) MeasurableSet.univ
  have hformEg : Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) =
      DirichletForm.signedIntegralOn
        (GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
        (fun x => Real.exp (g x)) := by
    calc
      Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) =
          GammaEg.cross (uEg - uE) ((uFg - uF) - (uEg - uE)) Set.univ :=
        (GammaEg.cross_univ (uEg - uE) (hdomEg ▸ hvE)
          ((uFg - uF) - (uEg - uE)) (hdomEg ▸ hzE)).symm
      _ = DirichletForm.signedIntegralOn
          (GammaEg.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
          (fun _ => (1 : ℝ)) := by
        exact (aux_cor_14_signedIntegralOn_one
          (GammaEg.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
          MeasurableSet.univ).symm
      _ = DirichletForm.signedIntegralOn
          (GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
          (fun x => Real.exp (g x)) :=
        aux_cor_14_weighted_cross_one GammaE GammaEg hdomEg g hg G hG hweightE
          hvE hzE MeasurableSet.univ
  have hDform : Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) -
        c * Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) =
      DirichletForm.signedIntegralOn
        (GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE)) -
          c • GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
        (fun x => Real.exp (g x)) := by
    have hexp : ∀ x : SpatialCoordinates d, ‖Real.exp (g x)‖ ≤ Real.exp G := by
      intro x
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        (Real.exp_le_exp.mpr ((abs_le.mp (hgbound x)).2))
    have hadd := aux_cor_14_signedIntegralOn_add
      (GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE)))
      (-(c • GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE)))) Set.univ
      MeasurableSet.univ (fun x : SpatialCoordinates d => Real.exp (g x)) hg.exp
      (Real.exp_nonneg G) hexp
    have hsmul := aux_cor_14_signedIntegralOn_smul_nonneg
      (GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
      (fun x : SpatialCoordinates d => Real.exp (g x)) hcpos.le
    calc
      Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) -
          c * Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) =
          DirichletForm.signedIntegralOn
              (GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
              (fun x => Real.exp (g x)) -
            c * DirichletForm.signedIntegralOn
              (GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
              (fun x => Real.exp (g x)) := by rw [hformFg, hformEg]
      _ = DirichletForm.signedIntegralOn
          (GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE)) -
            c • GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
          (fun x => Real.exp (g x)) := by
        calc
          _ = DirichletForm.signedIntegralOn
              (GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
              (fun x => Real.exp (g x)) +
              DirichletForm.signedIntegralOn
                (-(c • GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE)))) Set.univ
                (fun x => Real.exp (g x)) := by
            rw [aux_lem_common_energy_estimate_signedIntegralOn_neg, hsmul]
            ring
          _ = DirichletForm.signedIntegralOn
              (GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE)) +
                -(c • GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE)))) Set.univ
                (fun x => Real.exp (g x)) := hadd.symm
          _ = _ := by rfl
  have hTV3raw := lem_diff_measure_bound d hd zQ rQ hrQ E F GammaE GammaF hdomEF
    m M c hmpos hmc hcM horder (uEg - uE) ((uFg - uF) - (uEg - uE)) hvE hzE
    Set.univ MeasurableSet.univ
  have hTV3 : ((GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE)) -
        c • GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE))).totalVariation Set.univ).toReal ≤
      (M - m) * Real.sqrt
        (E.form (uEg - uE) (uEg - uE) *
          E.form ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE))) := by
    calc
      _ ≤ (M - m) * Real.sqrt
          ((GammaE.measure (uEg - uE) Set.univ).toReal *
            (GammaE.measure ((uFg - uF) - (uEg - uE)) Set.univ).toReal) := hTV3raw
      _ = _ := by
        rw [GammaE.measure_univ (uEg - uE) hvE,
          GammaE.measure_univ ((uFg - uF) - (uEg - uE)) hzE]
  have hEformv : E.form (uEg - uE) (uEg - uE) ≤
      Real.exp G * Eg.form (uEg - uE) (uEg - uE) := hE_le_Eg _ hvE
  have hEformz : E.form ((uFg - uF) - (uEg - uE))
      ((uFg - uF) - (uEg - uE)) ≤
      Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
        ((uFg - uF) - (uEg - uE)) := hE_le_Eg _ hzE
  have hI3 :
      |Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) -
          c * Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE))| ≤
      (M - m) * Real.exp (2 * G) *
        Real.sqrt (Eg.form (uEg - uE) (uEg - uE)) *
          Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE))) := by
    have hexp := aux_lem_common_energy_estimate_signedIntegralOn_bounded
      (GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE)) -
        c • GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE))) Set.univ
      MeasurableSet.univ (fun x : SpatialCoordinates d => Real.exp (g x)) hg.exp
      (Real.exp G) (Real.exp_nonneg G) (by
        intro x
        simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
          (Real.exp_le_exp.mpr ((abs_le.mp (hgbound x)).2)))
    have hprod : E.form (uEg - uE) (uEg - uE) *
          E.form ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE)) ≤
        (Real.exp G * Eg.form (uEg - uE) (uEg - uE)) *
          (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE))) := by
      have hv0 : 0 ≤ E.form (uEg - uE) (uEg - uE) := E.form_nonneg _ hvE
      have hz0 : 0 ≤ E.form ((uFg - uF) - (uEg - uE))
          ((uFg - uF) - (uEg - uE)) := E.form_nonneg _ hzE
      have huv : 0 ≤ Real.exp G * Eg.form (uEg - uE) (uEg - uE) :=
        mul_nonneg (Real.exp_nonneg _) (Eg.form_nonneg _ (hdomEg ▸ hvE))
      exact mul_le_mul hEformv hEformz hz0 huv
    have hrootprod3 := Real.sqrt_le_sqrt hprod
    have hrootprod3' : Real.sqrt
        ((Real.exp G * Eg.form (uEg - uE) (uEg - uE)) *
          (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE)))) =
        Real.exp G * Real.sqrt (Eg.form (uEg - uE) (uEg - uE)) *
          Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
            ((uFg - uF) - (uEg - uE))) := by
      have he2 : Real.exp G * Real.exp G = Real.exp (2 * G) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      have he4 : Real.sqrt (Real.exp (2 * G)) = Real.exp G := by
        apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_nonneg (2 * G))
          (Real.exp_nonneg G)).2
        rw [← Real.exp_add]
        congr 1 <;> ring
      calc
        Real.sqrt
            ((Real.exp G * Eg.form (uEg - uE) (uEg - uE)) *
              (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
                ((uFg - uF) - (uEg - uE)))) =
            Real.sqrt ((Real.exp G * Real.exp G) *
              (Eg.form (uEg - uE) (uEg - uE) *
                Eg.form ((uFg - uF) - (uEg - uE))
                  ((uFg - uF) - (uEg - uE)))) := by
              congr 1 <;> ring
        _ = Real.sqrt (Real.exp (2 * G) *
              (Eg.form (uEg - uE) (uEg - uE) *
                Eg.form ((uFg - uF) - (uEg - uE))
                  ((uFg - uF) - (uEg - uE)))) := by rw [he2]
        _ = Real.sqrt (Real.exp (2 * G)) *
              Real.sqrt (Eg.form (uEg - uE) (uEg - uE) *
                Eg.form ((uFg - uF) - (uEg - uE))
                  ((uFg - uF) - (uEg - uE))) :=
          Real.sqrt_mul (Real.exp_nonneg (2 * G)) _
        _ = Real.exp G *
              (Real.sqrt (Eg.form (uEg - uE) (uEg - uE)) *
                Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
                  ((uFg - uF) - (uEg - uE)))) := by
            rw [he4, Real.sqrt_mul (Eg.form_nonneg _ (hdomEg ▸ hvE))]
        _ = _ := by ring
    calc
      |Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) -
          c * Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE))| ≤
          Real.exp G *
            ((GammaF.cross (uEg - uE) ((uFg - uF) - (uEg - uE)) -
              c • GammaE.cross (uEg - uE) ((uFg - uF) - (uEg - uE))).totalVariation Set.univ).toReal := by
        rw [hDform]
        exact hexp
      _ ≤ Real.exp G * ((M - m) * Real.sqrt
          (E.form (uEg - uE) (uEg - uE) *
            E.form ((uFg - uF) - (uEg - uE)) ((uFg - uF) - (uEg - uE)))) := by
        exact mul_le_mul_of_nonneg_left hTV3 (Real.exp_nonneg _)
      _ ≤ Real.exp G * ((M - m) * Real.sqrt
          ((Real.exp G * Eg.form (uEg - uE) (uEg - uE)) *
            (Real.exp G * Eg.form ((uFg - uF) - (uEg - uE))
              ((uFg - uF) - (uEg - uE))))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrootprod3 hDel) (Real.exp_nonneg _)
      _ = (M - m) * Real.exp (2 * G) *
          Real.sqrt (Eg.form (uEg - uE) (uEg - uE)) *
            Real.sqrt (Eg.form ((uFg - uF) - (uEg - uE))
              ((uFg - uF) - (uEg - uE))) := by
        rw [hrootprod3']
        have he : Real.exp G * Real.exp G = Real.exp (2 * G) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
        rw [← he]
        ring
  have hEvE : Eg.form (uEg - uE) (uEg - uE) ≤
      3 * G ^ 2 * Real.exp (4 * G) *
        (GammaE.measure uE B).toReal :=
    aux_lem_common_energy_estimate_weighted_variation_energy
      (centeredCube zQ rQ hrQ) E Eg GammaE hdomEg uE (uEg - uE) huE hvE
      g hg B hB G hGnonneg hgbound
      (hweightedE_bounds (uEg - uE) hvE).1
      (hEulerEg (uEg - uE) htraceEg)
  let EwB : ℝ := (GammaE.measure (uF - uE) B).toReal
  let EuB : ℝ := (GammaE.measure uE B).toReal
  let Ez : ℝ := Eg.form ((uFg - uF) - (uEg - uE))
      ((uFg - uF) - (uEg - uE))
  let Ev : ℝ := Eg.form (uEg - uE) (uEg - uE)
  let K0 : ℝ := G * Real.exp G
  have hK0 : 0 ≤ K0 := mul_nonneg hGnonneg (Real.exp_nonneg _)
  have hI1' :
      |DirichletForm.signedIntegralOn
          (GammaF.cross (uF - uE) ((uFg - uF) - (uEg - uE))) B
          (fun x => Real.exp (g x) - 1)| ≤
        K0 * M * Real.sqrt (Real.exp G) * Real.sqrt EwB * Real.sqrt Ez := by
    simpa [K0, EwB, Ez] using hI1
  have hI2' :
      |DirichletForm.signedIntegralOn
          (GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
            c • GammaE.cross uE ((uFg - uF) - (uEg - uE))) B
          (fun x => Real.exp (g x) - 1)| ≤
        K0 * (M - m) * Real.sqrt (Real.exp G) * Real.sqrt EuB * Real.sqrt Ez := by
    simpa [K0, EuB, Ez] using hI2
  have hD' :
      |Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) -
          c * Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE))| ≤
        (M - m) * Real.exp (2 * G) * Real.sqrt Ev * Real.sqrt Ez := by
    simpa [Ev, Ez, mul_assoc] using hI3
  have hEuler_raw :
      m * Real.exp (-2 * G) * Ez ≤
        K0 * M * Real.sqrt (Real.exp G) * Real.sqrt EwB * Real.sqrt Ez +
          K0 * (M - m) * Real.sqrt (Real.exp G) * Real.sqrt EuB * Real.sqrt Ez +
          (M - m) * Real.exp (2 * G) * Real.sqrt Ev * Real.sqrt Ez := by
    have hsum := aux_cor_14_signedIntegralOn_add
      (GammaF.cross (uF - uE) ((uFg - uF) - (uEg - uE)))
      (GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
        c • GammaE.cross uE ((uFg - uF) - (uEg - uE))) B hB
      (fun x : SpatialCoordinates d => Real.exp (g x) - 1) hf hK0 hfb
    have hid : Fg.form ((uFg - uF) - (uEg - uE))
        ((uFg - uF) - (uEg - uE)) =
        -(DirichletForm.signedIntegralOn
            (GammaF.cross (uF - uE) ((uFg - uF) - (uEg - uE))) B
            (fun x => Real.exp (g x) - 1) +
          DirichletForm.signedIntegralOn
            (GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
              c • GammaE.cross uE ((uFg - uF) - (uEg - uE))) B
            (fun x => Real.exp (g x) - 1)) -
          (Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) -
            c * Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE))) := by
      calc
        _ = -DirichletForm.signedIntegralOn
              (GammaF.cross (uF - uE) ((uFg - uF) - (uEg - uE)) +
                (GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
                  c • GammaE.cross uE ((uFg - uF) - (uEg - uE)))) B
              (fun x => Real.exp (g x) - 1) -
            (Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) -
              c * Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE))) :=
          hidentity ((uFg - uF) - (uEg - uE)) hV0z
        _ = _ := by rw [hsum]
    have habs :
        -(DirichletForm.signedIntegralOn
            (GammaF.cross (uF - uE) ((uFg - uF) - (uEg - uE))) B
            (fun x => Real.exp (g x) - 1) +
          DirichletForm.signedIntegralOn
            (GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
              c • GammaE.cross uE ((uFg - uF) - (uEg - uE))) B
            (fun x => Real.exp (g x) - 1)) -
          (Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) -
            c * Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE))) ≤
        |DirichletForm.signedIntegralOn
            (GammaF.cross (uF - uE) ((uFg - uF) - (uEg - uE))) B
            (fun x => Real.exp (g x) - 1)| +
          |DirichletForm.signedIntegralOn
            (GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
              c • GammaE.cross uE ((uFg - uF) - (uEg - uE))) B
            (fun x => Real.exp (g x) - 1)| +
          |Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) -
            c * Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE))| := by
      linarith [neg_le_abs (DirichletForm.signedIntegralOn
          (GammaF.cross (uF - uE) ((uFg - uF) - (uEg - uE))) B
          (fun x => Real.exp (g x) - 1)),
        neg_le_abs (DirichletForm.signedIntegralOn
          (GammaF.cross uE ((uFg - uF) - (uEg - uE)) -
            c • GammaE.cross uE ((uFg - uF) - (uEg - uE))) B
          (fun x => Real.exp (g x) - 1)),
        neg_le_abs (Fg.form (uEg - uE) ((uFg - uF) - (uEg - uE)) -
          c * Eg.form (uEg - uE) ((uFg - uF) - (uEg - uE)))]
    calc
      _ ≤ Fg.form ((uFg - uF) - (uEg - uE))
          ((uFg - uF) - (uEg - uE)) := hcoercive _ hzE
      _ ≤ _ := by rw [hid]; exact habs.trans (by
        have h := add_le_add (add_le_add hI1' hI2') hD'
        simpa [Ez, Ev, EwB, EuB, K0, add_assoc] using h)
  have hEuler_finish :
      m * Real.exp (-2 * G) * Ez ≤
        G * Real.exp G * M * Real.sqrt (Real.exp G) * Real.sqrt EwB * Real.sqrt Ez +
          G * Real.exp G * (M - m) * Real.sqrt (Real.exp G) * Real.sqrt EuB * Real.sqrt Ez +
          (M - m) * Real.exp (2 * G) * Real.sqrt Ev * Real.sqrt Ez := by
    simpa [K0] using hEuler_raw
  exact (by
    simpa [Ez, EwB, EuB] using
      (aux_lem_common_energy_estimate_finish C0 m M G EwB EuB Ez Ev
        hC0 hmpos hm hmM hM hGnonneg hDel
        (by dsimp [EwB]; positivity) (by dsimp [EuB]; positivity)
        (by dsimp [Ez]; exact Eg.form_nonneg _ (hdomEg ▸ hzE))
        (by dsimp [Ev]; exact Eg.form_nonneg _ (hdomEg ▸ hvE))
        hEuler_finish hEvE))
  

  
end
end Paper
