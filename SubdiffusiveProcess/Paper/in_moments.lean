module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.stationary_family
public import SubdiffusiveProcess.Paper.in_moments_family_transport
public import SubdiffusiveProcess.Paper.in_moments_response_moment
public import SubdiffusiveProcess.Paper.in_moments_ellipticity_tail
public import SubdiffusiveProcess.Section4.CoarseGrainedBound
public import SubdiffusiveProcess.Section4.MultiscaleResponseLargeCubes
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Book.Ch02.Matrices
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Auxiliary: log(2+xi) > 1 when xi ≥ 128*d and d ≥ 2. -/
theorem aux_in_moments_log_gt_one (d : ℕ) (hd : 2 ≤ d) (xi : ℕ) (hxiDim : 128 * d ≤ xi) :
    1 < Real.log (2 + (xi : ℝ)) := by
  have h_exp1_lt_3 : Real.exp 1 < 3 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have h_exp1_lt_258 : Real.exp 1 < 258 := by linarith
  have h_258_le_2plusxi : (258 : ℝ) ≤ 2 + (xi : ℝ) := by
    have hxi128 : (128 * d : ℝ) ≤ (xi : ℝ) := by exact_mod_cast hxiDim
    have hd_ge_2 : (256 : ℝ) ≤ 128 * (d : ℝ) := by
      have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith
    have h256_le_xi : (256 : ℝ) ≤ (xi : ℝ) := by linarith
    linarith
  have h_exp1_lt_2plusxi : Real.exp 1 < 2 + (xi : ℝ) := by linarith
  have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos _
  have h := Real.log_lt_log h_exp_pos h_exp1_lt_2plusxi
  simpa [Real.log_exp] using h



theorem in_moments (d : ℕ) (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d) :
    ∃ Cc : ℝ, 0 < Cc ∧
      ∀ (xi : ℕ), Even xi → 128 * d ≤ xi →
        ∃ disorder0 : ℝ, 0 < disorder0 ∧
          ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
            [BorelSpace C(SpatialCoordinates d, ℝ)]
            (model : _root_.SubdiffusiveProcess.Model.GMCModel d),
            model.delta ≤ disorder0 →
              ∃ family : ℕ → BilateralField d → TriadicCoeffFamily d,
                ∃ Jsup : ℕ → ℕ → BilateralField d → ℝ,
                  ((xi : ℝ) ≤
                      Cc⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹) ∧
                    (∀ (N : ℕ) (ω : BilateralField d) (Q : TriadicCube d),
                      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
                        ((family N ω).coeffOn Q).toCoeffField x =
                          scalarMatrix
                            (cutoffCoefficient model
                              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x)) ∧
                    (∀ (N k : ℕ) (ω : BilateralField d),
                      IsGreatest
                        {v : ℝ | ∃ e : Fin d → ℝ,
                          (∑ i : Fin d, e i ^ 2) = 1 ∧
                          v = responseJ (cubeDomain (originCube d (k : ℤ)))
                                ((family N ω).coeffOn (originCube d (k : ℤ))) e e}
                        (Jsup N k ω)) ∧
                    (∀ (N k : ℕ),
                      AEStronglyMeasurable (Jsup N k)
                        (chaosSampleLaw model).toMeasure) ∧
                    (∀ (N k : ℕ),
                      eLpNorm (Jsup N k) (ENNReal.ofReal (xi : ℝ))
                          (chaosSampleLaw model).toMeasure ≤
                        ENNReal.ofReal
                          (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) *
                            model.delta ^ 2)) ∧
                    (∀ (N : ℕ) (ω : BilateralField d) (k : ℕ),
                      0 < lambdaSq (originCube d (k : ℤ)) (1 / 4)
                            (MultiscaleExponent.finite 1) (family N ω) ∧
                      0 ≤ LambdaSq (originCube d (k : ℤ)) (1 / 4)
                            (MultiscaleExponent.finite 1) (family N ω)) ∧
                    (∀ eps : ℝ, 0 < eps → ∃ A : ℝ, 0 < A ∧
                      ∀ N k : ℕ,
                        (chaosSampleLaw model).toMeasure
                            {ω : BilateralField d |
                              A < 1 +
                                    LambdaSq (originCube d (k : ℤ)) (1 / 4)
                                      (MultiscaleExponent.finite 1) (family N ω) +
                                  (lambdaSq (originCube d (k : ℤ)) (1 / 4)
                                    (MultiscaleExponent.finite 1) (family N ω))⁻¹} ≤
                          ENNReal.ofReal eps) := by
  classical
  -- Get the coarse-grained bound constant C
  obtain ⟨c, C, hc, hC, hcg⟩ :=
    _root_.SubdiffusiveProcess.Section4.coarse_grained_bound
  -- Get the response moment constant
  obtain ⟨Cresp, hCresp, hresp⟩ :=
    in_moments_response_moment d hd I
  -- Get K from multiscale_response_large_cubes (needed for Cc and h_third)
  let K : ℝ := Classical.choose (_root_.SubdiffusiveProcess.Section4.multiscale_response_large_cubes (d := d))
  have hKpos : 0 < K := by
    have h := Classical.choose_spec (_root_.SubdiffusiveProcess.Section4.multiscale_response_large_cubes (d := d))
    obtain ⟨_, hKpos', _, _⟩ := h
    exact hKpos'
  -- Choose Cc at least Cresp, coarse C, 8/K, and 1
  let Cc : ℝ := max (max (max Cresp C) (8 / K)) 1
  have hCc : 0 < Cc := by
    apply lt_max_of_lt_left
    apply lt_max_of_lt_left
    apply lt_max_of_lt_left
    exact hCresp
  have hCc_ge_Cresp : Cresp ≤ Cc :=
    calc
      Cresp ≤ max Cresp C := le_max_left _ _
      _ ≤ max (max Cresp C) (8 / K) := le_max_left _ _
      _ ≤ Cc := le_max_left _ _
  have hCc_ge_C : C ≤ Cc :=
    calc
      C ≤ max Cresp C := le_max_right _ _
      _ ≤ max (max Cresp C) (8 / K) := le_max_left _ _
      _ ≤ Cc := le_max_left _ _
  have hCc_ge_one : 1 ≤ Cc := le_max_right _ _
  have hCc_ge_8divK : 8 / K ≤ Cc :=
    calc
      8 / K ≤ max (max Cresp C) (8 / K) := le_max_right _ _
      _ ≤ Cc := le_max_left _ _
  refine ⟨Cc, hCc, ?_⟩
  intro xi hxiEven hxiDim
  obtain ⟨disorder0, hdisorder0, hresp0⟩ :=
    hresp xi hxiEven hxiDim
  have hxi1 : 1 ≤ (xi : ℝ) := by
    have : 1 ≤ xi := by omega
    exact_mod_cast this
  have hxi_pos : 0 < (xi : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (2 + (xi : ℝ)) :=
    Real.log_pos (by linarith)
  -- Disorder is the minimum of all thresholds
  let disorder : ℝ := min disorder0 (min
    (Real.exp (-((Cc + 1) * (xi : ℝ) ^ 2)))
    ((Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)))⁻¹))
  have hdisorder_pos : 0 < disorder := by
    apply lt_min hdisorder0
    refine lt_min (Real.exp_pos _) ?_
    apply inv_pos.mpr
    exact mul_pos (mul_pos hCc hxi_pos) hlog_pos
  refine ⟨disorder, hdisorder_pos, ?_⟩
  intro _ _ model hmodel
  have hmodel0 : model.delta ≤ disorder0 :=
    le_trans hmodel (min_le_left _ _)
  have hdelta_pos : 0 < model.delta := model.shellPrefix.delta_pos
  have hdelta_le_half : model.delta ≤ 1 / 2 := model.shellPrefix.delta_le_half
  have hdelta_lt_one : model.delta < 1 := by linarith
  have hdeltaThreshold : model.delta ≤ Real.exp (-((Cc + 1) * (xi : ℝ) ^ 2)) := by
    have : disorder ≤ Real.exp (-((Cc + 1) * (xi : ℝ) ^ 2)) :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    exact le_trans hmodel this
  have hdeltaThreshold1 : model.delta ≤ (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)))⁻¹ := by
    have : disorder ≤ (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)))⁻¹ :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    exact le_trans hmodel this
  -- Prove the xi inequality with Cc
  have hxi :
      (xi : ℝ) ≤
        Cc⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹ := by
    have hδpos : 0 < model.delta := model.shellPrefix.delta_pos
    have hδle : model.delta ≤ 1 / 2 := model.shellPrefix.delta_le_half
    have hδlt : model.delta < 1 := lt_of_le_of_lt hδle (by norm_num)
    have htpos : 0 < |Real.log model.delta| := by
      rw [abs_pos]
      exact ne_of_lt (Real.log_neg hδpos hδlt)
    have hlog : |Real.log model.delta| ≤ model.delta⁻¹ := by
      rw [abs_of_neg (Real.log_neg hδpos hδlt)]
      have hlog' : -Real.log model.delta ≤ Real.exp (-Real.log model.delta) := by
        have := Real.add_one_le_exp (-Real.log model.delta)
        linarith
      simpa [Real.exp_neg, Real.exp_log hδpos] using hlog'
    have hlin : Cc * (xi : ℝ) ≤ (Cc + 1) * (xi : ℝ) ^ 2 := by
      calc
        Cc * (xi : ℝ) ≤ Cc * (xi : ℝ) + (xi : ℝ) := by
          have : 0 ≤ (xi : ℝ) := by exact_mod_cast Nat.zero_le _
          linarith
        _ = (Cc + 1) * (xi : ℝ) := by ring
        _ ≤ (Cc + 1) * ((xi : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (by
            have hxige1 : 1 ≤ (xi : ℝ) := hxi1
            calc
              (xi : ℝ) = (xi : ℝ) * 1 := by ring
              _ ≤ (xi : ℝ) * (xi : ℝ) :=
                mul_le_mul_of_nonneg_left hxige1 (by exact_mod_cast Nat.zero_le _)
              _ = (xi : ℝ) ^ 2 := by ring
            ) (by linarith)
    have hexp0 : Cc * (xi : ℝ) ≤ Real.exp (Cc * (xi : ℝ)) := by
      have h := Real.add_one_le_exp (Cc * (xi : ℝ))
      linarith
    have hexp1 : Real.exp (Cc * (xi : ℝ)) ≤
        Real.exp ((Cc + 1) * (xi : ℝ) ^ 2) :=
      Real.exp_le_exp.mpr hlin
    have hinvexp : Real.exp ((Cc + 1) * (xi : ℝ) ^ 2) ≤ model.delta⁻¹ := by
      have hinv := (inv_le_inv₀
        (Real.exp_pos _) hδpos).2 hdeltaThreshold
      simpa [Real.exp_neg] using hinv
    have hδinv : Cc * (xi : ℝ) ≤ model.delta⁻¹ :=
      hexp0.trans (hexp1.trans hinvexp)
    have hprod : Cc * (xi : ℝ) * |Real.log model.delta| ≤
        model.delta⁻¹ ^ 2 := by
      calc
        Cc * (xi : ℝ) * |Real.log model.delta| ≤
            model.delta⁻¹ * model.delta⁻¹ :=
          mul_le_mul hδinv hlog (by positivity)
            (inv_pos.mpr hδpos).le
        _ = model.delta⁻¹ ^ 2 := by ring
    apply (le_div_iff₀ htpos).2
    calc
      (xi : ℝ) * |Real.log model.delta| =
          Cc⁻¹ * (Cc * (xi : ℝ) * |Real.log model.delta|) := by
        field_simp [hCc.ne']
      _ ≤ Cc⁻¹ * model.delta⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left hprod (inv_pos.mpr hCc).le
      _ = Cc⁻¹ * (model.delta ^ 2)⁻¹ := by
        rw [inv_pow]
  -- xi inequality with Cresp (needed by hresp0)
  have hxi_for_resp : (xi : ℝ) ≤ Cresp⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹ := by
    apply le_trans hxi
    have hCinv_ge : Cc⁻¹ ≤ Cresp⁻¹ := by
      apply (inv_le_inv₀ hCc hCresp).2 hCc_ge_Cresp
    have hpos_sq : 0 ≤ (model.delta ^ 2)⁻¹ := by positivity
    have hpos_log : 0 ≤ |Real.log model.delta|⁻¹ := by positivity
    have h1 : Cc⁻¹ * (model.delta ^ 2)⁻¹ ≤ Cresp⁻¹ * (model.delta ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hCinv_ge hpos_sq
    have h2 : Cc⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹ ≤
        Cresp⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹ :=
      mul_le_mul_of_nonneg_right h1 hpos_log
    exact h2
  -- Construct hlarger: the three pre-conditions for in_moments_ellipticity_tail
  have hlarger : model.delta ^ 2 ≤ Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2 ∧
      Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2 < 1 ∧
      (xi : ℝ) ≤ K * (1 / 8 : ℝ) * (model.delta ^ 2)⁻¹ *
        (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2) := by
    have h_first : model.delta ^ 2 ≤ Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2 := by
      have hpos : 0 < model.delta ^ 2 := pow_pos model.shellPrefix.delta_pos 2
      have hlog_gt_one : 1 < Real.log (2 + (xi : ℝ)) :=
        aux_in_moments_log_gt_one d hd xi hxiDim
      have hineq : 1 ≤ Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) := by
        have hxi128 : (128 * d : ℝ) ≤ (xi : ℝ) := by exact_mod_cast hxiDim
        have hd_ge_2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 2 ≤ d from hd)
        have hxige256 : (256 : ℝ) ≤ (xi : ℝ) := by nlinarith
        have hlog_ge_1 : 1 ≤ Real.log (2 + (xi : ℝ)) := by linarith
        have h1 : (1 : ℝ) ≤ Cc := hCc_ge_one
        have h2 : (1 : ℝ) ≤ (xi : ℝ) := by
          have : 1 ≤ xi := by omega
          exact_mod_cast this
        have h12 : (1 : ℝ) * (1 : ℝ) ≤ Cc * (xi : ℝ) :=
          mul_le_mul h1 h2 (by positivity) (by linarith)
        have h123 : (1 : ℝ) * (1 : ℝ) * (1 : ℝ) ≤ (Cc * (xi : ℝ)) * Real.log (2 + (xi : ℝ)) :=
          mul_le_mul h12 hlog_ge_1 (by positivity) (by positivity)
        simpa [mul_assoc] using h123
      nlinarith
    have h_second : Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2 < 1 := by
      have hXpos : 0 < Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) := by positivity
      have h1 : Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ≤ 1 := by
        calc
          Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ≤
              Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) *
                ((Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)))⁻¹) := by
            apply mul_le_mul_of_nonneg_left hdeltaThreshold1 (by positivity)
          _ = 1 := by field_simp [hXpos.ne']
      have hsq : model.delta ^ 2 < model.delta := by
        nlinarith
      nlinarith
    have h_third : (xi : ℝ) ≤ K * (1 / 8 : ℝ) * (model.delta ^ 2)⁻¹ *
        (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2) := by
      have hpos_sq : model.delta ^ 2 ≠ 0 := pow_ne_zero 2 model.shellPrefix.delta_pos.ne'
      have hKc : 8 ≤ K * Cc := by
        have h := (div_le_iff₀ hKpos).mp hCc_ge_8divK
        calc
          8 ≤ Cc * K := h
          _ = K * Cc := mul_comm _ _
      have h_one_le : 1 ≤ K * Cc / 8 * Real.log (2 + (xi : ℝ)) := by
        have h1 : 1 ≤ K * Cc / 8 := by linarith
        have h2 : 1 ≤ Real.log (2 + (xi : ℝ)) := by
          have hlog_gt_one : 1 < Real.log (2 + (xi : ℝ)) :=
            aux_in_moments_log_gt_one d hd xi hxiDim
          linarith
        calc
          1 = 1 * 1 := by norm_num
          _ ≤ (K * Cc / 8) * Real.log (2 + (xi : ℝ)) :=
            mul_le_mul h1 h2 (by linarith) (by positivity)
      have hpos_xi : 0 ≤ (xi : ℝ) := by exact_mod_cast Nat.zero_le _
      calc
        (xi : ℝ) = (xi : ℝ) * 1 := by ring
        _ ≤ (xi : ℝ) * (K * Cc / 8 * Real.log (2 + (xi : ℝ))) :=
          mul_le_mul_of_nonneg_left h_one_le hpos_xi
        _ = (xi : ℝ) * (K * Cc / 8) * Real.log (2 + (xi : ℝ)) := by ring
        _ = K * (1 / 8 : ℝ) * Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) := by ring
        _ = K * (1 / 8 : ℝ) * (model.delta ^ 2)⁻¹ *
            (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2) := by
          field_simp [hpos_sq]
    exact ⟨h_first, h_second, h_third⟩
  -- Construct the induction hypothesis hInd
  have hInd : ∀ (m0 : ℕ),
      SubdiffusiveProcess.CoarseGrainingVocab.inductionHypothesis model m0 (xi : ℝ)
        (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2) := by
    intro m0
    have hpos : 0 < Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2 := by
      refine mul_pos (mul_pos (mul_pos hCc hxi_pos) ?_) (pow_pos model.shellPrefix.delta_pos 2)
      exact Real.log_pos (by linarith)
    have hlt : Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2 < 1 := by
      have hXpos : 0 < Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) := by
        refine mul_pos (mul_pos hCc hxi_pos) (Real.log_pos (by linarith))
      have h1 : Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ≤ 1 := by
        calc
          Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ≤
              Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) *
                ((Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)))⁻¹) := by
            apply mul_le_mul_of_nonneg_left hdeltaThreshold1 (by positivity)
          _ = 1 := by field_simp [hXpos.ne']
      have hsq : model.delta ^ 2 < model.delta := by
        have hpos' : 0 < model.delta := model.shellPrefix.delta_pos
        have hle : model.delta ≤ 1 / 2 := model.shellPrefix.delta_le_half
        calc
          model.delta ^ 2 = model.delta * model.delta := by ring
          _ < model.delta * 1 := mul_lt_mul_of_pos_left (by linarith) hpos'
          _ = model.delta := mul_one _
      calc
        Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2 <
            Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta :=
          mul_lt_mul_of_pos_left hsq (by positivity)
        _ ≤ 1 := h1
    have hxi_for_C : (xi : ℝ) ≤ C⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹ := by
      apply le_trans hxi
      have hCinv_ge : Cc⁻¹ ≤ C⁻¹ := by
        apply (inv_le_inv₀ hCc hC).2 hCc_ge_C
      have hpos_sq : 0 ≤ (model.delta ^ 2)⁻¹ := by positivity
      have hpos_log : 0 ≤ |Real.log model.delta|⁻¹ := by positivity
      have h1 : Cc⁻¹ * (model.delta ^ 2)⁻¹ ≤ C⁻¹ * (model.delta ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hCinv_ge hpos_sq
      have h2 : Cc⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹ ≤
          C⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹ :=
        mul_le_mul_of_nonneg_right h1 hpos_log
      exact h2
    have hcg_bound := hcg model (xi : ℝ) hxi1 hxi_for_C
    have hscale : ∀ m : ℕ, m ≤ m0 →
        SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
          (SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect model m
            (cubeDomain (originCube d (m : ℤ)))) ≤
        ENNReal.ofReal (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2) := by
      intro m hm
      have hbound := (hcg_bound m).1
      apply le_trans hbound
      apply ENNReal.ofReal_le_ofReal
      gcongr
    have hsup : (⨆ m : Fin (m0 + 1),
        SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
          (SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect model m.val
            (cubeDomain (originCube d (m.val : ℤ))))) ≤
        ENNReal.ofReal (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2) := by
      apply ciSup_le
      intro m
      apply hscale m.val
      exact Nat.le_of_lt_succ m.2
    exact ⟨hxi1, hpos, hlt, hsup⟩
  obtain ⟨family, hfamily⟩ :=
    in_moments_family_transport d hd model
  obtain ⟨Jsup, hgreat, hmeas, hmoment⟩ :=
    hresp0 model hmodel0 family hfamily hxi_for_resp
  -- Upgrade hmoment from Cresp to Cc
  have hmoment_final : ∀ (N k : ℕ),
      eLpNorm (Jsup N k) (ENNReal.ofReal (xi : ℝ))
          (chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal
          (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2) := by
    intro N k
    apply le_trans (hmoment N k)
    apply ENNReal.ofReal_le_ofReal
    gcongr
  obtain ⟨hell, htail⟩ :=
    in_moments_ellipticity_tail d hd I model xi hxiEven hxiDim
      Cc disorder0 hCc hmodel0 hlarger hInd family hfamily Jsup hgreat hmeas hmoment_final hxi
  exact ⟨family, Jsup, hxi, hfamily, hgreat, hmeas, hmoment_final, hell, htail⟩

end SubdiffusiveProcess.Paper
