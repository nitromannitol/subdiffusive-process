import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_cell_moment
import SubdiffusiveProcess.Paper.lem_extension_cell_moment_uniform

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open Homogenization Homogenization.Book.Ch02

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper


/-- Same construction as `aux_lem_prefix_limit_g9_cell_moment_below_native`, specialized to the
origin unit root `z0 = 0`, `R = 1`, with the prefactor `C0` exposed as an explicit monotone
function `C0fn` of `delta` alone, chosen before `∀ M`. -/
theorem aux_lem_prefix_limit_g9_cell_moment_uniform_below_native {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (p : ℝ) (hp : 0 < p) :
    ∃ C1 : ℝ, 0 < C1 ∧
      ∃ C0fn : ℝ → ℝ, (∀ delta : ℝ, 0 < C0fn delta) ∧
        (∀ delta1 delta2 : ℝ, 0 ≤ delta1 → delta1 ≤ delta2 → C0fn delta1 ≤ C0fn delta2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
          centeredCube (0 : SpatialCoordinates d) 1 one_pos) →
      ∀ n : ℕ, N < k + n →
      ∀ Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)),
      ∃ lo hi : BilateralField d → ℝ,
        (∀ om, 0 < lo om ∧ lo om ≤ hi om ∧
          ∀ x ∈ Homogenization.openCubeSet Q,
            lo om ≤ cutoffCoefficient M H om N
                (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∧
              cutoffCoefficient M H om N
                (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ≤ hi om) ∧
        eLpNorm (fun om => 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 +
            4 * (d : ℝ) * (lo om)⁻¹)
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * ((N : ℝ) + 1))) := by
  let B : ℝ := 6 * Real.log 2 + 9 * p *
    (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨C, hC, hCM⟩ := aux_lem_extension_cell_moment_totalLogNorm_eLpNorm hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  let z0 : SpatialCoordinates d := 0
  let R : ℝ := 1
  let hR : (0 : ℝ) < R := one_pos
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall z0 R, isCompact_closedBall _ _⟩
  have hCK : 0 ≤ C K := hC K
  let C0fn : ℝ → ℝ := fun delta => 8 * (d : ℝ) * Real.exp (Real.log 4 / p + 36 * p * C K * delta ^ 2)
  have hC0fn_pos : ∀ delta : ℝ, 0 < C0fn delta := by intro delta; dsimp [C0fn]; positivity
  have hC0fn_mono : ∀ delta1 delta2 : ℝ, 0 ≤ delta1 → delta1 ≤ delta2 →
      C0fn delta1 ≤ C0fn delta2 := by
    intro delta1 delta2 h1 h12
    dsimp only [C0fn]
    have hsq : delta1 ^ 2 ≤ delta2 ^ 2 := by nlinarith
    have hcoef : 0 ≤ 36 * p * C K := by positivity
    have hexp_le : Real.log 4 / p + 36 * p * C K * delta1 ^ 2 ≤
        Real.log 4 / p + 36 * p * C K * delta2 ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq hcoef
      linarith
    have := Real.exp_le_exp.mpr hexp_le
    nlinarith [Real.exp_pos (Real.log 4 / p + 36 * p * C K * delta1 ^ 2)]
  refine ⟨B, hB, C0fn, hC0fn_pos, hC0fn_mono, ?_⟩
  intro M H hH
  let P : ℝ := Real.log 4 / p + 36 * p * C K * M.delta ^ 2
  let C0 : ℝ := C0fn M.delta
  have hC0def : C0 = 8 * (d : ℝ) * Real.exp P := rfl
  intro w N k _hk hcell n hbelow Q hQ
  let z : SpatialCoordinates d :=
    (3 : ℝ) ^ (N : ℤ) • (w + (3 : ℝ) ^ (-(k : ℤ)) • Homogenization.cubeCenter Q)
  let G : BilateralField d → ℝ := fun om =>
    ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
      aux_lem_extension_cell_moment_physicalLogNorm M N z om
  have hG0 : ∀ om, 0 ≤ G om := by
    intro om
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  let lo : BilateralField d → ℝ := fun om => Real.exp (-G om)
  let hi : BilateralField d → ℝ := fun om => Real.exp (G om)
  have hloinv : ∀ om, (lo om)⁻¹ = hi om := by
    intro om
    dsimp [lo, hi]
    rw [Real.exp_neg, inv_inv]
  refine ⟨lo, hi, ?_, ?_⟩
  · intro om
    refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr (by have := hG0 om; linarith), ?_⟩
    intro x hx
    let ξ : SpatialCoordinates d :=
      (3 : ℝ) ^ ((N : ℤ) - (k : ℤ)) • (x - Homogenization.cubeCenter Q)
    have hξ := aux_lem_extension_cell_moment_descendant_micro_mem N k n hbelow Q hQ x hx
    have hid := aux_lem_extension_cell_moment_descendant_micro_identity N k Q w x
    have hxroot : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) :=
      Homogenization.openCubeSet_subset_of_mem_descendantsAtScale (by simp) hQ hx
    have hyroot : (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈
        (centeredCube z0 R hR : Set (SpatialCoordinates d)) :=
      hcell (aux_lem_extension_cell_moment_cellAffine_mem w _ (by positivity) hxroot)
    have hyK : (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈
        (K : Set (SpatialCoordinates d)) := by
      change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 ≤ R
      change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 < R / 2 at hyroot
      linarith
    have hHpt : |H om (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i)| ≤
        ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ :=
      ContinuousMap.norm_coe_le_norm ((H om).restrict (K : Set (SpatialCoordinates d))) ⟨_, hyK⟩
    have hlog := aux_lem_extension_cell_moment_physicalLogNorm_bounds M H N z ξ hξ om
    rw [hid] at hlog
    have hbound : |Real.log (cutoffCoefficient M H om N
        (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i))| ≤ G om :=
      hlog.trans (add_le_add hHpt (le_refl _))
    have hpos : 0 < cutoffCoefficient M H om N
        (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) :=
      mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
    constructor
    · exact (Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log hpos)
    · exact (Real.exp_log hpos).symm.trans_le (Real.exp_le_exp.mpr hhi)
  · have henv : ∀ om,
        4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 + 4 * (d : ℝ) * (lo om)⁻¹ ≤
          (8 * (d : ℝ)) * Real.exp (3 * G om) := by
      intro om
      have hh : hi om * hi om ^ 2 = Real.exp (3 * G om) := by
        change Real.exp (G om) * Real.exp (G om) ^ 2 = Real.exp (3 * G om)
        rw [show 3 * G om = G om + G om + G om by ring,
          Real.exp_add (G om + G om) (G om), Real.exp_add (G om) (G om)]
        ring
      have hh' : hi om ≤ Real.exp (3 * G om) :=
        Real.exp_le_exp.mpr (by have := hG0 om; linarith)
      rw [hloinv]
      calc
        _ = 4 * (d : ℝ) * (hi om * hi om ^ 2) + 4 * (d : ℝ) * hi om := by ring
        _ ≤ 4 * (d : ℝ) * Real.exp (3 * G om) + 4 * (d : ℝ) * Real.exp (3 * G om) := by
          rw [hh]
          exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hh' (by positivity))
        _ = _ := by ring
    have hnorm : eLpNorm (fun om => 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 +
        4 * (d : ℝ) * (lo om)⁻¹) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (8 * (d : ℝ)) *
          eLpNorm (fun om => Real.exp (3 * G om)) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards with om
      rw [Real.norm_of_nonneg (by dsimp [lo, hi]; positivity),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact henv om
    have hGe : eLpNorm (fun om => Real.exp (3 * G om)) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * ((N : ℝ) + 1))) := by
      have h := hCM M H hH K N z 3 p (by norm_num) hp
      convert h using 2 <;> dsimp [G, P, B] <;> congr 1 <;> ring
    calc
      _ ≤ ENNReal.ofReal (8 * (d : ℝ)) *
          ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * ((N : ℝ) + 1))) :=
        hnorm.trans (mul_le_mul_left' hGe _)
      _ = ENNReal.ofReal (C0 * Real.exp (B * M.delta ^ 2 * ((N : ℝ) + 1))) := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.exp_add]
        rw [hC0def]
        congr 1
        ring


/-- Model-uniform version of `aux_lem_prefix_limit_g9_cell_moment_low`, with the prefactor `C1`
exposed as an explicit monotone function of `delta`, chosen before `∀ M`. -/
theorem aux_lem_prefix_limit_g9_cell_moment_uniform_low {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta1 A1 : ℝ, 0 < delta1 ∧ 0 ≤ A1 ∧
      ∃ C1fn : ℝ → ℝ, (∀ delta : ℝ, 0 < C1fn delta) ∧
        (∀ delta1' delta2' : ℝ, 0 ≤ delta1' → delta1' ≤ delta2' → C1fn delta1' ≤ C1fn delta2') ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta1 →
      ∀ (_Rm : Paper.in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (n : ℕ) (R : Homogenization.TriadicCube d),
        R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(n : ℤ)) →
        ∀ K : ℕ, n ≤ K →
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C1fn M.delta * Real.exp (A1 * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseBMatrixNorm R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C1fn M.delta * Real.exp (A1 * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega) 1).toReal)
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (2 * C1fn M.delta * Real.exp (A1 * M.delta ^ 2 * n)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨deltaq, Cd, hdeltaq, hCd, Cq_fn, hCq_fn_pos, hCq_fn_mono, hext⟩ :=
    lem_extension_cell_moment_uniform hd I (3 / 4) q ⟨by norm_num, by norm_num⟩ hq
  have hs : ((3 / 4 : ℝ) - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by norm_num
  have hw0pos : 0 < Homogenization.Book.Ch02.geometricDiscount (((3 / 4 : ℝ) - 1 / 2) / 4) 2 := by
    unfold Homogenization.Book.Ch02.geometricDiscount
    have : Real.rpow (3 : ℝ) (-(((3 / 4 : ℝ) - 1 / 2) / 4) * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith
  set c0 : ℝ := (Homogenization.Book.Ch02.geometricDiscount (((3 / 4 : ℝ) - 1 / 2) / 4) 2) ^
    (-(2 / (2 : ℝ))) with hc0
  have hc0pos : 0 < c0 := Real.rpow_pos_of_pos hw0pos _
  refine ⟨deltaq, Cd * (q + q ^ 2), hdeltaq, by positivity,
    fun delta => c0 * Cq_fn delta, fun delta => mul_pos hc0pos (hCq_fn_pos delta),
    fun delta1' delta2' h1 h12 =>
      mul_le_mul_of_nonneg_left (hCq_fn_mono delta1' delta2' h1 h12) hc0pos.le, ?_⟩
  intro M hM _Rm H hH n R hR K hnK
  obtain ⟨-, hL⟩ := hext M H hH hM
    (fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) * ((R.index i : ℤ) : ℝ))
    K n hnK (by
      obtain ⟨hscale, hcenter, hsub⟩ := aux_lem_prefix_limit_g9_cell_moment_cell_geom n R hR
      exact hsub)
  obtain ⟨hscale, hcenter, hsub⟩ := aux_lem_prefix_limit_g9_cell_moment_cell_geom n R hR
  set w : SpatialCoordinates d :=
    fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) * ((R.index i : ℤ) : ℝ) with hw
  have hρ : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℤ)) := by positivity
  have hsubset : (centeredCube w ((3 : ℝ) ^ (-(n : ℤ))) hρ : Set (SpatialCoordinates d)) ⊆
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := hsub
  set G : BilateralField d → ℝ := fun om =>
    I.Lam 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w ((3 : ℝ) ^ (-(n : ℤ)))
        (((3 / 4 : ℝ) - 1 / 2) / 4) 2 +
      (I.lam 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w ((3 : ℝ) ^ (-(n : ℤ)))
        (((3 / 4 : ℝ) - 1 / 2) / 4) 2)⁻¹ with hG
  have hpt : ∀ om : BilateralField d,
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
          (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) ≤ c0 * G om ∧
      Homogenization.Book.Ch02.coarseBMatrixNorm R
          (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) ≤ c0 * G om := by
    intro om
    have hsig := aux_lem_prefix_limit_g9_cell_moment_chart_sigma_le_lam I 0 1 one_pos
      (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w ((3 : ℝ) ^ (-(n : ℤ))) hρ hsubset
      (((3 / 4 : ℝ) - 1 / 2) / 4) hs
    have hbb := aux_lem_prefix_limit_g9_cell_moment_chart_b_le_Lam I 0 1 one_pos
      (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w ((3 : ℝ) ^ (-(n : ℤ))) hρ hsubset
      (((3 / 4 : ℝ) - 1 / 2) / 4) hs
    have hlampos := I.lam_pos 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
      ((3 : ℝ) ^ (-(n : ℤ))) (((3 / 4 : ℝ) - 1 / 2) / 4) 2
    have hLampos := I.Lam_pos 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
      ((3 : ℝ) ^ (-(n : ℤ))) (((3 / 4 : ℝ) - 1 / 2) / 4) 2
    have hce := aux_lem_prefix_limit_g9_cell_moment_cell_eq I M H om K n R hR
    have hcell_sig : Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
          (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) =
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
            ((3 : ℝ) ^ (-(n : ℤ)))) := hce.1
    have hcell_b : Homogenization.Book.Ch02.coarseBMatrixNorm R
          (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) =
        Homogenization.Book.Ch02.coarseBMatrixNorm (Homogenization.originCube d 0)
          (I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
            ((3 : ℝ) ^ (-(n : ℤ)))) := hce.2
    have hinv : 0 < (I.lam 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
      ((3 : ℝ) ^ (-(n : ℤ))) (((3 / 4 : ℝ) - 1 / 2) / 4) 2)⁻¹ := inv_pos.mpr hlampos
    constructor
    · rw [hcell_sig]
      calc _ ≤ c0 * (I.lam 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
            ((3 : ℝ) ^ (-(n : ℤ))) (((3 / 4 : ℝ) - 1 / 2) / 4) 2)⁻¹ := hsig
        _ ≤ c0 * G om := by
          apply mul_le_mul_of_nonneg_left _ hc0pos.le
          simp only [hG]; linarith
    · rw [hcell_b]
      calc _ ≤ c0 * I.Lam 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
            ((3 : ℝ) ^ (-(n : ℤ))) (((3 / 4 : ℝ) - 1 / 2) / 4) 2 := hbb
        _ ≤ c0 * G om := by
          apply mul_le_mul_of_nonneg_left _ hc0pos.le
          simp only [hG]; linarith
  have hGbound : eLpNorm (fun om => c0 * G om) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (c0 * Cq_fn M.delta * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * n)) := by
    rw [mul_assoc]
    exact aux_lem_prefix_limit_g9_cell_moment_eLpNorm_const_mul _ _ c0 _ hc0pos.le G hL
  have hG2bound : eLpNorm (fun om => (2 * c0) * G om) (ENNReal.ofReal q)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (c0 * Cq_fn M.delta) * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * n)) := by
    have := aux_lem_prefix_limit_g9_cell_moment_eLpNorm_const_mul _ (ENNReal.ofReal q) (2 * c0)
      (Cq_fn M.delta * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * n)) (by positivity) G hL
    calc _ ≤ _ := this
      _ = _ := by ring_nf
  refine ⟨?_, ?_, ?_⟩
  rotate_left 2
  · refine le_trans (eLpNorm_mono_real (fun om => ?_)) hG2bound
    have hple := aux_lem_prefix_limit_g9_cell_moment_probe_le R
      (aux_lem_prefix_limit_g9_cell_moment_F I M H K om)
    have hp0 : 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) 1).toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hp0]
    have h1 := (hpt om).1
    have h2 := (hpt om).2
    linarith
  · refine le_trans (eLpNorm_mono_real (fun om => ?_)) hGbound
    have := (hpt om).1
    have h0 : 0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) := Homogenization.Book.Ch02.matrixNorm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact this
  · refine le_trans (eLpNorm_mono_real (fun om => ?_)) hGbound
    have := (hpt om).2
    have h0 : 0 ≤ Homogenization.Book.Ch02.coarseBMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) := Homogenization.Book.Ch02.matrixNorm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact this


/-- Model-uniform version of `aux_lem_prefix_limit_g9_cell_moment_high`, with the prefactor `C2`
exposed as an explicit monotone function of `delta`, chosen before `∀ M`. -/
theorem aux_lem_prefix_limit_g9_cell_moment_uniform_high {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta2 A2 : ℝ, 0 < delta2 ∧ 0 ≤ A2 ∧
      ∃ C2fn : ℝ → ℝ, (∀ delta : ℝ, 0 < C2fn delta) ∧
        (∀ delta1' delta2' : ℝ, 0 ≤ delta1' → delta1' ≤ delta2' → C2fn delta1' ≤ C2fn delta2') ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta2 →
      ∀ (_Rm : Paper.in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (n : ℕ) (R : Homogenization.TriadicCube d),
        R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(n : ℤ)) →
        ∀ K : ℕ, K < n →
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C2fn M.delta * Real.exp (A2 * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseBMatrixNorm R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C2fn M.delta * Real.exp (A2 * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega) 1).toReal)
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (2 * C2fn M.delta * Real.exp (A2 * M.delta ^ 2 * n)) := by
  obtain ⟨C1, hC1, C0fn, hC0fn_pos, hC0fn_mono, hnat⟩ :=
    aux_lem_prefix_limit_g9_cell_moment_uniform_below_native hd q (by linarith)
  refine ⟨1, C1, one_pos, hC1.le, C0fn, hC0fn_pos, hC0fn_mono, ?_⟩
  intro M hM _Rm H hH n R hR K hKn
  have h30 : (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) = 1 := by simp
  have hcell : centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) (by positivity) ≤
      centeredCube 0 1 one_pos := by
    have key : ∀ (r : ℝ) (hr : 0 < r), r = 1 →
        centeredCube (0 : SpatialCoordinates d) r hr ≤ centeredCube 0 1 one_pos := by
      rintro r hr rfl; exact le_rfl
    exact key _ _ h30
  have hscale : (Homogenization.originCube d 0).scale - (n : ℤ) = -(n : ℤ) := by
    simp [Homogenization.originCube]
  have hR' : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ)) := by
    rw [hscale]; exact hR
  have hsubR : Homogenization.openCubeSet R ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0) := fun x hx =>
    Homogenization.openCubeSet_subset_of_mem_descendantsAtScale (by simp) hR' hx
  have hb' := hnat M H hH 0 K 0 (Nat.zero_le K) hcell n (by omega) R hR'
  rcases hb' with ⟨lo, hi, hpt, hmom⟩
  have henv : ∀ om, Homogenization.Book.Ch02.coarseBMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) ≤ 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 ∧
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) ≤ 4 * (d : ℝ) * (lo om)⁻¹ := by
    intro om
    have hbd : ∀ x ∈ Homogenization.openCubeSet R,
        lo om ≤ cutoffCoefficient M H om K (fun i => (0 : SpatialCoordinates d) i + 1 * x i) ∧
          cutoffCoefficient M H om K (fun i => (0 : SpatialCoordinates d) i + 1 * x i) ≤ hi om := by
      intro x hx
      have := (hpt om).2.2 x hx
      simpa using this
    exact aux_lem_extension_cell_moment_chart_envelope I M H om K 0 1 one_pos 0 1 one_pos
      subset_rfl R hsubR (hpt om).1 (hpt om).2.1 hbd
  have hC0fnM_pos : 0 < C0fn M.delta := hC0fn_pos M.delta
  have hrate : ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * ((K : ℝ) + 1))) ≤
      ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * n)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC0fnM_pos.le
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast (show K + 1 ≤ n by omega)
  have hmom' := hmom.trans hrate
  have hlo : ∀ om, 0 ≤ 4 * (d : ℝ) * (lo om)⁻¹ := fun om => by
    have := (hpt om).1; positivity
  have hhi : ∀ om, 0 ≤ 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 := fun om => by
    have := (hpt om).1; positivity
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans (eLpNorm_mono_real (fun om => ?_)) hmom'
    have h0 : 0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) := Homogenization.Book.Ch02.matrixNorm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    linarith [(henv om).2, hhi om]
  · refine le_trans (eLpNorm_mono_real (fun om => ?_)) hmom'
    have h0 : 0 ≤ Homogenization.Book.Ch02.coarseBMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) := Homogenization.Book.Ch02.matrixNorm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    linarith [(henv om).1, hlo om]
  · have h2 := aux_lem_prefix_limit_g9_cell_moment_eLpNorm_const_mul _ (ENNReal.ofReal q) 2
      (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * n)) (by norm_num)
      (fun om => 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 + 4 * (d : ℝ) * (lo om)⁻¹) hmom'
    refine le_trans (eLpNorm_mono_real (fun om => ?_)) (h2.trans (le_of_eq (by ring_nf)))
    have hple := aux_lem_prefix_limit_g9_cell_moment_probe_le R
      (aux_lem_prefix_limit_g9_cell_moment_F I M H K om)
    have hp0 : 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) 1).toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hp0]
    linarith [(henv om).1, (henv om).2, hlo om, hhi om]


/-- Model-uniform version of `aux_lem_prefix_limit_g9_cell_moment_root`. -/
theorem aux_lem_prefix_limit_g9_cell_moment_uniform_root {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta4 : ℝ, 0 < delta4 ∧
      ∃ C4fn : ℝ → ℝ, (∀ delta : ℝ, 0 < C4fn delta) ∧
        (∀ delta1' delta2' : ℝ, 0 ≤ delta1' → delta1' ≤ delta2' → C4fn delta1' ≤ C4fn delta2') ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta4 →
      ∀ (_Rm : Paper.in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ K : ℕ,
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          0 < Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
            (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega)) ∧
        eLpNorm (fun omega => (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
              (Homogenization.originCube d 0) (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega))⁻¹)
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C4fn M.delta) := by
  obtain ⟨δ1, A1, hδ1, hA1, C1fn, hC1fn_pos, hC1fn_mono, h1⟩ :=
    aux_lem_prefix_limit_g9_cell_moment_uniform_low hd I q hq
  refine ⟨δ1, hδ1, C1fn, hC1fn_pos, hC1fn_mono, ?_⟩
  intro M hM Rm H hH
  refine fun K => ⟨Filter.Eventually.of_forall (fun om =>
    aux_lem_prefix_limit_g9_cell_moment_sigmaStarInv_norm_pos _ _), ?_⟩
  have hR0 : Homogenization.originCube d 0 ∈ Homogenization.descendantsAtScale
      (Homogenization.originCube d 0) (-((0 : ℕ) : ℤ)) := by
    have h := Homogenization.descendantsAtScale_self (Homogenization.originCube d 0)
    have h0 : (-((0 : ℕ) : ℤ)) = (Homogenization.originCube d 0).scale := by
      simp [Homogenization.originCube]
    rw [h0, h]
    exact Finset.mem_singleton_self _
  have hb := (h1 M hM Rm H hH 0 (Homogenization.originCube d 0) hR0 K (Nat.zero_le K)).2.1
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] at hb
  refine le_trans (eLpNorm_mono_real (fun om => ?_)) hb
  have hpos := aux_lem_prefix_limit_g9_cell_moment_sigmaStarInv_norm_pos (Homogenization.originCube d 0)
    (aux_lem_prefix_limit_g9_cell_moment_F I M H K om)
  have hle := aux_lem_prefix_limit_g9_cell_moment_inv_sigmaStarInv_le_b (Homogenization.originCube d 0)
    (aux_lem_prefix_limit_g9_cell_moment_F I M H K om)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact hle

/-- Model-uniform version of `lem_prefix_limit_g9_cell_moment`: the root prefactor `C` is chosen
before `∀ M`, as an explicit monotone function of `delta`. -/
theorem lem_prefix_limit_g9_cell_moment_uniform {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_Poincare : Paper.in_poincare d hd I)
    (_Extension : Paper.in_extension d hd I) (_Perturbation : Lane4.SmallPerturbationInput d)
    (_Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 A : ℝ, 0 < delta0 ∧ 0 ≤ A ∧
      ∃ Cfn : ℝ → ℝ, (∀ delta : ℝ, 0 < Cfn delta) ∧
        (∀ delta1' delta2' : ℝ, 0 ≤ delta1' → delta1' ≤ delta2' → Cfn delta1' ≤ Cfn delta2') ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      let F : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d :=
        fun K omega => I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1
      (∀ (n : ℕ) (R : Homogenization.TriadicCube d),
        R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(n : ℤ)) →
        ∀ K : ℕ,
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (F K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cfn M.delta * Real.exp (A * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseBMatrixNorm R (F K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cfn M.delta * Real.exp (A * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (F K omega) 1).toReal)
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cfn M.delta * Real.exp (A * M.delta ^ 2 * n))) ∧
      (∀ K : ℕ,
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          0 < Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
            (F K omega)) ∧
        eLpNorm (fun omega => (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
              (Homogenization.originCube d 0) (F K omega))⁻¹)
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cfn M.delta)) := by
  obtain ⟨δ1, A1, hδ1, hA1, C1fn, hC1fn_pos, hC1fn_mono, h1⟩ :=
    aux_lem_prefix_limit_g9_cell_moment_uniform_low hd I q hq
  obtain ⟨δ2, A2, hδ2, hA2, C2fn, hC2fn_pos, hC2fn_mono, h2⟩ :=
    aux_lem_prefix_limit_g9_cell_moment_uniform_high hd I q hq
  obtain ⟨δ4, hδ4, C4fn, hC4fn_pos, hC4fn_mono, h4⟩ :=
    aux_lem_prefix_limit_g9_cell_moment_uniform_root hd I q hq
  refine ⟨min δ1 (min δ2 δ4), max A1 A2, lt_min hδ1 (lt_min hδ2 hδ4), le_max_of_le_left hA1,
    fun delta => max (2 * C1fn delta) (max (2 * C2fn delta) (C4fn delta)),
    fun delta => lt_max_of_lt_left (by have := hC1fn_pos delta; linarith),
    fun delta1' delta2' h1' h12 => by
      have e1 := hC1fn_mono delta1' delta2' h1' h12
      have e2 := hC2fn_mono delta1' delta2' h1' h12
      have e4 := hC4fn_mono delta1' delta2' h1' h12
      exact max_le_max (by linarith) (max_le_max (by linarith) e4), ?_⟩
  intro M hM Rm _hRm _Sreg _It H hH
  have hM1 : M.delta ≤ δ1 := hM.trans (min_le_left _ _)
  have hM2 : M.delta ≤ δ2 := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hM4 : M.delta ≤ δ4 := hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  have b1 := h1 M hM1 Rm H hH
  have b2 := h2 M hM2 Rm H hH
  have b4 := h4 M hM4 Rm H hH
  set C1 := C1fn M.delta with hC1def
  set C2 := C2fn M.delta with hC2def
  set C4 := C4fn M.delta with hC4def
  have hC1 : 0 < C1 := hC1fn_pos M.delta
  have hC2 : 0 < C2 := hC2fn_pos M.delta
  have hC4 : 0 < C4 := hC4fn_pos M.delta
  set A := max A1 A2 with hAdef
  set C := max (2 * C1) (max (2 * C2) C4) with hCdef
  have hA1A : A1 ≤ A := le_max_left _ _
  have hA2A : A2 ≤ A := le_max_right _ _
  have hC1C2 : 2 * C1 ≤ C := le_max_left _ _
  have hC2C2 : 2 * C2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC1C : C1 ≤ C := le_trans (by linarith) hC1C2
  have hC2C : C2 ≤ C := le_trans (by linarith) hC2C2
  have hC4C : C4 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  intro F
  refine ⟨fun n R hR K => ?_, fun K => ?_⟩
  · rcases le_or_lt n K with hnK | hKn
    · obtain ⟨hs, hb, hp⟩ := b1 n R hR K hnK
      exact ⟨hs.trans (aux_lem_prefix_limit_g9_cell_moment_mono C1 C A1 A M.delta n hC1.le hC1C hA1A),
        hb.trans (aux_lem_prefix_limit_g9_cell_moment_mono C1 C A1 A M.delta n hC1.le hC1C hA1A),
        hp.trans (aux_lem_prefix_limit_g9_cell_moment_mono (2 * C1) C A1 A M.delta n (by positivity)
          hC1C2 hA1A)⟩
    · obtain ⟨hs, hb, hp⟩ := b2 n R hR K hKn
      exact ⟨hs.trans (aux_lem_prefix_limit_g9_cell_moment_mono C2 C A2 A M.delta n hC2.le hC2C hA2A),
        hb.trans (aux_lem_prefix_limit_g9_cell_moment_mono C2 C A2 A M.delta n hC2.le hC2C hA2A),
        hp.trans (aux_lem_prefix_limit_g9_cell_moment_mono (2 * C2) C A2 A M.delta n (by positivity)
          hC2C2 hA2A)⟩
  · obtain ⟨hpos, hinv⟩ := b4 K
    exact ⟨hpos, hinv.trans (ENNReal.ofReal_le_ofReal hC4C)⟩

end Paper
