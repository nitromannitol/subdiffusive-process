import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.lem_extension_cell_moment

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open Homogenization Homogenization.Book.Ch02

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper


/-- Same construction as `aux_lem_extension_cell_moment_above_core`, at a general root `z0, R`, with the prefactor `C0` exposed as an explicit, monotone function `C0fn` of `delta` alone,
chosen before `∀ M`, instead of hidden behind a per-`M` `∃ C0`. -/
theorem aux_lem_extension_cell_moment_uniform_root_above_core {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (I : in_J d) (p ε : ℝ) (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
      ∃ C0fn : ℝ → ℝ, (∀ delta : ℝ, 0 < C0fn delta) ∧
        (∀ delta1 delta2 : ℝ, 0 ≤ delta1 → delta1 ≤ delta2 → C0fn delta1 ≤ C0fn delta2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
      ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
          centeredCube z0 R hR) →
      ∀ n : ℕ, k + n ≤ N →
      ∀ Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)),
      ∀ a : BilateralField d → CoeffOn (cubeDomain Q),
        (∀ om, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
          (a om).toCoeffField x = scalarMatrix (cutoffCoefficient M H om N
            (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i))) →
        eLpNorm (fun om => matrixNorm (Homogenization.Book.Ch02.bCoarse (cubeDomain Q) (a om)))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) ∧
        eLpNorm (fun om =>
            matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain Q) (a om)))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < 2 * p := by positivity
  obtain ⟨δresp, CJ, hδresp, hCJ, hresponse⟩ :=
    aux_lem_extension_cell_moment_matched_response hd I p hp
  obtain ⟨CH, hCHnn, hHM⟩ := aux_lem_extension_cell_moment_aboveEnvelope_moment hd
  let B := aux_lem_extension_cell_moment_aboveRate d (2 * p)
  have hB : 0 < B := aux_lem_extension_cell_moment_aboveRate_pos d (2 * p) hp2
  let δrate := Real.sqrt (ε / B)
  have hδrate : 0 < δrate := Real.sqrt_pos.2 (div_pos hε hB)
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall z0 R, isCompact_closedBall _ _⟩
  have hCHK : 0 ≤ CH K := hCHnn K
  let C0fn : ℝ → ℝ :=
    fun delta => 2 * (CJ + 1) * Real.exp (Real.log 4 / (2 * p) + 4 * (2 * p) * CH K * delta ^ 2 +
      B * delta ^ 2)
  have hC0fn_pos : ∀ delta : ℝ, 0 < C0fn delta := by intro delta; dsimp [C0fn]; positivity
  have hC0fn_mono : ∀ delta1 delta2 : ℝ, 0 ≤ delta1 → delta1 ≤ delta2 →
      C0fn delta1 ≤ C0fn delta2 := by
    intro delta1 delta2 h1 h12
    dsimp only [C0fn]
    have hsq : delta1 ^ 2 ≤ delta2 ^ 2 := by nlinarith
    have hcoef1 : 0 ≤ 4 * (2 * p) * CH K := by positivity
    have hexp_le : Real.log 4 / (2 * p) + 4 * (2 * p) * CH K * delta1 ^ 2 + B * delta1 ^ 2 ≤
        Real.log 4 / (2 * p) + 4 * (2 * p) * CH K * delta2 ^ 2 + B * delta2 ^ 2 := by
      have h1' : 4 * (2 * p) * CH K * delta1 ^ 2 ≤ 4 * (2 * p) * CH K * delta2 ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hcoef1
      have h2' : B * delta1 ^ 2 ≤ B * delta2 ^ 2 := mul_le_mul_of_nonneg_left hsq hB.le
      linarith
    have := Real.exp_le_exp.mpr hexp_le
    nlinarith [Real.exp_pos (Real.log 4 / (2 * p) + 4 * (2 * p) * CH K * delta1 ^ 2 + B * delta1 ^ 2)]
  refine ⟨min δresp δrate, B, lt_min hδresp hδrate, hB, C0fn, hC0fn_pos, hC0fn_mono, ?_⟩
  intro M H hH hδ
  have hrate : B * M.delta ^ 2 ≤ ε := by
    have hsq : M.delta ^ 2 ≤ δrate ^ 2 :=
      pow_le_pow_left₀ M.shellPrefix.delta_pos.le (hδ.trans (min_le_right _ _)) 2
    calc
      _ ≤ B * δrate ^ 2 := mul_le_mul_of_nonneg_left hsq hB.le
      _ = ε := by dsimp [δrate]; rw [Real.sq_sqrt (div_pos hε hB).le]; field_simp
  obtain ⟨family, J, hfamily, hJgreat, hJmeas, hJnorm⟩ :=
    hresponse M (hδ.trans (min_le_left _ _))
  let P := Real.log 4 / (2 * p) + 4 * (2 * p) * CH K * M.delta ^ 2 + B * M.delta ^ 2
  let C0 := C0fn M.delta
  have hC0def : C0 = 2 * (CJ + 1) * Real.exp P := rfl
  intro w N k _hk hcell n habove Q hQ a ha
  let m := k + n
  let c := w + (3 : ℝ) ^ (-(k : ℤ)) • cubeCenter Q
  let T := aux_lem_extension_cell_moment_zoom (m : ℤ) c
  have hT : MeasurePreserving T (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    aux_lem_extension_cell_moment_zoom_measurePreserving M (m : ℤ) c
  let F : BilateralField d → ℝ := fun om =>
    Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K m c om)
  let X : BilateralField d → ℝ := fun om => J (N - m) (T om) + 1
  have hJ0 : ∀ om, 0 ≤ J (N - m) (T om) := by
    intro om
    obtain ⟨e, _, he⟩ := (hJgreat (N - m) (T om)).1
    rw [he]
    exact Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
  have hX0 : ∀ om, 0 ≤ X om := fun om => by dsimp [X]; linarith [hJ0 om]
  have hJTm : AEStronglyMeasurable (fun om => J (N - m) (T om))
      (chaosSampleLaw M).toMeasure := (hJmeas (N - m)).comp_measurePreserving hT
  have hXm : AEStronglyMeasurable X (chaosSampleLaw M).toMeasure :=
    hJTm.add aestronglyMeasurable_const
  have hFm : AEStronglyMeasurable F (chaosSampleLaw M).toMeasure :=
    (aux_lem_extension_cell_moment_aboveEnvelope_measurable M H hH.1 K m c).exp.aestronglyMeasurable
  have hXnorm : eLpNorm X (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CJ + 1) := by
    have hJT : eLpNorm (fun om => J (N - m) (T om)) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CJ := by
      change eLpNorm (J (N - m) ∘ T) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CJ
      rw [eLpNorm_comp_measurePreserving (hJmeas (N - m)) hT]
      exact hJnorm (N - m)
    have hone : eLpNorm (fun _ : BilateralField d => (1 : ℝ)) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure = 1 := by
      rw [eLpNorm_const' _ (ENNReal.ofReal_ne_zero_iff.mpr hp2) ENNReal.ofReal_ne_top]
      simp
    have hpone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2 * p by linarith))
    have hadd := eLpNorm_add_le hJTm
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : BilateralField d => (1 : ℝ))
        (chaosSampleLaw M).toMeasure) hpone
    refine hadd.trans ?_
    rw [hone, ENNReal.ofReal_add hCJ.le zero_le_one, ENNReal.ofReal_one]
    exact add_le_add hJT (le_refl _)
  have hFnorm : eLpNorm F (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * m)) := hHM M H hH K m c (2 * p) hp2
  have hproduct : eLpNorm (fun om => F om * X om) (ENNReal.ofReal p)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * m)) * ENNReal.ofReal (CJ + 1) :=
    (aux_lem_extension_cell_moment_eLpNorm_mul (chaosSampleLaw M).toMeasure p hp0 F X hFm hXm).trans
      (mul_le_mul' hFnorm hXnorm)
  have hK : ∀ x ∈ openCubeSet Q,
      (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈ (K : Set (SpatialCoordinates d)) := by
    intro x hx
    have hxroot : x ∈ openCubeSet (originCube d 0) :=
      openCubeSet_subset_of_mem_descendantsAtScale (by simp) hQ hx
    have hyroot := hcell (aux_lem_extension_cell_moment_cellAffine_mem w _ (by positivity) hxroot)
    change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 ≤ R
    change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 < R / 2 at hyroot
    linarith
  have hpoint : ∀ om,
      matrixNorm (Homogenization.Book.Ch02.bCoarse (cubeDomain Q) (a om)) ≤ 2 * (F om * X om) ∧
        matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain Q) (a om)) ≤
          2 * (F om * X om) := by
    intro om
    exact aux_lem_extension_cell_moment_above_coarse_pointwise M H K N k n habove Q hQ w hK
      om (a om) (ha om) ((family (N - m) (T om)).coeffOn (originCube d 0))
      (hfamily (N - m) (T om) (originCube d 0)) (J (N - m) (T om)) (hJgreat (N - m) (T om))
  have hgrowth : B * M.delta ^ 2 * (m : ℝ) ≤ B * M.delta ^ 2 * k + ε * n := by
    dsimp [m]
    rw [Nat.cast_add, mul_add]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hrate (by positivity))
  have hfinish : ENNReal.ofReal 2 *
      (ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * m)) * ENNReal.ofReal (CJ + 1)) ≤
      ENNReal.ofReal (C0 * Real.exp (B * M.delta ^ 2 * k + ε * n)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_add]
    calc
      _ = C0 * Real.exp (B * M.delta ^ 2 * m) := by rw [hC0def]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgrowth) (by rw [hC0def]; positivity)
  have hbound : ∀ Z : BilateralField d → ℝ, (∀ om, 0 ≤ Z om) →
      (∀ om, Z om ≤ 2 * (F om * X om)) →
      eLpNorm Z (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C0 * Real.exp (B * M.delta ^ 2 * k + ε * n)) := by
    intro Z hZ0 hZ
    have hz : eLpNorm Z (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal 2 * eLpNorm (fun om => F om * X om) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards with om
      rw [Real.norm_of_nonneg (hZ0 om), Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hX0 om))]
      exact hZ om
    exact (hz.trans (mul_le_mul_left' hproduct _)).trans hfinish
  constructor
  · exact hbound _ (fun _ => matrixNorm_nonneg _) (fun om => (hpoint om).1)
  · exact hbound _ (fun _ => matrixNorm_nonneg _) (fun om => (hpoint om).2)


/-- Same construction as `aux_lem_extension_cell_moment_below_extremes`, at a general root `z0, R`, with the prefactor `C0` exposed as an explicit, monotone
function `C0fn` of `delta` alone, chosen before `∀ M`. -/
theorem aux_lem_extension_cell_moment_uniform_root_below_extremes {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
      ∃ C0fn : ℝ → ℝ, (∀ delta : ℝ, 0 < C0fn delta) ∧
        (∀ delta1 delta2 : ℝ, 0 ≤ delta1 → delta1 ≤ delta2 → C0fn delta1 ≤ C0fn delta2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
      ∀ (w : SpatialCoordinates d) (N k : ℕ),
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
          centeredCube z0 R hR) →
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
          ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) := by
  let B : ℝ := 6 * Real.log 2 + 9 * p *
    (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  let δ0 := Real.sqrt (ε / B)
  have hδ0 : 0 < δ0 := Real.sqrt_pos.2 (div_pos hε hB)
  obtain ⟨C, hC, hCM⟩ := aux_lem_extension_cell_moment_totalLogNorm_eLpNorm hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
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
  refine ⟨δ0, B, hδ0, hB, C0fn, hC0fn_pos, hC0fn_mono, ?_⟩
  intro M H hH hδ
  have hrate : B * M.delta ^ 2 ≤ ε := by
    have hsq : M.delta ^ 2 ≤ δ0 ^ 2 :=
      pow_le_pow_left₀ M.shellPrefix.delta_pos.le hδ 2
    calc
      B * M.delta ^ 2 ≤ B * δ0 ^ 2 := mul_le_mul_of_nonneg_left hsq hB.le
      _ = ε := by
        dsimp [δ0]
        rw [Real.sq_sqrt (div_pos hε hB).le]
        field_simp
  let P : ℝ := Real.log 4 / p + 36 * p * C K * M.delta ^ 2
  let C0 : ℝ := C0fn M.delta
  have hC0def : C0 = 8 * (d : ℝ) * Real.exp P := rfl
  intro w N k hcell n hbelow Q hQ
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
    have hNl : (N : ℝ) + 1 ≤ (k : ℝ) + (n : ℝ) := by
      exact_mod_cast (show N + 1 ≤ k + n by omega)
    have hgrowth : B * M.delta ^ 2 * ((N : ℝ) + 1) ≤
        B * M.delta ^ 2 * k + ε * n := by
      calc
        _ ≤ B * M.delta ^ 2 * ((k : ℝ) + n) :=
          mul_le_mul_of_nonneg_left hNl (by positivity)
        _ = B * M.delta ^ 2 * k + (B * M.delta ^ 2) * n := by ring
        _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hrate (by positivity))
    calc
      _ ≤ ENNReal.ofReal (8 * (d : ℝ)) *
          ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * ((N : ℝ) + 1))) :=
        hnorm.trans (mul_le_mul_left' hGe _)
      _ = ENNReal.ofReal (C0 * Real.exp (B * M.delta ^ 2 * ((N : ℝ) + 1))) := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.exp_add]
        rw [hC0def]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgrowth) (by rw [hC0def]; positivity))


/-- Chart-level wrapper of `aux_lem_extension_cell_moment_uniform_root_above_core`, mirroring
`aux_lem_extension_cell_moment_above_chart`. -/
theorem aux_lem_extension_cell_moment_uniform_root_above_chart {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (I : in_J d) (p ε : ℝ) (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
      ∃ C0fn : ℝ → ℝ, (∀ delta : ℝ, 0 < C0fn delta) ∧
        (∀ delta1 delta2 : ℝ, 0 ≤ delta1 → delta1 ≤ delta2 → C0fn delta1 ≤ C0fn delta2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
      ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
          centeredCube z0 R hR) →
      ∀ n : ℕ, k + n ≤ N →
      ∀ Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)),
        eLpNorm (fun om => coarseBMatrixNorm Q
            (I.chart z0 R hR
              (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) ∧
        eLpNorm (fun om => coarseSigmaStarInvMatrixNorm Q
            (I.chart z0 R hR
              (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) := by
  obtain ⟨δ0, C1, hδ0, hC1, C0fn, hC0fn_pos, hC0fn_mono, hcore⟩ :=
    aux_lem_extension_cell_moment_uniform_root_above_core hd z0 R hR I p ε hp hε
  refine ⟨δ0, C1, hδ0, hC1, C0fn, hC0fn_pos, hC0fn_mono, ?_⟩
  intro M H hH hδ w N k hk hcell n habove Q hQ
  apply hcore M H hH hδ w N k hk hcell n habove Q hQ
    (fun om => (I.chart z0 R hR
      (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))).coeffOn Q)
  intro om
  exact aux_lem_extension_cell_moment_chart_scalar_identity I M H om N z0 R hR w _
    (by positivity) hcell Q (openCubeSet_subset_of_mem_descendantsAtScale (by simp) hQ)

/-- Combine the above- and below-wavelength explicit bridges, mirroring
`aux_lem_extension_cell_moment_descBridge_of_split`. -/
theorem aux_lem_extension_cell_moment_uniform_root_desc {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (I : in_J d) (p ε : ℝ) (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
      ∃ C0fn : ℝ → ℝ, (∀ delta : ℝ, 0 < C0fn delta) ∧
        (∀ delta1 delta2 : ℝ, 0 ≤ delta1 → delta1 ≤ delta2 → C0fn delta1 ≤ C0fn delta2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
      ∀ (w : SpatialCoordinates d) (N k : ℕ),
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
          centeredCube z0 R hR) →
      ∀ n : ℕ, ∀ Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)),
        eLpNorm (fun om => coarseBMatrixNorm Q
            (I.chart z0 R hR
              (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) ∧
        eLpNorm (fun om => coarseSigmaStarInvMatrixNorm Q
            (I.chart z0 R hR
              (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨δa, Ca, hδa, hCa, C0fnA, hC0fnA_pos, hC0fnA_mono, hA⟩ :=
    aux_lem_extension_cell_moment_uniform_root_above_chart hd z0 R hR I p ε hp hε
  obtain ⟨δb, Cb, hδb, hCb, C0fnB, hC0fnB_pos, hC0fnB_mono, hB⟩ :=
    aux_lem_extension_cell_moment_uniform_root_below_extremes hd z0 R hR p ε (by linarith) hε
  refine ⟨min δa δb, max Ca Cb, lt_min hδa hδb, lt_max_of_lt_left hCa,
    fun delta => max (C0fnA delta) (C0fnB delta),
    fun delta => lt_max_of_lt_left (hC0fnA_pos delta),
    fun delta1 delta2 h1 h12 => max_le_max (hC0fnA_mono delta1 delta2 h1 h12)
      (hC0fnB_mono delta1 delta2 h1 h12), ?_⟩
  intro M H hH hδ w N k hcell n Q hQ
  have hδa' : M.delta ≤ δa := hδ.trans (min_le_left _ _)
  have hδb' : M.delta ≤ δb := hδ.trans (min_le_right _ _)
  set C0a := C0fnA M.delta with hC0a_def
  set C0b := C0fnB M.delta with hC0b_def
  have hmono : ∀ {C0' C1' : ℝ}, 0 ≤ C0' → C0' ≤ max C0a C0b → C1' ≤ max Ca Cb →
      ENNReal.ofReal (C0' * Real.exp (C1' * M.delta ^ 2 * k + ε * n)) ≤
        ENNReal.ofReal (max C0a C0b * Real.exp (max Ca Cb * M.delta ^ 2 * k + ε * n)) := by
    intro C0' C1' h0 hC0' hC1'
    refine ENNReal.ofReal_le_ofReal ?_
    have hδk : 0 ≤ M.delta ^ 2 * (k : ℝ) := by positivity
    have hexp : Real.exp (C1' * M.delta ^ 2 * k + ε * n) ≤
        Real.exp (max Ca Cb * M.delta ^ 2 * k + ε * n) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_right hC1' hδk
      nlinarith [this]
    exact mul_le_mul hC0' hexp (Real.exp_pos _).le (le_trans h0 hC0')
  rcases le_or_gt (k + n) N with hkn | hkn
  · obtain ⟨h1, h2⟩ := hA M H hH hδa' w N k (by omega) hcell n hkn Q hQ
    exact ⟨h1.trans (hmono (hC0fnA_pos M.delta).le (le_max_left _ _) (le_max_left _ _)),
      h2.trans (hmono (hC0fnA_pos M.delta).le (le_max_left _ _) (le_max_left _ _))⟩
  · obtain ⟨lo, hi, hbd, hmom⟩ := hB M H hH hδb' w N k hcell n hkn Q hQ
    have hk' : (originCube d 0).scale - (n : ℤ) ≤ (originCube d 0).scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hQsub := openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
    have hsub : (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
        Set (SpatialCoordinates d)) ⊆
        (centeredCube z0 R hR : Set (SpatialCoordinates d)) := hcell
    have henv := fun om => aux_lem_extension_cell_moment_chart_envelope I M H om N
      z0 R hR w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) hsub Q hQsub
      (hbd om).1 (hbd om).2.1 (hbd om).2.2
    have hnn : ∀ om, 0 ≤ 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 := fun om => by
      have := (hbd om).1; positivity
    have hnn' : ∀ om, 0 ≤ 4 * (d : ℝ) * (lo om)⁻¹ := fun om => by
      have := (hbd om).1; positivity
    constructor
    · refine le_trans (eLpNorm_mono_real fun om => ?_) (hmom.trans
        (hmono (hC0fnB_pos M.delta).le (le_max_right _ _) (le_max_right _ _)))
      rw [Real.norm_of_nonneg (coarseBMatrixNorm_nonneg _ _)]
      linarith [(henv om).1, hnn' om]
    · refine le_trans (eLpNorm_mono_real fun om => ?_) (hmom.trans
        (hmono (hC0fnB_pos M.delta).le (le_max_right _ _) (le_max_right _ _)))
      rw [Real.norm_of_nonneg (coarseSigmaStarInvMatrixNorm_nonneg _ _)]
      linarith [(henv om).2, hnn om]


/-- Finite-grid maximum reduction, mirroring `aux_lem_extension_cell_moment_scaleBridge_of_descBridge`,
with `C0` exposed as an explicit monotone function of `delta`. -/
theorem aux_lem_extension_cell_moment_uniform_root_scale {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (I : in_J d) (p ε : ℝ) (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ δ0 C1 : ℝ, 0 < δ0 ∧ 0 < C1 ∧
      ∃ C0fn : ℝ → ℝ, (∀ delta : ℝ, 0 < C0fn delta) ∧
        (∀ delta1 delta2 : ℝ, 0 ≤ delta1 → delta1 ≤ delta2 → C0fn delta1 ≤ C0fn delta2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
      ∀ (w : SpatialCoordinates d) (N k : ℕ),
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
          centeredCube z0 R hR) →
      ∀ n : ℕ,
        eLpNorm (fun om => maxDescendantBMatrixNormAtScale (originCube d 0)
            ((originCube d 0).scale - (n : ℤ))
            (I.chart z0 R hR
              (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) ∧
        eLpNorm (fun om => maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0)
            ((originCube d 0).scale - (n : ℤ))
            (I.chart z0 R hR
              (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0fn M.delta * Real.exp (C1 * M.delta ^ 2 * k + ε * n)) := by
  obtain ⟨δ0, C1, hδ0, hC1, C0fn, hC0fn_pos, hC0fn_mono, hb⟩ :=
    aux_lem_extension_cell_moment_uniform_root_desc hd z0 R hR I (max p (2 * d * Real.log 3 / ε)) (ε / 2)
      (hp.trans (le_max_left _ _)) (by positivity)
  refine ⟨δ0, C1, hδ0, hC1, C0fn, hC0fn_pos, hC0fn_mono, ?_⟩
  intro M H hH hδ w N k hcell n
  set p' : ℝ := max p (2 * d * Real.log 3 / ε) with hp'_def
  have hp'pos : 0 < p' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hpp' : ENNReal.ofReal p ≤ ENNReal.ofReal p' :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hsub : (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
      Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)) := hcell
  have hk' : (originCube d 0).scale - (n : ℤ) ≤ (originCube d 0).scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hcard := aux_lem_extension_cell_moment_card_rpow_le d n hε (le_max_right _ _) hp'pos
  set A : ℝ := C1 * M.delta ^ 2 * k with hA
  have hC0fnM_pos : 0 < C0fn M.delta := hC0fn_pos M.delta
  have key : ∀ X : Homogenization.TriadicCube d → BilateralField d → ℝ,
      (∀ Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)),
        AEStronglyMeasurable (X Q) (chaosSampleLaw M).toMeasure) →
      (∀ Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)),
        eLpNorm (X Q) (ENNReal.ofReal p') (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C0fn M.delta * Real.exp (A + ε / 2 * n))) →
      AEStronglyMeasurable (fun om => finsetSupReal
          (descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)))
          (fun Q => X Q om)) (chaosSampleLaw M).toMeasure →
      eLpNorm (fun om => finsetSupReal
          (descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)))
          (fun Q => X Q om)) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C0fn M.delta * Real.exp (A + ε * n)) := by
    intro X hX hXb hmax
    refine (eLpNorm_le_eLpNorm_of_exponent_le hpp' hmax).trans ?_
    refine (aux_lem_extension_cell_moment_eLpNorm_finsetSup_le _ X hX hp'pos hXb).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [aux_lem_extension_cell_moment_card_desc]
    calc ((((3 ^ d) ^ n : ℕ) : ℝ)) ^ (1 / p') * (C0fn M.delta * Real.exp (A + ε / 2 * n))
        ≤ Real.exp (ε / 2 * n) * (C0fn M.delta * Real.exp (A + ε / 2 * n)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = C0fn M.delta * Real.exp (A + ε * n) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hdesc : ∀ Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)),
      openCubeSet Q ⊆ openCubeSet (originCube d 0) :=
    fun Q hQ => openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
  constructor
  · exact key (fun Q om => coarseBMatrixNorm Q
        (I.chart z0 R hR
          (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))))
      (fun Q hQ => aux_lem_extension_cell_moment_aesm_coarseB_chart hd I M H hH.1 N
        z0 R hR w _ (by positivity) hsub Q (hdesc Q hQ))
      (fun Q hQ => (hb M H hH hδ w N k hcell n Q hQ).1)
      (aux_lem_extension_cell_moment_aesm_maxB_chart hd I M H hH.1 N z0
        R hR w _ (by positivity) hsub n)
  · exact key (fun Q om => coarseSigmaStarInvMatrixNorm Q
        (I.chart z0 R hR
          (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))))
      (fun Q hQ => aux_lem_extension_cell_moment_aesm_coarseS_chart hd I M H hH.1 N
        z0 R hR w _ (by positivity) hsub Q (hdesc Q hQ))
      (fun Q hQ => (hb M H hH hδ w N k hcell n Q hQ).2)
      (aux_lem_extension_cell_moment_aesm_maxS_chart hd I M H hH.1 N z0
        R hR w _ (by positivity) hsub n)


/-- Model-uniform version of `lem_extension_cell_moment`, at a general root `z0, R`, with the root
prefactor `Cq` exposed as an explicit monotone function `Cq_fn` of `delta` alone, chosen
before `∀ M`, instead of hidden behind a per-`M` `∃ Cq`. -/
theorem lem_extension_cell_moment_uniform_root {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (beta q : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) (hq : 1 ≤ q)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    ∃ deltaq Cd : ℝ, 0 < deltaq ∧ 0 < Cd ∧
      ∃ Cq_fn : ℝ → ℝ, (∀ delta : ℝ, 0 < Cq_fn delta) ∧
        (∀ delta1 delta2 : ℝ, 0 ≤ delta1 → delta1 ≤ delta2 → Cq_fn delta1 ≤ Cq_fn delta2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ deltaq →
      ∀ (w : SpatialCoordinates d) (N k : ℕ),
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
          centeredCube z0 R hR) →
        AEStronglyMeasurable
            (fun om =>
              I.Lam z0 R hR
                  (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))
                  ((beta - 1 / 2) / 4) 2 +
                (I.lam z0 R hR
                  (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))
                  ((beta - 1 / 2) / 4) 2)⁻¹)
            (chaosSampleLaw M).toMeasure ∧
        eLpNorm
            (fun om =>
              I.Lam z0 R hR
                  (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))
                  ((beta - 1 / 2) / 4) 2 +
                (I.lam z0 R hR
                  (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))
                  ((beta - 1 / 2) / 4) 2)⁻¹)
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal
              (Cq_fn M.delta * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * (k : ℝ))) := by
  have hε : 0 < (beta - 1 / 2) / 4 * Real.log 3 :=
    mul_pos (aux_lem_extension_cell_moment_order hbeta).1 (Real.log_pos (by norm_num))
  obtain ⟨δ0, C1, hδ0, hC1, C0fn, hC0fn_pos, hC0fn_mono, hscale⟩ :=
    aux_lem_extension_cell_moment_uniform_root_scale hd z0 R hR I q ((beta - 1 / 2) / 4 * Real.log 3) hq hε
  have hqq : 0 < q + q ^ 2 := by positivity
  set s : ℝ := (beta - 1 / 2) / 4 with hs_def
  set r : ℝ := Real.exp (-(s * Real.log 3)) with hr_def
  have hs : s ∈ Set.Ioc (0 : ℝ) 1 := aux_lem_extension_cell_moment_order hbeta
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr
    (neg_neg_of_pos (mul_pos hs.1 (Real.log_pos (by norm_num))))
  have h1r : 0 < 1 - r := by linarith
  refine ⟨δ0, C1 / (q + q ^ 2), hδ0, div_pos hC1 hqq,
    fun delta => 2 * (C0fn delta * (1 - r)⁻¹),
    fun delta => by have := hC0fn_pos delta; positivity,
    fun delta1 delta2 h1 h12 => by
      have := hC0fn_mono delta1 delta2 h1 h12
      have h1r' : (0:ℝ) ≤ (1 - r)⁻¹ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this h1r'], ?_⟩
  intro M H hH hδ w N k hcell
  have hmain := aux_lem_extension_cell_moment_cell_bound_of_scale hd I M H hH.1 N
    z0 R hR w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) hcell hs
    (p := q) hq (C0 := C0fn M.delta) (A := C1 * M.delta ^ 2 * k) (hC0fn_pos M.delta).le
    (fun n => by
      have := (hscale M H hH hδ w N k hcell n).1
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this)
    (fun n => by
      have := (hscale M H hH hδ w N k hcell n).2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this)
  refine ⟨aux_lem_extension_cell_moment_aestronglyMeasurable hd I M H hH _
    (aux_lem_extension_cell_moment_order hbeta) z0 R hR N _ _ _ hcell,
    hmain.trans (le_of_eq ?_)⟩
  congr 1
  have hCd : C1 / (q + q ^ 2) * (q + q ^ 2) * M.delta ^ 2 * (k : ℝ) =
      C1 * M.delta ^ 2 * k := by field_simp
  rw [hCd]
  ring

