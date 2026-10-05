module

public import SubdiffusiveProcess.Paper.lem_19_limit_membership
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lem_19_interpolation_upgrade_seminorm_sub_le
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1)
    (f g : Fin 1 → DomainL2 (centeredCube z r hr)) :
    cubeFractionalL2Seminorm hd z r hr s (fun i => f i - g i) ≤
      2 * (cubeFractionalL2Seminorm hd z r hr s f +
        cubeFractionalL2Seminorm hd z r hr s g) := by
  classical
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let den : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun q =>
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2))) ^
      ((d : ℝ) + 2 * (s : ℝ))
  let Ff : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((f 0 q.1 - f 0 q.2) ^ 2) / den q
  let Fg : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((g 0 q.1 - g 0 q.2) ^ 2) / den q
  let Fsub : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((f 0 q.1 - g 0 q.1) - (f 0 q.2 - g 0 q.2)) ^ 2) / den q
  let Factual : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal
      (((((f 0 - g 0 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) q.1) -
        (((f 0 - g 0 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) q.2)) ^ 2) /
      den q
  let If : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, Ff (x, y) ∂μ ∂μ
  let Ig : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, Fg (x, y) ∂μ ∂μ
  let Isub : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, Fsub (x, y) ∂μ ∂μ
  let a : ℝ≥0∞ := ENNReal.ofReal (s : ℝ) / volume U
  have hden : Measurable den := by
    dsimp [den]
    apply Measurable.pow
    · apply Measurable.ennreal_ofReal
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun j _ =>
        (((measurable_pi_apply j).comp measurable_fst).sub
          ((measurable_pi_apply j).comp measurable_snd)).pow_const 2
    · exact measurable_const
  have hfm : AEStronglyMeasurable (fun x : SpatialCoordinates d => (f 0 x : ℝ)) μ := by
    simpa only [μ] using Lp.aestronglyMeasurable (f 0)
  have hgm : AEStronglyMeasurable (fun x : SpatialCoordinates d => (g 0 x : ℝ)) μ := by
    simpa only [μ] using Lp.aestronglyMeasurable (g 0)
  have hFf : AEMeasurable Ff (μ.prod μ) := by
    dsimp [Ff]
    have hnum : AEMeasurable
        (fun q : SpatialCoordinates d × SpatialCoordinates d =>
          ((f 0 q.1 - f 0 q.2) ^ 2)) (μ.prod μ) :=
      (((hfm.aemeasurable.comp_fst).sub (hfm.aemeasurable.comp_snd)).pow_const 2)
    exact hnum.ennreal_ofReal.div hden.aemeasurable
  have hFg : AEMeasurable Fg (μ.prod μ) := by
    dsimp [Fg]
    have hnum : AEMeasurable
        (fun q : SpatialCoordinates d × SpatialCoordinates d =>
          ((g 0 q.1 - g 0 q.2) ^ 2)) (μ.prod μ) :=
      (((hgm.aemeasurable.comp_fst).sub (hgm.aemeasurable.comp_snd)).pow_const 2)
    exact hnum.ennreal_ofReal.div hden.aemeasurable
  have hFsub : AEMeasurable Fsub (μ.prod μ) := by
    dsimp [Fsub]
    have hnum : AEMeasurable
        (fun q : SpatialCoordinates d × SpatialCoordinates d =>
          (((f 0 q.1 - g 0 q.1) - (f 0 q.2 - g 0 q.2)) ^ 2)) (μ.prod μ) :=
      (((hfm.aemeasurable.comp_fst).sub (hgm.aemeasurable.comp_fst)).sub
        ((hfm.aemeasurable.comp_snd).sub (hgm.aemeasurable.comp_snd))).pow_const 2
    exact hnum.ennreal_ofReal.div hden.aemeasurable
  have hsubm : AEStronglyMeasurable
      (fun x : SpatialCoordinates d => ((f 0 - g 0) x : ℝ)) μ := by
    simpa only [μ] using Lp.aestronglyMeasurable (f 0 - g 0)
  have hFactual : AEMeasurable Factual (μ.prod μ) := by
    dsimp [Factual]
    have hnum : AEMeasurable
        (fun q : SpatialCoordinates d × SpatialCoordinates d =>
          (((f 0 - g 0) q.1 - (f 0 - g 0) q.2) ^ 2)) (μ.prod μ) :=
      ((hsubm.aemeasurable.comp_fst).sub (hsubm.aemeasurable.comp_snd)).pow_const 2
    exact hnum.ennreal_ofReal.div hden.aemeasurable
  have hFf_x (x : SpatialCoordinates d) :
      AEMeasurable (fun y : SpatialCoordinates d => Ff (x, y)) μ := by
    dsimp [Ff, den]
    have hnum : AEMeasurable
        (fun y : SpatialCoordinates d => ((f 0 x - f 0 y) ^ 2)) μ :=
      ((measurable_const.aemeasurable.sub hfm.aemeasurable).pow_const 2)
    have hdenx : Measurable
        (fun y : SpatialCoordinates d =>
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) := by
      apply Measurable.pow
      · apply Measurable.ennreal_ofReal
        apply Measurable.sqrt
        exact Finset.measurable_sum Finset.univ fun j _ =>
          (measurable_const.sub (measurable_pi_apply j)).pow_const 2
      · exact measurable_const
    exact hnum.ennreal_ofReal.div hdenx.aemeasurable
  have hFg_x (x : SpatialCoordinates d) :
      AEMeasurable (fun y : SpatialCoordinates d => Fg (x, y)) μ := by
    dsimp [Fg, den]
    have hnum : AEMeasurable
        (fun y : SpatialCoordinates d => ((g 0 x - g 0 y) ^ 2)) μ :=
      ((measurable_const.aemeasurable.sub hgm.aemeasurable).pow_const 2)
    have hdenx : Measurable
        (fun y : SpatialCoordinates d =>
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) := by
      apply Measurable.pow
      · apply Measurable.ennreal_ofReal
        apply Measurable.sqrt
        exact Finset.measurable_sum Finset.univ fun j _ =>
          (measurable_const.sub (measurable_pi_apply j)).pow_const 2
      · exact measurable_const
    exact hnum.ennreal_ofReal.div hdenx.aemeasurable
  have hpoint : ∀ x y, Fsub (x, y) ≤ 2 * Ff (x, y) + 2 * Fg (x, y) := by
    intro x y
    dsimp [Fsub, Ff, Fg]
    have hsq :
        ((f 0 x - g 0 x) - (f 0 y - g 0 y)) ^ 2 ≤
          2 * (f 0 x - f 0 y) ^ 2 + 2 * (g 0 x - g 0 y) ^ 2 := by
      nlinarith [sq_nonneg ((f 0 x - f 0 y) + (g 0 x - g 0 y))]
    calc
      _ ≤ ENNReal.ofReal
          (2 * (f 0 x - f 0 y) ^ 2 + 2 * (g 0 x - g 0 y) ^ 2) /
            den (x, y) := by
        apply ENNReal.div_le_div_right
        exact ENNReal.ofReal_le_ofReal hsq
      _ = (2 * ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) +
          2 * ENNReal.ofReal ((g 0 x - g 0 y) ^ 2)) / den (x, y) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ = _ := by
        calc
          _ = (2 * ENNReal.ofReal ((f 0 x - f 0 y) ^ 2)) / den (x, y) +
              (2 * ENNReal.ofReal ((g 0 x - g 0 y) ^ 2)) / den (x, y) :=
            by
              simp only [ENNReal.div_eq_inv_mul, mul_add]
          _ = _ := by rw [mul_div_assoc, mul_div_assoc]
  have hinner (x : SpatialCoordinates d) :
      (∫⁻ y, Fsub (x, y) ∂μ) ≤
        2 * (∫⁻ y, Ff (x, y) ∂μ) + 2 * (∫⁻ y, Fg (x, y) ∂μ) := by
    calc
      _ ≤ ∫⁻ y, 2 * Ff (x, y) + 2 * Fg (x, y) ∂μ :=
        lintegral_mono (fun y => hpoint x y)
      _ = 2 * (∫⁻ y, Ff (x, y) ∂μ) +
          2 * (∫⁻ y, Fg (x, y) ∂μ) := by
        rw [lintegral_add_left' ((hFf_x x).const_mul (2 : ℝ≥0∞)),
          lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
  have hIf_meas : AEMeasurable (fun x => ∫⁻ y, Ff (x, y) ∂μ) μ :=
    hFf.lintegral_prod_right
  have hIg_meas : AEMeasurable (fun x => ∫⁻ y, Fg (x, y) ∂μ) μ :=
    hFg.lintegral_prod_right
  have hraw : Isub ≤ 2 * If + 2 * Ig := by
    have houter :
        (∫⁻ x, ∫⁻ y, Fsub (x, y) ∂μ ∂μ) ≤
          ∫⁻ x, (2 * (∫⁻ y, Ff (x, y) ∂μ) +
            2 * (∫⁻ y, Fg (x, y) ∂μ)) ∂μ :=
      lintegral_mono (fun x => hinner x)
    calc
      Isub = ∫⁻ x, ∫⁻ y, Fsub (x, y) ∂μ ∂μ := rfl
      _ ≤ ∫⁻ x, (2 * (∫⁻ y, Ff (x, y) ∂μ) +
          2 * (∫⁻ y, Fg (x, y) ∂μ)) ∂μ := houter
      _ = 2 * If + 2 * Ig := by
        rw [lintegral_add_left' (hIf_meas.const_mul (2 : ℝ≥0∞)),
          lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
  have hpair : Factual =ᵐ[μ.prod μ] Fsub := by
    have hcoe :
        (fun x : SpatialCoordinates d => ((f 0 - g 0) x : ℝ)) =ᵐ[μ]
          (fun x => (f 0 x : ℝ) - g 0 x) := by
      simpa only using! (Lp.coeFn_sub (f 0) (g 0))
    have hfst :=
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp hcoe
    have hsnd :=
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq_comp hcoe
    have hfst' :
        (fun q : SpatialCoordinates d × SpatialCoordinates d =>
          ((f 0 - g 0) q.1 : ℝ)) =ᵐ[μ.prod μ]
          (fun q => (f 0 q.1 : ℝ) - g 0 q.1) := by
      simpa only [Function.comp_apply] using! hfst
    have hsnd' :
        (fun q : SpatialCoordinates d × SpatialCoordinates d =>
          ((f 0 - g 0) q.2 : ℝ)) =ᵐ[μ.prod μ]
          (fun q => (f 0 q.2 : ℝ) - g 0 q.2) := by
      simpa only [Function.comp_apply] using! hsnd
    have hdiff :
        (fun q : SpatialCoordinates d × SpatialCoordinates d =>
          ((f 0 - g 0) q.1 : ℝ) - (f 0 - g 0) q.2) =ᵐ[μ.prod μ]
          (fun q => (f 0 q.1 - g 0 q.1) - (f 0 q.2 - g 0 q.2)) := by
      filter_upwards [hfst', hsnd'] with q hq₁ hq₂
      rw [hq₁, hq₂]
    filter_upwards [hdiff] with q hq
    dsimp [Factual, Fsub]
    change ENNReal.ofReal
        (((((f 0 - g 0) q.1 : ℝ) - (f 0 - g 0) q.2) ^ 2)) / den q = _
    rw [hq]
  have hIsub_actual :
      (∫⁻ x, ∫⁻ y, Factual (x, y) ∂μ ∂μ) = Isub := by
    calc
      (∫⁻ x, ∫⁻ y, Factual (x, y) ∂μ ∂μ) =
          ∫⁻ q, Factual q ∂μ.prod μ :=
        (lintegral_prod Factual hFactual).symm
      _ = ∫⁻ q, Fsub q ∂μ.prod μ := lintegral_congr_ae hpair
      _ = Isub := lintegral_prod Fsub hFsub
  have hbase : a * Isub ≤ 2 * (a * If) + 2 * (a * Ig) := by
    calc
      a * Isub ≤ a * (2 * If + 2 * Ig) := mul_le_mul_of_nonneg_left hraw zero_le
      _ = 2 * (a * If) + 2 * (a * Ig) := by ring
  have hroot : (a * Isub) ^ (1 / 2 : ℝ) ≤
      2 * ((a * If) ^ (1 / 2 : ℝ) + (a * Ig) ^ (1 / 2 : ℝ)) := by
    calc
      (a * Isub) ^ (1 / 2 : ℝ) ≤
          (2 * (a * If) + 2 * (a * Ig)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hbase (by norm_num)
      _ = (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          ((a * If) + (a * Ig)) ^ (1 / 2 : ℝ) := by
        rw [show 2 * (a * If) + 2 * (a * Ig) =
            (2 : ℝ≥0∞) * ((a * If) + (a * Ig)) by ring,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ ≤ (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          ((a * If) ^ (1 / 2 : ℝ) + (a * Ig) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
      _ ≤ 2 * ((a * If) ^ (1 / 2 : ℝ) + (a * Ig) ^ (1 / 2 : ℝ)) := by
        gcongr
        have h := ENNReal.rpow_le_rpow
          (show (2 : ℝ≥0∞) ≤ 4 by norm_num)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rw [show (4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 2 by norm_num,
          ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h
        norm_num at h ⊢
        exact h
  have hroot_actual :
      (a * (∫⁻ x, ∫⁻ y, Factual (x, y) ∂μ ∂μ)) ^ (1 / 2 : ℝ) ≤
        2 * ((a * If) ^ (1 / 2 : ℝ) + (a * Ig) ^ (1 / 2 : ℝ)) := by
    rw [hIsub_actual]
    exact hroot
  simpa only [cubeFractionalL2Seminorm, U, μ, a, If, Ig, Factual, den,
    Fin.sum_univ_one] using hroot_actual

theorem aux_lem_19_interpolation_upgrade_half_mem
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : Fin 1 → DomainL2 (centeredCube z r hr))
    (hf : cubeFractionalL2Seminorm hd z r hr
        (⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) f < ⊤) :
    cubeFractionalL2Seminorm hd z r hr halfFractionalOrder f < ⊤ := by
  classical
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let Ihalf : ℝ≥0∞ := ∫⁻ x in U, ∫⁻ y in U,
      ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (halfFractionalOrder : ℝ))
  let Ithree : ℝ≥0∞ := ∫⁻ x in U, ∫⁻ y in U,
      ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * ((⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) : ℝ))
  let ahalf : ℝ≥0∞ := ENNReal.ofReal (halfFractionalOrder : ℝ) / volume U
  let athree : ℝ≥0∞ := ENNReal.ofReal
      ((⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) : ℝ) / volume U
  let K : ℝ≥0∞ := (ENNReal.ofReal (Real.sqrt d * r)) ^ (1 / 2 : ℝ)
  have hUmeas : MeasurableSet U := by
    exact centeredCube z r hr |>.isOpen.measurableSet
  have hvol_ne_zero : volume U ≠ 0 := by
    simp only [U, centeredCube_volume]
    exact (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  have hvol_ne_top : volume U ≠ ⊤ := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hKtop : K ≠ ⊤ := by
    dsimp [K]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hbase_three : athree * Ithree < ⊤ := by
    have h := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp hf
    simpa only [cubeFractionalL2Seminorm, U, athree, Ithree, Fin.sum_univ_one] using h
  have hpoint : ∀ x ∈ U, ∀ y ∈ U,
      (ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (halfFractionalOrder : ℝ))) ≤
        K * (ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 *
              ((⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) : ℝ))) := by
    intro x hx y hy
    let q : ℝ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)
    let qe : ℝ≥0∞ := ENNReal.ofReal q
    have hqle : q ≤ Real.sqrt d * r := by
      dsimp [q]
      exact euclideanDist_le_sqrt_dim_mul_side_of_mem_centeredCube z hr hx hy
    have hqnonneg : 0 ≤ q := Real.sqrt_nonneg _
    by_cases hq : q = 0
    · have hsum : (∑ j : Fin d, (x j - y j) ^ 2) = 0 := by
        exact (Real.sqrt_eq_zero (Finset.sum_nonneg fun j _ => sq_nonneg (x j - y j))).mp hq
      have hcoord : ∀ j : Fin d, x j = y j := by
        intro j
        have hle : (x j - y j) ^ 2 ≤ ∑ i : Fin d, (x i - y i) ^ 2 := by
          exact Finset.single_le_sum (fun i _ => sq_nonneg (x i - y i))
            (Finset.mem_univ j)
        have hz : (x j - y j) ^ 2 = 0 := le_antisymm (hsum ▸ hle) (sq_nonneg _)
        nlinarith
      have hxy : x = y := funext hcoord
      simp [hxy]
    · have hqpos : 0 < q := lt_of_le_of_ne hqnonneg (Ne.symm hq)
      have hqetop : qe ≠ ⊤ := ENNReal.ofReal_ne_top
      have hqezero : qe ≠ 0 := (ENNReal.ofReal_pos.mpr hqpos).ne'
      have hqpowpos : 0 < qe ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr hqpos) (by norm_num)
      have hqpowtop : qe ^ (1 / 2 : ℝ) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) hqetop
      have hApos : 0 < qe ^ ((d : ℝ) + 2 * (1 / 2 : ℝ)) :=
        ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr hqpos) (by positivity)
      have hAtop : qe ^ ((d : ℝ) + 2 * (1 / 2 : ℝ)) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) hqetop
      have hK : qe ^ (1 / 2 : ℝ) ≤ K := by
        dsimp [K, qe]
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hqle) (by norm_num)
      have hiden :
          qe ^ (1 / 2 : ℝ) *
              (ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
                qe ^ ((d : ℝ) + 2 *
                  ((⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) : ℝ))) =
            ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
              qe ^ ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) := by
        have hhalf : (halfFractionalOrder : ℝ) = 1 / 2 := rfl
        have hthree :
            (⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) = (3 / 4 : ℝ) := rfl
        have he : (d : ℝ) + 2 * (3 / 4 : ℝ) =
            ((d : ℝ) + 2 * (1 / 2 : ℝ)) + (1 / 2 : ℝ) := by ring
        rw [hhalf, hthree, he, ENNReal.rpow_add _ _ hqezero hqetop]
        rw [ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inr hqpowtop) (Or.inl hAtop)]
        calc
          qe ^ (1 / 2 : ℝ) *
                ((qe ^ ((d : ℝ) + 2 * (1 / 2 : ℝ)))⁻¹ *
                  (qe ^ (1 / 2 : ℝ))⁻¹ *
                  ENNReal.ofReal ((f 0 x - f 0 y) ^ 2)) =
              (qe ^ (1 / 2 : ℝ) * (qe ^ (1 / 2 : ℝ))⁻¹) *
                ((qe ^ ((d : ℝ) + 2 * (1 / 2 : ℝ)))⁻¹ *
                  ENNReal.ofReal ((f 0 x - f 0 y) ^ 2)) := by ac_rfl
          _ = (qe ^ ((d : ℝ) + 2 * (1 / 2 : ℝ)))⁻¹ *
                ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) := by
            rw [ENNReal.mul_inv_cancel hqpowpos.ne' hqpowtop, one_mul]
          _ = ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
                qe ^ ((d : ℝ) + 2 * (1 / 2 : ℝ)) := by
            rw [ENNReal.div_eq_inv_mul]
      calc
        _ = qe ^ (1 / 2 : ℝ) *
            (ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
              qe ^ ((d : ℝ) + 2 *
                ((⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) : ℝ))) := by
          simpa only [qe, q] using hiden.symm
        _ ≤ K * (ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
              qe ^ ((d : ℝ) + 2 *
                ((⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) : ℝ))) :=
          mul_le_mul_of_nonneg_right hK zero_le
        _ = _ := by rfl
  have hinner : ∀ x ∈ U,
      (∫⁻ y in U, ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (halfFractionalOrder : ℝ))) ≤
      K * (∫⁻ y in U, ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 *
            ((⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) : ℝ))) := by
    intro x hx
    calc
      _ ≤ ∫⁻ y in U, K * (ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 *
              ((⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) : ℝ))) := by
        exact setLIntegral_mono_ae' hUmeas
          (ae_of_all _ (fun y hy => hpoint x hx y hy))
      _ = _ := by
        rw [lintegral_const_mul' K _ hKtop]
  have houter :
      ahalf * Ihalf ≤ K * (athree * Ithree) := by
    have hI : Ihalf ≤ K * Ithree := by
      dsimp [Ihalf, Ithree]
      calc
        _ ≤ ∫⁻ x in U, K * (∫⁻ y in U, ENNReal.ofReal ((f 0 x - f 0 y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 *
                ((⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) : ℝ))) := by
          exact setLIntegral_mono_ae' hUmeas
            (ae_of_all _ (fun x hx => hinner x hx))
        _ = _ := by rw [lintegral_const_mul' K _ hKtop]
    have ha : ahalf ≤ athree := by
      dsimp [ahalf, athree]
      gcongr
      change (1 / 2 : ℝ) ≤ 3 / 4
      norm_num
    calc
      ahalf * Ihalf ≤ athree * Ihalf := mul_le_mul_of_nonneg_right ha zero_le
      _ ≤ athree * (K * Ithree) := mul_le_mul_of_nonneg_left hI zero_le
      _ = K * (athree * Ithree) := by ac_rfl
  have hbase : ahalf * Ihalf < ⊤ := by
    have hKlt : K < ⊤ := lt_top_iff_ne_top.mpr hKtop
    have hR : K * (athree * Ithree) < ⊤ := ENNReal.mul_lt_top hKlt hbase_three
    exact lt_of_le_of_lt houter hR
  simpa only [cubeFractionalL2Seminorm, U, ahalf, Ihalf, Fin.sum_univ_one] using
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (ne_of_lt hbase))

theorem aux_lem_19_interpolation_upgrade_norm_sub_le
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1)
    (u v : CubeFractionalL2 (k := 1) hd z r hr s) :
    cubeFractionalL2Norm hd z r hr s
        (⟨fun i => u.val i - v.val i,
          cubeFractionalL2Seminorm_sub_lt_top hd z r hr s u.val v.val
            u.property v.property⟩) ≤
      2 * (cubeFractionalL2Norm hd z r hr s u +
        cubeFractionalL2Norm hd z r hr s v) := by
  classical
  let hsub := cubeFractionalL2Seminorm_sub_lt_top hd z r hr s u.val v.val
    u.property v.property
  let q : CubeFractionalL2 (k := 1) hd z r hr s :=
    ⟨fun i => u.val i - v.val i, hsub⟩
  have hsemi := aux_lem_19_interpolation_upgrade_seminorm_sub_le
    d hd z r hr s u.val v.val
  have hsumtop :
      2 * (cubeFractionalL2Seminorm hd z r hr s u.val +
        cubeFractionalL2Seminorm hd z r hr s v.val) < ⊤ := by
    apply ENNReal.mul_lt_top
    · norm_num
    · exact (ENNReal.add_lt_top.mpr ⟨u.property, v.property⟩)
  have hsemi_real :
      (cubeFractionalL2Seminorm hd z r hr s q.val).toReal ≤
        2 * ((cubeFractionalL2Seminorm hd z r hr s u.val).toReal +
          (cubeFractionalL2Seminorm hd z r hr s v.val).toReal) := by
    have h := (ENNReal.toReal_le_toReal (ne_of_lt hsub) (ne_of_lt hsumtop)).mpr hsemi
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_add (ne_of_lt u.property) (ne_of_lt v.property)] at h
    norm_num at h
    simpa only [q] using h
  have hroot :
      Real.sqrt (∑ i : Fin 1, ‖q.val i‖ ^ 2) ≤
        Real.sqrt (∑ i : Fin 1, ‖u.val i‖ ^ 2) +
          Real.sqrt (∑ i : Fin 1, ‖v.val i‖ ^ 2) := by
    dsimp [q]
    simp only [Fin.sum_univ_one, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact norm_sub_le _ _
  have hfrac :
      Real.sqrt (∑ i : Fin 1, ‖q.val i‖ ^ 2) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        Real.sqrt (∑ i : Fin 1, ‖u.val i‖ ^ 2) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) +
          Real.sqrt (∑ i : Fin 1, ‖v.val i‖ ^ 2) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hroot (Real.sqrt_nonneg _)
  have hL2 :
      r ^ (-(s : ℝ)) *
          (Real.sqrt (∑ i : Fin 1, ‖q.val i‖ ^ 2) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ≤
        r ^ (-(s : ℝ)) *
          (Real.sqrt (∑ i : Fin 1, ‖u.val i‖ ^ 2) /
              Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) +
            Real.sqrt (∑ i : Fin 1, ‖v.val i‖ ^ 2) /
              Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) :=
    mul_le_mul_of_nonneg_left hfrac (by positivity)
  let Su : ℝ := (cubeFractionalL2Seminorm hd z r hr s u.val).toReal
  let Sv : ℝ := (cubeFractionalL2Seminorm hd z r hr s v.val).toReal
  let Sq : ℝ := (cubeFractionalL2Seminorm hd z r hr s q.val).toReal
  let Lu : ℝ := r ^ (-(s : ℝ)) *
    (Real.sqrt (∑ i : Fin 1, ‖u.val i‖ ^ 2) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))
  let Lv : ℝ := r ^ (-(s : ℝ)) *
    (Real.sqrt (∑ i : Fin 1, ‖v.val i‖ ^ 2) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))
  let Lq : ℝ := r ^ (-(s : ℝ)) *
    (Real.sqrt (∑ i : Fin 1, ‖q.val i‖ ^ 2) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))
  have hcombine : Sq + Lq ≤ 2 * ((Su + Lu) + (Sv + Lv)) := by
    have hLu : 0 ≤ Lu := by positivity
    have hLv : 0 ≤ Lv := by positivity
    have hsemi' : Sq ≤ 2 * (Su + Sv) := by
      simpa only [Sq, Su, Sv] using hsemi_real
    have hL2' : Lq ≤ Lu + Lv := by
      simpa only [Lq, Lu, Lv, mul_add] using hL2
    calc
      Sq + Lq ≤ 2 * (Su + Sv) + (Lu + Lv) := add_le_add hsemi' hL2'
      _ ≤ 2 * ((Su + Lu) + (Sv + Lv)) := by nlinarith
  simpa only [cubeFractionalL2Norm, q, Su, Sv, Sq, Lu, Lv, Lq,
    Fin.sum_univ_one] using hcombine

/-- Final interpolation step of Lemma 19, paper label `mfd:lem-19`.
Inputs:
- SOURCE: arbitrary positive-side cube, H3/4-bounded sequence and its actual
  L2 limit, as in the paper.
- PUBLISHED INPUT: hInterp is the existing deferred fractional interpolation
  input (Di Nezza–Palatucci–Valdinoci / Lions–Magenes), invoked explicitly; its cube-dependent normalization is recorded.
- DEPENDENCY lem_19_limit_membership concludes the H3/4 membership and bound
  of the L2 limit, needed to form bounded H3/4 differences before interpolation.
- CONCLUDED HERE: H1/2 membership of the limit, admissible H1/2 differences
  and full-sequence H1/2 convergence. None is a carried hypothesis.
The type is exactly the second conjunct of lem_19, without unused t data. -/
theorem lem_19_interpolation_upgrade
    (d : ℕ) (hd : 2 ≤ d) (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∀ (threeQuarters : Set.Ioo (0 : ℝ) 1), (threeQuarters : ℝ) = 3 / 4 →
      ∀ (w : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters)
        (vlim : DomainL2 (centeredCube z r hr)) (M : ℝ),
        (∀ n : ℕ, cubeFractionalL2Norm hd z r hr threeQuarters (w n) ≤ M) →
        Tendsto (fun n : ℕ => (w n).val 0) atTop (𝓝 vlim) →
        ∃ vhalf : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
          vhalf.val 0 = vlim ∧
          ∃ diff : ℕ → CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
            (∀ n : ℕ, (diff n).val 0 = (w n).val 0 - vlim) ∧
            Tendsto (fun n : ℕ =>
              cubeFractionalL2Norm hd z r hr halfFractionalOrder (diff n))
              atTop (𝓝 0) := by
  intro threeQuarters hthree
  have hthreeQuarters :
      threeQuarters = (⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) := by
    apply Subtype.ext
    exact hthree
  subst threeQuarters
  intro w vlim M hbound hlim
  let threeQuarters : Set.Ioo (0 : ℝ) 1 :=
    ⟨3 / 4, by norm_num, by norm_num⟩
  obtain ⟨vthree, hvthree, hvthreebound⟩ :=
    lem_19_limit_membership d hd z r hr threeQuarters rfl w vlim M hbound hlim
  have hvhalf_mem : cubeFractionalL2Seminorm hd z r hr halfFractionalOrder vthree.val < ⊤ :=
    aux_lem_19_interpolation_upgrade_half_mem d hd z r hr vthree.val vthree.property
  let vhalf : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder :=
    ⟨vthree.val, hvhalf_mem⟩
  let diffThree : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters := fun n =>
    ⟨fun i => (w n).val i - vthree.val i,
      cubeFractionalL2Seminorm_sub_lt_top hd z r hr threeQuarters
        (w n).val vthree.val (w n).property vthree.property⟩
  let diff : ℕ → CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder := fun n =>
    ⟨(diffThree n).val,
      aux_lem_19_interpolation_upgrade_half_mem d hd z r hr
        (diffThree n).val (diffThree n).property⟩
  have hdiff_val : ∀ n, (diff n).val 0 = (w n).val 0 - vlim := by
    intro n
    dsimp [diff, diffThree]
    rw [hvthree]
  have hdiff_bound : ∀ n,
      cubeFractionalL2Norm hd z r hr threeQuarters (diffThree n) ≤ 4 * M := by
    have hM : 0 ≤ M := by
      have hnon : 0 ≤ cubeFractionalL2Norm hd z r hr threeQuarters (w 0) := by
        unfold cubeFractionalL2Norm
        positivity
      linarith [hbound 0]
    intro n
    have haux := aux_lem_19_interpolation_upgrade_norm_sub_le
      d hd z r hr threeQuarters (w n) vthree
    calc
      cubeFractionalL2Norm hd z r hr threeQuarters (diffThree n) ≤
          2 * (cubeFractionalL2Norm hd z r hr threeQuarters (w n) +
            cubeFractionalL2Norm hd z r hr threeQuarters vthree) := by
        simpa only [diffThree] using haux
      _ ≤ 4 * M := by
        linarith [hbound n, hvthreebound]
  obtain ⟨C, hC, hinterp⟩ :=
    hInterp.interpolation_half z r hr threeQuarters rfl
  have hnorm : Tendsto (fun n : ℕ => ‖(w n).val 0 - vlim‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
  have hdiv : Tendsto
      (fun n : ℕ => ‖(w n).val 0 - vlim‖ /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))
      atTop (𝓝 0) := by
    simpa using hnorm.div_const
      (Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))
  have hpow : Tendsto
      (fun n : ℕ =>
        (‖(w n).val 0 - vlim‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
            (1 / 3 : ℝ)) atTop (𝓝 0) := by
    have hexp : Tendsto (fun _ : ℕ => (1 / 3 : ℝ)) atTop (𝓝 (1 / 3 : ℝ)) :=
      tendsto_const_nhds
    simpa using hdiv.rpow hexp (Or.inr (by norm_num))
  have hM4 : 0 ≤ 4 * M := by
    have hnon : 0 ≤ cubeFractionalL2Norm hd z r hr threeQuarters (w 0) := by
      unfold cubeFractionalL2Norm
      positivity
    linarith [hbound 0]
  have hupper : ∀ n,
      cubeFractionalL2Norm hd z r hr halfFractionalOrder (diff n) ≤
        C * (‖(w n).val 0 - vlim‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
            (1 / 3 : ℝ) * (4 * M) ^ (2 / 3 : ℝ) := by
    intro n
    have hi := hinterp (diff n) (diffThree n) (by
      rfl)
    have hpow_bound :
        cubeFractionalL2Norm hd z r hr threeQuarters (diffThree n) ^ (2 / 3 : ℝ) ≤
          (4 * M) ^ (2 / 3 : ℝ) := by
      apply Real.rpow_le_rpow
      · unfold cubeFractionalL2Norm
        positivity
      · exact hdiff_bound n
      · norm_num
    calc
      cubeFractionalL2Norm hd z r hr halfFractionalOrder (diff n) ≤
          C * (‖(diff n).val 0‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
              (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd z r hr threeQuarters (diffThree n) ^
              (2 / 3 : ℝ) := hi
      _ = C * (‖(w n).val 0 - vlim‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
              (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd z r hr threeQuarters (diffThree n) ^
              (2 / 3 : ℝ) := by rw [hdiff_val n]
      _ ≤ C * (‖(w n).val 0 - vlim‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
              (1 / 3 : ℝ) * (4 * M) ^ (2 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_left hpow_bound
        positivity
  have hupper_tendsto : Tendsto
      (fun n : ℕ =>
        C * (‖(w n).val 0 - vlim‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
            (1 / 3 : ℝ) * (4 * M) ^ (2 / 3 : ℝ)) atTop (𝓝 0) := by
    have hCt : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    have hBt : Tendsto (fun _ : ℕ => (4 * M) ^ (2 / 3 : ℝ)) atTop
        (𝓝 ((4 * M) ^ (2 / 3 : ℝ))) := tendsto_const_nhds
    simpa using (hCt.mul hpow).mul hBt
  refine ⟨vhalf, ?_, diff, hdiff_val, ?_⟩
  · simpa only [vhalf] using hvthree
  · apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n => by
        unfold cubeFractionalL2Norm
        positivity)
    · exact Filter.Eventually.of_forall hupper
    · exact hupper_tendsto

end SubdiffusiveProcess.Paper
