module

public import SubdiffusiveProcess.Paper.lem_19_smooth_trace_bound
public import SubdiffusiveProcess.Paper.lem_19_smooth_density
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Sobolev.FractionalSubtraction
public import SubdiffusiveProcess.Sobolev.MeasureTraceBoundedDensity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_lem_19_trace_completion_norm_sub
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u v w : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    (hw : w.val 0 = u.val 0 - v.val 0) :
    cubeFractionalL2Norm hd z r hr halfFractionalOrder w ≤
      2 * (cubeFractionalL2Norm hd z r hr halfFractionalOrder u +
        cubeFractionalL2Norm hd z r hr halfFractionalOrder v) := by
  classical
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let a : ℝ≥0∞ := ENNReal.ofReal (halfFractionalOrder : ℝ) / volume U
  let f := u.val
  let g := v.val
  let If : ℝ≥0∞ := ∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (∑ i : Fin 1, (f i x - f i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ∂μ ∂μ
  let Ig : ℝ≥0∞ := ∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (∑ i : Fin 1, (g i x - g i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ∂μ ∂μ
  let Isub : ℝ≥0∞ := ∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (∑ i : Fin 1,
        ((f i - g i) x - (f i - g i) y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ∂μ ∂μ
  have hvoltop : volume U ≠ ⊤ := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hvolpos : 0 < volume U := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_pos.mpr (pow_pos hr _)
  have ha0 : a ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    exact ⟨(ENNReal.ofReal_pos.mpr halfFractionalOrder.2.1).ne', hvoltop⟩
  have hfa : (a * If) ^ (1 / 2 : ℝ) < ⊤ := by
    simpa only [a, If, U, μ, f, cubeFractionalL2Seminorm] using! u.property
  have hga : (a * Ig) ^ (1 / 2 : ℝ) < ⊤ := by
    simpa only [a, Ig, U, μ, g, cubeFractionalL2Seminorm] using! v.property
  have hIf : If < ⊤ := by
    have hprod : a * If < ⊤ := by
      by_contra h
      have heq : a * If = ⊤ := top_unique (le_of_not_gt h)
      exact (ne_of_lt hfa) (by rw [heq, ENNReal.top_rpow_of_pos (by norm_num)])
    rcases (ENNReal.mul_lt_top_iff.mp hprod) with h | h | h
    · exact h.2
    · exact (ha0 h).elim
    · simp [h]
  have hIg : Ig < ⊤ := by
    have hprod : a * Ig < ⊤ := by
      by_contra h
      have heq : a * Ig = ⊤ := top_unique (le_of_not_gt h)
      exact (ne_of_lt hga) (by rw [heq, ENNReal.top_rpow_of_pos (by norm_num)])
    rcases (ENNReal.mul_lt_top_iff.mp hprod) with h | h | h
    · exact h.2
    · exact (ha0 h).elim
    · simp [h]
  have hfi (i : Fin 1) : AEStronglyMeasurable (fun x => (f i x : ℝ)) μ := by
    simpa only [μ, f] using! (Lp.aestronglyMeasurable (u.val i))
  have hgi (i : Fin 1) : AEStronglyMeasurable (fun x => (g i x : ℝ)) μ := by
    simpa only [μ, g] using! (Lp.aestronglyMeasurable (v.val i))
  have hcoordf (i : Fin 1) :
      AEMeasurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        (f i q.1 - f i q.2) ^ 2) (μ.prod μ) := by
    exact (((hfi i).aemeasurable.comp_fst).sub
      ((hfi i).aemeasurable.comp_snd)).pow_const 2
  have hcoordg (i : Fin 1) :
      AEMeasurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        (g i q.1 - g i q.2) ^ 2) (μ.prod μ) := by
    exact (((hgi i).aemeasurable.comp_fst).sub
      ((hgi i).aemeasurable.comp_snd)).pow_const 2
  have hnumf : AEMeasurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        ∑ i : Fin 1, (f i q.1 - f i q.2) ^ 2) (μ.prod μ) :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ => hcoordf i
  have hnumg : AEMeasurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        ∑ i : Fin 1, (g i q.1 - g i q.2) ^ 2) (μ.prod μ) :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ => hcoordg i
  have hden : Measurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2))) ^
          ((d : ℝ) + 2 * (halfFractionalOrder : ℝ))) := by
    apply Measurable.pow
    · apply Measurable.ennreal_ofReal
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun j _ =>
        (((measurable_pi_apply j).comp measurable_fst).sub
          ((measurable_pi_apply j).comp measurable_snd)).pow_const 2
    · exact measurable_const
  let Tf : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (∑ i : Fin 1, (f i q.1 - f i q.2) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2))) ^
        ((d : ℝ) + 2 * (halfFractionalOrder : ℝ))
  let Tg : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (∑ i : Fin 1, (g i q.1 - g i q.2) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2))) ^
        ((d : ℝ) + 2 * (halfFractionalOrder : ℝ))
  have hTf : AEMeasurable Tf (μ.prod μ) := by
    exact hnumf.ennreal_ofReal.div hden.aemeasurable
  have hTg : AEMeasurable Tg (μ.prod μ) := by
    exact hnumg.ennreal_ofReal.div hden.aemeasurable
  have hTf_x (x : SpatialCoordinates d) : AEMeasurable (fun y => Tf (x, y)) μ := by
    have hnum : AEMeasurable (fun y => ∑ i : Fin 1, (f i x - f i y) ^ 2) μ :=
      Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
        (measurable_const.aemeasurable.sub (hfi i).aemeasurable).pow_const 2
    have hdenx : Measurable (fun y : SpatialCoordinates d =>
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (halfFractionalOrder : ℝ))) := by
      apply Measurable.pow
      · apply Measurable.ennreal_ofReal
        apply Measurable.sqrt
        exact Finset.measurable_sum Finset.univ fun j _ =>
          (measurable_const.sub (measurable_pi_apply j)).pow_const 2
      · exact measurable_const
    exact hnum.ennreal_ofReal.div hdenx.aemeasurable
  have hTg_x (x : SpatialCoordinates d) : AEMeasurable (fun y => Tg (x, y)) μ := by
    have hnum : AEMeasurable (fun y => ∑ i : Fin 1, (g i x - g i y) ^ 2) μ :=
      Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
        (measurable_const.aemeasurable.sub (hgi i).aemeasurable).pow_const 2
    have hdenx : Measurable (fun y : SpatialCoordinates d =>
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (halfFractionalOrder : ℝ))) := by
      apply Measurable.pow
      · apply Measurable.ennreal_ofReal
        apply Measurable.sqrt
        exact Finset.measurable_sum Finset.univ fun j _ =>
          (measurable_const.sub (measurable_pi_apply j)).pow_const 2
      · exact measurable_const
    exact hnum.ennreal_ofReal.div hdenx.aemeasurable
  have hinnerf : AEMeasurable (fun x => ∫⁻ y, Tf (x, y) ∂μ) μ :=
    hTf.lintegral_prod_right
  have hinnerg : AEMeasurable (fun x => ∫⁻ y, Tg (x, y) ∂μ) μ :=
    hTg.lintegral_prod_right
  have hpoint (x y : SpatialCoordinates d) :
      ENNReal.ofReal (∑ i : Fin 1, ((f i x - g i x) - (f i y - g i y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ≤
        2 * Tf (x, y) + 2 * Tg (x, y) := by
    have hi (i : Fin 1) :
        ((f i x - g i x) - (f i y - g i y)) ^ 2 ≤
          2 * (f i x - f i y) ^ 2 + 2 * (g i x - g i y) ^ 2 := by
      nlinarith [sq_nonneg ((f i x - f i y) + (g i x - g i y))]
    have hs :
        ∑ i : Fin 1, ((f i x - g i x) - (f i y - g i y)) ^ 2 ≤
          2 * (∑ i : Fin 1, (f i x - f i y) ^ 2) +
            2 * (∑ i : Fin 1, (g i x - g i y) ^ 2) := by
      calc
        _ ≤ ∑ i : Fin 1, (2 * (f i x - f i y) ^ 2 +
            2 * (g i x - g i y) ^ 2) := Finset.sum_le_sum fun i _ => hi i
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have hsf : 0 ≤ ∑ i : Fin 1, (f i x - f i y) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsg : 0 ≤ ∑ i : Fin 1, (g i x - g i y) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hdiv :
        ENNReal.ofReal (∑ i : Fin 1,
          ((f i x - g i x) - (f i y - g i y)) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ≤
          ENNReal.ofReal (2 * (∑ i : Fin 1, (f i x - f i y) ^ 2) +
              2 * (∑ i : Fin 1, (g i x - g i y) ^ 2)) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) :=
      ENNReal.div_le_div (ENNReal.ofReal_le_ofReal hs) (le_refl _)
    have heq :
        ENNReal.ofReal (2 * (∑ i : Fin 1, (f i x - f i y) ^ 2) +
            2 * (∑ i : Fin 1, (g i x - g i y) ^ 2)) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) =
          2 * Tf (x, y) + 2 * Tg (x, y) := by
      dsimp [Tf, Tg]
      rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hsf)
        (mul_nonneg (by norm_num) hsg)]
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
      rw [ENNReal.add_div, mul_div_assoc, mul_div_assoc]
      norm_num
    exact hdiv.trans_eq heq
  have hinner (x : SpatialCoordinates d) :
      (∫⁻ y, ENNReal.ofReal (∑ i : Fin 1,
          ((f i x - g i x) - (f i y - g i y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ∂μ) ≤
        2 * (∫⁻ y, Tf (x, y) ∂μ) + 2 * (∫⁻ y, Tg (x, y) ∂μ) := by
    have hmono := lintegral_mono (μ := μ) (fun y => hpoint x y)
    calc
      _ ≤ ∫⁻ y, 2 * Tf (x, y) + 2 * Tg (x, y) ∂μ := hmono
      _ = _ := by
        have hTf2 : AEMeasurable (fun y => (2 : ℝ≥0∞) * Tf (x, y)) μ :=
          measurable_const.aemeasurable.mul (hTf_x x)
        rw [lintegral_add_left' hTf2]
        rw [lintegral_const_mul'' 2 (hTf_x x)]
        rw [lintegral_const_mul'' 2 (hTg_x x)]
  have houter' :
      (∫⁻ x, ∫⁻ y,
        ENNReal.ofReal (∑ i : Fin 1,
          ((f i x - g i x) - (f i y - g i y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ∂μ ∂μ) ≤
        2 * (∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (∑ i : Fin 1, (f i x - f i y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ∂μ ∂μ) +
        2 * (∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (∑ i : Fin 1, (g i x - g i y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ∂μ ∂μ) := by
    have hmono := lintegral_mono (μ := μ) (fun x => hinner x)
    calc
      _ ≤ ∫⁻ x, 2 * (∫⁻ y, Tf (x, y) ∂μ) +
          2 * (∫⁻ y, Tg (x, y) ∂μ) ∂μ := hmono
      _ = 2 * (∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (∑ i : Fin 1, (f i x - f i y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ∂μ ∂μ) +
          2 * (∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (∑ i : Fin 1, (g i x - g i y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ∂μ ∂μ) := by
        have hinnerf2 : AEMeasurable
            (fun x => (2 : ℝ≥0∞) * (∫⁻ y, Tf (x, y) ∂μ)) μ :=
          measurable_const.aemeasurable.mul hinnerf
        rw [lintegral_add_left' hinnerf2]
        rw [lintegral_const_mul'' 2 hinnerf]
        rw [lintegral_const_mul'' 2 hinnerg]
  have hsub_all : ∀ᵐ x ∂μ, ∀ i : Fin 1, (f i - g i) x = f i x - g i x := by
    exact ae_all_iff.mpr fun i => Lp.coeFn_sub (f i) (g i)
  have hIsub_eq : Isub =
      (∫⁻ x, ∫⁻ y,
        ENNReal.ofReal (∑ i : Fin 1,
          ((f i x - g i x) - (f i y - g i y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (halfFractionalOrder : ℝ)) ∂μ ∂μ) := by
    dsimp [Isub]
    apply lintegral_congr_ae
    filter_upwards [hsub_all] with x hx
    apply lintegral_congr_ae
    filter_upwards [hsub_all] with y hy
    congr 1
    apply congrArg ENNReal.ofReal
    apply Finset.sum_congr rfl
    intro i hi
    change (((f i - g i : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x -
      ((f i - g i : DomainL2 (centeredCube z r hr)) :
        SpatialCoordinates d → ℝ) y) ^ 2 = _
    rw [hx i, hy i]
  have houter : Isub ≤ 2 * If + 2 * Ig := by
    rw [hIsub_eq]
    exact houter'
  have hsum : 2 * If + 2 * Ig < ⊤ := by
    apply ENNReal.add_lt_top.mpr
    constructor <;> exact ENNReal.mul_lt_top (by norm_num) (by finiteness)
  have hIsub : Isub < ⊤ := lt_of_le_of_lt houter hsum
  have hprodsub : a * Isub < ⊤ := ENNReal.mul_lt_top
    (by
      dsimp [a]
      exact ENNReal.div_lt_top ENNReal.ofReal_ne_top (ne_of_gt hvolpos)) hIsub
  have hsubpow : (a * Isub) ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hprodsub.ne
  have hprod : a * Isub ≤ 2 * (a * If) + 2 * (a * Ig) := by
    calc
      a * Isub ≤ a * (2 * If + 2 * Ig) := mul_le_mul_of_nonneg_left houter zero_le
      _ = 2 * (a * If) + 2 * (a * Ig) := by
        rw [mul_add]
        ring
  have hprodreal : (a * Isub).toReal ≤ 2 * (a * If).toReal +
      2 * (a * Ig).toReal := by
    have h := ENNReal.toReal_mono (by finiteness :
        (2 * (a * If) + 2 * (a * Ig)) ≠ ⊤) hprod
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul] at h
    norm_num at h ⊢
    exact h
  have hroot : Real.sqrt (a * Isub).toReal ≤
      2 * (Real.sqrt (a * If).toReal + Real.sqrt (a * Ig).toReal) := by
    have hIf0 : 0 ≤ (a * If).toReal := ENNReal.toReal_nonneg
    have hIg0 : 0 ≤ (a * Ig).toReal := ENNReal.toReal_nonneg
    have hsq : 2 * (a * If).toReal + 2 * (a * Ig).toReal ≤
        (2 * (Real.sqrt (a * If).toReal + Real.sqrt (a * Ig).toReal)) ^ 2 := by
      nlinarith [Real.sq_sqrt hIf0, Real.sq_sqrt hIg0,
        mul_nonneg (Real.sqrt_nonneg (a * If).toReal)
          (Real.sqrt_nonneg (a * Ig).toReal)]
    exact (Real.sqrt_le_left (by positivity)).2 (hprodreal.trans hsq)
  have hsem : ((a * Isub) ^ (1 / 2 : ℝ)).toReal ≤
      2 * (((a * If) ^ (1 / 2 : ℝ)).toReal +
        ((a * Ig) ^ (1 / 2 : ℝ)).toReal) := by
    simpa only [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow] using! hroot
  have hsem' : (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder w.val).toReal ≤
      2 * ((cubeFractionalL2Seminorm hd z r hr halfFractionalOrder u.val).toReal +
        (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder v.val).toReal) := by
    have hwu : w.val = fun i => u.val i - v.val i := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst hi
      exact hw
    rw [hwu]
    simpa only [a, If, Ig, Isub, U, μ, f, g, cubeFractionalL2Seminorm] using! hsem
  have hnorm_sub : ‖w.val 0‖ ≤ ‖u.val 0‖ + ‖v.val 0‖ := by
    rw [hw]
    exact norm_sub_le _ _
  have hκ : 0 ≤ r ^ (-(halfFractionalOrder : ℝ)) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    div_nonneg (Real.rpow_nonneg hr.le _) (Real.sqrt_nonneg _)
  have hform (q : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder) :
      cubeFractionalL2Norm hd z r hr halfFractionalOrder q =
        (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder q.val).toReal +
          (r ^ (-(halfFractionalOrder : ℝ)) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) *
            ‖q.val 0‖ := by
    unfold cubeFractionalL2Norm
    rw [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
    ring
  rw [hform w, hform u, hform v]
  have hmul : 0 ≤ (r ^ (-(halfFractionalOrder : ℝ)) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) *
      (‖u.val 0‖ + ‖v.val 0‖) := mul_nonneg hκ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  nlinarith [hsem', hnorm_sub, hκ]

lemma aux_lem_19_trace_completion_sqrt_tendsto_zero
    {a : ℝ} {q : ℕ → ℝ}
    (h : Tendsto (fun n => a * (q n) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (a * (q n) ^ 2)) atTop (𝓝 0) := by
  have hs := h.sqrt
  simpa only [Real.sqrt_zero] using! hs

lemma aux_lem_19_trace_completion_tendsto_of_rev_norm
    {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (y : E)
    (h : Tendsto (fun n => ‖y - x n‖) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 y) := by
  have h' : Tendsto (fun n => ‖x n - y‖) atTop (𝓝 0) :=
    Filter.Tendsto.congr (fun n => norm_sub_rev _ _) h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr h'

lemma aux_lem_19_trace_completion_norm_tendsto_of_sq
    {E : Type*} [NormedAddCommGroup E]
    {B : ℝ} (X : ℕ → E) (q : ℕ → ℝ)
    (hsq : ∀ n, ‖X n‖ ^ 2 ≤ B * (q n) ^ 2)
    (hq : Tendsto q atTop (𝓝 0)) :
    Tendsto (fun n => ‖X n‖) atTop (𝓝 0) := by
  have harg : Tendsto (fun n => B * (q n) ^ 2) atTop (𝓝 0) := by
    convert Filter.Tendsto.const_mul B (hq.pow 2) using 1 ; norm_num
  have hsqrt : Tendsto (fun n => Real.sqrt (B * (q n) ^ 2)) atTop (𝓝 0) :=
    aux_lem_19_trace_completion_sqrt_tendsto_zero harg
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n => norm_nonneg (X n))
  · exact Filter.Eventually.of_forall (fun n => Real.le_sqrt_of_sq_le (hsq n))
  · exact hsqrt

lemma aux_lem_19_trace_completion_exists_sub
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder) :
    ∃ w : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
      w.val 0 = u.val 0 - v.val 0 := by
  refine ⟨⟨fun i => u.val i - v.val i,
    cubeFractionalL2Seminorm_sub_lt_top hd z r hr halfFractionalOrder
      u.val v.val u.property v.property⟩, ?_⟩
  rfl

lemma aux_lem_19_trace_completion_unique
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (nu : Measure (SpatialCoordinates d)) (C B : ℝ)
    (hmem : ∀ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f → MemLp f 2 nu)
    (T T' : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder → Lp ℝ 2 nu)
    (hTdiff : ∀ (u v w : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
      w.val 0 = u.val 0 - v.val 0 →
        ‖T u - T v‖ ^ 2 ≤ C * B *
          (cubeFractionalL2Norm hd z r hr halfFractionalOrder w) ^ 2)
    (hT'diff : ∀ (u v w : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
      w.val 0 = u.val 0 - v.val 0 →
        ‖T' u - T' v‖ ^ 2 ≤ C * B *
          (cubeFractionalL2Norm hd z r hr halfFractionalOrder w) ^ 2)
    (hTsmooth : ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
        (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f →
        ∀ hf : MemLp f 2 nu, T v = hf.toLp f)
    (hT'smooth : ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
        (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f →
        ∀ hf : MemLp f 2 nu, T' v = hf.toLp f) :
    T' = T := by
  classical
  funext u
  obtain ⟨a, f, w, hfcont, hfae, hwdiff, hwlim⟩ :=
    lem_19_smooth_density d hd z r hr u
  have haeq : ∀ n, T' (a n) = T (a n) := by
    intro n
    exact (hT'smooth (f n) (hfcont n) (a n) (hfae n)
      (hmem (f n) (hfcont n))).trans
      (hTsmooth (f n) (hfcont n) (a n) (hfae n)
        (hmem (f n) (hfcont n))).symm
  have hnorm₁ : Tendsto (fun n => ‖T' u - T' (a n)‖) atTop (𝓝 0) := by
    have hsq : ∀ n, ‖T' u - T' (a n)‖ ^ 2 ≤
        C * B * (cubeFractionalL2Norm hd z r hr halfFractionalOrder (w n)) ^ 2 := by
      intro n
      exact hT'diff u (a n) (w n) (hwdiff n)
    exact aux_lem_19_trace_completion_norm_tendsto_of_sq
      (fun n => T' u - T' (a n))
      (fun n => cubeFractionalL2Norm hd z r hr halfFractionalOrder (w n))
      hsq hwlim
  have hnorm₂ : Tendsto (fun n => ‖T (a n) - T u‖) atTop (𝓝 0) := by
    have hsq : ∀ n, ‖T u - T (a n)‖ ^ 2 ≤
        C * B * (cubeFractionalL2Norm hd z r hr halfFractionalOrder (w n)) ^ 2 := by
      intro n
      exact hTdiff u (a n) (w n) (hwdiff n)
    have hbase := aux_lem_19_trace_completion_norm_tendsto_of_sq
      (fun n => T u - T (a n))
      (fun n => cubeFractionalL2Norm hd z r hr halfFractionalOrder (w n))
      hsq hwlim
    have hfe : (fun n => ‖T (a n) - T u‖) =
        fun n => ‖T u - T (a n)‖ := by
      funext n
      exact norm_sub_rev _ _
    rw [hfe]
    exact hbase
  have hsum : Tendsto
      (fun n => ‖T' u - T' (a n)‖ + ‖T (a n) - T u‖)
      atTop (𝓝 0) := by
    simpa only [add_zero] using! hnorm₁.add hnorm₂
  have htri (x y z : Lp ℝ 2 nu) :
      ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
    simpa only [dist_eq_norm] using! (dist_triangle x y z)
  have hfixed : ‖T' u - T u‖ ≤ 0 := by
    apply ge_of_tendsto hsum
    exact Filter.Eventually.of_forall fun n => by
      calc
        ‖T' u - T u‖ ≤ ‖T' u - T' (a n)‖ + ‖T' (a n) - T u‖ :=
          htri _ _ _
        _ ≤ ‖T' u - T' (a n)‖ +
            (‖T' (a n) - T (a n)‖ + ‖T (a n) - T u‖) := by
          gcongr
          exact htri _ _ _
        _ = ‖T' u - T' (a n)‖ + ‖T (a n) - T u‖ := by
          rw [haeq n]
          simp only [sub_self, norm_zero, zero_add]
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hfixed (norm_nonneg _)))

/-- Completion and bounded-density identification in Lemma 19, `mfd:lem-19`.
Carried-input tick list:
- SOURCE: cube, exponent, finite supported measure and ball-growth bound are
  exactly `mfd:lem-19`; the constant precedes the measure and K.
- DEPENDENCY lem_19_smooth_trace_bound concludes the smooth-data estimate
  by the cell-average argument.
- DEPENDENCY lem_19_smooth_density concludes the approximation used in
  completion and uniqueness.
- CONCLUDED HERE: existence and uniqueness of the completed trace, admissible
  differences, the difference estimate, smooth identification, the norm bound
  and ordinary L2 identification for a bounded density.
The two cited results are imported conclusions, not theorem hypotheses.
This is exactly the first conjunct of lem_19, with no interpolation premise. -/
theorem lem_19_trace_completion
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (nu : Measure (SpatialCoordinates d)) (K : ℝ),
        nu Set.univ < (⊤ : ℝ≥0∞) →
        nu (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0 →
        0 ≤ K →
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            nu (Metric.ball x rr) ≤ ENNReal.ofReal (K * rr ^ t)) →
        ∃! T : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder →
            Lp ℝ 2 nu,
          (∀ u v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
            ∃ w : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
              w.val 0 = u.val 0 - v.val 0) ∧
          (∀ (u v w : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
            w.val 0 = u.val 0 - v.val 0 →
            ‖T u - T v‖ ^ 2 ≤
              C * (K + (nu (closure
                    (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) *
                (cubeFractionalL2Norm hd z r hr halfFractionalOrder w) ^ 2) ∧
          (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
            ∀ (v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
              (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d))] f →
              ∀ hf : MemLp f 2 nu, T v = hf.toLp f) ∧
          (∀ u : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
            ‖T u‖ ^ 2 ≤
              C * (K + (nu (closure
                    (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) *
                (cubeFractionalL2Norm hd z r hr halfFractionalOrder u) ^ 2) ∧
          (∀ D : ℝ, 0 ≤ D →
            nu ≤ ENNReal.ofReal D •
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) →
            ∀ u : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
              MemLp (u.val 0) 2 nu ∧
                ∀ hu : MemLp (u.val 0) 2 nu, T u = hu.toLp (u.val 0)) := by
  classical
  obtain ⟨C₀, hC₀, hbound₀⟩ := lem_19_smooth_trace_bound d hd z r hr t ht
  refine ⟨4 * C₀, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro nu K hnu hsupp hK hgrowth
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let X := CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder
  let B : ℝ := K + (nu (closure U)).toReal
  let : IsFiniteMeasure nu := ⟨hnu⟩
  have hB : 0 ≤ B := by
    exact add_nonneg hK ENNReal.toReal_nonneg
  have hmem (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f) : MemLp f 2 nu :=
    (hbound₀ nu K hnu hsupp hK hgrowth f hf).1
  have hdense (u : X) :
      ∃ (a : ℕ → X) (f : ℕ → SpatialCoordinates d → ℝ)
        (diff : ℕ → X),
        (∀ n, ContDiff ℝ ∞ (f n)) ∧
        (∀ n, ((a n).val 0 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict U] f n) ∧
        (∀ n, (diff n).val 0 = u.val 0 - (a n).val 0) ∧
        Tendsto (fun n => cubeFractionalL2Norm hd z r hr halfFractionalOrder (diff n))
          atTop (𝓝 0) := by
    simpa only [U, X] using! lem_19_smooth_density d hd z r hr u
  choose aa ff dd hff hfae hdd hlim using hdense
  have hfmem (u : X) (n : ℕ) : MemLp (ff u n) 2 nu :=
    hmem (ff u n) (hff u n)
  let P : X → ℕ → Lp ℝ 2 nu := fun u n => (hfmem u n).toLp (ff u n)
  let qv : X → ℝ := fun v =>
    cubeFractionalL2Norm hd z r hr halfFractionalOrder v
  let q : X → ℕ → ℝ := fun u n =>
    qv (dd u n)
  have hqnonneg (u : X) (n : ℕ) : 0 ≤ q u n := by
    dsimp [q, qv]
    unfold cubeFractionalL2Norm
    exact add_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (Real.rpow_nonneg hr.le _) (div_nonneg
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  have hform (v : X) :
      cubeFractionalL2Norm hd z r hr halfFractionalOrder v =
        (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder v.val).toReal +
          (r ^ (-(halfFractionalOrder : ℝ)) /
            Real.sqrt (volume.real U)) * ‖v.val 0‖ := by
    unfold cubeFractionalL2Norm
    rw [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
    ring
  let W (u v : X) (n m : ℕ) : X :=
    (aux_lem_19_trace_completion_exists_sub hd z r hr (aa u n) (aa v m)).choose
  have hW (u v : X) (n m : ℕ) :
      (W u v n m).val 0 = (aa u n).val 0 - (aa v m).val 0 := by
    exact (aux_lem_19_trace_completion_exists_sub hd z r hr
      (aa u n) (aa v m)).choose_spec
  have hPdiff (u v : X) (n m : ℕ) :
      ‖P u n - P v m‖ ^ 2 ≤
        C₀ * B * (qv (W u v n m) ^ 2) := by
    have hwae :
        ((W u v n m).val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict U]
          (ff u n - ff v m) := by
      rw [hW]
      filter_upwards [Lp.coeFn_sub ((aa u n).val 0) ((aa v m).val 0),
        hfae u n, hfae v m] with x hx hxu hxv
      calc
        ((aa u n).val 0 - (aa v m).val 0) x =
            (aa u n).val 0 x - (aa v m).val 0 x := hx
        _ = ff u n x - ff v m x := by rw [hxu, hxv]
    have hineq := (hbound₀ nu K hnu hsupp hK hgrowth
      (ff u n - ff v m) ((hff u n).sub (hff v m))).2.2
        (W u v n m) hwae
      ((hfmem u n).sub (hfmem v m))
    have hsublp :
        ((hfmem u n).sub (hfmem v m)).toLp (ff u n - ff v m) =
          P u n - P v m := (hfmem u n).toLp_sub (hfmem v m)
    rw [← hsublp]
    simpa [B, U] using! hineq
  have hdiff_bound (u : X) (n m : ℕ) :
      ‖P u n - P u m‖ ^ 2 ≤
        C₀ * B * (2 * (q u n + q u m)) ^ 2 := by
    have hqW := aux_lem_19_trace_completion_norm_sub hd z r hr
      (dd u m) (dd u n) (W u u n m)
    have hrel : (W u u n m).val 0 = (dd u m).val 0 - (dd u n).val 0 := by
      rw [hW u u n m, hdd u m, hdd u n]
      abel
    have hqW' : qv (W u u n m) ≤ 2 * (q u m + q u n) := by
      simpa [q] using! hqW hrel
    have hmain := hPdiff u u n m
    have hcoef : 0 ≤ C₀ * B := mul_nonneg hC₀ hB
    have hsq : qv (W u u n m) ^ 2 ≤ (2 * (q u m + q u n)) ^ 2 := by
      nlinarith [hqW', hqnonneg u m, hqnonneg u n,
        show 0 ≤ qv (W u u n m) from by
          dsimp [qv]
          unfold cubeFractionalL2Norm
          exact add_nonneg ENNReal.toReal_nonneg
            (mul_nonneg (Real.rpow_nonneg hr.le _) (div_nonneg
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))]
    have hsq' : qv (W u u n m) ^ 2 ≤ (2 * (q u n + q u m)) ^ 2 := by
      simpa [add_comm] using! hsq
    exact hmain.trans (mul_le_mul_of_nonneg_left hsq' hcoef)
  have hqpair (u : X) :
      Tendsto (fun p : ℕ × ℕ => q u p.1 + q u p.2) atTop (𝓝 0) := by
    rw [← prod_atTop_atTop_eq]
    simpa [q, qv] using! ((hlim u).comp tendsto_fst).add ((hlim u).comp tendsto_snd)
  have hnormpair (u : X) :
      Tendsto (fun p : ℕ × ℕ => ‖P u p.1 - P u p.2‖) atTop (𝓝 0) := by
    have hupper : Tendsto
        (fun p : ℕ × ℕ => Real.sqrt (C₀ * B *
          (2 * (q u p.1 + q u p.2)) ^ 2)) atTop (𝓝 0) := by
      have harg := (hqpair u).pow 2
      have hmul := harg.const_mul (4 * C₀ * B)
      have hmul' : Tendsto
          (fun p : ℕ × ℕ => C₀ * B * (2 * (q u p.1 + q u p.2)) ^ 2)
          atTop (𝓝 0) := by
        convert hmul using 1 <;> ring
      have hs := hmul'.sqrt
      simpa only [Real.sqrt_zero] using! hs
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun p => norm_nonneg _)
    · exact Filter.Eventually.of_forall (fun p =>
        Real.le_sqrt_of_sq_le (hdiff_bound u p.1 p.2))
    · exact hupper
  have hP_cauchy (u : X) : CauchySeq (P u) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    simpa only [dist_eq_norm] using! hnormpair u
  have hexT (u : X) : ∃ y : Lp ℝ 2 nu, Tendsto (P u) atTop (𝓝 y) := by
    exact ⟨(cauchySeq_tendsto_of_complete (hP_cauchy u)).choose,
      (cauchySeq_tendsto_of_complete (hP_cauchy u)).choose_spec⟩
  choose T hT using hexT
  let S (u v : X) (n : ℕ) : X :=
    (aux_lem_19_trace_completion_exists_sub hd z r hr (dd u n) (dd v n)).choose
  have hS (u v : X) (n : ℕ) :
      (S u v n).val 0 = (dd u n).val 0 - (dd v n).val 0 := by
    exact (aux_lem_19_trace_completion_exists_sub hd z r hr
      (dd u n) (dd v n)).choose_spec
  have hqS (u v : X) (n : ℕ) :
      qv (S u v n) ≤ 2 * (q u n + q v n) := by
    have h := aux_lem_19_trace_completion_norm_sub hd z r hr
      (dd u n) (dd v n) (S u v n) (hS u v n)
    simpa [q, qv] using! h
  have hqS_tend (u v : X) :
      Tendsto (fun n => qv (S u v n)) atTop (𝓝 0) := by
    have hu : Tendsto (fun n => q u n) atTop (𝓝 0) := by
      simpa [q, qv] using! hlim u
    have hv : Tendsto (fun n => q v n) atTop (𝓝 0) := by
      simpa [q, qv] using! hlim v
    have hupper : Tendsto (fun n => 2 * (q u n + q v n)) atTop (𝓝 0) := by
      simpa using! (hu.add hv).const_mul 2
    apply squeeze_zero
    · exact fun n => by
        dsimp [qv]
        unfold cubeFractionalL2Norm
        exact add_nonneg ENNReal.toReal_nonneg
          (mul_nonneg (Real.rpow_nonneg hr.le _) (div_nonneg
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    · exact hqS u v
    · exact hupper
  have hTdiff
      (u v w : X) (hw : w.val 0 = u.val 0 - v.val 0) :
      ‖T u - T v‖ ^ 2 ≤ 4 * C₀ * B * qv w ^ 2 := by
    have hWrel (n : ℕ) :
        (W u v n n).val 0 = w.val 0 - (S u v n).val 0 := by
      rw [hW u v n n, hw, hS u v n, hdd u n, hdd v n]
      abel
    have hqW (n : ℕ) :
        qv (W u v n n) ≤ 2 * (qv w + qv (S u v n)) := by
      exact aux_lem_19_trace_completion_norm_sub hd z r hr w
        (S u v n) (W u v n n) (hWrel n)
    have hcoef : 0 ≤ C₀ * B := mul_nonneg hC₀ hB
    have hsqbound (n : ℕ) :
        ‖P u n - P v n‖ ^ 2 ≤
          C₀ * B * (2 * (qv w + qv (S u v n))) ^ 2 := by
      have h := hPdiff u v n n
      have hs : qv (W u v n n) ^ 2 ≤
          (2 * (qv w + qv (S u v n))) ^ 2 := by
        nlinarith [hWrel n, hqW n,
          show 0 ≤ qv w from by
            dsimp [qv]
            unfold cubeFractionalL2Norm
            exact add_nonneg ENNReal.toReal_nonneg
              (mul_nonneg (Real.rpow_nonneg hr.le _) (div_nonneg
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))),
          show 0 ≤ qv (S u v n) from by
            dsimp [qv]
            unfold cubeFractionalL2Norm
            exact add_nonneg ENNReal.toReal_nonneg
              (mul_nonneg (Real.rpow_nonneg hr.le _) (div_nonneg
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))),
          show 0 ≤ qv (W u v n n) from by
            dsimp [qv]
            unfold cubeFractionalL2Norm
            exact add_nonneg ENNReal.toReal_nonneg
              (mul_nonneg (Real.rpow_nonneg hr.le _) (div_nonneg
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))]
      exact h.trans (mul_le_mul_of_nonneg_left hs hcoef)
    have hdiffT : Tendsto (fun n => P u n - P v n) atTop (𝓝 (T u - T v)) :=
      (hT u).sub (hT v)
    have hnormsq : Tendsto (fun n => ‖P u n - P v n‖ ^ 2) atTop
        (𝓝 (‖T u - T v‖ ^ 2)) := by
      have hn := continuous_norm.continuousAt.tendsto.comp hdiffT
      exact hn.pow 2
    have hbase : Tendsto (fun n => 2 * (qv w + qv (S u v n))) atTop
        (𝓝 (2 * qv w)) := by
      have hs := (hqS_tend u v).const_mul 2
      have hs' : Tendsto (fun n => 2 * qv (S u v n)) atTop (𝓝 0) := by
        simpa [mul_comm] using! hs
      simpa [mul_add] using! (hs'.const_add (2 * qv w))
    have hupper : Tendsto
        (fun n => C₀ * B * (2 * (qv w + qv (S u v n))) ^ 2) atTop
        (𝓝 (C₀ * B * (2 * qv w) ^ 2)) := by
      have hs := (hbase.pow 2).const_mul (C₀ * B)
      simpa [mul_comm] using! hs
    have hlimineq : ‖T u - T v‖ ^ 2 ≤ C₀ * B * (2 * qv w) ^ 2 :=
      le_of_tendsto_of_tendsto' hnormsq hupper hsqbound
    calc
      ‖T u - T v‖ ^ 2 ≤ C₀ * B * (2 * qv w) ^ 2 := hlimineq
      _ = 4 * C₀ * B * qv w ^ 2 := by ring
  have hT_smooth
      (f : SpatialCoordinates d → ℝ) (hfcont : ContDiff ℝ ∞ f)
      (v : X) (hv : (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict U] f)
      (hf : MemLp f 2 nu) : T v = hf.toLp f := by
    have hsq (n : ℕ) :
        ‖hf.toLp f - P v n‖ ^ 2 ≤ C₀ * B * qv (dd v n) ^ 2 := by
      have hwae :
          ((dd v n).val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict U]
            (f - ff v n) := by
        rw [hdd v n]
        filter_upwards [Lp.coeFn_sub (v.val 0) ((aa v n).val 0), hv,
          hfae v n] with x hx hxv hxa
        calc
          (v.val 0 - (aa v n).val 0) x =
              v.val 0 x - (aa v n).val 0 x := hx
          _ = f x - ff v n x := by rw [hxv, hxa]
      have hineq := (hbound₀ nu K hnu hsupp hK hgrowth
        (f - ff v n) (hfcont.sub (hff v n))).2.2
          (dd v n) hwae (hf.sub (hfmem v n))
      have hsublp :
          (hf.sub (hfmem v n)).toLp (f - ff v n) =
            hf.toLp f - P v n := hf.toLp_sub (hfmem v n)
      rw [← hsublp]
      simpa [B, U] using! hineq
    have hq : Tendsto (fun n => qv (dd v n)) atTop (𝓝 0) := by
      simpa [q, qv] using! hlim v
    have hn : Tendsto (fun n => ‖hf.toLp f - P v n‖) atTop (𝓝 0) :=
      aux_lem_19_trace_completion_norm_tendsto_of_sq
        (fun n => hf.toLp f - P v n) (fun n => qv (dd v n)) hsq hq
    have hsource : Tendsto (P v) atTop (𝓝 (hf.toLp f)) :=
      aux_lem_19_trace_completion_tendsto_of_rev_norm (P v) (hf.toLp f) hn
    exact tendsto_nhds_unique (hT v) hsource
  have hTnorm (u : X) : ‖T u‖ ^ 2 ≤ 4 * C₀ * B * qv u ^ 2 := by
    have hsq (n : ℕ) : ‖P u n‖ ^ 2 ≤
        C₀ * B * (2 * (qv u + qv (dd u n))) ^ 2 := by
      have hineq := (hbound₀ nu K hnu hsupp hK hgrowth
        (ff u n) (hff u n)).2.2 (aa u n) (hfae u n) (hfmem u n)
      have haa : (aa u n).val 0 = u.val 0 - (dd u n).val 0 := by
        rw [hdd u n]
        abel
      have hqaa := aux_lem_19_trace_completion_norm_sub hd z r hr
        u (dd u n) (aa u n) haa
      have hcoef : 0 ≤ C₀ * B := mul_nonneg hC₀ hB
      have hs : qv (aa u n) ^ 2 ≤
          (2 * (qv u + qv (dd u n))) ^ 2 := by
        nlinarith [hqaa,
          show 0 ≤ qv u from by
            dsimp [qv]
            unfold cubeFractionalL2Norm
            exact add_nonneg ENNReal.toReal_nonneg
              (mul_nonneg (Real.rpow_nonneg hr.le _) (div_nonneg
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))),
          show 0 ≤ qv (dd u n) from by
            dsimp [qv]
            unfold cubeFractionalL2Norm
            exact add_nonneg ENNReal.toReal_nonneg
              (mul_nonneg (Real.rpow_nonneg hr.le _) (div_nonneg
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))),
          show 0 ≤ qv (aa u n) from by
            dsimp [qv]
            unfold cubeFractionalL2Norm
            exact add_nonneg ENNReal.toReal_nonneg
              (mul_nonneg (Real.rpow_nonneg hr.le _) (div_nonneg
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))]
      rw [show P u n = (hfmem u n).toLp (ff u n) from rfl]
      exact hineq.trans (mul_le_mul_of_nonneg_left hs hcoef)
    have hq : Tendsto (fun n => qv (dd u n)) atTop (𝓝 0) := by
      simpa [q, qv] using! hlim u
    have hbase : Tendsto (fun n => 2 * (qv u + qv (dd u n))) atTop
        (𝓝 (2 * qv u)) := by
      have hs := hq.const_add (qv u)
      have hs' : Tendsto (fun n => qv u + qv (dd u n)) atTop (𝓝 (qv u + 0)) := by
        simpa [add_comm] using! hs
      simpa using! hs'.const_mul 2
    have hupper : Tendsto
        (fun n => C₀ * B * (2 * (qv u + qv (dd u n))) ^ 2) atTop
        (𝓝 (C₀ * B * (2 * qv u) ^ 2)) := by
      simpa [mul_comm] using! (hbase.pow 2).const_mul (C₀ * B)
    have hn := (continuous_norm.continuousAt.tendsto.comp (hT u)).pow 2
    have hle := le_of_tendsto_of_tendsto' hn hupper hsq
    calc
      ‖T u‖ ^ 2 ≤ C₀ * B * (2 * qv u) ^ 2 := hle
      _ = 4 * C₀ * B * qv u ^ 2 := by ring
  have hkpos : 0 < r ^ (-(halfFractionalOrder : ℝ)) /
      Real.sqrt (volume.real U) := by
    apply div_pos
    · exact Real.rpow_pos_of_pos hr _
    · exact Real.sqrt_pos.mpr (by simpa [U] using! centeredCube_volume_pos z hr)
  have hnormdiff (u : X) :
      Tendsto (fun n => ‖(dd u n).val 0‖) atTop (𝓝 0) := by
    have hterm (n : ℕ) :
        (r ^ (-(halfFractionalOrder : ℝ)) / Real.sqrt (volume.real U)) *
            ‖(dd u n).val 0‖ ≤ qv (dd u n) := by
      change (r ^ (-(halfFractionalOrder : ℝ)) / Real.sqrt (volume.real U)) *
          ‖(dd u n).val 0‖ ≤
        cubeFractionalL2Norm hd z r hr halfFractionalOrder (dd u n)
      rw [hform (dd u n)]
      exact le_add_of_nonneg_left ENNReal.toReal_nonneg
    have hmul : Tendsto (fun n =>
        (r ^ (-(halfFractionalOrder : ℝ)) / Real.sqrt (volume.real U)) *
          ‖(dd u n).val 0‖) atTop (𝓝 0) := by
      apply squeeze_zero
      · exact fun n => mul_nonneg (le_of_lt hkpos) (norm_nonneg _)
      · exact hterm
      · simpa [q, qv] using! hlim u
    have hinv := hmul.const_mul
      (r ^ (-(halfFractionalOrder : ℝ)) / Real.sqrt (volume.real U))⁻¹
    have hne : (r ^ (-(halfFractionalOrder : ℝ)) /
        Real.sqrt (volume.real U)) ≠ 0 := hkpos.ne'
    have hfe :
        (fun n => (r ^ (-(halfFractionalOrder : ℝ)) /
          Real.sqrt (volume.real U))⁻¹ *
          ((r ^ (-(halfFractionalOrder : ℝ)) /
            Real.sqrt (volume.real U)) * ‖(dd u n).val 0‖)) =
          fun n => ‖(dd u n).val 0‖ := by
      funext n
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [hfe] at hinv
    simpa using! hinv
  have hbounded
      (D : ℝ) (hD : 0 ≤ D)
      (hνle : nu ≤ ENNReal.ofReal D • volume.restrict U) :
      ∀ u : X, MemLp (u.val 0) 2 nu ∧
        ∀ hu : MemLp (u.val 0) 2 nu, T u = hu.toLp (u.val 0) := by
    have hDfin : ENNReal.ofReal D ≠ ⊤ := ENNReal.ofReal_ne_top
    have hp2 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    intro u
    have hmemu : MemLp (u.val 0) 2 nu :=
      MemLp.of_measure_le_smul hDfin hνle (Lp.memLp (u.val 0))
    have hcoe (n : ℕ) :
        ((dd u n).val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict U]
          (fun x => u.val 0 x - ff u n x) := by
      rw [hdd u n]
      filter_upwards [Lp.coeFn_sub (u.val 0) ((aa u n).val 0), hfae u n] with x hx hxa
      calc
        (u.val 0 - (aa u n).val 0) x =
            u.val 0 x - (aa u n).val 0 x := hx
        _ = u.val 0 x - ff u n x := by rw [hxa]
    have heq (n : ℕ) :
        eLpNorm (fun x => ff u n x - u.val 0 x) 2 (volume.restrict U) =
          eLpNorm ((dd u n).val 0 : SpatialCoordinates d → ℝ) 2
            (volume.restrict U) := by
      have hneg : (fun x => u.val 0 x - ff u n x) =
          -(fun x => ff u n x - u.val 0 x) := by
        funext x
        change u.val 0 x - ff u n x = -(ff u n x - u.val 0 x)
        ring
      calc
        eLpNorm (fun x => ff u n x - u.val 0 x) 2 (volume.restrict U) =
            eLpNorm (-(fun x => ff u n x - u.val 0 x)) 2
              (volume.restrict U) :=
          (eLpNorm_neg (fun x => ff u n x - u.val 0 x) 2
            (volume.restrict U)).symm
        _ = eLpNorm (fun x => u.val 0 x - ff u n x) 2
              (volume.restrict U) := by simp only [hneg]
        _ = eLpNorm ((dd u n).val 0 : SpatialCoordinates d → ℝ) 2
              (volume.restrict U) :=
          (eLpNorm_congr_ae (hcoe n)).symm
    have hnormeq (n : ℕ) :
        ‖(dd u n).val 0‖ =
          (eLpNorm ((dd u n).val 0 : SpatialCoordinates d → ℝ) 2
            (volume.restrict U)).toReal := by
      rw [Lp.norm_def]
    have hreal : Tendsto (fun n =>
        (eLpNorm (fun x => ff u n x - u.val 0 x) 2
          (volume.restrict U)).toReal) atTop (𝓝 0) := by
      have hfe : (fun n =>
          (eLpNorm (fun x => ff u n x - u.val 0 x) 2
            (volume.restrict U)).toReal) =
          fun n => ‖(dd u n).val 0‖ := by
        funext n
        rw [heq n, ← hnormeq n]
      rw [hfe]
      exact hnormdiff u
    have hfin (n : ℕ) :
        eLpNorm (fun x => ff u n x - u.val 0 x) 2 (volume.restrict U) ≠ ⊤ := by
      rw [heq n]
      exact (Lp.memLp ((dd u n).val 0)).eLpNorm_ne_top
    have hvol : Tendsto (fun n =>
        eLpNorm (fun x => ff u n x - u.val 0 x) 2 (volume.restrict U))
        atTop (𝓝 0) := by
      have hfe : (fun n =>
          eLpNorm (fun x => ff u n x - u.val 0 x) 2 (volume.restrict U)) =
          fun n => ENNReal.ofReal
            (eLpNorm (fun x => ff u n x - u.val 0 x) 2
              (volume.restrict U)).toReal := by
        funext n
        exact (ENNReal.ofReal_toReal (hfin n)).symm
      rw [hfe]
      have hc := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
      simpa using! hc
    have hupper (n : ℕ) :
        eLpNorm (fun x => ff u n x - u.val 0 x) 2 nu ≤
          (ENNReal.ofReal D) ^ (1 / (2 : ℝ≥0∞)).toReal *
            eLpNorm (fun x => ff u n x - u.val 0 x) 2 (volume.restrict U) := by
      calc
        _ ≤ eLpNorm (fun x => ff u n x - u.val 0 x) 2
            (ENNReal.ofReal D • volume.restrict U) :=
          eLpNorm_mono_measure _ hνle
        _ = _ := by
          rw [eLpNorm_smul_measure_of_ne_top hp2 _ _
            (aestronglyMeasurable_of_eLpNorm_ne_top (hfin n))]
          rfl
    have hupperlim : Tendsto (fun n =>
        (ENNReal.ofReal D) ^ (1 / (2 : ℝ≥0∞)).toReal *
          eLpNorm (fun x => ff u n x - u.val 0 x) 2 (volume.restrict U))
        atTop (𝓝 0) := by
      have hcfin : (ENNReal.ofReal D) ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hDfin
      have hc := (ENNReal.continuous_const_mul hcfin).tendsto (0 : ℝ≥0∞)
      simpa using! hc.comp hvol
    have hnu : Tendsto (fun n =>
        eLpNorm (fun x => ff u n x - u.val 0 x) 2 nu) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
        hupperlim ?_ hupper
      exact fun _ => bot_le
    refine ⟨hmemu, ?_⟩
    intro hu
    have hsource : Tendsto (P u) atTop (𝓝 (hu.toLp (u.val 0))) := by
      simpa [P] using!
        (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (ff u) (fun n => hfmem u n)
          (u.val 0) hu).mpr hnu
    exact tendsto_nhds_unique (hT u) hsource
  have hprop :
      (∀ u v : X, ∃ w : X, w.val 0 = u.val 0 - v.val 0) ∧
      (∀ (u v w : X), w.val 0 = u.val 0 - v.val 0 →
        ‖T u - T v‖ ^ 2 ≤ 4 * C₀ * B * qv w ^ 2) ∧
      (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
        ∀ (v : X), (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict U] f →
          ∀ hf : MemLp f 2 nu, T v = hf.toLp f) ∧
      (∀ u : X, ‖T u‖ ^ 2 ≤ 4 * C₀ * B * qv u ^ 2) ∧
      (∀ D : ℝ, 0 ≤ D → nu ≤ ENNReal.ofReal D • volume.restrict U →
        ∀ u : X, MemLp (u.val 0) 2 nu ∧
          ∀ hu : MemLp (u.val 0) 2 nu, T u = hu.toLp (u.val 0)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u v
      exact aux_lem_19_trace_completion_exists_sub hd z r hr u v
    · intro u v w hw
      exact hTdiff u v w hw
    · intro f hfcont v hv hf
      exact hT_smooth f hfcont v hv hf
    · intro u
      exact hTnorm u
    · intro D hD hνle
      have hνle' : nu ≤ ENNReal.ofReal D • volume.restrict U := by
        simpa [U] using! hνle
      exact hbounded D hD hνle'
  refine ⟨T, hprop, ?_⟩
  intro T' hT'
  exact aux_lem_19_trace_completion_unique hd z r hr nu (4 * C₀) B hmem T T'
    hprop.2.1 hT'.2.1 hprop.2.2.1 hT'.2.2.1

end SubdiffusiveProcess.Paper

