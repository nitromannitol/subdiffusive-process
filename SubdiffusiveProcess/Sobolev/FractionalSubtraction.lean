module

public import SubdiffusiveProcess.Main.CubeFractionalL2

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
namespace SubdiffusiveProcess

/-- The stated finite fractional-seminorm carrier is closed under coordinatewise L2 subtraction. -/
theorem cubeFractionalL2Seminorm_sub_lt_top
    {d k : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1)
    (f g : Fin k → DomainL2 (centeredCube z r hr))
    (hf : cubeFractionalL2Seminorm hd z r hr s f < ⊤)
    (hg : cubeFractionalL2Seminorm hd z r hr s g < ⊤) :
    cubeFractionalL2Seminorm hd z r hr s (fun i ↦ f i - g i) < ⊤ := by
  classical
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let a : ℝ≥0∞ := ENNReal.ofReal (s : ℝ) / volume U
  let If : ℝ≥0∞ := ∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ)) ∂μ ∂μ
  let Ig : ℝ≥0∞ := ∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (∑ i : Fin k, (g i x - g i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ)) ∂μ ∂μ
  let Isub : ℝ≥0∞ := ∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (∑ i : Fin k,
        ((f i - g i) x - (f i - g i) y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ)) ∂μ ∂μ
  have hvoltop : volume U ≠ ⊤ := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hvolpos : 0 < volume U := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_pos.mpr (pow_pos hr _)
  have ha0 : a ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    exact ⟨(ENNReal.ofReal_pos.mpr s.2.1).ne', hvoltop⟩
  have hfa : (a * If) ^ (1 / 2 : ℝ) < ⊤ := by
    simpa only [a, If, U, μ, cubeFractionalL2Seminorm] using hf
  have hga : (a * Ig) ^ (1 / 2 : ℝ) < ⊤ := by
    simpa only [a, Ig, U, μ, cubeFractionalL2Seminorm] using hg
  have hIfpow : (a * If) ^ (1 / 2 : ℝ) < ⊤ := by
    exact hfa
  have hIgpow : (a * Ig) ^ (1 / 2 : ℝ) < ⊤ := by
    exact hga
  have hIf : If < ⊤ := by
    have hprod : a * If < ⊤ := by
      by_contra h
      have heq : a * If = ⊤ := top_unique (le_of_not_gt h)
      exact (ne_of_lt hIfpow) (by rw [heq, ENNReal.top_rpow_of_pos (by norm_num)])
    rcases (ENNReal.mul_lt_top_iff.mp hprod) with h | h | h
    · exact h.2
    · exact (ha0 h).elim
    · simp [h]
  have hIg : Ig < ⊤ := by
    have hprod : a * Ig < ⊤ := by
      by_contra h
      have heq : a * Ig = ⊤ := top_unique (le_of_not_gt h)
      exact (ne_of_lt hIgpow) (by rw [heq, ENNReal.top_rpow_of_pos (by norm_num)])
    rcases (ENNReal.mul_lt_top_iff.mp hprod) with h | h | h
    · exact h.2
    · exact (ha0 h).elim
    · simp [h]
  have hfi (i : Fin k) : AEStronglyMeasurable (fun x => (f i x : ℝ)) μ := by
    simpa only [μ] using (Lp.aestronglyMeasurable (f i))
  have hgi (i : Fin k) : AEStronglyMeasurable (fun x => (g i x : ℝ)) μ := by
    simpa only [μ] using (Lp.aestronglyMeasurable (g i))
  have hcoordf (i : Fin k) :
      AEMeasurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        (f i q.1 - f i q.2) ^ 2) (μ.prod μ) := by
    exact (((hfi i).aemeasurable.comp_fst).sub
      ((hfi i).aemeasurable.comp_snd)).pow_const 2
  have hcoordg (i : Fin k) :
      AEMeasurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        (g i q.1 - g i q.2) ^ 2) (μ.prod μ) := by
    exact (((hgi i).aemeasurable.comp_fst).sub
      ((hgi i).aemeasurable.comp_snd)).pow_const 2
  have hnumf : AEMeasurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        ∑ i : Fin k, (f i q.1 - f i q.2) ^ 2) (μ.prod μ) :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ => hcoordf i
  have hnumg : AEMeasurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        ∑ i : Fin k, (g i q.1 - g i q.2) ^ 2) (μ.prod μ) :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ => hcoordg i
  have hden : Measurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ))) := by
    apply Measurable.pow
    · apply Measurable.ennreal_ofReal
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun j _ =>
        (((measurable_pi_apply j).comp measurable_fst).sub
          ((measurable_pi_apply j).comp measurable_snd)).pow_const 2
    · exact measurable_const
  let Tf : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (∑ i : Fin k, (f i q.1 - f i q.2) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2))) ^
        ((d : ℝ) + 2 * (s : ℝ))
  let Tg : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (∑ i : Fin k, (g i q.1 - g i q.2) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2))) ^
        ((d : ℝ) + 2 * (s : ℝ))
  have hTf : AEMeasurable Tf (μ.prod μ) := by
    exact hnumf.ennreal_ofReal.div hden.aemeasurable
  have hTg : AEMeasurable Tg (μ.prod μ) := by
    exact hnumg.ennreal_ofReal.div hden.aemeasurable
  have hTf_x (x : SpatialCoordinates d) : AEMeasurable (fun y => Tf (x, y)) μ := by
    have hnum : AEMeasurable (fun y =>
        ∑ i : Fin k, (f i x - f i y) ^ 2) μ :=
      Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
        (measurable_const.aemeasurable.sub (hfi i).aemeasurable).pow_const 2
    have hdenx : Measurable (fun y : SpatialCoordinates d =>
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ))) := by
      apply Measurable.pow
      · apply Measurable.ennreal_ofReal
        apply Measurable.sqrt
        exact Finset.measurable_sum Finset.univ fun j _ =>
          (measurable_const.sub (measurable_pi_apply j)).pow_const 2
      · exact measurable_const
    exact hnum.ennreal_ofReal.div hdenx.aemeasurable
  have hTg_x (x : SpatialCoordinates d) : AEMeasurable (fun y => Tg (x, y)) μ := by
    have hnum : AEMeasurable (fun y =>
        ∑ i : Fin k, (g i x - g i y) ^ 2) μ :=
      Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
        (measurable_const.aemeasurable.sub (hgi i).aemeasurable).pow_const 2
    have hdenx : Measurable (fun y : SpatialCoordinates d =>
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ))) := by
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
      ENNReal.ofReal (∑ i : Fin k, ((f i x - g i x) - (f i y - g i y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ)) ≤
        2 * Tf (x, y) + 2 * Tg (x, y) := by
    have hi (i : Fin k) :
        ((f i x - g i x) - (f i y - g i y)) ^ 2 ≤
          2 * (f i x - f i y) ^ 2 + 2 * (g i x - g i y) ^ 2 := by
      nlinarith [sq_nonneg ((f i x - f i y) + (g i x - g i y))]
    have hs :
        ∑ i : Fin k, ((f i x - g i x) - (f i y - g i y)) ^ 2 ≤
          2 * (∑ i : Fin k, (f i x - f i y) ^ 2) +
            2 * (∑ i : Fin k, (g i x - g i y) ^ 2) := by
      calc
        _ ≤ ∑ i : Fin k, (2 * (f i x - f i y) ^ 2 +
            2 * (g i x - g i y) ^ 2) :=
          Finset.sum_le_sum fun i _ => hi i
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have hsf : 0 ≤ ∑ i : Fin k, (f i x - f i y) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsg : 0 ≤ ∑ i : Fin k, (g i x - g i y) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hdiv :
        ENNReal.ofReal (∑ i : Fin k,
          ((f i x - g i x) - (f i y - g i y)) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (s : ℝ)) ≤
          ENNReal.ofReal (2 * (∑ i : Fin k, (f i x - f i y) ^ 2) +
              2 * (∑ i : Fin k, (g i x - g i y) ^ 2)) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (s : ℝ)) :=
      ENNReal.div_le_div (ENNReal.ofReal_le_ofReal hs) (le_refl _)
    have heq :
        ENNReal.ofReal (2 * (∑ i : Fin k, (f i x - f i y) ^ 2) +
            2 * (∑ i : Fin k, (g i x - g i y) ^ 2)) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (s : ℝ)) =
          2 * Tf (x, y) + 2 * Tg (x, y) := by
      dsimp [Tf, Tg]
      rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hsf)
        (mul_nonneg (by norm_num) hsg)]
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
      rw [ENNReal.add_div, mul_div_assoc, mul_div_assoc]
      norm_num
    exact hdiv.trans_eq heq
  have hinner (x : SpatialCoordinates d) :
      (∫⁻ y, ENNReal.ofReal (∑ i : Fin k,
          ((f i x - g i x) - (f i y - g i y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ)) ∂μ) ≤
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
        ENNReal.ofReal (∑ i : Fin k,
          ((f i x - g i x) - (f i y - g i y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ)) ∂μ ∂μ) ≤
        2 * (∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (s : ℝ)) ∂μ ∂μ) +
        2 * (∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (∑ i : Fin k, (g i x - g i y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (s : ℝ)) ∂μ ∂μ) := by
    have hmono := lintegral_mono (μ := μ) (fun x => hinner x)
    calc
      _ ≤ ∫⁻ x, 2 * (∫⁻ y, Tf (x, y) ∂μ) +
          2 * (∫⁻ y, Tg (x, y) ∂μ) ∂μ := hmono
      _ = 2 * (∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (s : ℝ)) ∂μ ∂μ) +
          2 * (∫⁻ x, ∫⁻ y,
          ENNReal.ofReal (∑ i : Fin k, (g i x - g i y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (s : ℝ)) ∂μ ∂μ) := by
        have hinnerf2 : AEMeasurable
            (fun x => (2 : ℝ≥0∞) * (∫⁻ y, Tf (x, y) ∂μ)) μ :=
          measurable_const.aemeasurable.mul hinnerf
        rw [lintegral_add_left' hinnerf2]
        rw [lintegral_const_mul'' 2 hinnerf]
        rw [lintegral_const_mul'' 2 hinnerg]
  have hsub_all : ∀ᵐ x ∂μ, ∀ i : Fin k, (f i - g i) x = f i x - g i x := by
    exact ae_all_iff.mpr fun i => Lp.coeFn_sub (f i) (g i)
  have hIsub_eq : Isub =
      (∫⁻ x, ∫⁻ y,
        ENNReal.ofReal (∑ i : Fin k,
          ((f i x - g i x) - (f i y - g i y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ)) ∂μ ∂μ) := by
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
  have hresult : (a * Isub) ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hprodsub.ne
  simpa only [a, Isub, U, μ, cubeFractionalL2Seminorm] using hresult

end SubdiffusiveProcess
