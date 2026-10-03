module

public import SubdiffusiveProcess.Sobolev.FractionalSubtraction

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

private theorem finset_double_lintegral_sum
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (t : Finset ι) (F : ι → α → α → ℝ≥0∞)
    (hF : ∀ i ∈ t, AEMeasurable (Function.uncurry (F i)) (μ.prod μ))
    (hFx : ∀ i ∈ t, ∀ x, AEMeasurable (F i x) μ) :
    (∫⁻ x, ∫⁻ y, ∑ i ∈ t, F i x y ∂μ ∂μ) =
      ∑ i ∈ t, ∫⁻ x, ∫⁻ y, F i x y ∂μ ∂μ := by
  have hinner (i : ι) (hi : i ∈ t) :
      AEMeasurable (fun x => ∫⁻ y, F i x y ∂μ) μ :=
    (hF i hi).lintegral_prod_right
  simp_rw [lintegral_finset_sum' t (fun i hi => hFx i hi _)]
  exact lintegral_finset_sum' t hinner

theorem cubeFractionalL2Seminorm_vector_lt_top_of_components
    {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr))
    (hf : ∀ i, cubeFractionalL2Seminorm hd z r hr s
      (fun _ : Fin 1 => f i) < ⊤) :
    cubeFractionalL2Seminorm hd z r hr s f < ⊤ := by
  classical
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let a : ℝ≥0∞ := ENNReal.ofReal (s : ℝ) / volume U
  let D : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun x y =>
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
      ((d : ℝ) + 2 * (s : ℝ))
  let F : Fin k → SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ :=
    fun i x y => ENNReal.ofReal ((f i x - f i y) ^ 2) / D x y
  have hfi (i : Fin k) : AEStronglyMeasurable (fun x => (f i x : ℝ)) μ := by
    simpa only [μ] using (Lp.aestronglyMeasurable (f i))
  have hD : Measurable (Function.uncurry D) := by
    apply Measurable.pow
    · apply Measurable.ennreal_ofReal
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun j _ =>
        (((measurable_pi_apply j).comp measurable_fst).sub
          ((measurable_pi_apply j).comp measurable_snd)).pow_const 2
    · exact measurable_const
  have hFx (i : Fin k) (x : SpatialCoordinates d) : AEMeasurable (F i x) μ := by
    have hDx : Measurable (D x) := by
      apply Measurable.pow
      · apply Measurable.ennreal_ofReal
        apply Measurable.sqrt
        exact Finset.measurable_sum Finset.univ fun j _ =>
          (measurable_const.sub (measurable_pi_apply j)).pow_const 2
      · exact measurable_const
    exact ((measurable_const.aemeasurable.sub (hfi i).aemeasurable).pow_const 2).ennreal_ofReal.div
      hDx.aemeasurable
  have hF (i : Fin k) : AEMeasurable (Function.uncurry (F i)) (μ.prod μ) := by
    exact ((((hfi i).aemeasurable.comp_fst).sub
      ((hfi i).aemeasurable.comp_snd)).pow_const 2).ennreal_ofReal.div
        hD.aemeasurable
  have hsum :
      (∫⁻ x, ∫⁻ y, ∑ i : Fin k, F i x y ∂μ ∂μ) =
        ∑ i : Fin k, ∫⁻ x, ∫⁻ y, F i x y ∂μ ∂μ := by
    exact finset_double_lintegral_sum μ Finset.univ F
      (fun i _ => hF i) (fun i _ => hFx i)
  have hpoint (x y : SpatialCoordinates d) :
      ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) / D x y =
        ∑ i : Fin k, F i x y := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _), div_eq_mul_inv,
      Finset.sum_mul]
    simp only [F, div_eq_mul_inv]
  have hscalar (i : Fin k) : (a * (∫⁻ x, ∫⁻ y, F i x y ∂μ ∂μ)) ^ (1 / 2 : ℝ) < ⊤ := by
    simpa only [cubeFractionalL2Seminorm, U, μ, a, D, F, Fin.sum_univ_one]
      using hf i
  have hprod (i : Fin k) : a * (∫⁻ x, ∫⁻ y, F i x y ∂μ ∂μ) < ⊤ := by
    by_contra h
    have heq : a * (∫⁻ x, ∫⁻ y, F i x y ∂μ ∂μ) = ⊤ :=
      top_unique (le_of_not_gt h)
    exact (ne_of_lt (hscalar i)) (by rw [heq, ENNReal.top_rpow_of_pos (by norm_num)])
  have hsumprod : (∑ i : Fin k, a * (∫⁻ x, ∫⁻ y, F i x y ∂μ ∂μ)) < ⊤ := by
    exact ENNReal.sum_lt_top.mpr (fun i _ => hprod i)
  have htotal : a * (∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) / D x y ∂μ ∂μ) < ⊤ := by
    simp_rw [hpoint]
    rw [hsum, Finset.mul_sum]
    exact hsumprod
  have hpow : (a * (∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) / D x y ∂μ ∂μ)) ^
        (1 / 2 : ℝ) < ⊤ := by
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) htotal.ne
  simpa only [cubeFractionalL2Seminorm, U, μ, a, D] using hpow


end SubdiffusiveProcess
