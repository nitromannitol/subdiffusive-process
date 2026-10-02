import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum

/-!
# Restriction transport for the frozen fractional seminorm

The frozen seminorm uses one power of volume to normalize a two-slot integral.
Consequently restriction from `A` to `B ⊆ A` costs precisely
`sqrt(|A|/|B|)`.  This is the finite-cover transport used by the projected
boundary cubes.

PROVENANCE: finite-`p` counterpart of
`Algsuperdiff/Section4/Provider/Regularity/StepFourSeminormComparisons.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private noncomputable def normalizedFractionalMeasure (W : Set (Vec d)) :
    Measure (Vec d × Vec d) :=
  (volume W)⁻¹ •
    ((volume.restrict W).prod (volume.restrict W))

private theorem fractionalSeminormOn_eq_sqrt_mul_eLpNorm_normalized
    (W : Set (Vec d)) (s : ℝ) (f : Vec d → Vec d) :
    fractionalSeminormOn W s f =
      (ENNReal.ofReal s) ^ (1 / 2 : ℝ) *
        eLpNorm (fractionalKernel s f) 2 (normalizedFractionalMeasure W) := by
  rw [normalizedFractionalMeasure,
    eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  unfold fractionalSeminormOn
  rw [ENNReal.div_eq_inv_mul,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num [smul_eq_mul]
  ac_rfl

private theorem normalizedFractionalMeasure_translateSet
    (z : Vec d) (A : Set (Vec d)) :
    normalizedFractionalMeasure (translateSet z A) =
      Measure.map (Prod.map (fun x : Vec d ↦ x + z) (fun x : Vec d ↦ x + z))
        (normalizedFractionalMeasure A) := by
  haveI : SFinite (volume.restrict A) := inferInstance
  have hmeas : Measurable (fun x : Vec d ↦ x + z) := measurable_id.add_const z
  rw [normalizedFractionalMeasure, normalizedFractionalMeasure,
    volume_translateSet_eq, Measure.map_smul,
    ← Measure.map_prod_map _ _ hmeas hmeas,
    (measurePreserving_addRight_restrict_translateSet z A).map_eq]

/-- Exact real-translation covariance of the frozen fractional seminorm. -/
theorem fractionalSeminormOn_translateSet
    (z : Vec d) (A : Set (Vec d)) (s : ℝ) (f : Vec d → Vec d) :
    fractionalSeminormOn (translateSet z A) s f =
      fractionalSeminormOn A s (fun x ↦ f (x + z)) := by
  rw [fractionalSeminormOn_eq_sqrt_mul_eLpNorm_normalized,
    fractionalSeminormOn_eq_sqrt_mul_eLpNorm_normalized]
  congr 1
  let T : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight z
  let TP : Vec d × Vec d ≃ᵐ Vec d × Vec d := T.prodCongr T
  rw [normalizedFractionalMeasure_translateSet]
  change eLpNorm (fractionalKernel s f) 2
      (Measure.map TP (normalizedFractionalMeasure A)) = _
  rw [TP.measurableEmbedding.eLpNorm_map_measure]
  congr 1
  funext w
  change fractionalKernel s f (w.1 + z, w.2 + z) =
    fractionalKernel s (fun x ↦ f (x + z)) w
  unfold fractionalKernel
  have hsub : w.1 + z - (w.2 + z) = w.1 - w.2 := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsub]

private theorem normalizedFractionalMeasure_mono_scaled
    {A B : Set (Vec d)} (hBA : B ⊆ A)
    (hA0 : volume A ≠ 0) (hAtop : volume A ≠ ∞) :
    normalizedFractionalMeasure B ≤
      ((volume B)⁻¹ * volume A) • normalizedFractionalMeasure A := by
  have hcancel : (volume B)⁻¹ * volume A * (volume A)⁻¹ = (volume B)⁻¹ := by
    rw [mul_assoc, ENNReal.mul_inv_cancel hA0 hAtop, mul_one]
  rw [normalizedFractionalMeasure, normalizedFractionalMeasure,
    Measure.prod_restrict, Measure.prod_restrict, smul_smul, hcancel]
  refine Measure.le_iff'.mpr fun S ↦ ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl
    (Measure.restrict_mono (Set.prod_mono hBA hBA) le_rfl S)

/-- Restricting the frozen fractional seminorm costs the square root of the
volume ratio. -/
theorem fractionalSeminormOn_mono_set
    {A B : Set (Vec d)} (hBA : B ⊆ A)
    (hA0 : volume A ≠ 0) (hAtop : volume A ≠ ∞)
    (s : ℝ) (f : Vec d → Vec d) :
    fractionalSeminormOn B s f ≤
      ((volume B)⁻¹ * volume A) ^ (1 / 2 : ℝ) *
        fractionalSeminormOn A s f := by
  rw [fractionalSeminormOn_eq_sqrt_mul_eLpNorm_normalized,
    fractionalSeminormOn_eq_sqrt_mul_eLpNorm_normalized]
  have hnorm :
    eLpNorm (fractionalKernel s f) 2 (normalizedFractionalMeasure B) ≤
        eLpNorm (fractionalKernel s f) 2
          (((volume B)⁻¹ * volume A) • normalizedFractionalMeasure A) :=
      eLpNorm_mono_measure _
        (normalizedFractionalMeasure_mono_scaled hBA hA0 hAtop)
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] at hnorm
  norm_num at hnorm
  calc
    (ENNReal.ofReal s) ^ (1 / 2 : ℝ) *
        eLpNorm (fractionalKernel s f) 2 (normalizedFractionalMeasure B) ≤
      (ENNReal.ofReal s) ^ (1 / 2 : ℝ) *
        (((volume B)⁻¹ * volume A) ^ (1 / 2 : ℝ) *
          eLpNorm (fractionalKernel s f) 2 (normalizedFractionalMeasure A)) :=
      by gcongr
    _ = ((volume B)⁻¹ * volume A) ^ (1 / 2 : ℝ) *
        ((ENNReal.ofReal s) ^ (1 / 2 : ℝ) *
        eLpNorm (fractionalKernel s f) 2 (normalizedFractionalMeasure A)) := by
      ac_rfl

/-- Real-valued form of `fractionalSeminormOn_mono_set`. -/
theorem fractionalSeminormOn_toReal_mono_set
    {A B : Set (Vec d)} (hBA : B ⊆ A)
    (hB0 : volume B ≠ 0) (hBtop : volume B ≠ ∞)
    (hA0 : volume A ≠ 0) (hAtop : volume A ≠ ∞)
    (s : ℝ) (f : Vec d → Vec d)
    (hAfin : fractionalSeminormOn A s f ≠ ∞) :
    (fractionalSeminormOn B s f).toReal ≤
      Real.sqrt ((volume A).toReal / (volume B).toReal) *
        (fractionalSeminormOn A s f).toReal := by
  have hmono := fractionalSeminormOn_mono_set hBA hA0 hAtop s f
  have hcoefTop : ((volume B)⁻¹ * volume A) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hB0) hAtop)
  have hrightTop : ((volume B)⁻¹ * volume A) ^ (1 / 2 : ℝ) *
      fractionalSeminormOn A s f ≠ ∞ := ENNReal.mul_ne_top hcoefTop hAfin
  have hreal := ENNReal.toReal_mono hrightTop hmono
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_mul, ENNReal.toReal_inv] at hreal
  rw [← Real.sqrt_eq_rpow] at hreal
  have hBreal : (volume B).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hB0, hBtop⟩
  simpa [div_eq_mul_inv, hBreal, mul_comm, mul_left_comm, mul_assoc] using hreal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
