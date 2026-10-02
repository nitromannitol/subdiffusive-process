import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DirichletSpectralReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceScalePrices

/-!
# Source-facing prices for the canonical divergence lift

This is the final adapter from the unit-cube Poisson lift budget to the two
real positive-datum prices used by the energy and prebalance rows.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- On the unit cube, the frozen unnormalized `L²` size is exactly the
extended norm of the canonical `L²` representative. -/
theorem l2Size_originCube_zero_eq_ofReal_norm_toScalarL2
    {d : ℕ} (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0)))) :
    l2Size (originCube d 0) f = ENNReal.ofReal ‖toScalarL2 hf‖ := by
  unfold l2Size
  exact (MeasureTheory.Lp.enorm_toLp hf).symm.trans
    (ofReal_norm_eq_enorm (toScalarL2 hf)).symm

/-- The real source-plus-boundary size reconstructs the literal frozen
extended-real datum factor. -/
theorem ofReal_norm_toScalarL2_add_h2DatumNorm_toReal
    {d : ℕ} (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))))
    (h : H2Datum (originCube d 0)) :
    ENNReal.ofReal (‖toScalarL2 hf‖ + h.norm.toReal) =
      l2Size (originCube d 0) f + h.norm := by
  rw [ENNReal.ofReal_add (norm_nonneg _) ENNReal.toReal_nonneg,
    ← l2Size_originCube_zero_eq_ofReal_norm_toScalarL2 f hf,
    ENNReal.ofReal_toReal (h2Datum_norm_lt_top h).ne]

/-- The canonical divergence lift has a finite real unit-cube `H¹` budget. -/
theorem exists_unitDivergenceLift_with_real_budget
    (d : ℕ) [NeZero d]
    (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0)))) :
    ∃ F : CubeVectorH1Function (originCube d 0),
      (∀ phi : H10Function (openCubeSet (originCube d 0)),
        ∫ x in openCubeSet (originCube d 0),
            f x * phi.toH1Function.toFun x ∂volume =
          -∫ x in openCubeSet (originCube d 0),
            vecDot (F.toField x) (phi.toH1Function.grad x) ∂volume) ∧
      (unitCubeVectorH1ENormBudget F).toReal ≤
        unitDivergenceLiftConstant d * ‖toScalarL2 hf‖ := by
  obtain ⟨F, hpair, hbudget⟩ :=
    (exists_unitCubeVectorH1Function_divergence_lift_h1ENormBudget d).choose_spec.2
      f hf
  refine ⟨F, hpair, ?_⟩
  have hnonneg : 0 ≤ unitDivergenceLiftConstant d * ‖toScalarL2 hf‖ :=
    mul_nonneg (unitDivergenceLiftConstant_nonneg d) (norm_nonneg _)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbudget).trans_eq
    (ENNReal.toReal_ofReal hnonneg)

/-- One divergence lift simultaneously carries the weak identity and the
source-scale upper bounds needed by both positive-datum appearances. -/
theorem exists_unitDivergenceLift_with_source_prices
    (d : ℕ) [NeZero d]
    (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))))
    (alpha : ℝ) (m : ℤ) (s s2 : FractionalOrder) :
    ∃ F : CubeVectorH1Function (originCube d 0),
      (∀ phi : H10Function (openCubeSet (originCube d 0)),
        ∫ x in openCubeSet (originCube d 0),
            f x * phi.toH1Function.toFun x ∂volume =
          -∫ x in openCubeSet (originCube d 0),
            vecDot (F.toField x) (phi.toH1Function.grad x) ∂volume) ∧
      scaledVectorDatumPositiveBesovSeminormBound alpha m s F ≤
        |alpha| * (centeredCubeScale m)⁻¹ *
          sourceForcingPositiveBesovConstant d s *
            (unitDivergenceLiftConstant d * ‖toScalarL2 hf‖) ∧
      scaledVectorDatumFractionalBound alpha m s2 F ≤
        (centeredCubeScale m) ^ (-s2.1) *
          (|alpha| * (centeredCubeScale m)⁻¹) *
            sourceForcingFractionalConstant d s2 *
              (unitDivergenceLiftConstant d * ‖toScalarL2 hf‖) := by
  obtain ⟨F, hpair, hbudget⟩ :=
    exists_unitDivergenceLift_with_real_budget d f hf
  refine ⟨F, hpair, ?_, ?_⟩
  · rw [scaledVectorDatumPositiveBesovSeminormBound_eq_sourceDatum]
    exact mul_le_mul_of_nonneg_left hbudget
      (mul_nonneg
        (mul_nonneg (abs_nonneg alpha)
          (inv_nonneg.mpr (centeredCubeScale_pos m).le))
        (sourceForcingPositiveBesovConstant_nonneg d s))
  · rw [scaledVectorDatumFractionalBound_eq_sourceDatum]
    exact mul_le_mul_of_nonneg_left hbudget
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (centeredCubeScale_pos m).le _)
          (mul_nonneg (abs_nonneg alpha)
            (inv_nonneg.mpr (centeredCubeScale_pos m).le)))
        (sourceForcingFractionalConstant_nonneg d s2))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
