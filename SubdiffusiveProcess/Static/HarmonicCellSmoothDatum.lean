module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Static.CutoffHarmonicCellCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceEnergyPrice
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

@[expose] public section

/-! # Quantitative native weak-Hessian prices for smooth cutoff data -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The chart datum in the native weak-Hessian carrier. -/
def cutoffHarmonicCellH2Datum {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    H2Datum (originCube d 0) where
  toH1 := cutoffHarmonicCellDatum f hf hc
  weakHessian := hasWeakHessianOn_ofContDiff (isOpen_openCubeSet _) hf hc

private theorem norm_basisVec_one {d : ℕ} (i : Fin d) : ‖basisVec i‖ = (1 : ℝ) := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 ?_
    intro j
    by_cases hji : j = i
    · subst j
      simp [basisVec]
    · simp [basisVec, hji]
  · have hi := norm_le_pi_norm (basisVec i) i
    simpa [basisVec] using hi

/-- Every first and second coordinate derivative has the same global price
as the Fréchet derivative bounds in the cell contract. -/
theorem harmonicCutoffDatum_coordinate_bounds {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {B : ℝ}
    (hB : HarmonicCutoffDatumSizeBound f B) :
    ∀ x, (∀ i : Fin d, |euclideanCoordDeriv i f x| ≤ B) ∧
      ∀ i j : Fin d, |euclideanCoordSecondDeriv i j f x| ≤ B := by
  intro x
  constructor
  · intro i
    calc
      _ = ‖fderiv ℝ f x (basisVec i)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ f x‖ * ‖basisVec i‖ := (fderiv ℝ f x).le_opNorm _
      _ ≤ B := by simpa only [norm_basisVec_one, mul_one] using (hB x).2.1
  · intro i j
    rw [euclideanCoordSecondDeriv_eq_fderiv_fderiv hf]
    calc
      _ = ‖fderiv ℝ (fderiv ℝ f) x (basisVec j) (basisVec i)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) x (basisVec j)‖ * ‖basisVec i‖ :=
        (fderiv ℝ (fderiv ℝ f) x (basisVec j)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) x‖ * ‖basisVec j‖) * ‖basisVec i‖ := by
        gcongr
        exact (fderiv ℝ (fderiv ℝ f) x).le_opNorm _
      _ ≤ B := by simpa only [norm_basisVec_one, mul_one] using (hB x).2.2

/-- The unit-cube scalar norm pays no volume loss. -/
theorem l2Size_unit_le_of_bound {d : ℕ} (f : Vec d → ℝ) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) : SubdiffusiveProcess.RawLp.eLpNorm f 2
      (volume.restrict (openCubeSet (originCube d 0))) ≤ ENNReal.ofReal B := by
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0)
  have hmono := SubdiffusiveProcess.RawLp.eLpNorm_mono_ae (p := (2 : ℝ≥0∞))
    (μ := volume.restrict (openCubeSet (originCube d 0))) (f := f) (g := fun _ => B)
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hB0] using hB x)
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded aestronglyMeasurable_const] at hmono
  have hconst := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞))
    (μ := volume.restrict (openCubeSet (originCube d 0))) (f := fun _ => B) (C := B)
    aestronglyMeasurable_const (Filter.Eventually.of_forall fun _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg hB0])
  simpa only [Measure.restrict_apply_univ, volume_openCubeSet_originCube_zero,
    ENNReal.one_rpow, one_mul] using hmono.trans hconst

/-- The guarded unit-cube norm bound for measurable data. -/
theorem l2Size_unit_le_of_bound_of_aestronglyMeasurable {d : ℕ} (f : Vec d → ℝ)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hf : AEStronglyMeasurable f (volume.restrict (openCubeSet (originCube d 0)))) :
    l2Size (originCube d 0) f ≤ ENNReal.ofReal B := by
  unfold l2Size
  rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf]
  exact l2Size_unit_le_of_bound f hB

/-- The exact coordinate-sum norm is controlled by the cell datum
price, uniformly over the smooth function and its support. -/
theorem cutoffHarmonicCellH2Datum_norm_le {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : HarmonicCutoffDatumSizeBound f B) :
    (cutoffHarmonicCellH2Datum f hf hc).norm ≤
      ENNReal.ofReal ((1 + (d : ℝ) + (d : ℝ) ^ 2) * B) := by
  have hcoord := harmonicCutoffDatum_coordinate_bounds f hf hB
  have hval := l2Size_unit_le_of_bound_of_aestronglyMeasurable f
    (fun x => (hB x).1) hf.continuous.aestronglyMeasurable
  have hgrad : ∀ i : Fin d, l2Size (originCube d 0)
      (fun x => (cutoffHarmonicCellH2Datum f hf hc).toH1.grad x i) ≤ ENNReal.ofReal B := by
    intro i
    exact l2Size_unit_le_of_bound_of_aestronglyMeasurable _ (fun x => (hcoord x).1 i)
      ((cutoffHarmonicCellH2Datum f hf hc).toH1.grad_memL2 i).aestronglyMeasurable
  have hhess : ∀ i j : Fin d, l2Size (originCube d 0)
      ((cutoffHarmonicCellH2Datum f hf hc).weakHessian.hess i j) ≤ ENNReal.ofReal B := by
    intro i j
    exact l2Size_unit_le_of_bound_of_aestronglyMeasurable _ (fun x => (hcoord x).2 i j)
      ((cutoffHarmonicCellH2Datum f hf hc).weakHessian.hess_memL2 i j).aestronglyMeasurable
  unfold H2Datum.norm
  calc
    _ ≤ ENNReal.ofReal B + (∑ _i : Fin d, ENNReal.ofReal B) +
        ∑ _i : Fin d, ∑ _j : Fin d, ENNReal.ofReal B :=
      add_le_add (add_le_add hval (Finset.sum_le_sum fun i _ => hgrad i))
        (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hhess i j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add hB0 (by positivity),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring


/-- A dimension-only Euclidean gradient price for the canonical native datum. -/
theorem cutoffHarmonicCellDatum_gradient_le {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : HarmonicCutoffDatumSizeBound f B) (x : Vec d) :
    euclideanNorm ((cutoffHarmonicCellDatum f hf hc).grad x) ≤ (d : ℝ) * B := by
  have hcoord := (harmonicCutoffDatum_coordinate_bounds f hf hB x).1
  have hnorm : ‖(cutoffHarmonicCellDatum f hf hc).grad x‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB0).mpr
    intro i
    simpa only [Real.norm_eq_abs] using! hcoord i
  exact (euclideanNorm_le_dimension_mul_norm _).trans
    (mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _))

end SubdiffusiveProcess.Static
