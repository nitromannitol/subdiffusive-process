module

public import SubdiffusiveProcess.Analysis.RawLp
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule

@[expose] public section

/-!
# Smooth compactly supported test functions in the weighted `L²` of a bounded domain

This file supplies the two elementary facts about `C_c^∞(U)` that the strong-continuity
argument of `KilledStrongContinuity.lean` runs on:

* `h10OfTest` — a smooth compactly supported function with `tsupport ⊆ U` *is* an
  `H¹₀(U)` function, so it may be used as a test function in
  `Section8Resolvent.IsMassiveWeakSolutionOn`, and its `L²` class may be fed to
  `Section9SupportInput.LocalDiffusion`'s resolvent clause;
* `denseRange_testToLpWeighted` — those functions are dense in
  `L²(U, ρ dx)`.  The Lebesgue-measure statement is
  `Homogenization.denseRange_h1WeakTestFunction_toScalarL2`; the transfer is by the
  two-sided bound `lo ≤ ρ ≤ hi` of `Section9SupportInput.CoefficientOn`, which makes the
  two `L²` norms equivalent on `U`.
-/

set_option autoImplicit false

open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledTestFunctions

variable {d : ℕ} {rho : Vec d → ℝ} {U : Set (Vec d)}

/-! ## A test function as an `H¹₀` function -/

/-- **A smooth compactly supported test function supported in `U` is an `H¹₀(U)`
function**, with its classical gradient as weak gradient and the constant sequence as
approximating sequence. -/
def h10OfTest (φ : H1WeakTestFunction U) : H10Function U where
  toFun := φ
  grad := fun x i => (fderiv ℝ (φ : Vec d → ℝ) x) (basisVec i)
  memL2 := (φ.smooth.continuous.memLp_of_hasCompactSupport φ.compactSupport).restrict U
  gradMemL2 := by
    intro i
    have hcont : Continuous fun x => (fderiv ℝ (φ : Vec d → ℝ) x) (basisVec i) :=
      (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).continuous.comp
        (φ.smooth.continuous_fderiv (by simp))
    have hcs : HasCompactSupport fun x => (fderiv ℝ (φ : Vec d → ℝ) x) (basisVec i) :=
      (φ.compactSupport.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) rfl
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict U
  hasWeakGradient := HasWeakGradientOn.of_contDiff (φ.smooth.of_le (by exact_mod_cast le_top))
  approx := fun _ => φ
  approx_smooth := fun _ => φ.smooth
  approx_hasCompactSupport := fun _ => φ.compactSupport
  approx_support_subset := fun _ => φ.support_subset
  tendsto_approx := by simp
  tendsto_approx_grad := by intro i; simp

theorem h10OfTest_toFun (φ : H1WeakTestFunction U) :
    (h10OfTest φ).toH1Function.toFun = (φ : Vec d → ℝ) := by rfl

/-! ## Density in the weighted `L²` -/

theorem memLp_test_volume (φ : H1WeakTestFunction U) :
    MemLp (φ : Vec d → ℝ) 2 (volume.restrict U) :=
  (φ.smooth.continuous.memLp_of_hasCompactSupport φ.compactSupport).restrict U

theorem memLp_test_weighted (hU : MeasurableSet U) (hr : CoefficientOn U rho)
    (φ : H1WeakTestFunction U) :
    MemLp (φ : Vec d → ℝ) 2 ((weightedMeasure rho).restrict U) :=
  memLp_weighted_of_volume_restrict hU hr (memLp_test_volume φ)

/-- The `L²(U, ρ dx)` class of a smooth compactly supported test function. -/
def testToLpWeighted (hU : MeasurableSet U) (hr : CoefficientOn U rho)
    (φ : H1WeakTestFunction U) : Lp ℝ 2 ((weightedMeasure rho).restrict U) :=
  (memLp_test_weighted hU hr φ).toLp (φ : Vec d → ℝ)

theorem coeFn_testToLpWeighted (hU : MeasurableSet U) (hr : CoefficientOn U rho)
    (φ : H1WeakTestFunction U) :
    testToLpWeighted hU hr φ
      =ᵐ[(weightedMeasure rho).restrict U] (φ : Vec d → ℝ) :=
  (memLp_test_weighted hU hr φ).coeFn_toLp

/-- An upper density bound compares the weighted and Lebesgue `L²` seminorms. -/
theorem eLpNorm_weighted_le (hU : MeasurableSet U) {hi : ℝ}
    (hhi : ∀ᵐ x ∂volume.restrict U, rho x ≤ hi) (h : Vec d → ℝ) :
    SubdiffusiveProcess.RawLp.eLpNorm h 2 ((weightedMeasure rho).restrict U)
      ≤ (ENNReal.ofReal hi) ^ ((1:ℝ≥0∞)/2).toReal * SubdiffusiveProcess.RawLp.eLpNorm h 2 (volume.restrict U) := by
  norm_num only [SubdiffusiveProcess.RawLp.eLpNorm, ENNReal.toReal_ofNat, ite_false]
  calc eLpNorm' h 2 ((weightedMeasure rho).restrict U)
      ≤ eLpNorm' h 2 ((ENNReal.ofReal hi) • volume.restrict U) :=
        eLpNorm'_mono_measure _ (weightedMeasure_restrict_le_smul_volume_restrict hU hi hhi) (by norm_num)
    _ = _ := by rw [eLpNorm'_smul_measure (by norm_num)]; norm_num

/-- **Smooth compactly supported test functions supported in `U` are dense in
`L²(U, ρ dx)`.** -/
theorem denseRange_testToLpWeighted (hU : IsOpen U) (hUvol : volume U ≠ ⊤)
    (hr : CoefficientOn U rho) :
    DenseRange (testToLpWeighted hU.measurableSet hr) := by
  classical
  obtain ⟨lo, hi, hlo, hb⟩ := hr.2
  have hlo' : ∀ᵐ x ∂volume.restrict U, lo ≤ rho x := hb.mono fun _ h => h.1
  have hhi' : ∀ᵐ x ∂volume.restrict U, rho x ≤ hi := hb.mono fun _ h => h.2
  have hlo0 : (ENNReal.ofReal lo) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 hlo)
  set A : ℝ≥0∞ := (ENNReal.ofReal hi) ^ ((1:ℝ≥0∞)/2).toReal with hA
  have hAne : A ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  set M : ℝ := A.toReal with hM
  have hM0 : (0:ℝ) ≤ M := ENNReal.toReal_nonneg
  rw [Metric.denseRange_iff]
  intro F ε hε
  have hcmp : volume.restrict U
      ≤ (ENNReal.ofReal lo)⁻¹ • ((weightedMeasure rho).restrict U) := by
    have h := smul_volume_restrict_le_weightedMeasure_restrict hU.measurableSet lo hlo'
    refine Measure.le_iff'.mpr fun B => ?_
    have hB := Measure.le_iff'.mp h B
    simp only [Measure.smul_apply, smul_eq_mul] at hB ⊢
    calc (volume.restrict U) B
        = (ENNReal.ofReal lo)⁻¹ * ((ENNReal.ofReal lo) * (volume.restrict U) B) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hlo0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal lo)⁻¹ * ((weightedMeasure rho).restrict U) B :=
          mul_le_mul_right hB _
  have hFvol : MemLp (F : Vec d → ℝ) 2 (volume.restrict U) :=
    (Lp.memLp F).of_measure_le_smul (by simp [hlo0]) hcmp
  obtain ⟨φ, hφ⟩ := Metric.denseRange_iff.1
    (denseRange_h1WeakTestFunction_toScalarL2 hU hUvol) (hFvol.toLp (F : Vec d → ℝ))
    (ε / (M + 1)) (by positivity)
  refine ⟨φ, ?_⟩
  have hdiff : ∀ᵐ x ∂volume.restrict U,
      (hFvol.toLp (F : Vec d → ℝ)) x - (φ.toScalarL2 : Vec d → ℝ) x = F x - φ x := by
    filter_upwards [φ.coeFn_toScalarL2, hFvol.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have hvolEq : eLpNorm (⇑(hFvol.toLp (F : Vec d → ℝ)) - ⇑φ.toScalarL2) 2 (volume.restrict U)
      = eLpNorm (fun x => (F : Vec d → ℝ) x - φ x) 2 (volume.restrict U) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hdiff] with x hx
    simpa only [Pi.sub_apply] using! hx
  have hmuEq : eLpNorm (⇑F - ⇑(testToLpWeighted hU.measurableSet hr φ)) 2
        ((weightedMeasure rho).restrict U)
      = eLpNorm (fun x => (F : Vec d → ℝ) x - φ x) 2 ((weightedMeasure rho).restrict U) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [(memLp_test_weighted hU.measurableSet hr φ).coeFn_toLp] with x hx
    simpa only [testToLpWeighted, Pi.sub_apply] using! congrArg (fun y => (F : Vec d → ℝ) x - y) hx
  have hkey : dist F (testToLpWeighted hU.measurableSet hr φ)
      ≤ M * dist (hFvol.toLp (F : Vec d → ℝ)) φ.toScalarL2 := by
    rw [Lp.dist_def, Lp.dist_def, hmuEq, hvolEq, hM, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono
      (ENNReal.mul_ne_top hAne (hFvol.sub (memLp_test_volume φ)).eLpNorm_ne_top) ?_
    have hv : AEStronglyMeasurable (fun x => (F : Vec d → ℝ) x - φ x) (volume.restrict U) := by
      simpa only [Pi.sub_apply] using! (hFvol.sub (memLp_test_volume φ)).aestronglyMeasurable
    have hw : AEStronglyMeasurable (fun x => (F : Vec d → ℝ) x - φ x) ((weightedMeasure rho).restrict U) := by
      simpa only [Pi.sub_apply] using! (memLp_weighted_of_volume_restrict hU.measurableSet hr
        (hFvol.sub (memLp_test_volume φ))).aestronglyMeasurable
    simpa only [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hv, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hw] using!
      eLpNorm_weighted_le hU.measurableSet hhi' (fun x => (F : Vec d → ℝ) x - φ x)
  refine lt_of_le_of_lt hkey ?_
  calc M * dist (hFvol.toLp (F : Vec d → ℝ)) φ.toScalarL2
      ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hφ.le hM0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledTestFunctions
