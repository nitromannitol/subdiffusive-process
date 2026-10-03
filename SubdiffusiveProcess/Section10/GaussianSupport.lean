module

public import Mathlib
public import SubdiffusiveProcess.Sobolev.WeakGradient
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.Section10.GaussianLeaves
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace Paper
/-- Section 10, auditor Fixes 9/10, L:258–399. Independently harvested order `astra10r3_0927_gaussian_zero_variance_retry`. -/
theorem aux_lim_nongaussian_gaussian_zero_variance
    {d : ℕ} (P : Measure (SpatialCoordinates d)) [IsGaussian P]
    (L : StrongDual ℝ (SpatialCoordinates d)) (hvar : Var[L; P] = 0) :
    P {x | L x ≠ ∫ y, L y ∂P} = 0 := by
  have hmap : Measure.map L P = Measure.dirac (∫ y, L y ∂P) := by
    have h1 := IsGaussian.map_eq_gaussianReal (μ := P) L
    rw [hvar, Real.toNNReal_zero, gaussianReal_zero_var] at h1
    exact h1
  have hmeas : Measurable L := L.continuous.measurable
  have hset : {x : SpatialCoordinates d | L x ≠ ∫ y, L y ∂P} = L ⁻¹' {(∫ y, L y ∂P)}ᶜ := rfl
  rw [hset, ← Measure.map_apply hmeas (measurableSet_singleton _).compl, hmap,
    Measure.dirac_apply' _ (measurableSet_singleton _).compl]
  simp

/-- L:395–399: a dominated Gaussian would have strictly positive variance in every nonzero direction. -/
theorem aux_lim_nongaussian_variance_positive_of_domination
    {d : ℕ} (P mu : Measure (SpatialCoordinates d)) [IsGaussian P]
    (hac : P ≪ mu)
    (hplanes : ∀ L : StrongDual ℝ (SpatialCoordinates d), L ≠ 0 →
      ∀ a : ℝ, mu {x | L x = a} = 0)
    (L : StrongDual ℝ (SpatialCoordinates d)) (hL : L ≠ 0) :
    0 < Var[L; P] := by
  exact aux_lim_nongaussian_variance_positive P L (hac (hplanes L hL _))

end Paper
