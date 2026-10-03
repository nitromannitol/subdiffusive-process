module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.SlabMeanSplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CoarseL2Poincare

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The vanishing-fraction mean bound.**  If `f` vanishes on a measurable
subset `Z` of the open cube whose volume is at least `θ` times the cube's,
then the mean of `f` is controlled by `√(2/θ)` times its oscillation. -/
theorem sq_cubeAverage_le_of_vanishing_fraction
    (Q : TriadicCube d) {f : Vec d → ℝ} {Z : Set (Vec d)} {θ : ℝ}
    (hZmeas : MeasurableSet Z) (hZsub : Z ⊆ openCubeSet Q)
    (hθ : 0 < θ)
    (hfrac : θ * (volume (openCubeSet Q)).toReal ≤ (volume Z).toReal)
    (hzero : ∀ x ∈ Z, f x = 0)
    (hf : IntegrableOn f (openCubeSet Q))
    (hf2 : IntegrableOn (fun x => f x ^ 2) (openCubeSet Q))
    (hmem : MemLp (fun x => f x - cubeAverage Q f) 2
      (volume.restrict (openCubeSet Q))) :
    cubeAverage Q f ^ 2 ≤
      2 * θ⁻¹ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) ^ 2 := by
  have hPvol : (volume (openCubeSet Q)).toReal = cubeVolume Q := volume_openCubeSet_toReal Q
  have hPpos : 0 < (volume (openCubeSet Q)).toReal := by
    rw [hPvol]; exact cubeVolume_pos Q
  have hPtop : volume (openCubeSet Q) ≠ ⊤ := by
    intro htop
    rw [htop] at hPvol
    simp only [ENNReal.toReal_top] at hPvol
    exact absurd hPvol.symm (ne_of_gt (cubeVolume_pos Q))
  have hZpos : 0 < (volume Z).toReal :=
    lt_of_lt_of_le (by positivity) hfrac
  have hsplit := sq_averageOn_le_slab_add_oscillation
    (P := openCubeSet Q) (S := Z) (f := f) hZmeas hZsub hPtop hPpos hZpos hf hf2
  -- the vanishing set contributes nothing
  have hzeroL2 : normalizedL2On Z f = 0 := by
    have hint : ∫ x in Z, f x ^ 2 ∂volume = 0 := by
      rw [setIntegral_congr_fun hZmeas
        (g := fun _ : Vec d => (0 : ℝ)) (fun x hx => by rw [hzero x hx]; ring)]
      simp
    unfold normalizedL2On
    rw [volumeAverage_eq_zero_of_integral_eq_zero hint]
    simp
  rw [hzeroL2] at hsplit
  -- the volume ratio is at most `θ⁻¹`
  have hratio : (volume (openCubeSet Q)).toReal / (volume Z).toReal ≤ θ⁻¹ := by
    rw [div_le_iff₀ hZpos, inv_mul_eq_div, le_div_iff₀ hθ]
    linarith only [hfrac]
  have hoscnonneg : 0 ≤ normalizedL2On (openCubeSet Q)
      (fun x => f x - averageOn (openCubeSet Q) f) ^ 2 := sq_nonneg _
  have haveq : averageOn (openCubeSet Q) f = cubeAverage Q f :=
    volumeAverage_openCubeSet_eq_cubeAverage Q f
  have hL2eq : normalizedL2On (openCubeSet Q)
      (fun x => f x - cubeAverage Q f) = cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) := by
    rw [normalizedL2On_openCubeSet_eq_cubeLpNorm Q hmem]
    rfl
  rw [haveq] at hsplit
  rw [hL2eq] at hsplit
  calc
    cubeAverage Q f ^ 2 ≤
        2 * 0 ^ 2 +
          2 * ((volume (openCubeSet Q)).toReal / (volume Z).toReal) *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) ^ 2 := hsplit
    _ ≤ 2 * θ⁻¹ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) ^ 2 := by
          have hnn : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) ^ 2 := sq_nonneg _
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)) hnn
          simpa using this

variable [NeZero d]



theorem sq_cubeAverage_le_of_vanishing_fraction_of_lambdaSCap
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    {Z : Set (Vec d)} {θ t sigma K : ℝ}
    (hZmeas : MeasurableSet Z) (hZsub : Z ⊆ openCubeSet Q)
    (hθ : 0 < θ)
    (hfrac : θ * (volume (openCubeSet Q)).toReal ≤ (volume Z).toReal)
    (hzero : ∀ x ∈ Z, u.toFun x = 0)
    (hf : IntegrableOn u.toFun (openCubeSet Q))
    (hf2 : IntegrableOn (fun x => u.toFun x ^ 2) (openCubeSet Q))
    (hmem : MemLp (fun x => u.toFun x - cubeAverage Q u.toFun) 2
      (volume.restrict (openCubeSet Q)))
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hcap : (Ch02.lambdaS Q t (aCutoffFamily M L omega))⁻¹ ≤ K * sigma⁻¹) :
    cubeAverage Q u.toFun ^ 2 ≤
      2 * θ⁻¹ * (coarseL2PoincareConst d * Real.sqrt (K * sigma⁻¹) *
          cubeScaleFactor Q) ^ 2 *
        cubeAverage Q (coefficientEnergyDensity
          (publicCoeffField Q (aCutoffFamily M L omega)) u.grad) := by
  have hpoin := aCutoff_cubeFluctuation_lpNorm_le_of_lambdaSCap M L omega Q u
    ht ht1 hcap
  have hmean := sq_cubeAverage_le_of_vanishing_fraction Q hZmeas hZsub hθ hfrac
    hzero hf hf2 hmem
  set C : ℝ := coarseL2PoincareConst d * Real.sqrt (K * sigma⁻¹) *
    cubeScaleFactor Q with hC
  set E : ℝ := cubeAverage Q (coefficientEnergyDensity
    (publicCoeffField Q (aCutoffFamily M L omega)) u.grad) with hE
  have hEll := publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega)
  have hEnonneg : 0 ≤ E := by
    rw [hE]
    refine cubeAverage_nonneg_of_nonneg_on ?_
    intro x hx
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll u.grad x hx
  have hLp : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) :=
    ENNReal.toReal_nonneg
  have hsq : cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) ^ 2 ≤ C ^ 2 * E := by
    have h := pow_le_pow_left₀ hLp hpoin 2
    rwa [mul_pow, Real.sq_sqrt hEnonneg] at h
  have hcoef : (0 : ℝ) ≤ 2 * θ⁻¹ := by positivity
  calc
    cubeAverage Q u.toFun ^ 2 ≤
        2 * θ⁻¹ * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) ^ 2 := hmean
    _ ≤ 2 * θ⁻¹ * (C ^ 2 * E) := mul_le_mul_of_nonneg_left hsq hcoef
    _ = 2 * θ⁻¹ * C ^ 2 * E := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
