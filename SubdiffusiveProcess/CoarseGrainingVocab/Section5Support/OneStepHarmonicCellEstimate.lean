module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLpRestriction

@[expose] public section




open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

theorem four_le_oneStepHarmonicExponent (d : ℕ) (hd : 3 ≤ d) :
    (4 : ℝ≥0∞) ≤ (oneStepHarmonicExponent d hd).exponent := by
  rw [oneStepHarmonicExponent]
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hreal : (4 : ℝ) ≤ 16 * (d : ℝ) := by linarith
  simpa using ENNReal.ofReal_le_ofReal hreal

/-- A harmonic weak Hessian with coordinatewise normalized `L^(16d)` bound
`B` on `D` gives the scale-sharp normalized cell oscillation on the central
depth-`n` descendant of `D`. -/
theorem harmonic_cellGradientOscillation_le_highExponent
    {d : ℕ} (hd : 3 ≤ d) (D : TriadicCube d) (n : ℕ)
    (u : H1Function (openCubeSet D))
    (H : HasWeakHessianOn (openCubeSet D) u) (B : ℝ)
    (hmem : ∀ i j : Fin d,
      MemLp (fun x => H.hess i j x)
        (oneStepHarmonicExponent d hd).exponent
        (normalizedCubeMeasure D))
    (hbound : ∀ i j : Fin d,
      cubeLpNorm D (oneStepHarmonicExponent d hd).exponent
        (fun x => H.hess i j x) ≤ B) :
    let R := CubeCalderonZygmund.centralDescendant D n
    oneStepCellGradientOscillation R
        (u.restrictToOpenSubcube
          (CubeCalderonZygmund.centralDescendant_mem_descendantsAtDepth D n)) ≤
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        cubeScaleFactor R *
          ((d : ℝ) ^ 2 *
            ((((3 ^ d) ^ n : ℕ) : ℝ) ^
              (1 / (oneStepHarmonicExponent d hd).exponent).toReal) * B) := by
  let R := CubeCalderonZygmund.centralDescendant D n
  let hR := CubeCalderonZygmund.centralDescendant_mem_descendantsAtDepth D n
  let HR : HasWeakHessianOn (openCubeSet R) (u.restrictToOpenSubcube hR) :=
    H.restrict (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
  have hHRH : ∀ i j : Fin d, ∀ x : Vec d,
      HR.hess i j x = H.hess i j x := by
    intro i j x
    rfl
  have hH4 : ∀ i j : Fin d,
      MemLp (fun x => HR.hess i j x) (4 : ℝ≥0∞)
        (normalizedCubeMeasure R) := by
    intro i j
    have hqR := CubeCalderonZygmund.memLp_centralDescendant_of_memLp n
      (hmem i j)
    have h4R := hqR.mono_exponent (four_le_oneStepHarmonicExponent d hd)
    simpa only [hHRH] using h4R
  have hcoord : ∀ i j : Fin d,
      cubeLpNorm R 4 (fun x => HR.hess i j x) ≤
        ((((3 ^ d) ^ n : ℕ) : ℝ) ^
          (1 / (oneStepHarmonicExponent d hd).exponent).toReal) * B := by
    intro i j
    have hrestrict := cubeLpNorm_centralDescendant_downgrade_le_count_rpow
      D n (oneStepHarmonicExponent d hd) 4
      (four_le_oneStepHarmonicExponent d hd) (fun x => H.hess i j x)
      (hmem i j)
    rw [show (fun x => HR.hess i j x) = (fun x => H.hess i j x) by
      funext x; exact hHRH i j x]
    exact hrestrict.trans (mul_le_mul_of_nonneg_left (hbound i j) (by positivity))
  have hfour : oneStepCellHessianFourSize R HR ≤
      (d : ℝ) ^ 2 *
        (((((3 ^ d) ^ n : ℕ) : ℝ) ^
          (1 / (oneStepHarmonicExponent d hd).exponent).toReal) * B) := by
    unfold oneStepCellHessianFourSize
    calc
      ∑ i : Fin d, ∑ j : Fin d,
          cubeLpNorm R 4 (fun x => HR.hess i j x) ≤
        ∑ _i : Fin d, ∑ _j : Fin d,
          (((((3 ^ d) ^ n : ℕ) : ℝ) ^
            (1 / (oneStepHarmonicExponent d hd).exponent).toReal) * B) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcoord i j
      _ = (d : ℝ) ^ 2 *
          (((((3 ^ d) ^ n : ℕ) : ℝ) ^
            (1 / (oneStepHarmonicExponent d hd).exponent).toReal) * B) := by
        simp [nsmul_eq_mul]
        ring
  dsimp only
  calc
    oneStepCellGradientOscillation R (u.restrictToOpenSubcube hR) ≤
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
          cubeScaleFactor R * oneStepCellHessianFourSize R HR :=
      oneStepCellGradientOscillation_le_hessianFourSize R HR hH4
    _ ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        cubeScaleFactor R *
          ((d : ℝ) ^ 2 *
            ((((3 ^ d) ^ n : ℕ) : ℝ) ^
              (1 / (oneStepHarmonicExponent d hd).exponent).toReal) * B) :=
      mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hfour)
        (mul_nonneg
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
          (cubeScaleFactor_nonneg R))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
