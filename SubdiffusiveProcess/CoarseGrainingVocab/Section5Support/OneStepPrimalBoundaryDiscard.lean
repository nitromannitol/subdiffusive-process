import SubdiffusiveProcess.CoarseGrainingVocab.AhomCharacterization
import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixVariational
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepThermodynamicAggregation




open Filter MeasureTheory Homogenization Homogenization.Book

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The primal finite-volume scalar readout in the half-energy
normalization of the manuscript. -/
def oneStepPrimalFiniteVolumeReadout {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ) (p : Vec d) : ℝ :=
  (1 / 2 : ℝ) * vecDot p (matVecMul
    (abar M L (Ch02.cubeDomain (originCube d (K : ℤ)))) p)

/-- The primal readout is the expected random coarse quadratic form. -/
theorem oneStepPrimalFiniteVolumeReadout_eq_integral {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ) (p : Vec d) :
    oneStepPrimalFiniteVolumeReadout M L K p =
      ∫ omega : Sample d, (1 / 2 : ℝ) * vecDot p
        (matVecMul (randomAMatrix M L
          (Ch02.cubeDomain (originCube d (K : ℤ))) omega) p)
        ∂M.P.toMeasure := by
  exact (integral_randomAMatrix_quadratic M L
    (Ch02.cubeDomain (originCube d (K : ℤ))) p).symm

/-- The annealed primal readout converges to the homogenized scalar
quadratic form. -/
theorem tendsto_oneStepPrimalFiniteVolumeReadout {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (p : Vec d) :
    Tendsto (fun K : ℕ => oneStepPrimalFiniteVolumeReadout M L K p)
      atTop (nhds ((1 / 2 : ℝ) * ahom M L * vecNormSq p)) := by
  have hmatrix := tendsto_abar_originCube_ahom M L
  have hcontinuous : Continuous (fun A : Mat d =>
      (1 / 2 : ℝ) * vecDot p (matVecMul A p)) := by
    unfold vecDot matVecMul
    exact continuous_const.mul
      (continuous_finset_sum _ fun i _ => continuous_const.mul
        (continuous_finset_sum _ fun j _ =>
          ((continuous_apply j).comp (continuous_apply i)).mul continuous_const))
  have h := hcontinuous.continuousAt.tendsto.comp hmatrix
  have hlimit :
      (1 / 2 : ℝ) * vecDot p (matVecMul (ahom M L • (1 : Mat d)) p) =
        (1 / 2 : ℝ) * ahom M L * vecNormSq p := by
    unfold vecNormSq vecDot matVecMul
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have hquad :
      ∑ i, p i * ∑ j, (ahom M L * if i = j then 1 else 0) * p j =
          ahom M L * ∑ i, p i * p i := by
      calc
        _ = ∑ i, p i * (ahom M L * p i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          congr 1
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _hj hji
            simp [Ne.symm hji]
          · simp
        _ = ahom M L * ∑ i, p i * p i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    rw [hquad]
    ring
  simpa only [oneStepPrimalFiniteVolumeReadout, hlimit] using h

/-- A samplewise random-coarse-matrix comparison integrates to a bound on
the literal primal readout. -/
theorem oneStepPrimalFiniteVolumeReadout_le_integral_of_ae {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ) (p : Vec d)
    (energy : Sample d → ℝ)
    (henergy : Integrable energy M.P.toMeasure)
    (hle : ∀ᵐ omega ∂M.P.toMeasure,
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (randomAMatrix M L
          (Ch02.cubeDomain (originCube d (K : ℤ))) omega) p) ≤
        energy omega) :
    oneStepPrimalFiniteVolumeReadout M L K p ≤
      ∫ omega, energy omega ∂M.P.toMeasure := by
  rw [oneStepPrimalFiniteVolumeReadout_eq_integral]
  apply integral_mono_ae
  · have hmatrix := integrable_randomAMatrix M L
      (Ch02.cubeDomain (originCube d (K : ℤ)))
    have hquad : Integrable (fun omega : Sample d => vecDot p
        (matVecMul (randomAMatrix M L
          (Ch02.cubeDomain (originCube d (K : ℤ))) omega) p))
        M.P.toMeasure := by
      unfold vecDot matVecMul
      apply integrable_finset_sum
      intro i _hi
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro j _hj
      exact (((hmatrix.eval i).eval j).mul_const (p j))
    exact hquad.const_mul (1 / 2)
  · exact henergy
  · exact hle

/-- Boundary-discard passage for the primal one-step competitor. -/
theorem half_ahom_mul_vecNormSq_le_of_primal_boundary_discard {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (p : Vec d)
    (interior boundary : ℕ → ℝ) (interiorInf : ℝ)
    (hinterior : Tendsto interior atTop (nhds interiorInf))
    (hboundary : Tendsto boundary atTop (nhds 0))
    (hle : ∀ K : ℕ,
      oneStepPrimalFiniteVolumeReadout M L K p ≤ interior K + boundary K) :
    (1 / 2 : ℝ) * ahom M L * vecNormSq p ≤ interiorInf := by
  exact oneStep_limit_le_of_interior_add_boundary
    (tendsto_oneStepPrimalFiniteVolumeReadout M L p)
    hinterior hboundary hle

/-- Unit-probe form used by the scalar upper one-step estimate. -/
theorem half_ahom_le_of_primal_boundary_discard {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (p : Vec d)
    (hp : vecNormSq p = 1)
    (interior boundary : ℕ → ℝ) (interiorInf : ℝ)
    (hinterior : Tendsto interior atTop (nhds interiorInf))
    (hboundary : Tendsto boundary atTop (nhds 0))
    (hle : ∀ K : ℕ,
      oneStepPrimalFiniteVolumeReadout M L K p ≤ interior K + boundary K) :
    (1 / 2 : ℝ) * ahom M L ≤ interiorInf := by
  simpa only [hp, mul_one] using
    half_ahom_mul_vecNormSq_le_of_primal_boundary_discard
      M L p interior boundary interiorInf hinterior hboundary hle

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
