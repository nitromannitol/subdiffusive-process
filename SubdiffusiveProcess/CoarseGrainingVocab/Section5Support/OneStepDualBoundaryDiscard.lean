import SubdiffusiveProcess.CoarseGrainingVocab.AhomStarCharacterization
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedSourceParentReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepRetainedBoundaryGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepRetainedNeumannGluing
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepThermodynamicAggregation




open Filter MeasureTheory Homogenization Homogenization.Book

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The literal retained source cells are an admissible subfamily of the
depth partition used by the selected cell minimizers. -/
theorem oneStepRetainedSourceCells_subset_descendantsAtDepth {d : ℕ}
    {K source : ℤ} {N : ℕ} (hsource : source ≤ K) :
    oneStepRetainedSourceCells (d := d) K source N ⊆
      descendantsAtDepth (originCube d K) (Int.toNat (K - source)) := by
  intro R hR
  have hscale := (mem_oneStepRetainedSourceCells_iff.mp hR).1
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d K) hsource] at hscale
  simpa [originCube] using hscale

/-- Public cutoff specialization of the inverse-star/lower-right identity.
The analogous helper in `SharpCompareJ` is private; this support theorem is
needed by the retained finite-volume variational insertion. -/
theorem randomAStarMatrix_inv_eq_sigmaStarInvCoarse {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) :
    (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ =
      sigmaStarInvCoarse (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) := by
  let U := Ch02.cubeDomain Q
  let a := (aCutoffCoeffOnData M L omega U).toCoeffOn
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U a
    (aCutoffCoeffOnData M L omega U).isSymmetric
  change (aStarMatrix U a)⁻¹ = Ch02.sigmaStarInvCoarse U a
  rw [show aStarMatrix U a = Ch02.sigmaStarCoarse U a from
    hTheory.derived_matrices.2.1]
  unfold Ch02.sigmaStarCoarse
  exact Matrix.nonsing_inv_nonsing_inv _
    (Ch02.isUnit_det_sigmaStarInvCoarse U a)

/-- Samplewise retained-cell variational comparison in the exact random
inverse-star carrier used by the annealed thermodynamic readout. -/
theorem half_randomAStarMatrix_inv_quadratic_le_retainedGluedEnergy
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) (j : ℕ)
    (s : Finset (TriadicCube d))
    (P F : TriadicCube d → Vec d → Vec d)
    (background : Vec d → Vec d) (q : Vec d) {lam Lam : ℝ}
    (hs : s ⊆ descendantsAtDepth Q j)
    (hEllParent : IsEllipticFieldOn lam Lam (openCubeSet Q)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)))
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)))
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R))
    (hBackgroundL2 : MemVectorL2 (openCubeSet Q) background)
    (hBackground : IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x ↦ background x - q))
    (hex : ∃ Abar : BlockMat d,
      IsCoarseBlockMatrix (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) Abar)
    (hMuResp : ∀ r : Vec d,
      Mu (openCubeSet Q) (0, r)
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) =
        ResponseJ (openCubeSet Q) 0 r
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹) q) ≤
      (1 / 2 : ℝ) * volumeAverage (openCubeSet Q) (fun x ↦
        let flux := oneStepSelectedRetainedGluedNeumannTwoFlux
          Q j s
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))
          P F background hEll hP hF x
        vecDot flux
          (matVecMul
            ((blockMatrixOfCoeff
              (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
            flux)) := by
  rw [randomAStarMatrix_inv_eq_sigmaStarInvCoarse M L omega Q]
  exact mul_le_mul_of_nonneg_left
    (vecDot_sigmaStarInvCoarse_le_selectedRetainedGluedNeumannTwoFluxEnergy
      Q j s
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))
      P F background q hs hEllParent hEll hP hF hBackgroundL2 hBackground
      hex hMuResp) (by norm_num)

/-- The dual finite-volume scalar readout in the half-energy normalization
used by the manuscript's variational functional. -/
def oneStepDualFiniteVolumeReadout {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ) (q : Vec d) : ℝ :=
  (1 / 2 : ℝ) * vecDot q (matVecMul
    (abarStarInv M L (Ch02.cubeDomain (originCube d (K : ℤ)))) q)

/-- The finite-volume readout is exactly the expected random starred
quadratic energy. -/
theorem oneStepDualFiniteVolumeReadout_eq_integral {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ) (q : Vec d) :
    oneStepDualFiniteVolumeReadout M L K q =
      ∫ omega : Sample d, (1 / 2 : ℝ) * vecDot q
        (matVecMul ((randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d (K : ℤ))) omega)⁻¹) q)
        ∂M.P.toMeasure := by
  exact (integral_randomAStarMatrix_inv_quadratic M L
    (Ch02.cubeDomain (originCube d (K : ℤ))) q).symm

/-- The annealed dual readout converges to the scalar homogenized reciprocal
quadratic form. -/
theorem tendsto_oneStepDualFiniteVolumeReadout {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (q : Vec d) :
    Tendsto (fun K : ℕ ↦ oneStepDualFiniteVolumeReadout M L K q)
      atTop
      (nhds ((1 / 2 : ℝ) * (ahom M L)⁻¹ * vecNormSq q)) := by
  have hmatrix := tendsto_abarStarInv_originCube M L
  have hcontinuous : Continuous (fun A : Mat d ↦
      (1 / 2 : ℝ) * vecDot q (matVecMul A q)) := by
    unfold vecDot matVecMul
    exact continuous_const.mul
      (continuous_finset_sum _ fun i _ ↦ continuous_const.mul
        (continuous_finset_sum _ fun j _ ↦
          ((continuous_apply j).comp (continuous_apply i)).mul continuous_const))
  have h := hcontinuous.continuousAt.tendsto.comp hmatrix
  have hlimit :
      (1 / 2 : ℝ) * vecDot q
          (matVecMul ((ahom M L)⁻¹ • (1 : Mat d)) q) =
        (1 / 2 : ℝ) * (ahom M L)⁻¹ * vecNormSq q := by
    unfold vecNormSq vecDot matVecMul
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have hquad :
      ∑ i, q i * ∑ j, ((ahom M L)⁻¹ * if i = j then 1 else 0) * q j =
          (ahom M L)⁻¹ * ∑ i, q i * q i := by
      calc
        ∑ i, q i * ∑ j, ((ahom M L)⁻¹ * if i = j then 1 else 0) * q j =
            ∑ i, q i * ((ahom M L)⁻¹ * q i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            congr 1
            rw [Finset.sum_eq_single i]
            · simp
            · intro j _hj hji
              simp [Ne.symm hji]
            · simp
        _ = (ahom M L)⁻¹ * ∑ i, q i * q i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    rw [hquad]
    ring
  simpa only [oneStepDualFiniteVolumeReadout, hlimit] using h

/-- A samplewise upper bound on the random starred energy integrates to an
upper bound on the literal dual finite-volume readout. -/
theorem oneStepDualFiniteVolumeReadout_le_integral_of_ae {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ) (q : Vec d)
    (energy : Sample d → ℝ)
    (henergy : Integrable energy M.P.toMeasure)
    (hle : ∀ᵐ omega ∂M.P.toMeasure,
      (1 / 2 : ℝ) * vecDot q
        (matVecMul ((randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d (K : ℤ))) omega)⁻¹) q) ≤
        energy omega) :
    oneStepDualFiniteVolumeReadout M L K q ≤
      ∫ omega, energy omega ∂M.P.toMeasure := by
  rw [oneStepDualFiniteVolumeReadout_eq_integral]
  apply integral_mono_ae
  · have hmatrix := integrable_randomAStarMatrix_inv M L
      (Ch02.cubeDomain (originCube d (K : ℤ)))
    have hquad : Integrable (fun omega : Sample d ↦ vecDot q
        (matVecMul ((randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d (K : ℤ))) omega)⁻¹) q))
        M.P.toMeasure := by
      unfold vecDot matVecMul
      apply integrable_finset_sum
      intro i _hi
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro j _hj
      exact (((hmatrix.eval i).eval j).mul_const (q j))
    exact hquad.const_mul (1 / 2)
  · exact henergy
  · exact hle

/-- Boundary-discard identification for the dual one-step argument.

Once the finite-volume starred readout is bounded by an interior retained-cell
quantity plus a boundary contribution, the starred characterization turns
the left side into the homogenized reciprocal and the boundary disappears.
No convergence of the retained Hessian observable is asserted or needed. -/
theorem half_ahom_inv_mul_vecNormSq_le_of_dual_boundary_discard {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (q : Vec d)
    (interior boundary : ℕ → ℝ) (interiorInf : ℝ)
    (hinterior : Tendsto interior atTop (nhds interiorInf))
    (hboundary : Tendsto boundary atTop (nhds 0))
    (hle : ∀ K : ℕ,
      oneStepDualFiniteVolumeReadout M L K q ≤
        interior K + boundary K) :
    (1 / 2 : ℝ) * (ahom M L)⁻¹ * vecNormSq q ≤ interiorInf := by
  exact oneStep_limit_le_of_interior_add_boundary
    (tendsto_oneStepDualFiniteVolumeReadout M L q)
    hinterior hboundary hle

/-- Unit-probe form consumed by the scalar lower one-step estimate. -/
theorem half_ahom_inv_le_of_dual_boundary_discard {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (q : Vec d)
    (hq : vecNormSq q = 1)
    (interior boundary : ℕ → ℝ) (interiorInf : ℝ)
    (hinterior : Tendsto interior atTop (nhds interiorInf))
    (hboundary : Tendsto boundary atTop (nhds 0))
    (hle : ∀ K : ℕ,
      oneStepDualFiniteVolumeReadout M L K q ≤
        interior K + boundary K) :
    (1 / 2 : ℝ) * (ahom M L)⁻¹ ≤ interiorInf := by
  simpa only [hq, mul_one] using
    half_ahom_inv_mul_vecNormSq_le_of_dual_boundary_discard
      M L q interior boundary interiorInf hinterior hboundary hle

/-- Concrete retained-cell boundary-strip specialization.  The boundary
price is a fixed stationary energy budget times the explicit discarded
volume fraction proved in `OneStepRetainedBoundaryGeometry`. -/
theorem half_ahom_inv_le_of_retainedBoundaryFraction {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (q : Vec d)
    (hq : vecNormSq q = 1) (source : ℤ) (N : ℕ) (C : ℝ)
    (interior : ℕ → ℝ) (interiorInf : ℝ)
    (hinterior : Tendsto interior atTop (nhds interiorInf))
    (hle : ∀ K : ℕ,
      oneStepDualFiniteVolumeReadout M L K q ≤ interior K +
        C * oneStepRetainedBoundaryFraction
          (d := d) (K : ℤ) source N) :
    (1 / 2 : ℝ) * (ahom M L)⁻¹ ≤ interiorInf := by
  exact half_ahom_inv_le_of_dual_boundary_discard
    M L q hq interior
    (fun K ↦ C * oneStepRetainedBoundaryFraction
      (d := d) (K : ℤ) source N)
    interiorInf hinterior
    (tendsto_const_mul_oneStepRetainedBoundaryFraction_zero
      (d := d) source N C) hle

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
