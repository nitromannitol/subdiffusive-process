import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.GluedCellSplit




open MeasureTheory Homogenization Homogenization.Book Filter
open scoped BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-! ## A canonical parent ellipticity witness -/

/-- Pointwise ellipticity constants for one cutoff on a whole cube, together
with the constants themselves.  Unlike `OneStepDescendantEllipticityData` this
carries the **parent** bound, which the dual gluing carrier needs with the
*same* constants as the cell bounds. -/
structure DualParentEllipticityData {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) where
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  isElliptic : IsEllipticFieldOn lam Lam (openCubeSet Q)
    (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega))

/-- The canonical parent ellipticity witness, obtained from the depth-zero
instance of `exists_isEllipticFieldOn_aCutoff_descendants`. -/
def dualParentEllipticityData {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) :
    DualParentEllipticityData M L omega Q :=
  Classical.choice <| by
    obtain ⟨lam, Lam, hlam, hEll⟩ :=
      exists_isEllipticFieldOn_aCutoff_descendants (j := 0) M L omega Q
    exact ⟨⟨lam, Lam, hlam, hEll Q (by simp)⟩⟩

/-- Every descendant inherits the parent's ellipticity constants. -/
theorem dualParentEllipticityData_descendants {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) (j : ℕ) :
    ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn (dualParentEllipticityData M L omega Q).lam
        (dualParentEllipticityData M L omega Q).Lam (openCubeSet R)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) :=
  fun R hR ↦ (dualParentEllipticityData M L omega Q).isElliptic.mono
    (measurableSet_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hR)

/-! ## The literal oscillatory cell energy of the dual competitor -/

/-- The oscillatory cell energy that the glued dual competitor actually
produces on a source cell: the inverse-star energy, at the high cutoff, of the
selected Neumann cell minimizer with the manuscript flux's cell fluctuation as
datum. -/
def dualPaperRawOscillatory {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (R : Homogenization.TriadicCube d)
    (omega : Sample d) (hh : 0 < h) : ℝ :=
  if hR : R ∈ oneStepSourceCells d K n M.delta then
    volumeAverage (openCubeSet R) (fun x ↦
      vecDot ((oneStepSelectedNeumannCell
          (scalarCoeffField
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
          (fun S ↦ oneStepPaperNeumannCellFluctuationField M n h q
            (originCube d (K : ℤ)) S omega hh)
          (dualParentEllipticityData_descendants M (n + h) omega
            (originCube d (K : ℤ)) (K - oneStepLocalizationScale n M.delta))
          (oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
            M n h q (originCube d (K : ℤ)) omega hh) R
          (mem_oneStepSourceCells hR)).flux x)
        (matVecMul ((blockMatrixOfCoeff
          (scalarCoeffField
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega) x)).lowerRight)
          ((oneStepSelectedNeumannCell
            (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
            (fun S ↦ oneStepPaperNeumannCellFluctuationField M n h q
              (originCube d (K : ℤ)) S omega hh)
            (dualParentEllipticityData_descendants M (n + h) omega
              (originCube d (K : ℤ)) (K - oneStepLocalizationScale n M.delta))
            (oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
              M n h q (originCube d (K : ℤ)) omega hh) R
            (mem_oneStepSourceCells hR)).flux x)))
  else 0

/-- The oscillatory cell energy is nonnegative. -/
theorem dualPaperRawOscillatory_nonneg {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (R : Homogenization.TriadicCube d)
    (omega : Sample d) (hh : 0 < h) :
    0 ≤ dualPaperRawOscillatory (K := K) M n h q R omega hh := by
  unfold dualPaperRawOscillatory
  split
  · refine volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
      (fun x _hx ↦ ?_)
    have hx : IsEllipticMatrix
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega x)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega x)
        (scalarCoeffField
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega) x) := by
      simpa only [scalarCoeffField] using
        isEllipticMatrix_scalarMatrix
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M (n + h) omega x)
    simpa only [blockMatrixOfCoeff] using
      symmPart_inv_nonneg_of_isEllipticMatrix hx _
  · exact le_rfl

/-! ## The samplewise and almost-sure competitor -/

/-- **The samplewise dual competitor over the source cells.**  Manuscript-sign
mirror of `ae_half_randomAMatrix_le_oneStepPrimalMajorants`, with no boundary
summand. -/
theorem half_randomAStarInv_le_oneStepDualPaperMajorants
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : Sample d) (hh : 0 < h)
    (oscillatory : Homogenization.TriadicCube d → ℝ)
    (hosc : ∀ R ∈ oneStepSourceCells d K n M.delta,
      dualPaperRawOscillatory (K := K) M n h q R omega hh ≤ oscillatory R) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul ((randomAStarMatrix M (n + h)
          (Homogenization.Book.Ch02.cubeDomain
            (originCube d (K : ℤ))) omega)⁻¹) q) ≤
      (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ((1 / 2 : ℝ) *
              oneStepDualPrincipalMajorant (K := K) M n h q R omega hh +
            Real.sqrt (oneStepDualPrincipalMajorant
              (K := K) M n h q R omega hh) *
              Real.sqrt (oscillatory R) +
            (1 / 2 : ℝ) * oscillatory R) := by
  classical
  refine half_randomAStarInv_le_normalized_paperMajorantSum
    (j := K - oneStepLocalizationScale n M.delta) M n h q omega hh
    (dualParentEllipticityData M (n + h) omega (originCube d (K : ℤ))).isElliptic
    (dualParentEllipticityData_descendants M (n + h) omega
      (originCube d (K : ℤ)) (K - oneStepLocalizationScale n M.delta))
    (fun R ↦ oneStepDualPrincipalMajorant (K := K) M n h q R omega hh)
    oscillatory ?_ ?_
  · intro R hR
    exact volumeAverage_paperPrincipalCell_energy_le_majorant
      (j := K - oneStepLocalizationScale n M.delta) M n h q R omega hh
      (dualParentEllipticityData_descendants M n omega
        (originCube d (K : ℤ)) (K - oneStepLocalizationScale n M.delta))
      (dualParentEllipticityData_descendants M (n + h) omega
        (originCube d (K : ℤ)) (K - oneStepLocalizationScale n M.delta)) hR
  · intro R hR
    have hRsrc : R ∈ oneStepSourceCells d K n M.delta := hR
    have hthis := hosc R hRsrc
    unfold dualPaperRawOscillatory at hthis
    rw [dif_pos hRsrc] at hthis
    exact hthis



theorem ae_half_randomAStarInv_le_oneStepDualPaperMajorants
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (hh : 0 < h)
    (oscillatory : Homogenization.TriadicCube d → Sample d → ℝ)
    (hosc : ∀ᵐ omega ∂M.P.toMeasure,
      ∀ R ∈ oneStepSourceCells d K n M.delta,
        dualPaperRawOscillatory (K := K) M n h q R omega hh ≤
          oscillatory R omega) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (1 / 2 : ℝ) * vecDot q
          (matVecMul ((randomAStarMatrix M (n + h)
            (Homogenization.Book.Ch02.cubeDomain
              (originCube d (K : ℤ))) omega)⁻¹) q) ≤
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ((1 / 2 : ℝ) *
                oneStepDualPrincipalMajorant
                  (K := K) M n h q R omega hh +
              Real.sqrt (oneStepDualPrincipalMajorant
                (K := K) M n h q R omega hh) *
                Real.sqrt (oscillatory R omega) +
              (1 / 2 : ℝ) * oscillatory R omega) + 0 := by
  filter_upwards [hosc] with omega homega
  simpa only [add_zero] using
    half_randomAStarInv_le_oneStepDualPaperMajorants M n h q omega hh
      (fun R ↦ oscillatory R omega) homega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
