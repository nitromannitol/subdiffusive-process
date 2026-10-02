import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.SuccParentCell

/-!
# The competitor over a covered subfamily, with the boundary layer explicit

`Competitor.lean` produces the dual competitor when the oscillatory envelope
dominates the cell energy on **every** source cell.  The `delta ^ 30` envelope
of conjunct 4 (`exists_oneStepDualOscillatory_innerHalf_sourceCells_budget`,
`Section5FiniteFold/InnerHalfDualSourceOscillatory.lean`) is instead the
zero-extension of a family indexed by the source cells inside *retained*
overlap centres (`overlapCentersAtDepth` is a `filter` by
`overlapCubeSet S ⊆ cubeSet Q`), so it vanishes on a boundary layer of cells.

This module supplies the matching competitor.  The gluing family is still the
**whole** source-cell family — so the exact partition identity
`volumeAverage_eq_normalized_descendantsAtDepth_sum` still applies and no
Lebesgue-null strip appears — but oscillatory domination is required only on a
subfamily `covered`, and the uncovered cells contribute their own glued
half-energy `paperGluedCellHalfEnergy` as an explicit additive term.

Writing the boundary layer this way, rather than as an ambient-flux strip
integral, has one concrete advantage: every *integrability* obligation is
discharged here, so the only residual is the **expectation** bound on the
layer (`provider-45` §A5.2).
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}



theorem half_raw_le_half_majorants
    {rawP rawM rawO P O : ℝ}
    (hP : rawP ≤ P) (hO : rawO ≤ O)
    (hM : |rawM| ≤ Real.sqrt rawP * Real.sqrt rawO) :
    (1 / 2 : ℝ) * rawP + rawM + (1 / 2 : ℝ) * rawO ≤
      (1 / 2 : ℝ) * P + Real.sqrt P * Real.sqrt O + (1 / 2 : ℝ) * O := by
  have hsqrtP : Real.sqrt rawP ≤ Real.sqrt P := Real.sqrt_le_sqrt hP
  have hsqrtO : Real.sqrt rawO ≤ Real.sqrt O := Real.sqrt_le_sqrt hO
  have hproduct : Real.sqrt rawP * Real.sqrt rawO ≤
      Real.sqrt P * Real.sqrt O :=
    mul_le_mul hsqrtP hsqrtO (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hM' : rawM ≤ Real.sqrt P * Real.sqrt O :=
    (le_abs_self _).trans (hM.trans hproduct)
  linarith

/-- The half energy of the full-family glued dual competitor, averaged on one
cell.  The cellwise three-term split decomposes exactly this quantity, so it
is the natural carrier of the discarded boundary layer. -/
def paperGluedCellHalfEnergy {j K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : Sample d) (hh : 0 < h)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      IsEllipticFieldOn lam Lam (openCubeSet S)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega)))
    (R : Homogenization.TriadicCube d) : ℝ :=
  volumeAverage (openCubeSet R) (fun x ↦
    (1 / 2 : ℝ) * vecDot
      (oneStepSelectedRetainedGluedNeumannTwoFlux
        (originCube d (K : ℤ)) j
        (descendantsAtDepth (originCube d (K : ℤ)) j)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
        (fun S ↦ oneStepPaperNeumannCellMeanField M n h q
          (originCube d (K : ℤ)) S omega hh)
        (fun S ↦ oneStepPaperNeumannCellFluctuationField M n h q
          (originCube d (K : ℤ)) S omega hh)
        (oneStepPaperNeumannFlux M n h q (originCube d (K : ℤ)) omega hh)
        hEll
        (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
          M n h q (originCube d (K : ℤ)) omega hh)
        (oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
          M n h q (originCube d (K : ℤ)) omega hh) x)
      (matVecMul ((blockMatrixOfCoeff
        (scalarCoeffField
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega) x)).lowerRight)
        (oneStepSelectedRetainedGluedNeumannTwoFlux
          (originCube d (K : ℤ)) j
          (descendantsAtDepth (originCube d (K : ℤ)) j)
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
          (fun S ↦ oneStepPaperNeumannCellMeanField M n h q
            (originCube d (K : ℤ)) S omega hh)
          (fun S ↦ oneStepPaperNeumannCellFluctuationField M n h q
            (originCube d (K : ℤ)) S omega hh)
          (oneStepPaperNeumannFlux M n h q (originCube d (K : ℤ)) omega hh)
          hEll
          (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
            M n h q (originCube d (K : ℤ)) omega hh)
          (oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
            M n h q (originCube d (K : ℤ)) omega hh) x)))

/-- The cell half-energy is nonnegative. -/
theorem paperGluedCellHalfEnergy_nonneg {j K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : Sample d) (hh : 0 < h)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      IsEllipticFieldOn lam Lam (openCubeSet S)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega)))
    (R : Homogenization.TriadicCube d) :
    0 ≤ paperGluedCellHalfEnergy M n h q omega hh hEll R := by
  refine volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
    (fun x _hx ↦ ?_)
  have hx : IsEllipticMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega x)
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega x)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega) x) := by
    simpa only [scalarCoeffField] using
      isEllipticMatrix_scalarMatrix
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M (n + h) omega x)
  refine mul_nonneg (by norm_num) ?_
  simpa only [blockMatrixOfCoeff] using
    symmPart_inv_nonneg_of_isEllipticMatrix hx _

/-- **The covered-subfamily dual competitor.**  Oscillatory domination is
needed only on `covered`; the remaining cells contribute their glued
half-energy additively. -/
theorem half_randomAStarInv_le_normalized_paperMajorantSum_of_covered
    {j K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : Sample d) (hh : 0 < h)
    {lam Lam : ℝ}
    (hEllParent : IsEllipticFieldOn lam Lam
      (openCubeSet (originCube d (K : ℤ)))
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega)))
    (hEll : ∀ S ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      IsEllipticFieldOn lam Lam (openCubeSet S)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega)))
    (covered : Finset (Homogenization.TriadicCube d))
    (principal oscillatory : Homogenization.TriadicCube d → ℝ)
    (hprincipal0 : ∀ R, 0 ≤ principal R)
    (hoscillatory0 : ∀ R, 0 ≤ oscillatory R)
    (hprincipal : ∀ R, ∀ hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot ((oneStepSelectedNeumannCell
              (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
              (fun S ↦ oneStepPaperNeumannCellMeanField M n h q
                (originCube d (K : ℤ)) S omega hh) hEll
              (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
                M n h q (originCube d (K : ℤ)) omega hh) R hR).flux x)
            (matVecMul ((blockMatrixOfCoeff
              (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega)
                x)).lowerRight)
              ((oneStepSelectedNeumannCell
                (scalarCoeffField
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
                (fun S ↦ oneStepPaperNeumannCellMeanField M n h q
                  (originCube d (K : ℤ)) S omega hh) hEll
                (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
                  M n h q (originCube d (K : ℤ)) omega hh) R hR).flux x))) ≤
        principal R)
    (hoscillatory : ∀ R ∈ covered,
      ∀ hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot ((oneStepSelectedNeumannCell
              (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
              (fun S ↦ oneStepPaperNeumannCellFluctuationField M n h q
                (originCube d (K : ℤ)) S omega hh) hEll
              (oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
                M n h q (originCube d (K : ℤ)) omega hh) R hR).flux x)
            (matVecMul ((blockMatrixOfCoeff
              (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega)
                x)).lowerRight)
              ((oneStepSelectedNeumannCell
                (scalarCoeffField
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
                (fun S ↦ oneStepPaperNeumannCellFluctuationField M n h q
                  (originCube d (K : ℤ)) S omega hh) hEll
                (oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
                  M n h q (originCube d (K : ℤ)) omega hh) R hR).flux x))) ≤
        oscillatory R) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul ((randomAStarMatrix M (n + h)
          (Homogenization.Book.Ch02.cubeDomain
            (originCube d (K : ℤ))) omega)⁻¹) q) ≤
      (((descendantsAtDepth (originCube d (K : ℤ)) j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
          ((1 / 2 : ℝ) * principal R +
            Real.sqrt (principal R) * Real.sqrt (oscillatory R) +
            (1 / 2 : ℝ) * oscillatory R) +
      (((descendantsAtDepth (originCube d (K : ℤ)) j).card : ℝ)⁻¹) *
        ∑ R ∈ (descendantsAtDepth (originCube d (K : ℤ)) j) \ covered,
          paperGluedCellHalfEnergy M n h q omega hh hEll R := by
  classical
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  set D : Finset (TriadicCube d) := descendantsAtDepth Q j with hD
  set a : CoeffField d :=
    scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega) with ha
  set P : TriadicCube d → Vec d → Vec d := fun S ↦
    oneStepPaperNeumannCellMeanField M n h q Q S omega hh with hPdef
  set F : TriadicCube d → Vec d → Vec d := fun S ↦
    oneStepPaperNeumannCellFluctuationField M n h q Q S omega hh with hFdef
  have hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S) :=
    oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
      M n h q Q omega hh
  have hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S) :=
    oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
      M n h q Q omega hh
  have hs : D ⊆ descendantsAtDepth Q j := fun R hR ↦ hR
  set XP : ∀ R ∈ descendantsAtDepth Q j,
      OneStepNeumannCellMinimizer R a (P R) := fun R hR ↦
    oneStepSelectedNeumannCell a P hEll hP R hR with hXP
  set XF : ∀ R ∈ descendantsAtDepth Q j,
      OneStepNeumannCellMinimizer R a (F R) := fun R hR ↦
    oneStepSelectedNeumannCell a F hEll hF R hR with hXF
  set glued : Vec d → Vec d :=
    oneStepSelectedRetainedGluedNeumannTwoFlux Q j D a P F
      (oneStepPaperNeumannFlux M n h q Q omega hh) hEll hP hF with hglued
  set g : Vec d → ℝ := fun x ↦
    (1 / 2 : ℝ) * vecDot (glued x)
      (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (glued x)) with hg
  have hbackground : ∀ R ∈ D, ∀ x ∈ openCubeSet R,
      oneStepPaperNeumannFlux M n h q Q omega hh x = P R x + F R x := by
    intro R _hR x _hx
    simpa only [hPdef, hFdef] using
      (oneStepPaperNeumannCellMean_add_fluctuation M n h q Q R omega hh x).symm
  have hPPint : ∀ (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j),
      IntegrableOn (fun x ↦ vecDot ((XP R hR).flux x)
        (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
          ((XP R hR).flux x))) (openCubeSet R) := fun R hR ↦
    integrableOn_flux_lowerRight_flux M (n + h) omega
      (XP R hR) (XP R hR) (hEll R hR)
  have hPFint : ∀ (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j),
      IntegrableOn (fun x ↦ vecDot ((XP R hR).flux x)
        (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
          ((XF R hR).flux x))) (openCubeSet R) := fun R hR ↦
    integrableOn_flux_lowerRight_flux M (n + h) omega
      (XP R hR) (XF R hR) (hEll R hR)
  have hFFint : ∀ (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j),
      IntegrableOn (fun x ↦ vecDot ((XF R hR).flux x)
        (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
          ((XF R hR).flux x))) (openCubeSet R) := fun R hR ↦
    integrableOn_flux_lowerRight_flux M (n + h) omega
      (XF R hR) (XF R hR) (hEll R hR)
  have hsplit : ∀ (R : TriadicCube d) (hR : R ∈ D),
      volumeAverage (openCubeSet R) g =
      (1 / 2 : ℝ) * volumeAverage (openCubeSet R) (fun x ↦
          vecDot ((XP R (hs hR)).flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
              ((XP R (hs hR)).flux x))) +
        volumeAverage (openCubeSet R) (fun x ↦
          vecDot ((XP R (hs hR)).flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
              ((XF R (hs hR)).flux x))) +
        (1 / 2 : ℝ) * volumeAverage (openCubeSet R) (fun x ↦
          vecDot ((XF R (hs hR)).flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
              ((XF R (hs hR)).flux x))) := by
    intro R hR
    have hbase := volumeAverage_half_gluedNeumannTwoFlux_energy_eq
      (Q := Q) (R := R) (j := j) (s := D) a P F
      (oneStepPaperNeumannFlux M n h q Q omega hh) hs hEll hP hF hR
      (hbackground R hR)
      (((hPPint R (hs hR)).const_mul (1 / 2 : ℝ)))
      (hPFint R (hs hR))
      (((hFFint R (hs hR)).const_mul (1 / 2 : ℝ)))
    rw [hg, hglued]
    rw [hbase, volumeAverage_const_mul, volumeAverage_const_mul]
  have hgcell : ∀ R ∈ descendantsAtDepth Q j,
      IntegrableOn g (openCubeSet R) := by
    intro R hR
    have hcong : ∀ x ∈ openCubeSet R, g x =
        (1 / 2 : ℝ) * vecDot ((XP R hR).flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
              ((XP R hR).flux x)) +
          vecDot ((XP R hR).flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
              ((XF R hR).flux x)) +
          (1 / 2 : ℝ) * vecDot ((XF R hR).flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
              ((XF R hR).flux x)) := by
      intro x hx
      simpa only [hg, hglued, hXP, hXF] using
        oneStepSelectedRetainedGluedNeumannTwoFlux_half_energy_eq_of_mem
          (Q := Q) (R := R) (j := j) (s := D) a P F
          (oneStepPaperNeumannFlux M n h q Q omega hh) hs hEll hP hF hR hx
          (hbackground R hR x hx)
    refine IntegrableOn.congr_fun ?_ (fun x hx ↦ (hcong x hx).symm)
      (measurableSet_openCubeSet R)
    exact (((hPPint R hR).const_mul (1 / 2 : ℝ)).add (hPFint R hR)).add
      ((hFFint R hR).const_mul (1 / 2 : ℝ))
  have hgInt : IntegrableOn g (openCubeSet Q) :=
    integrableOn_openCubeSet_of_forall_descendantsAtDepth Q j g hgcell
  have hvar := half_randomAStarMatrix_inv_quadratic_le_paperRetainedGluedEnergy
    M n h q Q omega hh D hs hEllParent hEll
  have hvar' : (1 / 2 : ℝ) * vecDot q
      (matVecMul ((randomAStarMatrix M (n + h)
        (Homogenization.Book.Ch02.cubeDomain Q) omega)⁻¹) q) ≤
      volumeAverage (openCubeSet Q) g := by
    rw [hg, hglued, volumeAverage_const_mul]
    exact hvar
  have hquad0 : ∀ (x : Vec d) (w : Vec d),
      0 ≤ vecDot w (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) w) := by
    intro x w
    have hx : IsEllipticMatrix
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega x)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega x) (a x) := by
      simpa only [ha, scalarCoeffField] using
        isEllipticMatrix_scalarMatrix
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M (n + h) omega x)
    simpa only [blockMatrixOfCoeff] using
      symmPart_inv_nonneg_of_isEllipticMatrix hx w
  -- the cellwise comparison
  have hcell : ∀ R ∈ D, volumeAverage (openCubeSet R) g ≤
      ((1 / 2 : ℝ) * principal R +
        Real.sqrt (principal R) * Real.sqrt (oscillatory R) +
        (1 / 2 : ℝ) * oscillatory R) +
      (if R ∈ covered then 0 else volumeAverage (openCubeSet R) g) := by
    intro R hR
    have hmaj0 : 0 ≤ (1 / 2 : ℝ) * principal R +
        Real.sqrt (principal R) * Real.sqrt (oscillatory R) +
        (1 / 2 : ℝ) * oscillatory R := by
      have h1 := hprincipal0 R
      have h2 := hoscillatory0 R
      have h3 : 0 ≤ Real.sqrt (principal R) * Real.sqrt (oscillatory R) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      linarith
    by_cases hcov : R ∈ covered
    · rw [if_pos hcov, add_zero, hsplit R hR]
      letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
        isFiniteMeasure_volumeMeasureOn_openCubeSet R
      refine half_raw_le_half_majorants (hprincipal R (hs hR))
        (hoscillatory R hcov (hs hR)) ?_
      refine abs_volumeAverage_vecDot_matVecMul_le_sqrt_mul_sqrt
        (openCubeSet R) (fun x ↦ (blockMatrixOfCoeff (a x)).lowerRight)
        (fun x ↦ (XP R (hs hR)).flux x) (fun x ↦ (XF R (hs hR)).flux x)
        (fun x ↦ ?_) (fun x w ↦ hquad0 x w)
        (hPPint R (hs hR)) (hFFint R (hs hR)) (hPFint R (hs hR))
      exact Matrix.IsSymm.ext fun i₀ j₀ ↦ by
        have := blockMatrixOfCoeff_lowerRight_isSymm (a x)
        exact congrFun (congrFun this i₀) j₀
    · rw [if_neg hcov]
      linarith
  -- assemble
  have hsum : ∑ R ∈ D, volumeAverage (openCubeSet R) g ≤
      (∑ R ∈ D, ((1 / 2 : ℝ) * principal R +
        Real.sqrt (principal R) * Real.sqrt (oscillatory R) +
        (1 / 2 : ℝ) * oscillatory R)) +
      ∑ R ∈ D \ covered, volumeAverage (openCubeSet R) g := by
    have hstep := Finset.sum_le_sum hcell
    rw [Finset.sum_add_distrib] at hstep
    refine hstep.trans_eq ?_
    congr 1
    rw [Finset.sdiff_eq_filter]
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun R _hR ↦ by
      by_cases hcov : R ∈ covered <;> simp [hcov]
  have hcard0 : (0 : ℝ) ≤ ((D.card : ℝ))⁻¹ := by positivity
  have hfinal := mul_le_mul_of_nonneg_left hsum hcard0
  rw [mul_add] at hfinal
  have hstart : (1 / 2 : ℝ) * vecDot q
      (matVecMul ((randomAStarMatrix M (n + h)
        (Homogenization.Book.Ch02.cubeDomain Q) omega)⁻¹) q) ≤
      ((D.card : ℝ))⁻¹ * ∑ R ∈ D, volumeAverage (openCubeSet R) g := by
    refine hvar'.trans_eq ?_
    rw [volumeAverage_eq_normalized_descendantsAtDepth_sum Q j hgInt, ← hD]
  have hboundary : ∑ R ∈ D \ covered, volumeAverage (openCubeSet R) g =
      ∑ R ∈ D \ covered,
        paperGluedCellHalfEnergy M n h q omega hh hEll R := by
    exact Finset.sum_congr rfl fun R _hR ↦ rfl
  rw [hboundary] at hfinal
  simpa only [hD, hQ] using hstart.trans hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
