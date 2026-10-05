module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.FullFamilyAverage
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.PaperPrincipalMajorant
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.CellEnergySplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteMajorantAssembly

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

variable {d : ℕ}

/-! ## Reducing inverse-star pairings to gradient pairings -/

/-- The inverse-star pairing of two cell minimizers' fluxes is the coefficient
pairing of their potential gradients. -/
theorem vecDot_flux_lowerRight_flux_eq_gradientPairing
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : Sample d)
    {R : TriadicCube d} {G G' : Vec d → Vec d}
    (X : OneStepNeumannCellMinimizer R
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) G)
    (Y : OneStepNeumannCellMinimizer R
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) G')
    (x : Vec d) :
    vecDot (X.flux x)
        (matVecMul ((blockMatrixOfCoeff
          (scalarCoeffField
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)).lowerRight)
          (Y.flux x)) =
      vecDot (X.potential.toH1Function.grad x)
        (matVecMul
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)
          (Y.potential.toH1Function.grad x)) := by
  have hdet : IsUnit
      (scalarCoeffField
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x).det :=
    isUnit_det_of_isEllipticMatrix
      (isEllipticMatrix_scalarMatrix
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x))
  have haSymm : symmPart
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x) =
        scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x := by
    simp only [scalarCoeffField,
      Homogenization.Book.Ch02.symmPart_scalarMatrix]
  unfold OneStepNeumannCellMinimizer.flux blockMatrixOfCoeff
  dsimp only
  rw [haSymm, matVecMul_mul,
    Matrix.nonsing_inv_mul _ hdet, matVecMul_one]
  simp only [scalarCoeffField, matVecMul_scalarMatrix,
    Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_right]

/-- Integrability of an inverse-star pairing of two cell minimizers'
fluxes. -/
theorem integrableOn_flux_lowerRight_flux
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : Sample d)
    {R : TriadicCube d} {G G' : Vec d → Vec d}
    (X : OneStepNeumannCellMinimizer R
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) G)
    (Y : OneStepNeumannCellMinimizer R
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) G')
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))) :
    IntegrableOn (fun x ↦ vecDot (X.flux x)
        (matVecMul ((blockMatrixOfCoeff
          (scalarCoeffField
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)).lowerRight)
          (Y.flux x))) (openCubeSet R) := by
  have hrewrite : (fun x ↦ vecDot (X.flux x)
        (matVecMul ((blockMatrixOfCoeff
          (scalarCoeffField
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)).lowerRight)
          (Y.flux x))) =
      fun x ↦ vecDot (X.potential.toH1Function.grad x)
        (matVecMul
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)
          (Y.potential.toH1Function.grad x)) :=
    funext fun x ↦ vecDot_flux_lowerRight_flux_eq_gradientPairing M L omega X Y x
  rw [hrewrite]
  exact integrableOn_vecDot_of_memVectorL2
    X.potential.toH1Function.grad_memVectorL2
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      Y.potential.toH1Function.grad_memVectorL2)

/-! ## Assembling parent integrability from the cells -/

/-- A function integrable on every cell of a full descendant family is
integrable on the parent: the closed cells cover the closed parent cube
exactly. -/
theorem integrableOn_openCubeSet_of_forall_descendantsAtDepth
    (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ)
    (hf : ∀ R ∈ descendantsAtDepth Q j, IntegrableOn f (openCubeSet R)) :
    IntegrableOn f (openCubeSet Q) := by
  have hcell : ∀ R ∈ descendantsAtDepth Q j, IntegrableOn f (cubeSet R) := by
    intro R hR
    simpa only [IntegrableOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hf R hR
  have hunion : IntegrableOn f
      (⋃ R ∈ (descendantsAtDepth Q j : Set (TriadicCube d)), cubeSet R) :=
    integrableOn_finset_iUnion.2 hcell
  have hQ : IntegrableOn f (cubeSet Q) := by
    rwa [cubeSet_eq_iUnion_descendantsAtDepth Q j]
  simpa only [IntegrableOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hQ

/-- Scalars pull out of a volume average. -/
theorem volumeAverage_const_mul (U : Set (Vec d)) (c : ℝ) (f : Vec d → ℝ) :
    volumeAverage U (fun x ↦ c * f x) = c * volumeAverage U f := by
  unfold volumeAverage
  rw [integral_const_mul]
  ring

/-! ## The samplewise competitor over the full source-cell family -/

/-- **The samplewise dual competitor.**  For the *whole* descendant family at
depth `j`, the half inverse-star parent readout is dominated by the normalized
cell sum of the manuscript's three-term majorant, with **no** boundary
summand.

The principal and oscillatory cell energies are supplied as hypotheses at
their literal glued-competitor shapes; the mixed term is discharged internally
by Cauchy--Schwarz in the inverse-star metric. -/
theorem half_randomAStarInv_le_normalized_paperMajorantSum
    {j K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : Sample d) (hh : 0 < h)
    {lam Lam : ℝ}
    (hEllParent : IsEllipticFieldOn lam Lam
      (openCubeSet (originCube d (K : ℤ)))
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)))
    (hEll : ∀ S ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      IsEllipticFieldOn lam Lam (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)))
    (principal oscillatory : Homogenization.TriadicCube d → ℝ)
    (hprincipal : ∀ R, ∀ hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot ((oneStepSelectedNeumannCell
              (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega))
              (fun S ↦ oneStepPaperNeumannCellMeanField M n h q
                (originCube d (K : ℤ)) S omega hh) hEll
              (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
                M n h q (originCube d (K : ℤ)) omega hh) R hR).flux x)
            (matVecMul ((blockMatrixOfCoeff
              (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)
                x)).lowerRight)
              ((oneStepSelectedNeumannCell
                (scalarCoeffField
                  (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega))
                (fun S ↦ oneStepPaperNeumannCellMeanField M n h q
                  (originCube d (K : ℤ)) S omega hh) hEll
                (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
                  M n h q (originCube d (K : ℤ)) omega hh) R hR).flux x))) ≤
        principal R)
    (hoscillatory : ∀ R,
      ∀ hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot ((oneStepSelectedNeumannCell
              (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega))
              (fun S ↦ oneStepPaperNeumannCellFluctuationField M n h q
                (originCube d (K : ℤ)) S omega hh) hEll
              (oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
                M n h q (originCube d (K : ℤ)) omega hh) R hR).flux x)
            (matVecMul ((blockMatrixOfCoeff
              (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)
                x)).lowerRight)
              ((oneStepSelectedNeumannCell
                (scalarCoeffField
                  (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega))
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
            (1 / 2 : ℝ) * oscillatory R) := by
  classical
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  set D : Finset (TriadicCube d) := descendantsAtDepth Q j with hD
  set a : CoeffField d :=
    scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega) with ha
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
  -- cellwise minimizers
  set XP : ∀ R ∈ descendantsAtDepth Q j,
      OneStepNeumannCellMinimizer R a (P R) := fun R hR ↦
    oneStepSelectedNeumannCell a P hEll hP R hR with hXP
  set XF : ∀ R ∈ descendantsAtDepth Q j,
      OneStepNeumannCellMinimizer R a (F R) := fun R hR ↦
    oneStepSelectedNeumannCell a F hEll hF R hR with hXF
  -- the glued competitor and its half energy density
  set glued : Vec d → Vec d :=
    oneStepSelectedRetainedGluedNeumannTwoFlux Q j D a P F
      (oneStepPaperNeumannFlux M n h q Q omega hh) hEll hP hF with hglued
  set g : Vec d → ℝ := fun x ↦
    (1 / 2 : ℝ) * vecDot (glued x)
      (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (glued x)) with hg
  -- the background splits on every cell
  have hbackground : ∀ R ∈ D, ∀ x ∈ openCubeSet R,
      oneStepPaperNeumannFlux M n h q Q omega hh x = P R x + F R x := by
    intro R _hR x _hx
    simpa only [hPdef, hFdef] using
      (oneStepPaperNeumannCellMean_add_fluctuation M n h q Q R omega hh x).symm
  -- the three cellwise integrability facts
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
  -- the cellwise split
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
  -- integrability of the parent density
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
  -- the parent competitor
  have hvar := half_randomAStarMatrix_inv_quadratic_le_paperRetainedGluedEnergy
    M n h q Q omega hh D hs hEllParent hEll
  have hvar' : (1 / 2 : ℝ) * vecDot q
      (matVecMul ((randomAStarMatrix M (n + h)
        (Homogenization.Book.Ch02.cubeDomain Q) omega)⁻¹) q) ≤
      volumeAverage (openCubeSet Q) g := by
    rw [hg, hglued, volumeAverage_const_mul]
    exact hvar
  -- raw cell functionals
  set rawP : TriadicCube d → ℝ := fun R ↦
    if hR : R ∈ descendantsAtDepth Q j then
      volumeAverage (openCubeSet R) (fun x ↦
        vecDot ((XP R hR).flux x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
            ((XP R hR).flux x)))
    else 0 with hrawP
  set rawM : TriadicCube d → ℝ := fun R ↦
    if hR : R ∈ descendantsAtDepth Q j then
      volumeAverage (openCubeSet R) (fun x ↦
        vecDot ((XP R hR).flux x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
            ((XF R hR).flux x)))
    else 0 with hrawM
  set rawO : TriadicCube d → ℝ := fun R ↦
    if hR : R ∈ descendantsAtDepth Q j then
      volumeAverage (openCubeSet R) (fun x ↦
        vecDot ((XF R hR).flux x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
            ((XF R hR).flux x)))
    else 0 with hrawO
  -- positivity of the diagonal energies
  have hquad0 : ∀ (R : TriadicCube d) (x : Vec d) (w : Vec d),
      0 ≤ vecDot w (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) w) := by
    intro R x w
    have hx : IsEllipticMatrix
        (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x)
        (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x) (a x) := by
      simpa only [ha, scalarCoeffField] using
        isEllipticMatrix_scalarMatrix
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (n + h) omega x)
    simpa only [blockMatrixOfCoeff] using
      symmPart_inv_nonneg_of_isEllipticMatrix hx w
  have hrawP0 : ∀ R ∈ D, 0 ≤ rawP R := by
    intro R hR
    rw [hrawP]
    simp only [dite_eq_left (hs hR)]
    exact volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
      (fun x _hx ↦ hquad0 R x _)
  have hrawO0 : ∀ R ∈ D, 0 ≤ rawO R := by
    intro R hR
    rw [hrawO]
    simp only [dite_eq_left (hs hR)]
    exact volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
      (fun x _hx ↦ hquad0 R x _)
  -- Cauchy--Schwarz for the mixed term
  have hmixed : ∀ R ∈ D,
      |rawM R| ≤ Real.sqrt (rawP R) * Real.sqrt (rawO R) := by
    intro R hR
    rw [hrawM, hrawP, hrawO]
    simp only [dite_eq_left (hs hR)]
    let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
      isFiniteMeasure_volumeMeasureOn_openCubeSet R
    refine abs_volumeAverage_vecDot_matVecMul_le_sqrt_mul_sqrt
      (openCubeSet R) (fun x ↦ (blockMatrixOfCoeff (a x)).lowerRight)
      (fun x ↦ (XP R (hs hR)).flux x) (fun x ↦ (XF R (hs hR)).flux x)
      (fun x ↦ ?_) (fun x w ↦ hquad0 R x w)
      (hPPint R (hs hR)) (hFFint R (hs hR)) (hPFint R (hs hR))
    exact Matrix.IsSymm.ext fun i j ↦ by
      have := blockMatrixOfCoeff_lowerRight_isSymm (a x)
      exact congrFun (congrFun this i) j
  -- the abstract fold
  have hvariational :
      (1 / 2 : ℝ) * (vecDot q
        (matVecMul ((randomAStarMatrix M (n + h)
          (Homogenization.Book.Ch02.cubeDomain Q) omega)⁻¹) q)) ≤
      ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
        ((1 / 2 : ℝ) * rawP R + rawM R + (1 / 2 : ℝ) * rawO R) := by
    refine hvar'.trans ?_
    rw [volumeAverage_eq_normalized_descendantsAtDepth_sum Q j hgInt]
    refine le_of_eq ?_
    rw [← hD]
    refine congrArg (fun z ↦ ((D.card : ℝ)⁻¹) * z) ?_
    refine Finset.sum_congr rfl fun R hR ↦ ?_
    rw [hsplit R hR, hrawP, hrawM, hrawO]
    simp only [dite_eq_left (hs hR)]
  have hfold := half_target_le_normalized_finset_majorants_of_raw
    D (vecDot q (matVecMul ((randomAStarMatrix M (n + h)
      (Homogenization.Book.Ch02.cubeDomain Q) omega)⁻¹) q))
    rawP rawM rawO principal oscillatory hrawP0 hrawO0
    (fun R hR ↦ by
      rw [hrawP]; simp only [dite_eq_left (hs hR)]; exact hprincipal R (hs hR))
    (fun R hR ↦ by
      rw [hrawO]; simp only [dite_eq_left (hs hR)]; exact hoscillatory R (hs hR))
    hmixed hvariational
  simpa only [hD, hQ] using hfold

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
