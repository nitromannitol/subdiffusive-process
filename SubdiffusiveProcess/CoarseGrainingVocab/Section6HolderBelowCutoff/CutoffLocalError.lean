module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalEllipticityControl
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.CutoffPaperError

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Cutoff companion of
`Section6HarmonicApproximation.homogenizationErrorOnCube_aCutoff_le_section6_of_goodEvent`,
with no relation between `L` and `m`. -/
theorem homogenizationErrorOnCube_aCutoff_le_section6_of_cutoffGoodEvent
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2) (L m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (hgood : omega ∈ goodEvent M (some L) m z 1 s) :
    Ch02.HomogenizationErrorOnCube (originCube d (m : ℤ)) s
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (scalarMatrix (d := d)
          (tailCoefficientCubeAverage M L m (translatePotentialSample z omega))) ≤
      section6HomogenizationError M s L m omega z := by
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  have hsigma : 0 < tailCoefficientCubeAverage M L m
      (translatePotentialSample z omega) :=
    tailCoefficientCubeAverage_pos M L m (translatePotentialSample z omega)
  have hraw := ofReal_homogenizationErrorOnCube_infinity_two_le_paper
    (originCube d (m : ℤ))
    (aCutoffFamily M L (translatePotentialSample z omega))
    (fun R => (aCutoffTriadicData M L
      (translatePotentialSample z omega)).onCube R |>.isSymmetric)
    hs0 hsigma
  change ENNReal.ofReal _ ≤ paperHomogenizationError
    (originCube d (m : ℤ)) (m : ℤ) s .infinity (.finite 2)
      (aCutoffFamily M L (translatePotentialSample z omega))
      (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) at hraw
  rw [Section6ThetaLadder.paperHomogenizationError_eq_ofReal_cutoffGoodEvent
    M hsLower hsUpper L m omega z zero_le_one le_rfl hgood] at hraw
  exact (ENNReal.ofReal_le_ofReal_iff
    (ENNReal.toReal_nonneg : 0 ≤ section6HomogenizationError M s L m omega z)).mp hraw

/-- **Cutoff local error transport.**  Companion of
`Section6HarmonicApproximation.localHomogenizationError_two_le_anchor_of_closedContainment`
on the cutoff good event, with the binder `n + 2 ≤ L` deleted. -/
theorem localHomogenizationError_two_le_cutoffAnchor_of_closedContainment
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (y z : Vec d)
    (hcontain : translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
      cubeSet (originCube d ((n : ℤ) + 2)))
    (hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  let P : TriadicCube d := originCube d ((n : ℤ) - 2)
  let K : TriadicCube d := originCube d ((n : ℤ) + 2)
  let w : Vec d := y - z
  let A := aCutoffFamily M L (translatePotentialSample z omega)
  let A' := aCutoffFamily M L (translatePotentialSample y omega)
  let a : CoeffField d :=
    scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega))
  let sigma : ℝ := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hrep : ∀ Q : TriadicCube d, (A.coeffOn Q).toCoeffField = a := by
    intro Q
    rfl
  have hcompact : IsCompact (closure (cubeSet K)) :=
    (isBounded_cubeSet K).isCompact_closure
  have hnonempty : (closure (cubeSet K)).Nonempty :=
    ⟨cubeCenter K, subset_closure (cubeCenter_mem_cubeSet K)⟩
  let a0 := _root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega)
  have ha : Continuous a0 :=
    _root_.SubdiffusiveProcess.Model.continuous_aCutoff M L (translatePotentialSample z omega)
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hnonempty ha.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hnonempty ha.continuousOn
  have hTmeas : MeasurableSet (translateSet w (cubeSet P)) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet P).preimage (measurable_id.sub measurable_const)
  have hEll : IsEllipticFieldOn (a0 xmin) (a0 xmax)
      (translateSet w (cubeSet P)) a := by
    constructor
    · have hmatrix : Continuous fun p : Vec d => scalarCoeffField a0 p :=
        ha.smul continuous_const
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      have hentry : Measurable fun p : Vec d => scalarCoeffField a0 p i j :=
        (continuous_apply j).comp ((continuous_apply i).comp hmatrix) |>.measurable
      exact Measurable.ite hTmeas hentry measurable_const
    · intro p hp
      have hpK : p ∈ closure (cubeSet K) := subset_closure (hcontain hp)
      have hlow : a0 xmin ≤ a0 p := hmin hpK
      have hupp : a0 p ≤ a0 xmax := hmax hpK
      exact (isEllipticMatrix_scalarMatrix
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L (translatePotentialSample z omega) p)).mono
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L
            (translatePotentialSample z omega) xmin) hlow hupp
  have hstab := offGridErrorFunctional_le_slot
    (w := w) (P := P) (K := K) A (scalarMatrix (d := d) sigma)
      hs0 (hs.2.trans (by norm_num)) hrep hEll hcontain
  have hscale : (((K.scale - P.scale).toNat : ℕ) : ℝ) = 4 := by
    change (((((n : ℤ) + 2) - ((n : ℤ) - 2)).toNat : ℕ) : ℝ) = 4
    rw [show ((n : ℤ) + 2) - ((n : ℤ) - 2) = 4 by ring]
    rfl
  rw [hscale] at hstab
  have hframe := offGridErrorFunctional_eq_homogenizationErrorOnCube_translate
    w P (by linarith only [hs0] : 0 < s / 6) A' a
      (aCutoffFamily_coeffField_translate_sub M L omega y z)
      (scalarMatrix (d := d) sigma)
  have hparent := homogenizationErrorOnCube_aCutoff_le_section6_of_cutoffGoodEvent
    M (s := s / 8) (by linarith only [hs.1]) (by linarith only [hs.2]) L (n + 2)
      omega z hgood
  have hparent' : Ch02.HomogenizationErrorOnCube K (s / 8)
        .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤
      section6HomogenizationError M (s / 8) L (n + 2) omega z := by
    simpa [K, A, sigma,
      Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] using hparent
  rw [← hframe]
  exact hstab.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hparent' (Real.rpow_nonneg (by norm_num) _))
    (Real.sqrt_nonneg _))

/-- The projected-cell variant of the cutoff transport: the comparison cube's
centre ranges over the next truncated window. -/
theorem localHomogenizationError_two_le_cutoffAnchor_nextWindow
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x y z : Vec d)
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hy : y ∈ truncatedCube d m n x)
    (hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  apply localHomogenizationError_two_le_cutoffAnchor_of_closedContainment M hs L n
    omega y z
  · exact closedOffGridCube_subset_originAnchorParent_of_mem_nextWindow hx hy
  · exact hgood

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
