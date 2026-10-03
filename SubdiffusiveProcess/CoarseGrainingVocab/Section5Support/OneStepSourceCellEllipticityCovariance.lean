module

public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRestrictionSymmetry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceEllipticityFactors
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSolutionLawTransport
public import Homogenization.Book.Ch04.Theorems.WidetildeTheta

@[expose] public section

/-!
# Translation covariance of source-cell ellipticity factors

The one-step partition uses arbitrary translated triadic cubes, whereas the
measurable high-cutoff moment representatives live on the centered cube at
the same scale.  This module supplies the deterministic identification.  It
is the arbitrary-scale version of the scale-zero covariance calculation in
`Homogenization.Book.Ch04.Theorems.WidetildeTheta`.
-/

open MeasureTheory Homogenization Homogenization.Book

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


theorem LambdaSqCoeffField_cutoff_eq_family
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Ch04.LambdaSqCoeffField Q (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega) =
      Ch02.LambdaSq Q (1 / 4) (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega) := by
  let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  unfold Ch04.LambdaSqCoeffField
  rw [dif_pos hlocal]
  exact Ch02.LambdaSq_eq_ofAEEq
    (by simpa using aCutoff_canonicalFamily_aeeq M L omega)
    Q (1 / 4) (.finite 1)

theorem lambdaSqCoeffField_cutoff_eq_family
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Ch04.lambdaSqCoeffField Q (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega) =
      Ch02.lambdaSq Q (1 / 4) (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega) := by
  let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  unfold Ch04.lambdaSqCoeffField
  rw [dif_pos hlocal]
  exact Ch02.lambdaSq_eq_ofAEEq
    (by simpa using aCutoff_canonicalFamily_aeeq M L omega)
    Q (1 / 4) (.finite 1)

theorem aux_dedup_d122_cubeSet_translateCube_descendant_eq_translateSet
    {d : ℕ} (m : ℤ) (z : Fin d → ℤ) (n : ℕ)
    {S : TriadicCube d} (hSscale : S.scale = m - (n : ℤ)) :
    cubeSet (translateCube (descendantTranslationShift n z) S) =
      translateSet (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) (cubeSet S) := by
  ext x
  rw [mem_cubeSet_translateCube_iff, mem_translateSet_iff_sub_mem]
  have hvec :
      (fun i ↦ ((descendantTranslationShift n z i : ℤ) : ℝ) *
          cubeScaleFactor S) =
        fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m := by
    funext i
    simp only [descendantTranslationShift, cubeScaleFactor, hSscale]
    push_cast
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    field_simp [pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0)]
  simp only [hvec]

private theorem cubeSet_translateCube_descendant_eq_translateSet
    {d : ℕ} (m : ℤ) (z : Fin d → ℤ) (n : ℕ)
    {S : TriadicCube d} (hSscale : S.scale = m - (n : ℤ)) :
    cubeSet (translateCube (descendantTranslationShift n z) S) =
      translateSet (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) (cubeSet S) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.aux_dedup_d122_cubeSet_translateCube_descendant_eq_translateSet (d := d) (m := m) (z := z) (n := n) (S := S) (hSscale := hSscale)

theorem aux_dedup_d046_coarseBlockMatrix_translateCube_descendant_eq_translateReg
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℤ) (z : Fin d → ℤ)
    (htranslate : Ch04.AELocallyUniformlyEllipticField
      (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a))
    (n : ℕ) {S : TriadicCube d}
    (hS : S ∈ descendantsAtScale (originCube d m) (m - (n : ℤ))) :
    Ch02.coarseBlockMatrix
        (Ch02.cubeDomain (translateCube (descendantTranslationShift n z) S))
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
          (translateCube (descendantTranslationShift n z) S)) =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain S)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a)
            htranslate).coeffOn S) := by
  let T := translateCube (descendantTranslationShift n z) S
  have hSscale : S.scale = m - (n : ℤ) := by
    exact scale_eq_of_mem_descendantsAtScale hS
  have hleft :
      Ch02.coarseBlockMatrix (Ch02.cubeDomain T)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
            ).coeffOn T) =
        coarseBlockMatrix (cubeSet T) a.toFun := by
    simpa only [T] using
      (Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha T).symm
  have hset : cubeSet T =
      translateSet (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) (cubeSet S) := by
    simpa only [T] using
      cubeSet_translateCube_descendant_eq_translateSet m z n hSscale
  have hright :
      coarseBlockMatrix (cubeSet S)
          (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a).toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain S)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
            (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a)
              htranslate).coeffOn S) := by
    simpa using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        htranslate S
  calc
    _ = coarseBlockMatrix (cubeSet T) a.toFun := hleft
    _ = coarseBlockMatrix
        (translateSet (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) (cubeSet S))
        a.toFun := by rw [hset]
    _ = coarseBlockMatrix (cubeSet S)
        (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a).toFun := by
      simpa using! coarseBlockMatrix_translateSet_eq_translateCoeffField
        (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) (cubeSet S) a.toFun
    _ = _ := hright

private theorem coarseBlockMatrix_translateCube_descendant_eq_translateReg
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℤ) (z : Fin d → ℤ)
    (htranslate : Ch04.AELocallyUniformlyEllipticField
      (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a))
    (n : ℕ) {S : TriadicCube d}
    (hS : S ∈ descendantsAtScale (originCube d m) (m - (n : ℤ))) :
    Ch02.coarseBlockMatrix
        (Ch02.cubeDomain (translateCube (descendantTranslationShift n z) S))
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
          (translateCube (descendantTranslationShift n z) S)) =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain S)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a)
            htranslate).coeffOn S) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.aux_dedup_d046_coarseBlockMatrix_translateCube_descendant_eq_translateReg (d := d) (a := a) (ha := ha) (m := m) (z := z) (htranslate := htranslate) (n := n) (S := S) (hS := hS)

theorem aux_dedup_d074_LambdaSqCoeffField_translate_originCube
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℤ) (z : Fin d → ℤ)
    (htranslate : Ch04.AELocallyUniformlyEllipticField
      (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a))
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    Ch04.LambdaSqCoeffField (translateCube z (originCube d m)) s q a =
      Ch04.LambdaSqCoeffField (originCube d m) s q
        (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a) := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a) htranslate
  have hB : ∀ (n : ℕ) (S : TriadicCube d),
      S ∈ descendantsAtScale (originCube d m) (m - (n : ℤ)) →
        Ch02.coarseBMatrixNorm (translateCube (descendantTranslationShift n z) S) F =
          Ch02.coarseBMatrixNorm S G := by
    intro n S hS
    have hmat := coarseBlockMatrix_translateCube_descendant_eq_translateReg
      ha m z htranslate n hS
    have hu := congrArg (fun A : BlockMat d ↦ Ch02.matrixNorm A.upperLeft) hmat
    simpa only [F, G, Ch02.coarseBMatrixNorm] using! hu
  have hcov := Ch02.LambdaSq_translateCube_of_coarseBMatrixNorm
    F G z (originCube d m) s q (by
      intro n S hS
      simpa only [originCube] using hB n S hS)
  unfold Ch04.LambdaSqCoeffField
  rw [dif_pos ha, dif_pos htranslate]
  simpa only [F, G] using hcov

private theorem LambdaSqCoeffField_translate_originCube
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℤ) (z : Fin d → ℤ)
    (htranslate : Ch04.AELocallyUniformlyEllipticField
      (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a))
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    Ch04.LambdaSqCoeffField (translateCube z (originCube d m)) s q a =
      Ch04.LambdaSqCoeffField (originCube d m) s q
        (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.aux_dedup_d074_LambdaSqCoeffField_translate_originCube (d := d) (a := a) (ha := ha) (m := m) (z := z) (htranslate := htranslate) (s := s) (q := q)

theorem aux_dedup_d075_lambdaSqCoeffField_translate_originCube
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℤ) (z : Fin d → ℤ)
    (htranslate : Ch04.AELocallyUniformlyEllipticField
      (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a))
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    Ch04.lambdaSqCoeffField (translateCube z (originCube d m)) s q a =
      Ch04.lambdaSqCoeffField (originCube d m) s q
        (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a) := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a) htranslate
  have hSigma : ∀ (n : ℕ) (S : TriadicCube d),
      S ∈ descendantsAtScale (originCube d m) (m - (n : ℤ)) →
        Ch02.coarseSigmaStarInvMatrixNorm
            (translateCube (descendantTranslationShift n z) S) F =
          Ch02.coarseSigmaStarInvMatrixNorm S G := by
    intro n S hS
    have hmat := coarseBlockMatrix_translateCube_descendant_eq_translateReg
      ha m z htranslate n hS
    have hl := congrArg
      (fun A : BlockMat d ↦ Ch02.matrixNorm A.lowerRight) hmat
    simpa only [F, G, Ch02.coarseSigmaStarInvMatrixNorm] using! hl
  have hcov := Ch02.lambdaSq_translateCube_of_coarseSigmaStarInvMatrixNorm
    F G z (originCube d m) s q (by
      intro n S hS
      simpa only [originCube] using hSigma n S hS)
  unfold Ch04.lambdaSqCoeffField
  rw [dif_pos ha, dif_pos htranslate]
  simpa only [F, G] using hcov

private theorem lambdaSqCoeffField_translate_originCube
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m : ℤ) (z : Fin d → ℤ)
    (htranslate : Ch04.AELocallyUniformlyEllipticField
      (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a))
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    Ch04.lambdaSqCoeffField (translateCube z (originCube d m)) s q a =
      Ch04.lambdaSqCoeffField (originCube d m) s q
        (translateReg (fun i ↦ (z i : ℝ) * (3 : ℝ) ^ m) a) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.aux_dedup_d075_lambdaSqCoeffField_translate_originCube (d := d) (a := a) (ha := ha) (m := m) (z := z) (htranslate := htranslate) (s := s) (q := q)

/-- Literal upper ellipticity on a translated source cell equals the centered
observable evaluated at the translated potential sample. -/
theorem LambdaSqCoeffField_eq_originCube_translatePotentialSequence
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Ch04.LambdaSqCoeffField R (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega) =
      Ch04.LambdaSqCoeffField (originCube d R.scale) (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L
          (translatePotentialSequence (triadicCubeShift R) omega)) := by
  have hR : translateCube R.index (originCube d R.scale) = R := by
    cases R
    simp [translateCube, originCube]
  have hshift : (fun i ↦ (R.index i : ℝ) * (3 : ℝ) ^ R.scale) =
      triadicCubeShift R := by
    funext i
    rfl
  have ha := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  have hat := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L
    (translatePotentialSequence (triadicCubeShift R) omega)
  have h := LambdaSqCoeffField_translate_originCube ha R.scale R.index
    (by simpa only [hshift, ← aCutoffRegCoeffField_translate] using hat)
    (1 / 4) (.finite 1)
  rw [hR, hshift, ← aCutoffRegCoeffField_translate] at h
  exact h

/-- Lower-ellipticity counterpart of
`LambdaSqCoeffField_eq_originCube_translatePotentialSequence`. -/
theorem lambdaSqCoeffField_eq_originCube_translatePotentialSequence
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Ch04.lambdaSqCoeffField R (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega) =
      Ch04.lambdaSqCoeffField (originCube d R.scale) (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L
          (translatePotentialSequence (triadicCubeShift R) omega)) := by
  have hR : translateCube R.index (originCube d R.scale) = R := by
    cases R
    simp [translateCube, originCube]
  have hshift : (fun i ↦ (R.index i : ℝ) * (3 : ℝ) ^ R.scale) =
      triadicCubeShift R := by
    funext i
    rfl
  have ha := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  have hat := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L
    (translatePotentialSequence (triadicCubeShift R) omega)
  have h := lambdaSqCoeffField_translate_originCube ha R.scale R.index
    (by simpa only [hshift, ← aCutoffRegCoeffField_translate] using hat)
    (1 / 4) (.finite 1)
  rw [hR, hshift, ← aCutoffRegCoeffField_translate] at h
  exact h

/-- The exact squared upper Poincaré factor on a translated scale-`m` cell
is almost surely the centered measurable representative evaluated on the
translated sample. -/
theorem oneStepUpperPoincareFactor_cell_ae_eq_measurable_translate
    {d m : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (R : TriadicCube d) (hRm : R.scale = (m : ℤ)) :
    (fun omega ↦
      (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareUpperEllipticityFactor R
          (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4) (.finite 1)) ^ 2)
      =ᵐ[M.P.toMeasure]
    fun omega ↦ oneStepUpperPoincareEnergyFactorMeasurable M L m
      (translatePotentialSequence (triadicCubeShift R) omega) := by
  have hae := (measurePreserving_translatePotentialSequence M
      (triadicCubeShift R)).quasiMeasurePreserving.ae_eq_comp
    (oneStepUpperPoincareEnergyFactorMeasurable_ae_eq M L m)
  filter_upwards [hae] with omega heq
  simp only [Function.comp_apply] at heq
  have hfactor :
      Ch03.poincareUpperEllipticityFactor R
          (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4) (.finite 1) =
        Ch03.poincareUpperEllipticityFactor (originCube d (m : ℤ))
          (aCutoffEnvelopeTriadicCoeffFamily M L
            (translatePotentialSequence (triadicCubeShift R) omega))
          (1 / 4) (.finite 1) := by
    unfold Ch03.poincareUpperEllipticityFactor
    rw [show originCube d (m : ℤ) = originCube d R.scale by rw [hRm]]
    rw [← LambdaSqCoeffField_cutoff_eq_family M L R omega,
      ← LambdaSqCoeffField_cutoff_eq_family M L (originCube d R.scale)
        (translatePotentialSequence (triadicCubeShift R) omega),
      LambdaSqCoeffField_eq_originCube_translatePotentialSequence]
  rw [hfactor]
  exact heq.symm

/-- Reciprocal counterpart of
`oneStepUpperPoincareFactor_cell_ae_eq_measurable_translate`. -/
theorem oneStepLowerPoincareFactor_cell_ae_eq_measurable_translate
    {d m : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (R : TriadicCube d) (hRm : R.scale = (m : ℤ)) :
    (fun omega ↦
      (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor R
          (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4) (.finite 1)) ^ 2)
      =ᵐ[M.P.toMeasure]
    fun omega ↦ oneStepLowerPoincareEnergyFactorMeasurable M L m
      (translatePotentialSequence (triadicCubeShift R) omega) := by
  have hae := (measurePreserving_translatePotentialSequence M
      (triadicCubeShift R)).quasiMeasurePreserving.ae_eq_comp
    (oneStepLowerPoincareEnergyFactorMeasurable_ae_eq M L m)
  filter_upwards [hae] with omega heq
  simp only [Function.comp_apply] at heq
  have hfactor :
      Ch03.poincareLowerEllipticityFactor R
          (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4) (.finite 1) =
        Ch03.poincareLowerEllipticityFactor (originCube d (m : ℤ))
          (aCutoffEnvelopeTriadicCoeffFamily M L
            (translatePotentialSequence (triadicCubeShift R) omega))
          (1 / 4) (.finite 1) := by
    unfold Ch03.poincareLowerEllipticityFactor
    rw [show originCube d (m : ℤ) = originCube d R.scale by rw [hRm]]
    rw [← lambdaSqCoeffField_cutoff_eq_family M L R omega,
      ← lambdaSqCoeffField_cutoff_eq_family M L (originCube d R.scale)
        (translatePotentialSequence (triadicCubeShift R) omega),
      lambdaSqCoeffField_eq_originCube_translatePotentialSequence]
  rw [hfactor]
  exact heq.symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
