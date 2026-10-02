import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.PieceGradientMeasurability
import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders




open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Translation of Hilbert-vector `L²` classes, as a linear isometry. -/
def nfTranslateHilbertVectorL2 (z : Vec d) (U : Set (Vec d)) :
    HilbertVectorL2 U →ₗᵢ[ℝ] HilbertVectorL2 (translateSet z U) :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ (fun x : Vec d => x - z)
    (measurePreserving_subRight_restrict_translateSet z U)

/-- The translation isometry realizes the gradient class of a translated
`H¹` function. -/
theorem nfTranslateHilbertVectorL2_gradToHilbertVectorL2
    (z : Vec d) {U : Set (Vec d)} (u : H1Function U) :
    (u.translate z).gradToHilbertVectorL2 =
      nfTranslateHilbertVectorL2 z U u.gradToHilbertVectorL2 := by
  have hmp := measurePreserving_subRight_restrict_translateSet z U
  have hae := hmp.quasiMeasurePreserving.ae u.coeFn_gradToHilbertVectorL2
  apply Lp.ext
  filter_upwards [(u.translate z).coeFn_gradToHilbertVectorL2,
    Lp.coeFn_compMeasurePreserving u.gradToHilbertVectorL2 hmp, hae]
    with x h1 h2 h3
  rw [h1]
  rw [show (nfTranslateHilbertVectorL2 z U u.gradToHilbertVectorL2 : _ → _) x =
      (Lp.compMeasurePreserving (fun y : Vec d => y - z) hmp
        u.gradToHilbertVectorL2 : _ → _) x from rfl, h2]
  change hilbertifyVecField (u.translate z).grad x =
    (u.gradToHilbertVectorL2 : _ → _) (x - z)
  rw [h3]
  rfl

/-- Measurability transports along the translation isometry. -/
theorem measurable_nfTranslate_gradToHilbertVectorL2
    {Omega : Type*} [MeasurableSpace Omega]
    (z : Vec d) {U : Set (Vec d)} (u : Omega → H1Function U)
    (hu : Measurable fun omega => (u omega).gradToHilbertVectorL2) :
    Measurable fun omega => ((u omega).translate z).gradToHilbertVectorL2 := by
  have heq : (fun omega => ((u omega).translate z).gradToHilbertVectorL2) =
      fun omega => nfTranslateHilbertVectorL2 z U
        ((u omega).gradToHilbertVectorL2) := by
    funext omega
    exact nfTranslateHilbertVectorL2_gradToHilbertVectorL2 z (u omega)
  rw [heq]
  exact (nfTranslateHilbertVectorL2 z U).continuous.measurable.comp hu

/-! ## Translated one-step correctors -/

/-- Gradient measurability of the translated local Neumann solution. -/
theorem measurable_oneStepTranslatedNeumannGradL2 [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p z : Vec d) (m : ℤ)
    (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (oneStepTranslatedNeumannSolution M n h p z m omega hh
        ).gradToHilbertVectorL2 := by
  have hbig : Measurable fun omega : NFSample d =>
      H1Function.gradToHilbertVectorL2
        (oneStepOriginNeumannSolution M n h p m
          (translatePotentialSequence z omega) hh).toH1Function :=
    (measurable_twoRadiusLarge_bigGrad M n h p m hh).comp
      (measurable_translatePotentialSequence z)
  exact measurable_nfTranslate_gradToHilbertVectorL2 z
    (fun omega => (oneStepOriginNeumannSolution M n h p m
      (translatePotentialSequence z omega) hh).toH1Function) hbig

/-- Gradient measurability of the translated local Dirichlet solution. -/
theorem measurable_oneStepTranslatedDirichletGradL2 [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p z : Vec d) (m : ℤ)
    (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (oneStepTranslatedDirichletSolution M n h p z m omega hh
        ).toH1Function.gradToHilbertVectorL2 := by
  have horigin : Measurable fun omega : NFSample d =>
      (oneStepOriginDirichletSolution M n h p m omega hh
        ).toH1Function.gradToHilbertVectorL2 := by
    apply measurable_oneStepShellDirichletGradL2 M n h p (originCube d m) hh
      (fun omega => oneStepOriginDirichletSolution M n h p m omega hh)
    intro omega phi
    have hweak :=
      oneStepOriginDirichletSolution_isWeakSolution M n h p m omega hh phi
    have hfield : ∀ x,
        (oneStepShellForcingH1 M n h omega p (originCube d m) hh).toField x =
          oneStepMultiplierAt M n h x omega • p := by
      intro x
      rw [oneStepShellForcing_paired_toField M n h omega p
        (originCube d m) hh, oneStepShellForcingW14_toField_apply]
    change (∫ x in openCubeSet (originCube d m),
        vecDot ((oneStepOriginDirichletSolution M n h p m omega hh
          ).toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) = _
    calc
      _ = ∫ x in openCubeSet (originCube d m),
          vecDot (-oneStepMultiplierAt M n h x omega • p)
            (phi.toH1Function.grad x) ∂volume := by
        simpa only [matVecMul_identityCoeffField, one_mul] using hweak
      _ = -∫ x in openCubeSet (originCube d m),
          vecDot ((oneStepShellForcingH1 M n h omega p
            (originCube d m) hh).toField x)
            (phi.toH1Function.grad x) ∂volume := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with x
        rw [hfield, neg_smul, vecDot_neg_left]
  have hbig : Measurable fun omega : NFSample d =>
      H1Function.gradToHilbertVectorL2
        (oneStepOriginDirichletSolution M n h p m
          (translatePotentialSequence z omega) hh).toH1Function :=
    horigin.comp (measurable_translatePotentialSequence z)
  exact measurable_nfTranslate_gradToHilbertVectorL2 z
    (fun omega => (oneStepOriginDirichletSolution M n h p m
      (translatePotentialSequence z omega) hh).toH1Function) hbig

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
