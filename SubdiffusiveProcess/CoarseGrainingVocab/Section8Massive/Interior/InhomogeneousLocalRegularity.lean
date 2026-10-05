module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.EuclideanBallRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.InhomogeneousBallRescaling

@[expose] public section

/-!
# Physical-ball regularity for an inhomogeneous massive equation

The unit-ball Schauder estimate is transported back to a continuous local
representative of the original Sobolev solution.  The representative is
identified with the canonical shrinking-ball-average representative, so local
outputs from overlapping balls require no separate gluing choice.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- The inhomogeneous Schauder theorem transported to a physical ball and
identified with the canonical global ball-average representative. -/
theorem exists_physicalBallRepresentative_smallContrast_inhomogeneous
    [NeZero d] {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) {u : H1Function W} {g : Vec d → Vec d}
    (hu : IsDivFormWeakSolutionOn s W u g)
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (hball : euclideanBall x rho ⊆ W)
    (kappa delta alpha : ℝ)
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hdelta1 : delta < 1)
    (hclose : ∀ y ∈ euclideanBall x rho,
      |kappa⁻¹ * s y - 1| ≤ delta)
    (hg : MemVectorLpOn W (schauderSourceExponent d alpha) g) :
    let uBall := u.restrict (isOpen_euclideanBall x rho) hball
    let gUnit := ballToUnitSource g x rho kappa
    let K := smallContrastSchauderConstant d *
      smallContrastDataSize d alpha (ballToUnitH1 x hrho uBall) gUnit
    ∃ uRep : Vec d → ℝ,
      ContinuousOn uRep (euclideanBall x (rho / 2)) ∧
      uRep =ᵐ[volume.restrict (euclideanBall x (rho / 2))] u.toFun ∧
      EuclideanHolderBoundOn (euclideanBall x (rho / 2)) alpha
        (K * rho ^ (1 - alpha)) uRep ∧
      ∀ y ∈ euclideanBall x (rho / 2),
        euclideanBallAverageRepresentative u.toFun y = uRep y := by
  let uBall := u.restrict (isOpen_euclideanBall x rho) hball
  let gUnit := ballToUnitSource g x rho kappa
  let K := smallContrastSchauderConstant d *
    smallContrastDataSize d alpha (ballToUnitH1 x hrho uBall) gUnit
  have hcontUnit : ContinuousOn (ballToUnitCoefficient s x rho kappa)
      (smallContrastUnitBall d) :=
    continuousOn_ballToUnitCoefficient hrho kappa (hs.mono hball)
  have hcloseUnit : ∀ y ∈ smallContrastUnitBall d,
      |ballToUnitCoefficient s x rho kappa y - 1| ≤ delta :=
    ballToUnitCoefficient_close_of_physical hrho hclose
  have huBall : IsDivFormWeakSolutionOn s (euclideanBall x rho) uBall g :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.isDivFormWeakSolutionOn_restrict
      hW (isOpen_euclideanBall x rho) hball hu
  have hgBall : MemVectorLpOn (euclideanBall x rho)
      (schauderSourceExponent d alpha) g :=
    hg.mono_measure (Measure.restrict_mono hball le_rfl)
  have hSchauder := smallContrastSchauder_ballToUnit_inhomogeneous
    hrho kappa delta alpha hd halpha hdelta0 hdelta hdelta1
      hcontUnit hcloseUnit huBall hgBall
  obtain ⟨_uGrad, unitRep, hcontRep, haeRep, hholderRep⟩ := hSchauder
  let uRep := physicalBallRepresentative x rho unitRep
  have hcont : ContinuousOn uRep (euclideanBall x (rho / 2)) :=
    continuousOn_physicalBallRepresentative (x := x) hrho hcontRep
  have hae : uRep =ᵐ[volume.restrict (euclideanBall x (rho / 2))] u.toFun := by
    simpa only [uRep, uBall] using!
      physicalBallRepresentative_ae_eq hrho (u := uBall) haeRep
  have hholder : EuclideanHolderBoundOn (euclideanBall x (rho / 2))
      alpha (K * rho ^ (1 - alpha)) uRep := by
    simpa only [K, gUnit, uRep] using!
      euclideanHolderBoundOn_physicalBallRepresentative hrho hholderRep
  refine ⟨uRep, hcont, hae, hholder, ?_⟩
  simpa only [uRep, uBall] using!
    euclideanBallAverageRepresentative_eq_physicalBallRepresentative
      hrho hball hcontRep haeRep

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
