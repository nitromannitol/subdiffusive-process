module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.EuclideanBallRepresentative

@[expose] public section

/-!
# Physical-ball readout of the small-contrast Schauder estimate

This module packages the carrier transports into a local continuous
representative on the original ball and identifies it with the canonical
global ball-average representative.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Filter MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- The proved Schauder theorem, transported back to a physical ball and
identified with the canonical global representative. -/
theorem exists_physicalBallRepresentative_smallContrast [NeZero d]
    {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) {u : H1Function W}
    (hu : IsWeaklyHarmonicOn s W u)
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (hball : euclideanBall x rho ⊆ W)
    (kappa delta alpha : ℝ)
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hdelta1 : delta < 1)
    (hclose : ∀ y ∈ euclideanBall x rho,
      |kappa⁻¹ * s y - 1| ≤ delta) :
    let uBall := u.restrict (isOpen_euclideanBall x rho) hball
    let K := smallContrastSchauderConstant d *
      smallContrastDataSize d alpha (ballToUnitH1 x hrho uBall) (fun _ ↦ 0)
    ∃ g : Vec d → ℝ,
      ContinuousOn g (euclideanBall x (rho / 2)) ∧
      g =ᵐ[volume.restrict (euclideanBall x (rho / 2))] u.toFun ∧
      EuclideanHolderBoundOn (euclideanBall x (rho / 2)) alpha
        (K * rho ^ (1 - alpha)) g ∧
      ∀ y ∈ euclideanBall x (rho / 2),
        euclideanBallAverageRepresentative u.toFun y = g y := by
  let uBall := u.restrict (isOpen_euclideanBall x rho) hball
  let K := smallContrastSchauderConstant d *
    smallContrastDataSize d alpha (ballToUnitH1 x hrho uBall) (fun _ ↦ 0)
  have hcontUnit : ContinuousOn (ballToUnitCoefficient s x rho kappa)
      (smallContrastUnitBall d) :=
    continuousOn_ballToUnitCoefficient hrho kappa (hs.mono hball)
  have hcloseUnit : ∀ y ∈ smallContrastUnitBall d,
      |ballToUnitCoefficient s x rho kappa y - 1| ≤ delta :=
    ballToUnitCoefficient_close_of_physical hrho hclose
  have huBall : IsWeaklyHarmonicOn s (euclideanBall x rho) uBall :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.isWeaklyHarmonicOn_restrict
      hW (isOpen_euclideanBall x rho) hball hu
  have hSchauder := smallContrastSchauder_ballToUnit hrho kappa delta alpha
    hd halpha hdelta0 hdelta hdelta1 hcontUnit hcloseUnit huBall
  obtain ⟨_uGrad, uRep, hcontRep, haeRep, hholderRep⟩ := hSchauder
  let g := physicalBallRepresentative x rho uRep
  have hcontG : ContinuousOn g (euclideanBall x (rho / 2)) :=
    continuousOn_physicalBallRepresentative (x := x) hrho hcontRep
  have haeG : g =ᵐ[volume.restrict (euclideanBall x (rho / 2))] u.toFun := by
    simpa [g, uBall] using! physicalBallRepresentative_ae_eq hrho
      (u := uBall) haeRep
  have hholderG : EuclideanHolderBoundOn (euclideanBall x (rho / 2))
      alpha (K * rho ^ (1 - alpha)) g := by
    simpa only [K, g] using
      euclideanHolderBoundOn_physicalBallRepresentative hrho hholderRep
  refine ⟨g, hcontG, haeG, hholderG, ?_⟩
  simpa only [g, uBall] using
    euclideanBallAverageRepresentative_eq_physicalBallRepresentative
      hrho hball hcontRep haeRep

/-- Point-to-local-average consequence of the physical Hölder readout. -/
theorem canonicalRepresentative_sub_ballAverage_le_of_smallContrast
    [NeZero d] {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) {u : H1Function W}
    (hu : IsWeaklyHarmonicOn s W u)
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (hball : euclideanBall x rho ⊆ W)
    (kappa delta alpha : ℝ)
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hdelta1 : delta < 1)
    (hclose : ∀ y ∈ euclideanBall x rho,
      |kappa⁻¹ * s y - 1| ≤ delta) :
    let uBall := u.restrict (isOpen_euclideanBall x rho) hball
    let K := smallContrastSchauderConstant d *
      smallContrastDataSize d alpha (ballToUnitH1 x hrho uBall) (fun _ ↦ 0)
    |euclideanBallAverageRepresentative u.toFun x -
        averageOn (euclideanBall x (rho / 2)) u.toFun| ≤
      K * rho ^ (1 - alpha) * (rho / 2) ^ alpha := by
  let uBall := u.restrict (isOpen_euclideanBall x rho) hball
  let K := smallContrastSchauderConstant d *
    smallContrastDataSize d alpha (ballToUnitH1 x hrho uBall) (fun _ ↦ 0)
  obtain ⟨g, hcontG, haeG, hholderG, hcanonical⟩ :=
    exists_physicalBallRepresentative_smallContrast hW hs hu hrho hball
      kappa delta alpha hd halpha hdelta0 hdelta hdelta1 hclose
  have hxInner : x ∈ euclideanBall x (rho / 2) := by
    change vecNormSq (x - x) < (rho / 2) ^ 2
    simpa [vecNormSq, vecDot] using
      sq_pos_of_pos (by positivity : 0 < rho / 2)
  have hK0 : 0 ≤ K := by
    exact mul_nonneg (smallContrastSchauderConstant_nonneg d)
      (smallContrastDataSize_nonneg halpha.2 _ _)
  have hrpow0 : 0 ≤ (rho / 2) ^ alpha :=
    Real.rpow_nonneg (by positivity) _
  have hbound : ∀ y ∈ euclideanBall x (rho / 2),
      |g y - g x| ≤ K * rho ^ (1 - alpha) * (rho / 2) ^ alpha := by
    intro y hy
    have hholder := hholderG y hy x hxInner
    have hdist : euclideanNorm (y - x) ≤ rho / 2 := by
      have hy' : vecNormSq (y - x) < (rho / 2) ^ 2 := hy
      rw [← euclideanNorm_sq] at hy'
      exact (sq_lt_sq₀ (euclideanNorm_nonneg _) (by positivity)).mp hy' |>.le
    have halpha0 : 0 ≤ alpha := by linarith [halpha.1]
    have hrpow := Real.rpow_le_rpow (euclideanNorm_nonneg _) hdist halpha0
    exact hholder.trans (mul_le_mul_of_nonneg_left hrpow
      (mul_nonneg hK0 (Real.rpow_nonneg hrho.le _)))
  have havg := abs_averageOn_euclideanBall_sub_le_of_ae_eq
    (by positivity : 0 < rho / 2)
    (Set.Subset.rfl) ((euclideanBall_subset_euclideanBall (by positivity)
      (by linarith)).trans hball) haeG
    (mul_nonneg (mul_nonneg hK0 (Real.rpow_nonneg hrho.le _)) hrpow0)
    hbound
  rw [hcanonical x hxInner]
  simpa only [abs_sub_comm] using havg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
