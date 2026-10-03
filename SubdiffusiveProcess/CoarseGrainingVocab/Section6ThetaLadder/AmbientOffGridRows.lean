module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.IntermediateCampanatoRestriction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.OffGridIntermediateReadout

@[expose] public section

/-!
# Theta ladder: ambient-event off-grid Campanato rows

This module composes the intermediate stopped row with the off-grid geometry.
It produces both deterministic row families needed by the final finite mean
telescope, on one parent-uniform ambient event.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

/-- Parent-uniform event package for the two off-grid point-centred rows. -/
theorem exists_ambientProductOffGridCampanatoRows
    (d : ℕ) [NeZero d] (step : ℕ) :
    ∃ Kbase Cgain Citer : ℝ,
      0 < Kbase ∧ 0 < Cgain ∧ 0 < Citer ∧
      ∀ C₁ C₂ Cabs : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 0 ≤ Cabs →
      ∀ k : ℕ, 6 ≤ k →
      (∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
        Real.exp
            (Citer * (k + 1) * (k + 2) +
              (Citer * (k + 2)) * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
          Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4)) →
      ∃ c Ctail : ℝ, 0 < c ∧ 0 < Ctail ∧ c ≤ 1 ∧
        ∃ j0 : ℕ, 0 < j0 ∧
          ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ c →
          64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) →
          ∀ L m : ℕ, ∀ z : Vec d,
            ∃ badTheta : Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
              MeasurableSet badTheta ∧
              M.P.toMeasure badTheta ≤ ENNReal.ofReal
                (Ctail * Real.exp
                  (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
              ∀ omega ∉ badTheta, ∀ s : ℕ, s + 4 ≤ m → j0 ≤ m - s →
              ∀ x : Vec d, ‖x - z‖ ≤ (3 : ℝ) ^ m / 4 →
              let eta := Section6Stopping.holderStoppingEpsilon
                C₂ thetaLadderExponent
              ∀ _heta : eta ∈
                Set.Icc ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) 1,
              ∀ b epsilon : ℝ, 0 < b → 0 < epsilon → epsilon ≤ 1 / 2 →
              Kbase * eta + Cgain * Real.sqrt epsilon ≤ 1 →
              productIterationSlopeCoefficient d M.shellPrefix.dimension k
                  (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
                C₁⁻¹ * (1 - thetaLadderExponent) →
              let contraction := (3 : ℝ) ^ (-(1 / 4 : ℝ))
              contraction ∈ Set.Ioo (0 : ℝ) 1 →
              contraction ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
              oneStepContractionConst d *
                    Section6Schauder.schauderInteriorConst d *
                    ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) +
                  productOriginRecurrenceErrorConstant d
                    M.shellPrefix.dimension k *
                    (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
                contraction ^ k →
              ∀ theta : Vec d → ℝ,
              ContinuousOn theta (translatedCube d (m : ℤ) z) →
              (∀ y ∈ translatedCube d (m : ℤ) z,
                |b⁻¹ * theta y - 1| ≤ epsilon) →
              ∀ h : H1Function (translatedCube d (m : ℤ) z),
              IsWeaklyHarmonicOn
                  (fun y ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y * theta y)
                  (translatedCube d (m : ℤ) z) h →
              ∀ hRep : Vec d → ℝ,
              ContinuousOn hRep (translatedCube d (m : ℤ) z) →
              hRep =ᵐ[volume.restrict (translatedCube d (m : ℤ) z)] h.toFun →
              let Krow := Cabs * (3 : ℝ) ^ (3 / 16 : ℝ)
              normalizedL2On (translatedCube d (s : ℤ) x)
                  (fun y ↦ h.toFun y - averageOn
                    (translatedCube d (s : ℤ) x) h.toFun) ≤
                Real.sqrt ((3 : ℝ) ^ d) *
                  (Krow * (3 : ℝ) ^
                    (-(1 / 2 : ℝ) *
                      (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
                  oscillationOn {y : Vec d | ‖y - z‖ ≤
                    3 * (3 : ℝ) ^ (m : ℤ) / 8} hRep) ∧
              normalizedL2On (translatedCube d (s : ℤ) x)
                  (fun y ↦ h.toFun y - averageOn
                    (translatedCube d (s : ℤ) x) h.toFun) ≤
                Real.sqrt ((3 : ℝ) ^ d) *
                  (Krow * (3 : ℝ) ^
                    (-(1 / 2 : ℝ) *
                      (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
                  (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
                    normalizedL2On (translatedCube d (m : ℤ) z)
                      (fun y ↦ h.toFun y - averageOn
                        (translatedCube d (m : ℤ) z) h.toFun))) := by
  obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, hcontract⟩ :=
    exists_ambientProductIntermediateCampanatoContractOnParent d step
  refine ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, ?_⟩
  intro C₁ C₂ Cabs hC₁ hC₂ hCabs k hk habs
  obtain ⟨c, Ctail, hc, hCtail, hcOne, j0, hj0, hevent⟩ :=
    hcontract C₁ C₂ Cabs hC₁ hC₂ hCabs k hk habs
  refine ⟨c, Ctail, hc, hCtail, hcOne, j0, hj0, ?_⟩
  intro M hdelta hsmall L m z
  obtain ⟨badTheta, hbadMeas, hbadTail, hpath⟩ :=
    hevent M hdelta hsmall L m z
  refine ⟨badTheta, hbadMeas, hbadTail, ?_⟩
  intro omega homega s hsm hdepth x hx
  dsimp only
  intro heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff
    hcontraction hcontractionPow hcontractionStep theta htheta hnear h hharm
    hRep hRepCont hRepAE
  let Krow := Cabs * (3 : ℝ) ^ (3 / 16 : ℝ)
  have hKrow : 0 ≤ Krow :=
    mul_nonneg hCabs (Real.rpow_nonneg (by norm_num) _)
  have hgrid : ∀ q : Vec d, OnTriadicGrid s q → q ∈ cube d (m : ℤ) →
      translatedCube d ((m : ℤ) - 2) (z + q) ⊆
          {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8} →
      normalizedL2On (translatedCube d ((s : ℤ) + 1) (z + q))
          (fun y ↦ h.toFun y - averageOn
            (translatedCube d ((s : ℤ) + 1) (z + q)) h.toFun) ≤
        Krow * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
          normalizedL2On (translatedCube d ((m : ℤ) - 2) (z + q))
            (fun y ↦ h.toFun y - averageOn
              (translatedCube d ((m : ℤ) - 2) (z + q)) h.toFun) := by
    intro q hqgrid hqmem htop
    have htopParent : translatedCube d ((m : ℤ) - 2) (z + q) ⊆
        translatedCube d (m : ℤ) z := by
      exact htop.trans (by
        intro y hy
        have hpowEq : (3 : ℝ) ^ (m : ℤ) = (3 : ℝ) ^ m := zpow_natCast _ _
        rw [translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm, hpowEq]
        rw [hpowEq] at hy
        have hp : 0 < (3 : ℝ) ^ m := by positivity
        exact lt_of_le_of_lt hy (by nlinarith))
    have htopCast : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
    have htopReal : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ m)]
      norm_num
    have htopParentNat : translatedCube d ((m - 2 : ℕ) : ℤ) (z + q) ⊆
        translatedCube d (m : ℤ) z := by
      simpa only [htopCast] using htopParent
    have hraw := hpath omega homega s (s + 1) (m - 2)
      (by omega) (by omega) (by omega) hdepth q hqgrid hqmem heta b epsilon
      hb hepsilon hepsilonHalf herrorOne hepsCoeff theta
      (htheta.mono htopParentNat) (fun y hy ↦ hnear y (htopParentNat hy))
      hcontraction hcontractionPow hcontractionStep
    have hrestricted := intermediateCampanatoRow_restrict hraw
      (Section6CutoffRegularity.isOpen_translatedCube d _ _)
      htopParentNat h hharm
    have hleftover :
        (((m : ℝ) - (s : ℝ) -
          ((m : ℝ) - 2 - ((s : ℝ) + 1))) / 16) = 3 / 16 := by ring
    norm_num only [Nat.cast_add, Nat.cast_one] at hrestricted
    rw [htopReal, hleftover] at hrestricted
    simpa only [Krow, htopCast, Nat.cast_add, Nat.cast_one,
      Int.cast_natCast] using hrestricted
  constructor
  · exact pointCenteredRow_le_ambientOscillation_of_intermediate
      hsm hx hRepCont hRepAE hKrow hgrid
  · exact pointCenteredRow_le_parentCentered_of_intermediate
      hsm hx hKrow hgrid

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
