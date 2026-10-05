module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductParameterSelection
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.PathwiseReadout

@[expose] public section

/-!
# Theta ladder: ambient unit-cell event contract

This is the ambient-measurable `j ≤ m` contract consumed by the
bounded-multiplier outer assembly.  Its pathwise part is the finite triadic
mean telescope in `PathwiseReadout`; this file only makes the dimension-only
parameter choices and packages the stopped recurrence event.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal

noncomputable section

/-- The exact ambient `hcellEvents` contract of the outer
bounded-multiplier assembly. -/
theorem exists_ambientThetaLadderCellEvents (d : ℕ) :
    ∃ epsilonTheta cTheta CTheta : ℝ,
      0 < epsilonTheta ∧ 0 < cTheta ∧ 0 < CTheta ∧
      let epsilonStar := min
        (boundedMultiplierEpsilonStar d) epsilonTheta
      let c := min cTheta (1 / 2)
      let C := CTheta + 1 +
        boundedMultiplierNonpositiveOscillationConst d c +
        boundedMultiplierNonpositiveL2Const d
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d,
        ∀ j : ℕ, 0 < j → (j : ℤ) ≤ m →
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ badTheta : Set (PotentialSample d),
            MeasurableSet badTheta ∧
            M.P.toMeasure badTheta ≤ ENNReal.ofReal
              ((C - 1) * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ badTheta,
              omega ∈ coveringRestrictedGradientGood M L m z →
                BoundedMultiplierPathwiseEstimate
                  M L m z j B' epsilonStar C c omega := by
  by_cases hd : 2 ≤ d
  · let : NeZero d := ⟨by omega⟩
    obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, hcontract⟩ :=
      exists_ambientProductOffGridCampanatoRows d 1
    obtain ⟨C₁, C₂, Cabs, hC₁, hC₂, hCabs, k, hk, habs,
        epsilonTheta, hepsilonTheta, hepsilonHalf, hetaPos, hetaOne,
        hnumerical⟩ :=
      exists_productOffGridNumericalParameters d hd hKbase hCgain hCiter
    obtain ⟨c0, Ctail, hc0, hCtail, hc0One, j0, hj0, hevent⟩ :=
      hcontract C₁ C₂ Cabs hC₁ hC₂ hCabs.le k hk habs
    obtain ⟨Kpoint, hKpoint, hpointPrice⟩ :=
      exists_positiveScaleZeroPointPrice_exponential_bound d
    let eta := Section6Stopping.holderStoppingEpsilon C₂ thetaLadderExponent
    let cTheta := min c0 (min (1 / 2048 : ℝ) (eta / 32))
    let Krow := Cabs * (3 : ℝ) ^ (3 / 16 : ℝ)
    let J := max 4 j0
    let Cpath := thetaLadderPathwiseConstant d J Krow Kpoint
    let CTheta := Ctail + Cpath + 1
    have hcTheta : 0 < cTheta := by
      dsimp only [cTheta]
      exact lt_min hc0 (lt_min (by norm_num) (div_pos hetaPos (by norm_num)))
    have hKrow : 0 ≤ Krow := by dsimp only [Krow]; positivity
    have hCpath : 0 < Cpath := by
      exact thetaLadderPathwiseConstant_pos d J hKrow hKpoint.le
    have hCTheta : 0 < CTheta := by dsimp only [CTheta]; positivity
    refine ⟨epsilonTheta, cTheta, CTheta, hepsilonTheta, hcTheta,
      hCTheta, ?_⟩
    dsimp only
    intro M hdelta L m z j hj hjm B' hB'
    let epsilonStar := min (boundedMultiplierEpsilonStar d) epsilonTheta
    let c := min cTheta (1 / 2)
    let C := CTheta + 1 +
      boundedMultiplierNonpositiveOscillationConst d c +
      boundedMultiplierNonpositiveL2Const d
    have hepsilonStar : 0 < epsilonStar :=
      lt_min (boundedMultiplierEpsilonStar_pos d) hepsilonTheta
    have hepsilonBounded : epsilonStar ≤ boundedMultiplierEpsilonStar d :=
      min_le_left _ _
    have hepsilonSelected : epsilonStar ≤ epsilonTheta := min_le_right _ _
    have hepsilonStarHalf : epsilonStar ≤ 1 / 2 :=
      hepsilonSelected.trans hepsilonHalf
    have hc0' : c ≤ c0 :=
      (min_le_left cTheta (1 / 2)).trans (min_le_left c0 _)
    have hcTiny : c ≤ (1 / 2048 : ℝ) :=
      (min_le_left cTheta (1 / 2)).trans
        ((min_le_right c0 _).trans (min_le_left _ _))
    have hcEta : c ≤ eta / 32 :=
      (min_le_left cTheta (1 / 2)).trans
        ((min_le_right c0 _).trans (min_le_right _ _))
    have hdelta0 : M.delta ≤ c0 := hdelta.trans hc0'
    have hdeltaTiny : M.delta ≤ (1 / 2048 : ℝ) := hdelta.trans hcTiny
    have hdeltaEta : M.delta ≤ eta / 32 := hdelta.trans hcEta
    have hdeltaOne : M.delta ≤ 1 := hdeltaTiny.trans (by norm_num)
    have hdeltaSq : M.delta ^ 2 ≤ M.delta := by
      nlinarith only [M.shellPrefix.delta_pos, hdeltaOne]
    have hsmall : 64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) := by
      nlinarith only [hdeltaSq, hdeltaTiny]
    have hetaLower : (1 / 32 : ℝ)⁻¹ * M.delta ^ 2 ≤ eta := by
      norm_num
      nlinarith only [hdeltaSq, hdeltaEta]
    have hetaMem : eta ∈ Set.Icc
        ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) 1 := ⟨hetaLower, hetaOne⟩
    have hmpos : 0 < m := by
      have hjz : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
      exact hjz.trans_le hjm
    let mn := m.toNat
    have hmnpos : 0 < mn := Int.pos_iff_toNat_pos.mp hmpos
    have hmEq : (mn : ℤ) = m := Int.toNat_of_nonneg hmpos.le
    have hjmnZ : (j : ℤ) ≤ (mn : ℤ) := by simpa only [hmEq] using hjm
    have hjmn : j ≤ mn := by exact_mod_cast hjmnZ
    have hB'n : IsMiddleHalfSubcube (mn : ℤ) z j B' := by
      simpa only [hmEq] using hB'
    obtain ⟨badTheta, hbadMeas, hbadTail, hpath⟩ :=
      hevent M hdelta0 hsmall L mn z
    refine ⟨badTheta, hbadMeas, ?_, ?_⟩
    · have hlog : Real.log M.delta < 0 :=
        Real.log_neg M.shellPrefix.delta_pos
          (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
      have hden : 0 < M.delta ^ 2 * |Real.log M.delta| ^ 2 :=
        mul_pos (sq_pos_of_pos M.shellPrefix.delta_pos)
          (sq_pos_of_pos (abs_pos.mpr hlog.ne))
      have hcc0 : c ≤ c0 := hc0'
      have hexp : Real.exp
          (-c0 / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) ≤
          Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) := by
        apply Real.exp_le_exp.mpr
        have hdiv := div_le_div_of_nonneg_right hcc0 hden.le
        simpa only [neg_div] using neg_le_neg hdiv
      have hcoef : Ctail ≤ C - 1 := by
        dsimp only [C, CTheta]
        have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
        have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d
        linarith only [hCpath, hosc, hL2]
      exact hbadTail.trans (ENNReal.ofReal_le_ofReal (by
        have hCminus : 0 ≤ C - 1 := hCtail.le.trans hcoef
        have hmul := mul_le_mul hcoef hexp (Real.exp_pos _).le hCminus
        exact hmul))
    · intro omega homega hgood
      have hnum := hnumerical hd epsilonStar hepsilonStar hepsilonSelected
      dsimp only at hnum
      obtain ⟨herrorOne, hslope, hcontraction, hcontractionPow,
        hcontractionStep⟩ := hnum
      have hrows : AmbientProductOffGridRows
          M L mn z omega j0 Krow epsilonStar := by
        intro s hs4 hdepth x hx b hb theta htheta hnear h hharm hRep
          hRepCont hRepAE
        have hr := hpath omega homega s hs4 hdepth x hx hetaMem b epsilonStar
          hb hepsilonStar hepsilonStarHalf herrorOne hslope hcontraction
          hcontractionPow hcontractionStep theta htheta hnear h hharm hRep
          hRepCont hRepAE
        simpa only [Krow] using hr
      have hCpathLe : Cpath ≤ C := by
        dsimp only [C, CTheta]
        have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
        have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d
        linarith only [hCtail, hosc, hL2]
      have hcNonneg : 0 ≤ c := (lt_min hcTheta (by norm_num)).le
      have hcQuarter : c ≤ 1 / 4 :=
        hcTiny.trans (by norm_num)
      have hgoodn : omega ∈
          coveringRestrictedGradientGood M L (mn : ℤ) z := by
        simpa only [hmEq] using hgood
      have hout := boundedMultiplierPathwiseEstimate_of_ambientProductOffGridRows
        hd M L mn hmnpos z omega j hj hjmn hB'n j0 hKrow hKpoint.le
        hpointPrice hepsilonBounded hcNonneg hcQuarter hCpathLe hgoodn hrows
      simpa only [hmEq, epsilonStar, c, C] using hout
  · refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    dsimp only
    intro M
    exact (hd M.shellPrefix.dimension).elim

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
