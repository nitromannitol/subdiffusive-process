module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.AnchorBoundary
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffInputs

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The full v4 boundary excess-decay conclusion at a finite cutoff follows
from the matching cutoff boundary harmonic comparison.  The cutoff
`𝓔`-cap is already a theorem and is discharged by the wrapper below. -/
theorem belowCutoffBoundaryExcessDecay_of_harmonic_and_cap (d : ℕ)
    (hharm : BoundaryCutoffHarmonicApproximationInputV6 d)
    (hcap : BelowCutoffMathcalECapInput d) :
    BoundaryCutoffHolderExcessDecayBoundaryInputV4 d := by
  unfold BoundaryCutoffHolderExcessDecayBoundaryInputV4
  by_cases hd2 : 2 ≤ d
  · haveI : NeZero d := ⟨by omega⟩
    have hdne : d ≠ 0 := by omega
    obtain ⟨CA, hCApos, hA⟩ := hharm
    obtain ⟨CB, hCBpos, hB⟩ := hcap
    obtain ⟨Csch, hCsch0, hstep⟩ := exists_excess_oneStep_boundary_anchor d hdne
    refine ⟨anchorBoundaryConst d CA CB Csch,
      anchorBoundaryConst_pos d hCApos.le hCBpos.le hCsch0, ?_⟩
    have hC0 : (0 : ℝ) ≤ anchorBoundaryConst d CA CB Csch :=
      anchorBoundaryConst_nonneg d hCApos.le hCBpos.le hCsch0
    have hCcontr : oneStepContractionConst d * Csch ≤ anchorBoundaryConst d CA CB Csch :=
      anchorBoundaryConst_contraction_le d hCApos.le hCBpos.le hCsch0
    have hCrem : (81 * taylorConst d * Csch + 1) *
        (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
          + correctorLegConst d)
        ≤ anchorBoundaryConst d CA CB Csch := anchorBoundaryConst_remainder_le d hCsch0
    have hCcrude : 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))
        ≤ anchorBoundaryConst d CA CB Csch :=
      anchorBoundaryConst_crude_le d hCApos.le hCBpos.le hCsch0
    set C : ℝ := anchorBoundaryConst d CA CB Csch with hCdef
    intro M s hs epsilon heps k hk L m n hkn hnm x hx z hz hxz hgate ω u h g hsol hgfrac
      hhold ell hell
    -- the standing numerical facts
    have hd1 : 1 ≤ d := by omega
    have hdel : 0 < M.delta := M.shellPrefix.delta_pos
    have hdel2 : (0 : ℝ) < M.delta ^ 2 := pow_pos hdel 2
    have hs0 : 0 < s := lt_of_lt_of_le (mul_pos (by norm_num) hdel2) hs.1
    have hs4 : s ≤ 1 / 4 := hs.2
    have heps0 : 0 ≤ epsilon :=
      le_trans (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hs0.le)) hdel2.le) heps.1
    have heps1 : epsilon ≤ 1 := heps.2
    -- signs of the atoms appearing on the right
    have hMemHW : MemHolder (truncatedCube d m n x) (1 / 2) h.grad :=
      memHolder_mono hhold (truncatedCube_subset_cube d m n x)
    have hEn : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u.toFun := excess_nonneg _ _ _
    have hErr : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z := ENNReal.toReal_nonneg
    have hTail : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ :=
      inv_nonneg.2 (tailAverage_nonneg _ _ _ _ _)
    have hFg : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
      ENNReal.toReal_nonneg
    have hSl : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
    have hAh : 0 ≤ Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) :=
      Real.sqrt_nonneg _
    have hHh : 0 ≤ holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad :=
      holderSeminormOn_nonneg hMemHW
    have hpow1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have hpow2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := Real.rpow_nonneg (by norm_num) _
    have hpow3 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * n) := Real.rpow_nonneg (by norm_num) _
    have hpow4 : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have hss : (0 : ℝ) ≤ s ^ (-2 : ℝ) := Real.rpow_nonneg hs0.le _
    have hssIn : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
    have hs15 : (0 : ℝ) ≤ s ^ (-8 : ℝ) := Real.rpow_nonneg hs0.le _
    have hs3 : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
    have hI1 : (0 : ℝ) ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
        s ^ (-3 / 2 : ℝ) *
          Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) else 0) := by
      split_ifs
      · exact mul_nonneg hssIn hAh
      · exact le_rfl
    have hI2 : (0 : ℝ) ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
        C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * (3 : ℝ) ^ ((n : ℝ) / 2) *
          holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad else 0) := by
      split_ifs
      · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hs3) hpow2) hpow4) hHh
      · exact le_rfl
    have hP : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon :=
      mul_nonneg (mul_nonneg hpow2 hss) heps0
    have hT2 : (0 : ℝ) ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) *
        section6HomogenizationError M (s / 8) L (n + 2) ω z *
        (Real.sqrt (vecNormSq ell.slope) +
          (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
            s ^ (-3 / 2 : ℝ) *
              Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
          else 0)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hpow2) hss) hErr) (add_nonneg hSl hI1)
    have hT3 : (0 : ℝ) ≤ C * s ^ (-8 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ * (3 : ℝ) ^ (s * n) *
        (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hs15) hpow2) hTail) hpow3) hFg
    refine indicatorValue_le ?_ ?_
    · exact add_nonneg (add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg hC0 (add_nonneg hpow1 hP)) hEn) hT2) hT3) hI2
    intro homega
    have hu_n : MemLp u.toFun 2 (volume.restrict (truncatedCube d m n x)) :=
      u.memL2.mono_measure (Measure.restrict_mono (truncatedCube_subset_cube d m n x) le_rfl)
    -- the boundary case switches both indicators on
    have hBT : BoundaryTouches (truncatedCube d m n x) (cube d m) :=
      boundaryTouches_of_not_translatedCube_subset (j := (n : ℤ) - 4) (l := (n : ℤ))
        hx (by omega) hgate
    by_cases hk6 : 6 ≤ k
    · -- the boundary branch `6 ≤ k`
      obtain ⟨y, hy, hy1, hy2⟩ := exists_windowChoice (m := (m : ℤ)) (n := (n : ℤ)) hx (by omega)
      have hYsub : translatedCube d ((n : ℤ) - 2) y ⊆ cube d (m : ℤ) :=
        hy2.trans (truncatedCube_subset_cube d m ((n : ℤ) - 1) x)
      have hYopen : IsOpen (translatedCube d ((n : ℤ) - 2) y) :=
        Section6Schauder.isOpen_translatedCube d _ y
      -- step `.2`: the harmonic-approximation premise, at the replacement cube
      have hhfrac : MemFractionalOn (cube d m) s h.grad :=
        memFractionalOn_cube_of_memHolder hd1 hs0 hs4 hhold
      obtain ⟨⟨v, hvharm, hvzt⟩, -, hHA⟩ :=
        hA M s hs L m n hnm z hz x hxz ω u h g hsol hgfrac hhfrac y hy hy1 hy2
          (u.restrict hYopen hYsub) (fun _ => rfl) (fun _ => rfl)
      -- the two `H¹₀` data the boundary competitor needs
      have hdat : Homogenization.MemH10 (openCubeSet (originCube d m))
          (fun p => u.toFun p - h.toFun p) := by
        obtain ⟨w, hval, -⟩ := hsol.1
        refine ⟨w, funext fun p => ?_⟩
        show w.toH1Function.toFun p = u.toFun p - h.toFun p
        rw [hval p]
        ring
      have hvu : Homogenization.MemH10 (translatedCube d ((n : ℤ) - 2) y)
          (fun p => v.toFun p - u.toFun p) := by
        obtain ⟨w, hval, -⟩ := hvzt
        refine ⟨w, funext fun p => ?_⟩
        show w.toH1Function.toFun p = v.toFun p - u.toFun p
        rw [hval p]
        show w.toH1Function.toFun p = u.toFun p + w.toH1Function.toFun p - u.toFun p
        ring
      -- steps `.3`/`.4`/`.5`: the boundary one-step
      have hone := hstep m n k hk6 hnm x y hx hy1 hy2 hgate u h hdat hMemHW v hvharm hvu
      -- step `.2` continued: the harmonic-approximation bound on the good event
      have homega1 : ω ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) :=
        goodEvent_mono heps0 heps1 homega
      have hD := hHA v hvharm hvzt
      rw [indicatorValue_of_mem homega1] at hD
      -- step `.7`: the `𝓔`-cap, transported to the translate `z`
      have hcapz : section6HomogenizationError M (s / 8) L (n + 2) ω z ≤ CB * epsilon := by
        refine Section6Covariance.section6HomogenizationError_le_of_translate_zero ?_ z homega
        intro ν hν
        refine hB M (s / 8) ⟨by linarith [hs.1], by linarith⟩ L (n + 2) ν epsilon
          ⟨?_, heps1⟩ hν
        have hrw : (s / 8)⁻¹ * M.delta ^ 2 = 8 * s⁻¹ * M.delta ^ 2 := by
          field_simp
        rw [hrw]
        exact heps.1
      -- step `.6`: the slope split of the normalized oscillation
      have hstep6 := normalizedL2On_sub_average_le (m := (m : ℤ)) (n := (n : ℤ)) (x := x)
        hx (by omega) hu_n hell
      
      have hstep8 := holderLeg_le (m := (m : ℤ)) (j := (n : ℤ)) (x := x) (f := h.grad)
        (s := s) hd1 hx hs0 hs4 hMemHW
      -- notation for the atoms of the display
      set E := excess (n : ℤ) (truncatedCube d m n x) u.toFun with hEdef
      set Err := section6HomogenizationError M (s / 8) L (n + 2) ω z with hErrdef
      set Sl := Real.sqrt (vecNormSq ell.slope) with hSldef
      set Ah := Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) with hAhdef
      set Fg := (fractionalSeminormOn (truncatedCube d m n x) s g).toReal with hFgdef
      set Fh := (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal with hFhdef
      set Hhv := holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad with hHhdef
      set Tinv := (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ with hTinvdef
      set Dv := normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
        (fun q => u.toFun q - v.toFun q) with hDdef
      set N := normalizedL2On (truncatedCube d m n x)
        (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) with hNdef
      -- the remainder constant is bounded by the printed `3^{(1+d/2)k}`
      have hKr0 : (0 : ℝ) ≤ oneStepRemainderConst d Csch k :=
        oneStepRemainderConst_nonneg d hCsch0 k
      have hb0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := hpow2
      have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have h0 : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          positivity
        simpa using h0
      have h81 : (0 : ℝ) ≤ 81 * taylorConst d * Csch :=
        mul_nonneg (mul_nonneg (by norm_num) (taylorConst_nonneg d)) hCsch0
      have hCrm0 : (0 : ℝ) ≤ 81 * taylorConst d * Csch + 1 := by linarith only [h81]
      have hKrb : oneStepRemainderConst d Csch k
          ≤ (81 * taylorConst d * Csch + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have hleft : 81 * taylorConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            ≤ 81 * taylorConst d * Csch * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
          mul_le_mul_of_nonneg_left (le_trans three_zpow_rpow_half_le_one hb1) h81
        have hright : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
            ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
          have ht0 : (0 : ℝ) < (3 : ℝ) ^ ((k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
          have htz : (3 : ℝ) ^ ((k : ℤ)) = (3 : ℝ) ^ ((k : ℝ)) := by
            rw [← Real.rpow_intCast (3 : ℝ) ((k : ℤ))]
            norm_num
          have hsq : Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) = ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
            sqrt_pow_eq_rpow_half ht0.le d
          have hmono : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
              ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) := by
            refine Real.sqrt_le_sqrt ?_
            rw [← htz]
            exact pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
              (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
          have hsplit : (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
              = (3 : ℝ) ^ ((k : ℝ)) * ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
            three_rpow_one_add_mul (k : ℝ) ((d : ℝ) / 2)
          rw [hsplit, htz]
          exact mul_le_mul_of_nonneg_left (le_trans hmono (le_of_eq hsq)) ht0.le
        rw [oneStepRemainderConst]
        linarith only [hleft, hright]
      -- the coefficient budgets
      have hCH0 : (0 : ℝ) ≤ fractionalHolderConst d := fractionalHolderConst_nonneg d
      have hsd0 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
      have hcorr0 : (0 : ℝ) ≤ correctorLegConst d := correctorLegConst_nonneg d
      have hbudget : ∀ c : ℝ, 0 ≤ c →
          CA * c ≤ CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
            + correctorLegConst d →
          oneStepRemainderConst d Csch k * CA * c
            ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        intro c hc0 hcle
        have hassoc : oneStepRemainderConst d Csch k * CA * c
            = oneStepRemainderConst d Csch k * (CA * c) := by ring
        rw [hassoc]
        have hCAc0 : (0 : ℝ) ≤ CA * c := mul_nonneg hCApos.le hc0
        have h1 : oneStepRemainderConst d Csch k * (CA * c)
            ≤ ((81 * taylorConst d * Csch + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) * (CA * c) :=
          mul_le_mul_of_nonneg_right hKrb hCAc0
        have h2 : ((81 * taylorConst d * Csch + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) * (CA * c)
            = ((81 * taylorConst d * Csch + 1) * (CA * c)) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by ring
        have h3 : (81 * taylorConst d * Csch + 1) * (CA * c)
            ≤ (81 * taylorConst d * Csch + 1) *
              (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
                + correctorLegConst d) :=
          mul_le_mul_of_nonneg_left hcle hCrm0
        have h4 : ((81 * taylorConst d * Csch + 1) * (CA * c)) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
            ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
          mul_le_mul_of_nonneg_right (le_trans h3 hCrem) hb0
        linarith only [h1, h2.le, h2.ge, h4]
      have hbrk : ∀ c : ℝ, c ≤ CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d →
          CA * c ≤ CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
            + correctorLegConst d := by
        intro c hcle
        have h1 : CA * c ≤ CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) :=
          mul_le_mul_of_nonneg_left hcle hCApos.le
        linarith only [h1, hcorr0]
      have hbCB := hbudget CB hCBpos.le (hbrk CB (by linarith only [hCH0, hsd0]))
      have hbOne := hbudget 1 zero_le_one (hbrk 1 (by linarith only [hCH0, hsd0, hCBpos.le]))
      have hbSqrt := hbudget (Real.sqrt (d : ℝ) / 2) (by linarith only [hsd0])
        (hbrk (Real.sqrt (d : ℝ) / 2) (by linarith only [hCH0, hsd0, hCBpos.le]))
      have hb3 : oneStepRemainderConst d Csch k * CA
          ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have := hbOne
        rw [mul_one] at this
        exact this
      -- the joint budget of the two Hölder legs of the fourth line
      have hbHolder : oneStepRemainderConst d Csch k *
            (CA * fractionalHolderConst d + correctorLegConst d)
          ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have hnn : (0 : ℝ) ≤ CA * fractionalHolderConst d + correctorLegConst d := by
          have h0 : (0 : ℝ) ≤ CA * fractionalHolderConst d := mul_nonneg hCApos.le hCH0
          linarith only [h0, hcorr0]
        have h1 : oneStepRemainderConst d Csch k *
              (CA * fractionalHolderConst d + correctorLegConst d)
            ≤ ((81 * taylorConst d * Csch + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
              (CA * fractionalHolderConst d + correctorLegConst d) :=
          mul_le_mul_of_nonneg_right hKrb hnn
        have h2 : ((81 * taylorConst d * Csch + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
              (CA * fractionalHolderConst d + correctorLegConst d)
            = ((81 * taylorConst d * Csch + 1) *
                (CA * fractionalHolderConst d + correctorLegConst d)) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by ring
        have h3 : (81 * taylorConst d * Csch + 1) *
              (CA * fractionalHolderConst d + correctorLegConst d)
            ≤ (81 * taylorConst d * Csch + 1) *
              (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
                + correctorLegConst d) := by
          refine mul_le_mul_of_nonneg_left ?_ hCrm0
          have hexpb : CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
              = CA * (CB + 1 + Real.sqrt (d : ℝ) / 2) + CA * fractionalHolderConst d := by ring
          have hnn2 : (0 : ℝ) ≤ CA * (CB + 1 + Real.sqrt (d : ℝ) / 2) :=
            mul_nonneg hCApos.le (by linarith only [hCBpos.le, hsd0])
          linarith only [hexpb.le, hexpb.ge, hnn2]
        have h4 : ((81 * taylorConst d * Csch + 1) *
                (CA * fractionalHolderConst d + correctorLegConst d)) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
            ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
          mul_le_mul_of_nonneg_right (le_trans h3 hCrem) hb0
        linarith only [h1, h2.le, h2.ge, h4]
      -- step `.8` in the `ℕ`-cast shape of the harmonic-approximation input
      simp only [Int.cast_natCast] at hstep8
      -- the `3^{-n}` weight, distributed over the harmonic-approximation bound
      have h3n : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℤ)) := zpow_pos (by norm_num) _
      have h3nn : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (n : ℕ) = 1 := by
        rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
      have hJeq : (3 : ℝ) ^ (-(n : ℤ)) *
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0)
          = (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              s ^ (-3 / 2 : ℝ) * Ah else 0) := by
        rw [if_pos hBT, if_pos hBT]
        calc (3 : ℝ) ^ (-(n : ℤ)) * (s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ (n : ℕ) * Ah)
            = ((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (n : ℕ)) * (s ^ (-3 / 2 : ℝ) * Ah) := by ring
          _ = s ^ (-3 / 2 : ℝ) * Ah := by rw [h3nn, one_mul]
      have hfront : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))
          = (3 : ℝ) ^ (s * (n : ℝ)) := by
        rw [← Real.rpow_intCast (3 : ℝ) (-(n : ℤ)), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        push_cast
        ring
      have hXHle : (3 : ℝ) ^ (-(n : ℤ)) *
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0)
          ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
             else 0) := by
        rw [if_pos hBT, if_pos hBT]
        have hre : (3 : ℝ) ^ (-(n : ℤ)) *
              (CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh)
            = CA * (s ^ (-4 : ℝ) * ((3 : ℝ) ^ (-(n : ℤ)) *
                ((3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh))) := by ring
        rw [hre]
        exact mul_le_mul_of_nonneg_left hstep8 hCApos.le
      have hCAErr : (0 : ℝ) ≤ CA * s ^ (-2 : ℝ) * Err :=
        mul_nonneg (mul_nonneg hCApos.le hss) hErr
      have hNterm : CA * s ^ (-2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) * N)
          ≤ CA * s ^ (-2 : ℝ) * Err * E +
            CA * s ^ (-2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl) := by
        have hstepN := mul_le_mul_of_nonneg_left hstep6 hCAErr
        linarith only [hstepN]
      have hDsD : (3 : ℝ) ^ (-(n : ℤ)) * Dv
          ≤ CA * s ^ (-2 : ℝ) * Err * E
            + CA * s ^ (-2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl)
            + CA * s ^ (-2 : ℝ) * Err *
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  s ^ (-3 / 2 : ℝ) * Ah else 0)
            + CA * s ^ (-8 : ℝ) * Tinv * (3 : ℝ) ^ (s * (n : ℝ)) * Fg
            + (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
               else 0) := by
        have hbase := mul_le_mul_of_nonneg_left hD h3n.le
        have hexp : (3 : ℝ) ^ (-(n : ℤ)) *
              (CA * s ^ (-2 : ℝ) * Err *
                  (N + (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0)) +
                CA * s ^ (-8 : ℝ) * Tinv * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg +
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0))
            = CA * s ^ (-2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) * N)
              + CA * s ^ (-2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) *
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0))
              + CA * s ^ (-8 : ℝ) * Tinv *
                  ((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))) * Fg
              + (3 : ℝ) ^ (-(n : ℤ)) *
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0) := by
          ring
        rw [hexp, hJeq, hfront] at hbase
        linarith only [hbase, hNterm, hXHle]
      -- the corrector leg joins the fourth line
      set XH : ℝ := (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
          CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
         else 0) + correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv with hXHdef
      set Ds : ℝ := (3 : ℝ) ^ (-(n : ℤ)) * Dv
          + correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv with hDsdef
      have hone' : excess ((n : ℤ) - (k : ℤ))
            (truncatedCube d m ((n : ℤ) - (k : ℤ)) x) u.toFun
          ≤ oneStepContractionConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E
            + oneStepRemainderConst d Csch k * Ds := by
        have hexp : oneStepRemainderConst d Csch k * Ds
            = oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-(n : ℤ)) * Dv)
              + oneStepRemainderConst d Csch k *
                (correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by
          rw [hDsdef]; ring
        linarith only [hone, hexp.le, hexp.ge]
      have hDs : Ds ≤ CA * s ^ (-2 : ℝ) * Err * E
            + CA * s ^ (-2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl)
            + CA * s ^ (-2 : ℝ) * Err *
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  s ^ (-3 / 2 : ℝ) * Ah else 0)
            + CA * s ^ (-8 : ℝ) * Tinv * (3 : ℝ) ^ (s * (n : ℝ)) * Fg + XH := by
        rw [hDsdef, hXHdef]
        linarith only [hDsD]
      have hKcle : oneStepContractionConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
          ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        have hpe : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (-(k : ℝ) / 2) := by
          rw [three_zpow_rpow_half_eq]
          push_cast
          ring_nf
        rw [hpe]
        exact mul_le_mul_of_nonneg_right hCcontr hpow1
      have hs3one : (1 : ℝ) ≤ s ^ (-7 / 2 : ℝ) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hs0
          (by linarith only [hs4]) (show (-7 / 2 : ℝ) ≤ 0 by norm_num)
        simpa using h
      have hXHfin : oneStepRemainderConst d Csch k * XH
          ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv
             else 0) := by
        rw [hXHdef, if_pos hBT, if_pos hBT]
        have hbase : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) :=
          mul_nonneg hs3 (mul_nonneg hpow4 hHh)
        have hsecond : correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv
            ≤ correctorLegConst d * (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)) := by
          have hph : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv := mul_nonneg hpow4 hHh
          have h1 : (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv
              ≤ s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by
            have := mul_le_mul_of_nonneg_right hs3one hph
            linarith only [this]
          have h2 := mul_le_mul_of_nonneg_left h1 hcorr0
          linarith only [h2]
        have hrewrite : oneStepRemainderConst d Csch k *
              (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
                + correctorLegConst d * (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)))
            = (oneStepRemainderConst d Csch k *
                (CA * fractionalHolderConst d + correctorLegConst d)) *
              (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)) := by ring
        have hmid : (oneStepRemainderConst d Csch k *
              (CA * fractionalHolderConst d + correctorLegConst d)) *
            (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))
            ≤ (C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
              (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)) :=
          mul_le_mul_of_nonneg_right hbHolder hbase
        have hfin : (C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
              (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))
            = C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv := by ring
        have hleg := mul_le_mul_of_nonneg_left hsecond hKr0
        have hsum : oneStepRemainderConst d Csch k *
              (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
                + correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
            ≤ oneStepRemainderConst d Csch k *
              (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
                + correctorLegConst d * (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))) := by
          have hd1' : oneStepRemainderConst d Csch k *
                (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
                  + correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
              = oneStepRemainderConst d Csch k *
                  (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) *
                    (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))
                + oneStepRemainderConst d Csch k *
                  (correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by ring
          have hd2' : oneStepRemainderConst d Csch k *
                (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
                  + correctorLegConst d * (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)))
              = oneStepRemainderConst d Csch k *
                  (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) *
                    (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))
                + oneStepRemainderConst d Csch k *
                  (correctorLegConst d * (s ^ (-7 / 2 : ℝ) *
                    ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))) := by ring
          linarith only [hleg, hd1'.le, hd1'.ge, hd2'.le, hd2'.ge]
        linarith only [hsum, hrewrite.le, hrewrite.ge, hmid, hfin.le, hfin.ge]
      exact excessDecayCombine hEn hErr hSl hFg hTail hI1 heps0 hss hs15 hpow3 hKr0 hCApos.le
        hone' hDs hcapz hKcle hbCB hbSqrt hb3 hXHfin
    -- the crude branch `k < 6`: no harmonic input at all
    have hcrude := excess_truncatedCube_le (m := (m : ℤ)) (j := (n : ℤ) - (k : ℤ))
      (l := (n : ℤ)) (x := x) hx (by omega) (by omega) (by omega) hu_n
    rw [show (n : ℤ) - ((n : ℤ) - (k : ℤ)) = (k : ℤ) by ring] at hcrude
    have hcoef : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
        ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
      have hA1 : (3 : ℝ) ^ ((k : ℤ)) ≤ 243 := by
        calc (3 : ℝ) ^ ((k : ℤ)) ≤ (3 : ℝ) ^ (5 : ℤ) :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = 243 := by norm_num
      have hA2 : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
        refine Real.sqrt_le_sqrt ?_
        calc ((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d ≤ ((3 : ℝ) ^ (7 : ℤ)) ^ d :=
              pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
                (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
          _ = (3 : ℝ) ^ (7 * d) := by
              rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast, ← pow_mul]
      have hA3 : (3 : ℝ) ^ (-(3 : ℝ)) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hkr : (k : ℝ) ≤ 5 := by exact_mod_cast (by omega : k ≤ 5)
        linarith
      have hA4 : (3 : ℝ) ^ (-(3 : ℝ)) = 1 / 27 := by
        rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      have hsq0 : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := Real.sqrt_nonneg _
      have hsq1 : (0 : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) := Real.sqrt_nonneg _
      have hleft : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
          ≤ 243 * Real.sqrt ((3 : ℝ) ^ (7 * d)) :=
        mul_le_mul hA1 hA2 hsq1 (by norm_num)
      have hmid : (243 : ℝ) * Real.sqrt ((3 : ℝ) ^ (7 * d))
          = (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27) := by
        rw [show ((3 : ℝ) ^ (8 : ℕ)) = 6561 by norm_num]; ring
      have hright : (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27)
          ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        rw [← hA4]
        refine mul_le_mul hCcrude hA3 (by rw [hA4]; norm_num) hC0
      linarith only [hleft, hmid, hright]
    have hstepc : excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m (n - k) x) u.toFun
        ≤ C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) *
            excess (n : ℤ) (truncatedCube d m n x) u.toFun := by
      have h1 : excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m (n - k) x) u.toFun
          ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) * excess (n : ℤ) (truncatedCube d m n x) u.toFun :=
        le_trans hcrude (mul_le_mul_of_nonneg_right hcoef hEn)
      have h2 : C * (3 : ℝ) ^ (-(k : ℝ) / 2) ≤ C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) :=
        mul_le_mul_of_nonneg_left (by linarith only [hP]) hC0
      exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hEn)
    exact le_trans (le_trans (le_trans hstepc (le_add_of_nonneg_right hT2))
      (le_add_of_nonneg_right hT3)) (le_add_of_nonneg_right hI2)
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension hd2⟩

/-- The source-shaped cutoff boundary excess-decay input, reduced to the one
remaining cutoff boundary harmonic-comparison proposition. -/
theorem belowCutoffBoundaryExcessDecay_of_harmonic (d : ℕ)
    (hharm : BoundaryCutoffHarmonicApproximationInputV6 d) :
    BoundaryCutoffHolderExcessDecayBoundaryInputV4 d :=
  belowCutoffBoundaryExcessDecay_of_harmonic_and_cap d hharm
    (belowCutoffMathcalECapInput_holds d)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
