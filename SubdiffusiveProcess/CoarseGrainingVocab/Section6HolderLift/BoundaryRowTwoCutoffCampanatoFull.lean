module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffIterationApplied
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.IterationApplied
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.BadScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffInputs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.IterationFamilies

@[expose] public section

/-!
# Hölder Step 5: full-domain Campanato estimate

This module combines the applied iteration lemma with the two concrete
interval budgets.  It deliberately retains the explicit exponential and
dimension-only constants; the subsequent parameter module performs the
single absorption into the printed Hölder power.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section

variable {L : ℕ}
attribute [local instance] Classical.propDecidable

/-- `e.Campanato.full.domain` before choosing `C₁`: the exact slope output
of iteration with both summed defects inserted. -/
theorem exists_boundaryRowTwoCutoffCampanatoFull (d : ℕ) [NeZero d]
    (hExcess : BoundaryCutoffHolderExcessDecayInputV4 d) :
    ∃ Cstep K Citer : ℝ, 0 < Cstep ∧ 0 < K ∧ 0 < Citer ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ epsilon ∈ Set.Icc
          (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
      ∀ lambda : ℝ, 0 ≤ lambda → M.delta ^ 2 ≤ lambda → epsilon ^ 8 ≤ lambda →
      ∀ k : ℕ, 0 < k → ∀ theta ∈ Set.Ioo (0 : ℝ) 1,
      theta ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      Cstep * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsilon) ≤ theta ^ k →
      ∀ L domain n top : ℕ, n < top → top + 5 ≤ domain → ∀ z ∈ cube d domain,
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      (∑ i ∈ Finset.Icc n domain,
          accumulatedError M (some L) i z Section6Stopping.holderStoppingS omega) ≤
        lambda * ((domain : ℝ) - (n : ℝ)) →
      (∑ i ∈ Finset.Icc n domain,
          ((1 : ℝ) - if omega ∈ goodEvent M (some L) i z epsilon
            Section6Stopping.holderStoppingS then 1 else 0)) <
        1 + lambda * ((domain : ℝ) - (n : ℝ)) →
      ∀ exponential : ℝ, 0 ≤ exponential →
      (∀ j ∈ Finset.Icc n top,
        tailCoefficientCubeAverage M L domain omega /
            tailAverage M L (j + 2) omega (translatedCube d (j + 2 : ℕ) z) ≤
          exponential) →
      ∀ (u h : H1Function (openCubeSet (originCube d domain))) (g : Vec d → Vec d),
      IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (originCube d domain) u h g →
      MemHolder (cube d domain) (1 / 2) g →
      MemHolder (cube d domain) (1 / 2) h.grad →
      let Keps := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K
      let Kforce := Cstep * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
      let Kmean := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)
      let Kboundary := Cstep * (1 / 4 : ℝ) ^ (-3 : ℤ) *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
      let topForcing := (tailCoefficientCubeAverage M L domain omega)⁻¹ *
        (3 : ℝ) ^ ((domain : ℝ) / 2) *
        holderSeminormOn (cube d domain) (1 / 2) g
      let topBoundary := (3 : ℝ) ^ ((domain : ℝ) / 2) *
        holderSeminormOn (cube d domain) (1 / 2) h.grad
      let boundaryTop :=
        if BoundaryTouches (truncatedCube d domain top z) (cube d domain) then (1 : ℝ) else 0
      let Ebudget := 3 * Keps * lambda * ((domain : ℝ) - (n : ℝ) + 1)
      let Dbudget :=
        (5 / 2 : ℝ) * Kforce *
            (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
            exponential * topForcing +
          Kmean * Ebudget * vectorSupNormOn (cube d domain) h.grad * boundaryTop +
          (5 / 2 : ℝ) * Kboundary *
            (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
            topBoundary * boundaryTop
      let Abar := Citer * (k + 1) *
          ((k : ℝ) + 2 + lambda * ((domain : ℝ) - (n : ℝ))) +
        Citer * Ebudget
      (3 : ℝ) ^ (-(n : ℤ)) *
          normalizedL2On (truncatedCube d domain n z)
            (fun x ↦ u.toFun x - averageOn (truncatedCube d domain n z) u.toFun) ≤
        Real.exp Abar *
          ((3 : ℝ) ^ (-(top : ℤ)) *
              normalizedL2On (truncatedCube d domain top z)
                (fun x ↦ u.toFun x - averageOn
                  (truncatedCube d domain top z) u.toFun) + Dbudget) := by
  obtain ⟨Cstep, K, Citer, hCstep, hK, hCiter, happly⟩ :=
    exists_boundaryRowTwoCutoffIterationApplied d hExcess
  refine ⟨Cstep, K, Citer, hCstep, hK, hCiter, ?_⟩
  intro M hsmall epsilon hepsilon lambda hlambda hdelta hepsilon8 k hk theta htheta
    hthetak hcontract L domain n top hntop htopDomain  z hz omega
    herrors hfail exponential hE0 hratio u h g hsol hg hh
  dsimp only
  let Keps := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K
  let Kforce := Cstep * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
  let Kmean := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)
  let Kboundary := Cstep * (1 / 4 : ℝ) ^ (-3 : ℤ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
  let topForcing := (tailCoefficientCubeAverage M L domain omega)⁻¹ *
    (3 : ℝ) ^ ((domain : ℝ) / 2) * holderSeminormOn (cube d domain) (1 / 2) g
  let topBoundary := (3 : ℝ) ^ ((domain : ℝ) / 2) *
    holderSeminormOn (cube d domain) (1 / 2) h.grad
  let boundaryTop :=
    if BoundaryTouches (truncatedCube d domain top z) (cube d domain) then (1 : ℝ) else 0
  let Ebudget := 3 * Keps * lambda * ((domain : ℝ) - (n : ℝ) + 1)
  let Dbudget :=
    (5 / 2 : ℝ) * Kforce *
        (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
        exponential * topForcing +
      Kmean * Ebudget * vectorSupNormOn (cube d domain) h.grad * boundaryTop +
      (5 / 2 : ℝ) * Kboundary *
        (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
        topBoundary * boundaryTop
  let bad := holderBadScales_cut L M epsilon Section6Stopping.holderStoppingS n top k z omega
  let epsRow := holderIterationEpsilon_cut L Keps M epsilon
    Section6Stopping.holderStoppingS z omega
  let defectRow := holderIterationDefect_cut L Kforce Kmean Kboundary exponential topForcing
    (vectorSupNormOn (cube d domain) h.grad) topBoundary Keps M epsilon
    Section6Stopping.holderStoppingS domain z omega
  let A := Citer * (k + 1) * (bad.card + 1) +
    Citer * ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow j
  let Abar := Citer * (k + 1) *
      ((k : ℝ) + 2 + lambda * ((domain : ℝ) - (n : ℝ))) + Citer * Ebudget
  have hcore := happly M hsmall epsilon hepsilon lambda hlambda hdelta hepsilon8
    k hk theta htheta hthetak hcontract L domain n top hntop htopDomain
    z hz omega herrors hfail exponential hE0 hratio u h g hsol hg hh
  dsimp only at hcore
  have hepsilon0 : 0 ≤ epsilon :=
    (mul_nonneg (inv_nonneg.mpr Section6Stopping.holderStoppingS_pos.le)
      (sq_nonneg M.delta)).trans hepsilon.1
  have hKeps : 0 ≤ Keps := by dsimp only [Keps]; positivity
  have hKforce : 0 ≤ Kforce := by
    have hfrac := Section6ExcessDecay.fractionalHolderConst_nonneg d
    dsimp only [Kforce]
    positivity
  have hKmean : 0 ≤ Kmean := by dsimp only [Kmean]; positivity
  have hKboundary : 0 ≤ Kboundary := by dsimp only [Kboundary]; positivity
  have htopForcing : 0 ≤ topForcing := by
    dsimp only [topForcing]
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (tailCoefficientCubeAverage_pos M L domain omega).le)
        (Real.rpow_nonneg (by norm_num) _))
      (holderSeminormOn_nonneg hg)
  have htopBoundary : 0 ≤ topBoundary := by
    dsimp only [topBoundary]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (holderSeminormOn_nonneg hh)
  have hsup : 0 ≤ vectorSupNormOn (cube d domain) h.grad :=
    vectorSupNormOn_cube_nonneg hh
  have hbudgets := holderIteration_interval_budgets_cut hKforce hKmean hKboundary
    hE0 htopForcing hsup htopBoundary hKeps hepsilon0 M domain n top hlambda
    hdelta hepsilon8 z omega (Nat.le_of_lt hntop) (by omega) herrors
  dsimp only at hbudgets
  have hA := holderIterationExponent_le_cut hKeps hCiter.le M domain n top k hlambda
    hdelta hepsilon8 z omega (Nat.le_of_lt hntop) (by omega) herrors hfail
  dsimp only at hA
  have hdef0 : 0 ≤ ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), defectRow j := by
    apply Finset.sum_nonneg
    intro j _
    exact holderIterationDefect_nonneg_cut hKforce hKmean hKboundary hE0 htopForcing
      hsup htopBoundary hKeps hepsilon0 M domain z omega j
  have hDle : (∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), defectRow j) ≤
      Dbudget := by
    simpa only [defectRow, Dbudget, boundaryTop, Ebudget] using hbudgets.2
  have hD0 : 0 ≤ Dbudget := hdef0.trans hDle
  have htopOsc0 : 0 ≤ (3 : ℝ) ^ (-(top : ℤ)) *
      normalizedL2On (truncatedCube d domain top z)
        (fun x ↦ u.toFun x - averageOn (truncatedCube d domain top z) u.toFun) := by
    have hnorm := Section6Iteration.normalizedL2On_nonneg
      (d := d) (truncatedCube d domain top z)
        (fun x ↦ u.toFun x - averageOn (truncatedCube d domain top z) u.toFun)
    have hpow : 0 ≤ (3 : ℝ) ^ (-(top : ℤ)) := by positivity
    exact mul_nonneg hpow hnorm
  change (3 : ℝ) ^ (-(n : ℤ)) *
      normalizedL2On (truncatedCube d domain n z)
        (fun x ↦ u.toFun x - averageOn (truncatedCube d domain n z) u.toFun) ≤
    Real.exp Abar *
      ((3 : ℝ) ^ (-(top : ℤ)) *
          normalizedL2On (truncatedCube d domain top z)
            (fun x ↦ u.toFun x - averageOn
              (truncatedCube d domain top z) u.toFun) + Dbudget)
  calc
    _ ≤ Real.exp A *
        ((3 : ℝ) ^ (-(top : ℤ)) *
            normalizedL2On (truncatedCube d domain top z)
              (fun x ↦ u.toFun x - averageOn
                (truncatedCube d domain top z) u.toFun) +
          ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), defectRow j) := hcore.1
    _ ≤ Real.exp A *
        ((3 : ℝ) ^ (-(top : ℤ)) *
            normalizedL2On (truncatedCube d domain top z)
              (fun x ↦ u.toFun x - averageOn
                (truncatedCube d domain top z) u.toFun) + Dbudget) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hDle)
        (Real.exp_pos A).le
    _ ≤ Real.exp Abar *
        ((3 : ℝ) ^ (-(top : ℤ)) *
            normalizedL2On (truncatedCube d domain top z)
              (fun x ↦ u.toFun x - averageOn
                (truncatedCube d domain top z) u.toFun) + Dbudget) := by
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hA)
        (add_nonneg htopOsc0 hD0)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
