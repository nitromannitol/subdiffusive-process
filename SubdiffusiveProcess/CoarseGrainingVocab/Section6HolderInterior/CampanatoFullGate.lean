module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.CampanatoFull
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.IterationAppliedGate

@[expose] public section

/-!
# Interior Hölder Step 5, with the interior gate as an explicit hypothesis

The interior mirror of `Section6Holder.exists_holderCampanatoFull`.  Both
interval budgets are the landed ones; with the two datum slots at `0` the
defect budget collapses to its single forcing term, so the conclusion carries
no datum norm at all.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- `e.Campanato.full.domain` on the interior branch, before choosing `C₁`. -/
theorem exists_interiorHolderCampanatoFullGate (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d) :
    ∃ Cstep K Citer : ℝ, 0 < Cstep ∧ 0 < K ∧ 0 < Citer ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ epsilon ∈ Set.Icc
          (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
      ∀ lambda : ℝ, 0 ≤ lambda → M.delta ^ 2 ≤ lambda → epsilon ^ 8 ≤ lambda →
      ∀ k : ℕ, 0 < k → ∀ theta ∈ Set.Ioo (0 : ℝ) 1,
      theta ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      Cstep * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsilon) ≤ theta ^ k →
      ∀ L domain n top : ℕ, n < top → top + 5 ≤ domain → domain ≤ L →
      ∀ z ∈ cube d domain,
      (∀ j : ℕ, j ≤ top →
        ¬ BoundaryTouches (truncatedCube d domain (j : ℤ) z) (cube d domain)) →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      (∑ i ∈ Finset.Icc n domain,
          accumulatedError M none i z Section6Stopping.holderStoppingS omega) ≤
        lambda * ((domain : ℝ) - (n : ℝ)) →
      (∑ i ∈ Finset.Icc n domain,
          ((1 : ℝ) - if omega ∈ goodEvent M none i z epsilon
            Section6Stopping.holderStoppingS then 1 else 0)) <
        1 + lambda * ((domain : ℝ) - (n : ℝ)) →
      ∀ exponential : ℝ, 0 ≤ exponential →
      (∀ j ∈ Finset.Icc n top,
        tailCoefficientCubeAverage M L domain omega /
            tailAverage M L (j + 2) omega (translatedCube d (j + 2 : ℕ) z) ≤
          exponential) →
      ∀ (u : H1Function (openCubeSet (originCube d domain))) (g : Vec d → Vec d),
      IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (cube d domain) u g →
      MemHolder (cube d domain) (1 / 2) g →
      let Keps := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K
      let Kforce := Cstep * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
      let topForcing := (tailCoefficientCubeAverage M L domain omega)⁻¹ *
        (3 : ℝ) ^ ((domain : ℝ) / 2) *
        holderSeminormOn (cube d domain) (1 / 2) g
      let Ebudget := 3 * Keps * lambda * ((domain : ℝ) - (n : ℝ) + 1)
      let Dbudget := (5 / 2 : ℝ) * Kforce *
        (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
        exponential * topForcing
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
    exists_interiorHolderIterationAppliedGate d hExcess
  refine ⟨Cstep, K, Citer, hCstep, hK, hCiter, ?_⟩
  intro M hsmall epsilon hepsilon lambda hlambda hdelta hepsilon8 k hk theta htheta
    hthetak hcontract L domain n top hntop htopDomain hdomainL z hz hgate omega
    herrors hfail exponential hE0 hratio u g hsol hg
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
  let Ebudget := 3 * Keps * lambda * ((domain : ℝ) - (n : ℝ) + 1)
  let Dbudget := (5 / 2 : ℝ) * Kforce *
    (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) * exponential * topForcing
  let bad := holderBadScales M epsilon Section6Stopping.holderStoppingS n top k z omega
  let epsRow := holderIterationEpsilon Keps M epsilon
    Section6Stopping.holderStoppingS z omega
  let defectRow := holderIterationDefect Kforce Kmean Kboundary exponential topForcing
    0 0 Keps M epsilon Section6Stopping.holderStoppingS domain z omega
  let A := Citer * (k + 1) * (bad.card + 1) +
    Citer * ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow j
  let Abar := Citer * (k + 1) *
      ((k : ℝ) + 2 + lambda * ((domain : ℝ) - (n : ℝ))) + Citer * Ebudget
  have hcore := happly M hsmall epsilon hepsilon lambda hlambda hdelta hepsilon8
    k hk theta htheta hthetak hcontract L domain n top hntop htopDomain hdomainL
    z hz hgate omega herrors hfail exponential hE0 hratio u g hsol hg
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
  have hbudgets := holderIteration_interval_budgets hKforce hKmean hKboundary
    hE0 htopForcing (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) hKeps hepsilon0
    M domain n top hlambda hdelta hepsilon8 z omega (Nat.le_of_lt hntop)
    (by omega) herrors
  dsimp only at hbudgets
  have hA := holderIterationExponent_le hKeps hCiter.le M domain n top k hlambda
    hdelta hepsilon8 z omega (Nat.le_of_lt hntop) (by omega) herrors hfail
  dsimp only at hA
  have hdef0 : 0 ≤ ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), defectRow j := by
    apply Finset.sum_nonneg
    intro j _
    exact holderIterationDefect_nonneg hKforce hKmean hKboundary hE0 htopForcing
      le_rfl le_rfl hKeps hepsilon0 M domain z omega j
  have hDle : (∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), defectRow j) ≤ Dbudget := by
    have := hbudgets.2
    simp only [mul_zero, zero_mul, add_zero] at this
    simpa only [defectRow, Dbudget] using this
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

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
