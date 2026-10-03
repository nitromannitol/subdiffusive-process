module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffCampanatoFull
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.CampanatoFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CampanatoFamily

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The printed boundary Campanato family: the stopped rows are based at `n`,
while the output window scale `n'` and top scale are free above it. -/
theorem exists_boundaryRowTwoCutoffCampanatoFamily (d : ℕ) [NeZero d]
    (hExcess : Section6ExcessDecay.BoundaryCutoffHolderExcessDecayInputV4 d) :
    ∃ Cstep K Citer : ℝ, 0 < Cstep ∧ 0 < K ∧ 0 < Citer ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ epsilon ∈ Set.Icc
          (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
      ∀ lambda lambda' : ℝ, 0 ≤ lambda' → M.delta ^ 2 ≤ lambda' →
        epsilon ^ 8 ≤ lambda' →
      ∀ k : ℕ, 0 < k → ∀ theta ∈ Set.Ioo (0 : ℝ) 1,
      theta ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      Cstep * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsilon) ≤ theta ^ k →
      ∀ L domain n n' top : ℕ, n ≤ n' → n' < top → top + 5 ≤ domain →

      ∀ z ∈ cube d domain,
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      (∑ i ∈ Finset.Icc n domain,
          accumulatedError M (some L) i z Section6Stopping.holderStoppingS omega) ≤
        lambda * ((domain : ℝ) - (n : ℝ)) →
      (∑ i ∈ Finset.Icc n domain,
          ((1 : ℝ) - if omega ∈ goodEvent M (some L) i z epsilon
            Section6Stopping.holderStoppingS then 1 else 0)) <
        1 + lambda * ((domain : ℝ) - (n : ℝ)) →
      lambda * ((domain : ℝ) - (n : ℝ)) ≤
        lambda' * ((domain : ℝ) - (n' : ℝ)) →
      ∀ exponential : ℝ, 0 ≤ exponential →
      (∀ j ∈ Finset.Icc n' top,
        tailCoefficientCubeAverage M L domain omega /
            tailAverage M L (j + 2) omega (translatedCube d (j + 2 : ℕ) z) ≤
          exponential) →
      ∀ (u h : H1Function (openCubeSet (originCube d domain)))
        (g : Vec d → Vec d),
      IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
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
        if BoundaryTouches (truncatedCube d domain top z) (cube d domain) then
          (1 : ℝ) else 0
      let Ebudget := 3 * Keps * lambda' * ((domain : ℝ) - (n' : ℝ) + 1)
      let Dbudget :=
        (5 / 2 : ℝ) * Kforce *
            (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
            exponential * topForcing +
          Kmean * Ebudget * vectorSupNormOn (cube d domain) h.grad * boundaryTop +
          (5 / 2 : ℝ) * Kboundary *
            (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
            topBoundary * boundaryTop
      let Abar := Citer * (k + 1) *
          ((k : ℝ) + 2 + lambda' * ((domain : ℝ) - (n' : ℝ))) +
        Citer * Ebudget
      (3 : ℝ) ^ (-(n' : ℤ)) *
          normalizedL2On (truncatedCube d domain n' z)
            (fun x ↦ u.toFun x - averageOn (truncatedCube d domain n' z) u.toFun) ≤
        Real.exp Abar *
          ((3 : ℝ) ^ (-(top : ℤ)) *
              normalizedL2On (truncatedCube d domain top z)
                (fun x ↦ u.toFun x - averageOn
                  (truncatedCube d domain top z) u.toFun) + Dbudget) := by
  obtain ⟨Cstep, K, Citer, hCstep, hK, hCiter, hfull⟩ :=
    exists_boundaryRowTwoCutoffCampanatoFull d hExcess
  refine ⟨Cstep, K, Citer, hCstep, hK, hCiter, ?_⟩
  intro M hdelta epsilon heps lambda lambda' hlam0 hlamd hlame k hk theta htheta
    hthetak hstep L domain n n' top hnn hn'top htopdom z hz omega
    herr hfail hinfl exponential hexp0 hexp u h g hsol hg hh
  refine hfull M hdelta epsilon heps lambda' hlam0 hlamd hlame k hk theta htheta
    hthetak hstep L domain n' top hn'top htopdom z hz omega ?_ ?_
    exponential hexp0 hexp u h g hsol hg hh
  · exact le_trans
      (accumulatedError_row_restrict_cut M
        Section6Stopping.holderStoppingS n n' domain z omega hnn)
      (le_trans herr hinfl)
  · have hrestrict := failure_row_restrict_cut (L := L) M epsilon
      Section6Stopping.holderStoppingS n (n' - n) domain z omega
    rw [show n + (n' - n) = n' by omega] at hrestrict
    linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
