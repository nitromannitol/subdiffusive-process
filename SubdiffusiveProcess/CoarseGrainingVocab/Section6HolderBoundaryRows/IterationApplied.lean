import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.ReadyStep
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.IterationFamilies
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.TruncatedIteration

/-!
# Hölder Step 4: application of the iteration lemma

This is the literal assembly at `e.iteration.slope.applied` and
`e.excess.decay.applied`.  The only hypotheses beyond the PDE data are the
already established stopped rows, the coefficient-ratio row, and the
dimension-only contraction inequality.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The concrete recurrence families and bad set satisfy every hypothesis of
the proved iteration lemma on the truncated-cube carrier. -/
theorem exists_boundaryHolderIterationApplied (d : ℕ) [NeZero d]
    (hExcess : BoundaryHolderExcessDecayInput d) :
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
          (1 / 4 : ℝ) ^ (-2 : ℝ) * epsilon) ≤ theta ^ k →
      ∀ L domain n top : ℕ, n < top → top + 5 ≤ domain → domain ≤ L →
      ∀ z ∈ cube d domain,
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      (∑ i ∈ Finset.Icc n domain,
          accumulatedError M none i z Section6Stopping.holderStoppingS omega) ≤
        lambda * ((domain : ℝ) - (n : ℝ)) →
      (∑ i ∈ Finset.Icc n domain,
          (1 - if omega ∈ goodEvent M none i z epsilon
            Section6Stopping.holderStoppingS then 1 else 0)) <
        1 + lambda * ((domain : ℝ) - (n : ℝ)) →
      ∀ exponential : ℝ, 0 ≤ exponential →
      (∀ j ∈ Finset.Icc n top,
        tailCoefficientCubeAverage M L domain omega /
            tailAverage M L (j + 2) omega (translatedCube d (j + 2 : ℕ) z) ≤
          exponential) →
      ∀ (u h : H1Function (openCubeSet (originCube d domain))) (g : Vec d → Vec d),
      IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (originCube d domain) u h g →
      MemHolder (cube d domain) (1 / 2) g →
      MemHolder (cube d domain) (1 / 2) h.grad →
      let Keps := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        (1 / 4 : ℝ) ^ (-2 : ℝ) * K
      let Kforce := Cstep * (1 / 4 : ℝ) ^ (-8 : ℝ) *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
      let Kmean := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)
      let Kboundary := Cstep * (1 / 4 : ℝ) ^ (-7 / 2 : ℝ) *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
      let topForcing := (tailCoefficientCubeAverage M L domain omega)⁻¹ *
        (3 : ℝ) ^ ((domain : ℝ) / 2) *
        holderSeminormOn (cube d domain) (1 / 2) g
      let topBoundary := (3 : ℝ) ^ ((domain : ℝ) / 2) *
        holderSeminormOn (cube d domain) (1 / 2) h.grad
      let bad := holderBadScales M epsilon Section6Stopping.holderStoppingS
        n top k z omega
      let epsRow := holderIterationEpsilon Keps M epsilon
        Section6Stopping.holderStoppingS z omega
      let defectRow := holderIterationDefect Kforce Kmean Kboundary exponential
        topForcing (vectorSupNormOn (cube d domain) h.grad) topBoundary Keps M epsilon
        Section6Stopping.holderStoppingS domain z omega
      let A := Citer * (k + 1) * (bad.card + 1) +
        Citer * ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow j
      (3 : ℝ) ^ (-(n : ℤ)) *
          normalizedL2On (truncatedCube d domain n z)
            (fun x ↦ u.toFun x - averageOn (truncatedCube d domain n z) u.toFun) ≤
        Real.exp A *
          ((3 : ℝ) ^ (-(top : ℤ)) *
              normalizedL2On (truncatedCube d domain top z)
                (fun x ↦ u.toFun x - averageOn
                  (truncatedCube d domain top z) u.toFun) +
            ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), defectRow j) ∧
      ∀ R : ℝ, 0 ≤ R →
        (∀ j ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow j ≤ R) →
        excess n (truncatedCube d domain n z) u.toFun ≤
          theta ^ (-Citer * (k + 1) * (bad.card + 1)) * Real.exp A *
            (theta ^ ((top : ℤ) - (n : ℤ)) *
                excess top (truncatedCube d domain top z) u.toFun +
              R * (3 : ℝ) ^ (-(top : ℤ)) *
                normalizedL2On (truncatedCube d domain top z)
                  (fun x ↦ u.toFun x - averageOn
                    (truncatedCube d domain top z) u.toFun) +
              (1 + R) *
                ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), defectRow j) := by
  obtain ⟨Cstep, K, hCstep, hK, hready⟩ := exists_boundaryHolderReadyStep hExcess
  obtain ⟨Citer, hCiter, hiter⟩ := truncatedCube_iteration d
  refine ⟨Cstep, K, Citer, hCstep, hK, hCiter, ?_⟩
  intro M hsmall epsilon hepsilon lambda hlambda hdelta hepsilon8 k hk theta htheta
    hthetak hcontract L domain n top hntop htopDomain hdomainL z hz omega
    herrors hfail exponential hE0 hratio u h g hsol hg hh
  dsimp only
  let Keps := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-2 : ℝ) * K
  let Kforce := Cstep * (1 / 4 : ℝ) ^ (-8 : ℝ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
  let Kmean := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)
  let Kboundary := Cstep * (1 / 4 : ℝ) ^ (-7 / 2 : ℝ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
  let topForcing := (tailCoefficientCubeAverage M L domain omega)⁻¹ *
    (3 : ℝ) ^ ((domain : ℝ) / 2) * holderSeminormOn (cube d domain) (1 / 2) g
  let topBoundary := (3 : ℝ) ^ ((domain : ℝ) / 2) *
    holderSeminormOn (cube d domain) (1 / 2) h.grad
  let bad := holderBadScales M epsilon Section6Stopping.holderStoppingS n top k z omega
  let epsRow := holderIterationEpsilon Keps M epsilon
    Section6Stopping.holderStoppingS z omega
  let defectRow := holderIterationDefect Kforce Kmean Kboundary exponential topForcing
    (vectorSupNormOn (cube d domain) h.grad) topBoundary Keps M epsilon
    Section6Stopping.holderStoppingS domain z omega
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
  have hnonneg : ∀ j ∈ Finset.Icc (n : ℤ) (top : ℤ),
      0 ≤ epsRow j ∧ 0 ≤ defectRow j := by
    intro j _
    exact ⟨holderIterationEpsilon_nonneg hKeps hepsilon0 M z omega j,
      holderIterationDefect_nonneg hKforce hKmean hKboundary hE0 htopForcing
        hsup htopBoundary hKeps hepsilon0 M domain z omega j⟩
  have hrec : ∀ j ∈ Finset.Icc (n : ℤ) (top : ℤ), j ∉ bad →
      ∀ ell : Affine d,
        ell ∈ affineMinimizers (truncatedCube d domain j z) u.toFun →
        excess (j - k) (truncatedCube d domain (j - k) z) u.toFun ≤
          theta ^ k * excess j (truncatedCube d domain j z) u.toFun +
            epsRow j * Real.sqrt (vecNormSq ell.slope) + defectRow j := by
    intro j hj hnot ell hell
    have hj0 : 0 ≤ j := (Int.natCast_nonneg n).trans (Finset.mem_Icc.1 hj).1
    have hjcast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
    obtain ⟨hjk, hgood⟩ := notMem_holderBadScales M epsilon
      Section6Stopping.holderStoppingS z omega hj hnot
    have hkj : k ≤ j.toNat := le_trans (Nat.le_add_left k n) hjk
    have hnj : n ≤ j.toNat := by
      have := (Finset.mem_Icc.1 hj).1
      rw [← hjcast] at this
      exact_mod_cast this
    have hjtop : j.toNat ≤ top := by
      have := (Finset.mem_Icc.1 hj).2
      rw [← hjcast] at this
      exact_mod_cast this
    have hjdomain : j.toNat + 5 ≤ domain := by omega
    have hratioJ := hratio j.toNat (Finset.mem_Icc.2 ⟨hnj, hjtop⟩)
    have hellNat : ell ∈ affineMinimizers
        (truncatedCube d domain j.toNat z) u.toFun := by
      rw [hjcast]
      exact hell
    have hstep := hready M hsmall epsilon hepsilon k hk theta L domain n j.toNat
      hnj hkj hdomainL hjdomain z hz omega u h g hsol hg hh ell
    have hstep' := hstep hellNat hgood hcontract exponential hE0 hratioJ
    dsimp only at hstep'
    dsimp only [epsRow, defectRow]
    rw [holderIterationEpsilon_of_nonneg _ _ _ _ _ _ hj0,
      holderIterationDefect_of_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj0]
    rw [← hjcast]
    norm_num only [Int.toNat_natCast, Nat.cast_sub hkj]
    norm_num only at hstep'
    dsimp only [Keps, Kforce, Kmean, Kboundary, topForcing, topBoundary]
    norm_num only
    exact hstep'
  exact hiter k hk theta htheta hthetak domain n top hntop
    (by omega) z hz u bad (holderBadScales_subset_Icc M epsilon
      Section6Stopping.holderStoppingS n top k z omega) epsRow defectRow
      hnonneg hrec

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows
