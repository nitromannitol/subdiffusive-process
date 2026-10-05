module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.CampanatoFull
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CampanatoFull
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RaisedFailureRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RaisedFailureRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.ExcessDecayInput

@[expose] public section

/-!
# The printed Campanato family: window scale free above the base scale

 (`e.Campanato.full.domain`) states the averaged
oscillation estimate

> for every `n, n', m'` with `n ≤ m - L(alpha,m)` and `n ≤ n' ≤ m' ≤ m - 5` and
> every `z ∈ 3^n Z^d ∩ cu_m`...

so the grid condition pins `z` to the grid of the **base** scale `n` — the scale
at which the stopping structure `B_z` is read — while the **window** scale `n'`
ranges freely above it.  Frozen row 1 is the specialization
`n' = ell`, `m' = m - 5`, `z = y` (the paper says exactly this ).

The proved `exists_interiorHolderCampanatoFull_cut` is already the printed estimate:
its centre binder is `z ∈ cube d (domain - 1)` with **no grid condition at all**.
What ties it to a single scale is not the Campanato step but its two *stopping*
hypotheses, which are read over `Finset.Icc n domain` with `n` the window scale.
Raising the window to `n'` therefore only needs those two rows restricted from
`Icc n domain` to `Icc n' domain` — both summands are nonnegative — together with
the rate inflation already used by `RaisedFailureRow`, since the restricted rows
must meet the smaller bound `lambda' * (domain - n')`.

This is the estimate row 2 consumes at the *selected* good scale, with the centre
on the base grid: precisely the paper's Step 6.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}
variable {L : ℕ}

/-- The accumulated-error row restricts to a raised base. -/
theorem accumulatedError_row_restrict_cut (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (n n' domain : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hnn : n ≤ n') :
    (∑ i ∈ Finset.Icc n' domain, accumulatedError M (some L) i z s omega) ≤
      ∑ i ∈ Finset.Icc n domain, accumulatedError M (some L) i z s omega := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  · intro i _ _
    exact Section6Holder.accumulatedError_nonneg M (some L) s i z omega

/-- **The printed Campanato family.**  The centre `z` carries the base scale `n`
through its stopping rows; the window scales `n'` and `top` are free above it. -/
theorem exists_interiorCampanatoFamily_cut (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput_cut d) :
    ∃ Cstep K Citer : ℝ, 0 < Cstep ∧ 0 < K ∧ 0 < Citer ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ epsilon ∈ Set.Icc
          (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
      ∀ lambda lambda' : ℝ, 0 ≤ lambda' → M.delta ^ 2 ≤ lambda' →
        epsilon ^ 8 ≤ lambda' →
      ∀ k : ℕ, 0 < k → ∀ theta ∈ Set.Ioo (0 : ℝ) 1,
      theta ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      Cstep * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (1 / 4 : ℝ) ^ (-2 : ℝ) * epsilon) ≤ theta ^ k →
      ∀ L domain n n' top : ℕ, n ≤ n' → n' < top → top + 5 ≤ domain →
        ∀ z ∈ cube d ((domain : ℤ) - 1),
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      -- the stopping rows at the **base** scale `n`
      (∑ i ∈ Finset.Icc n domain,
          accumulatedError M (some L) i z Section6Stopping.holderStoppingS omega) ≤
        lambda * ((domain : ℝ) - (n : ℝ)) →
      (∑ i ∈ Finset.Icc n domain,
          ((1 : ℝ) - if omega ∈ goodEvent M (some L) i z epsilon
            Section6Stopping.holderStoppingS then 1 else 0)) <
        1 + lambda * ((domain : ℝ) - (n : ℝ)) →
      -- the rate inflation paying for the raise
      lambda * ((domain : ℝ) - (n : ℝ)) ≤
        lambda' * ((domain : ℝ) - (n' : ℝ)) →
      ∀ exponential : ℝ, 0 ≤ exponential →
      (∀ j ∈ Finset.Icc n' top,
        tailCoefficientCubeAverage M L domain omega /
            tailAverage M L (j + 2) omega (translatedCube d (j + 2 : ℕ) z) ≤
          exponential) →
      ∀ (u : H1Function (openCubeSet (originCube d domain))) (g : Vec d → Vec d),
      IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (cube d domain) u g →
      MemHolder (cube d domain) (1 / 2) g →
      let Keps := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        (1 / 4 : ℝ) ^ (-2 : ℝ) * K
      let Kforce := Cstep * (1 / 4 : ℝ) ^ (-8 : ℝ) *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
      let topForcing := (tailCoefficientCubeAverage M L domain omega)⁻¹ *
        (3 : ℝ) ^ ((domain : ℝ) / 2) *
        holderSeminormOn (cube d domain) (1 / 2) g
      let Ebudget := 3 * Keps * lambda' * ((domain : ℝ) - (n' : ℝ) + 1)
      let Dbudget := (5 / 2 : ℝ) * Kforce *
        (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
        exponential * topForcing
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
    exists_interiorHolderCampanatoFull_cut d hExcess
  refine ⟨Cstep, K, Citer, hCstep, hK, hCiter, ?_⟩
  intro M hdelta epsilon heps lambda lambda' hlam0 hlamd hlame k hk theta htheta
    hthetak hstep L domain n n' top hnn hn'top htopdom  z hz omega
    herr hfail hinfl exponential hexp0 hexp u g hsol hg
  refine hfull M hdelta epsilon heps lambda' hlam0 hlamd hlame k hk theta htheta
    hthetak hstep L domain n' top hn'top htopdom  z hz omega ?_ ?_
    exponential hexp0 hexp u g hsol hg
  · exact le_trans
      (accumulatedError_row_restrict_cut M Section6Stopping.holderStoppingS
        n n' domain z omega hnn)
      (le_trans herr hinfl)
  · have hrestrict := failure_row_restrict_cut (L := L) M epsilon
      Section6Stopping.holderStoppingS n (n' - n) domain z omega
    rw [show n + (n' - n) = n' by omega] at hrestrict
    linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
