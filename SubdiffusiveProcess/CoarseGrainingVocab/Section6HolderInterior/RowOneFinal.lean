import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneOutput

/-!
# Frozen row 1 for the interior anchor

The deep-branch output of `RowOneOutput` and the shallow-branch window bound of
`RowOneWindows`, joined by `RowOneJoint.interiorRowOne_combinedJoint`.

In the shallow range the Campanato iteration is not run at all, so the
absorption slots are filled with `Aexp = exponential = 1`; the absorption
hypothesis is then `1 ≤ Cabs · 3^{(1-α)(m-ell)/4}`, which holds because
`Cabs ≥ 1` and the exponent is nonnegative.

**This closes frozen row 1 for the interior anchor**, conditional only on
`InteriorHolderExcessDecayInput`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **Frozen row 1 for the interior anchor.** -/
theorem exists_interiorRowOne (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d) :
    ∃ (C1 C2 Crow : ℝ), 0 < C1 ∧ 1 ≤ C2 ∧ 0 ≤ Crow ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ^ 8 ≤
          Section6Stopping.holderStoppingLambda C1 alpha →
        0 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingLambda C1 alpha < 1 →
      ∀ L m : ℕ, m ≤ L →
      ∀ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
          (cube d (m : ℤ)) u g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
      ∀ n : ℕ,
        (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) 0 m ω : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
      ∀ x : Vec d, x ∈ cube d ((m : ℤ) - 1) →
      ∀ ell : ℕ, ell ≤ n →
      ∀ y : Vec d, OnTriadicGrid ell y → y ∈ truncatedCube d (m : ℤ) (n : ℤ) x →
        (3 : ℝ) ^ (alpha * ((n : ℝ) - (ell : ℝ))) *
            normalizedL2On (truncatedCube d (m : ℤ) (ell : ℤ) y)
              (fun p => u.toFun p -
                averageOn (truncatedCube d (m : ℤ) (ell : ℤ) y) u.toFun) ≤
          Crow * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
            (normalizedL2On (cube d (m : ℤ))
                (fun p => u.toFun p - averageOn (cube d (m : ℤ)) u.toFun) +
              (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
                ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
                  holderSeminormOn (cube d (m : ℤ)) (1 / 2) g)) := by
  classical
  obtain ⟨C1, C2, Cabs, Kforce, hC1, hC2, hCabs, hKforce, hout⟩ :=
    exists_interiorCampanatoOutput d hExcess
  refine ⟨C1, C2, rowOneConstJoint d Cabs Kforce, hC1, hC2,
    rowOneConstJoint_nonneg d (by linarith), ?_⟩
  intro M hsmall alpha halpha hepsIcc hdelta heps8 hlam0 hlam1 L m hmL ω u g
    hsol hg n hstop x hx ell hell y hygrid hy
  have hycube : y ∈ cube d (m : ℤ) := rowOne_centre_mem hy
  have hnm5 : (n : ℤ) ≤ (m : ℤ) - 5 :=
    base_scale_le_of_stopping M alpha _ _ 0 m n ω hstop
  have hellZ : (ell : ℤ) ≤ (n : ℤ) := by exact_mod_cast hell
  have hellR : (ell : ℝ) ≤ (n : ℝ) := by exact_mod_cast hell
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by
    have : (n : ℤ) ≤ (m : ℤ) := by omega
    exact_mod_cast this
  have hellmZ : (ell : ℤ) ≤ (m : ℤ) := by omega
  have hglobal0 : 0 ≤ normalizedL2On (cube d (m : ℤ))
      (fun p => u.toFun p - averageOn (cube d (m : ℤ)) u.toFun) :=
    Section6Iteration.normalizedL2On_nonneg _ _
  have hdata0 : 0 ≤ (tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
      holderSeminormOn (cube d (m : ℤ)) (1 / 2) g := by
    have h1 : 0 < tailAverage M L m ω (cube d (m : ℤ)) := by
      rw [← tailCoefficientCubeAverage_eq_tailAverage_cube]
      exact tailCoefficientCubeAverage_pos M L m ω
    exact mul_nonneg (inv_nonneg.mpr h1.le) (Section6ExcessDecay.holderSeminormOn_nonneg hg)
  have htop := topWindow_le_global hycube u
  have hshallowW : (m : ℤ) - (ell : ℤ) ≤ 5 →
      normalizedL2On (truncatedCube d (m : ℤ) (ell : ℤ) y)
          (fun p => u.toFun p -
            averageOn (truncatedCube d (m : ℤ) (ell : ℤ) y) u.toFun) ≤
        Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) *
          normalizedL2On (cube d (m : ℤ))
            (fun p => u.toFun p - averageOn (cube d (m : ℤ)) u.toFun) :=
    fun h => shallowWindow_le_global hycube hellmZ h u
  by_cases hdeep : 5 < (m : ℝ) - (ell : ℝ)
  · obtain ⟨Aexp, expo, hA0, he1, habs, hlong⟩ :=
      hout M hsmall alpha halpha hepsIcc hdelta heps8 hlam0 hlam1 L m hmL ω u g
        hsol hg n hstop x hx ell hell hdeep y hygrid hy
    exact interiorRowOne_combinedJoint halpha.2 hellR hnmR hglobal0 hdata0 hA0
      hKforce he1 hCabs habs htop
      (fun h => absurd hdeep (by linarith only [h]))
      (fun _ => hlong)
  · push_neg at hdeep
    have hshallowZ : (m : ℤ) - (ell : ℤ) ≤ 5 := by
      have : ((m : ℝ) - (ell : ℝ)) ≤ 5 := hdeep
      have hcast : ((m : ℤ) - (ell : ℤ) : ℝ) ≤ 5 := by push_cast; linarith
      exact_mod_cast hcast
    have habs1 : (1 : ℝ) * 1 ≤ Cabs *
        (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (ell : ℝ)) / 4) := by
      have hexp0 : (0 : ℝ) ≤ (1 - alpha) * ((m : ℝ) - (ell : ℝ)) / 4 := by
        have h1 : (0 : ℝ) ≤ 1 - alpha := by linarith only [halpha.2]
        have h2 : (0 : ℝ) ≤ (m : ℝ) - (ell : ℝ) := by
          have : (ell : ℝ) ≤ (m : ℝ) := by exact_mod_cast hellmZ
          linarith
        positivity
      have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (ell : ℝ)) / 4) :=
        Real.one_le_rpow (by norm_num) hexp0
      nlinarith only [hCabs, hpow]
    exact interiorRowOne_combinedJoint halpha.2 hellR hnmR hglobal0 hdata0
      zero_le_one hKforce le_rfl hCabs habs1 htop
      (fun _ => hshallowW hshallowZ)
      (fun h => absurd h (by linarith only [hdeep]))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
