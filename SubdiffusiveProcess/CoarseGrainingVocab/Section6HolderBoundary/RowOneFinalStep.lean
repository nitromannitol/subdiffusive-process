module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.RowOneOutputStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.RowOneShared

@[expose] public section

/-!
# Boundary Holder row one at an arbitrary stopping margin

The deep output is joined with the branch-independent top and shallow window
bounds.  The result is the first row of `HolderRegularityConclusions`, including
the boundary-datum carrier and with no probabilistic packaging.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Statement boundary row one at an arbitrary deterministic margin `step`,
conditional only on the authorized Holder excess-decay input. -/
theorem exists_boundaryRowOneAtStep (d : ℕ) [NeZero d] (step : ℕ)
    (hExcess : Section6Holder.HolderExcessDecayInput d) :
    ∃ (C1 C2 Crow : ℝ), 0 < C1 ∧ 1 ≤ C2 ∧ 0 ≤ Crow ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
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
      ∀ ω : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
          (originCube d (m : ℤ)) u h g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        MemHolder (cube d (m : ℤ)) (1 / 2) h.grad →
      ∀ n : ℕ,
        (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
      ∀ x : Vec d, x ∈ cube d (m : ℤ) →
      ∀ ell : ℕ, ell ≤ n →
      ∀ y : Vec d, OnTriadicGrid ell y → y ∈ truncatedCube d (m : ℤ) (n : ℤ) x →
        (3 : ℝ) ^ (alpha * ((n : ℝ) - (ell : ℝ))) *
            normalizedL2On (truncatedCube d (m : ℤ) (ell : ℤ) y)
              (fun p => u.toFun p -
                averageOn (truncatedCube d (m : ℤ) (ell : ℤ) y) u.toFun) ≤
          Crow * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
            (normalizedL2On (cube d (m : ℤ))
                (fun p => u.toFun p - averageOn (cube d (m : ℤ)) u.toFun) +
              (tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
                (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
                holderSeminormOn (cube d (m : ℤ)) (1 / 2) g +
              (if x ∈ cube d ((m : ℤ) - 1) then 0 else
                (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d (m : ℤ))
                    ((3 : ℝ) ^ (m : ℤ)) (1 / 2) h.grad)) := by
  classical
  obtain ⟨C1, C2, Cabs, Kdata, hC1, hC2, hCabs, hKdata, hout⟩ :=
    exists_boundaryCampanatoOutputAtStep d step hExcess
  refine ⟨C1, C2, rowOneConstJoint d Cabs Kdata, hC1, hC2,
    rowOneConstJoint_nonneg d (by linarith), ?_⟩
  intro M hsmall alpha halpha hepsIcc hdelta heps8 hlam0 hlam1 L m hmL ω u h g
    hsol hg hh n hstop x hx ell hell y hygrid hy
  have hycube : y ∈ cube d (m : ℤ) := rowOne_centre_mem hy
  have hnm5 : (n : ℤ) ≤ (m : ℤ) - 5 :=
    base_scale_le_of_stopping M alpha _ _ step m n ω hstop
  have hellR : (ell : ℝ) ≤ (n : ℝ) := by exact_mod_cast hell
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by
    have : (n : ℤ) ≤ (m : ℤ) := by omega
    exact_mod_cast this
  have hellmZ : (ell : ℤ) ≤ (m : ℤ) := by omega
  let global := normalizedL2On (cube d (m : ℤ))
    (fun p => u.toFun p - averageOn (cube d (m : ℤ)) u.toFun)
  let forcing := (tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
    holderSeminormOn (cube d (m : ℤ)) (1 / 2) g
  let boundary := if x ∈ cube d ((m : ℤ) - 1) then 0 else
    fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
      (1 / 2) h.grad
  have hglobal0 : 0 ≤ global := by
    dsimp only [global]
    exact Section6Iteration.normalizedL2On_nonneg _ _
  have hforcing0 : 0 ≤ forcing := by
    dsimp only [forcing]
    have htail : 0 < tailAverage M L m ω (cube d (m : ℤ)) := by
      rw [← tailCoefficientCubeAverage_eq_tailAverage_cube]
      exact tailCoefficientCubeAverage_pos M L m ω
    exact mul_nonneg (inv_nonneg.mpr htail.le)
      (Section6ExcessDecay.holderSeminormOn_nonneg hg)
  have hboundary0 : 0 ≤ boundary := by
    dsimp only [boundary]
    split_ifs
    · norm_num
    · exact fractionalInfinityNormOn_cube_nonneg hh
  have htop := topWindow_le_global hycube u
  have hshallowW : (m : ℤ) - (ell : ℤ) ≤ 5 →
      normalizedL2On (truncatedCube d (m : ℤ) (ell : ℤ) y)
          (fun p => u.toFun p -
            averageOn (truncatedCube d (m : ℤ) (ell : ℤ) y) u.toFun) ≤
        Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global := by
    intro hshallow
    exact shallowWindow_le_global hycube hellmZ hshallow u
  have hrow :
      (3 : ℝ) ^ (alpha * ((n : ℝ) - (ell : ℝ))) *
          normalizedL2On (truncatedCube d (m : ℤ) (ell : ℤ) y)
            (fun p => u.toFun p -
              averageOn (truncatedCube d (m : ℤ) (ell : ℤ) y) u.toFun) ≤
        rowOneConstJoint d Cabs Kdata *
          (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
          (global + (3 : ℝ) ^ (3 * (m : ℝ) / 2) * forcing +
            (3 : ℝ) ^ (3 * (m : ℝ) / 2) * boundary) := by
    by_cases hdeep : 5 < (m : ℝ) - (ell : ℝ)
    · obtain ⟨Aexp, expo, hA0, he1, habs, hlong⟩ :=
        hout M hsmall alpha halpha hepsIcc hdelta heps8 hlam0 hlam1 L m hmL ω
          u h g hsol hg hh n hstop x hx ell hell hdeep y hygrid hy
      exact boundaryRowOne_combinedJoint halpha.2 hellR hnmR hglobal0 hforcing0
        hboundary0 hA0 hKdata he1 hCabs habs htop
        (fun hshort => absurd hdeep (by linarith only [hshort]))
        (fun _ => hlong)
    · push Not at hdeep
      have hshallowZ : (m : ℤ) - (ell : ℤ) ≤ 5 := by
        have hcast : (((m : ℤ) - (ell : ℤ) : ℤ) : ℝ) ≤ 5 := by
          push_cast
          linarith
        exact_mod_cast hcast
      have habs1 : (1 : ℝ) * 1 ≤ Cabs *
          (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (ell : ℝ)) / 4) := by
        have hexponent0 : 0 ≤ (1 - alpha) * ((m : ℝ) - (ell : ℝ)) / 4 := by
          have ha : 0 ≤ 1 - alpha := by linarith only [halpha.2]
          have hgap : 0 ≤ (m : ℝ) - (ell : ℝ) := by
            have : (ell : ℝ) ≤ (m : ℝ) := by exact_mod_cast hellmZ
            linarith
          positivity
        have hpow : 1 ≤ (3 : ℝ) ^
            ((1 - alpha) * ((m : ℝ) - (ell : ℝ)) / 4) :=
          Real.one_le_rpow (by norm_num) hexponent0
        nlinarith only [hCabs, hpow]
      exact boundaryRowOne_combinedJoint halpha.2 hellR hnmR hglobal0 hforcing0
        hboundary0 zero_le_one hKdata le_rfl hCabs habs1 htop
        (fun _ => hshallowW hshallowZ)
        (fun hlong => absurd hlong (by linarith only [hdeep]))
  dsimp only [global, forcing, boundary] at hrow
  by_cases hinterior : x ∈ cube d ((m : ℤ) - 1)
  · simp only [ite_eq_left hinterior, add_zero] at hrow ⊢
    convert hrow using 1
    ring
  · simp only [ite_eq_right hinterior] at hrow ⊢
    convert hrow using 1
    ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary
