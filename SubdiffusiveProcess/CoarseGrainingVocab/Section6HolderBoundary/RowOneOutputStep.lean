module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.RowOneBoundaryBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneGate
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneInstantiation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneShapeMatch

@[expose] public section

/-!
# Boundary Holder row one: deep Campanato output

This is the boundary analogue of the interior package's deep-branch output.
The full-domain Campanato ladder has three datum terms: forcing, the accumulated
boundary-gradient mean, and the boundary Holder seminorm.  The boundary budget
lemma combines them into the frozen forcing-plus-boundary carrier, while the
linear absorption lemma pays the one extra factor `1 + lambda * gap`.

The theorem is deterministic once the stopped controls are supplied by the
existing stopping scale.  In particular, it has no event-measurability or
sigma-field parameter.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The deep-branch boundary row-one output at an arbitrary deterministic
stopping-scale margin `step`. -/
theorem exists_boundaryCampanatoOutputAtStep (d : ℕ) [NeZero d] (step : ℕ)
    (hExcess : Section6Holder.HolderExcessDecayInput d) :
    ∃ (C1 C2 Cabs Kdata : ℝ), 0 < C1 ∧ 1 ≤ C2 ∧ 1 ≤ Cabs ∧ 0 ≤ Kdata ∧
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
      ∀ ell : ℕ, ell ≤ n → 5 < (m : ℝ) - (ell : ℝ) →
      ∀ y : Vec d, OnTriadicGrid ell y → y ∈ truncatedCube d (m : ℤ) (n : ℤ) x →
        ∃ Aexp exponential : ℝ, 0 ≤ Aexp ∧ 1 ≤ exponential ∧
          Aexp * exponential ≤
            Cabs * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (ell : ℝ)) / 4) ∧
          (3 : ℝ) ^ (-(ell : ℝ)) *
              normalizedL2On (truncatedCube d (m : ℤ) (ell : ℤ) y)
                (fun p => u.toFun p -
                  averageOn (truncatedCube d (m : ℤ) (ell : ℤ) y) u.toFun) ≤
            Aexp * ((3 : ℝ) ^ (-((m : ℝ) - 5)) *
                normalizedL2On (truncatedCube d (m : ℤ) ((m : ℤ) - 5) y)
                  (fun p => u.toFun p -
                    averageOn (truncatedCube d (m : ℤ) ((m : ℤ) - 5) y) u.toFun) +
              5 / 2 * Kdata * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
                ((3 : ℝ) ^ ((m : ℝ) / 2) *
                  ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
                      holderSeminormOn (cube d (m : ℤ)) (1 / 2) g +
                    (if x ∈ cube d ((m : ℤ) - 1) then 0 else
                      fractionalInfinityNormOnReal (cube d (m : ℤ))
                        ((3 : ℝ) ^ (m : ℤ)) (1 / 2) h.grad)))) := by
  classical
  obtain ⟨Cstep, K, Citer, hCstep, hK, hCiter, hcamp⟩ :=
    Section6Holder.exists_holderCampanatoFull d hExcess
  obtain ⟨k, C2, hk, hC2, hth⟩ :=
    Section6Holder.exists_holderContractionParameters d Cstep hCstep
  obtain ⟨hthetaIoo, hthetak, hcontract⟩ := hth
  set Keps : ℝ := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K with hKepsDef
  set Kforce : ℝ := Cstep * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
    with hKforceDef
  set Kmean : ℝ := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) with hKmeanDef
  set Kboundary : ℝ := Cstep * (1 / 4 : ℝ) ^ (-3 : ℤ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) with hKboundaryDef
  set Aforce : ℝ := 5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) with hAforceDef
  set Amean : ℝ := Kmean * (3 * Keps) with hAmeanDef
  set Abound : ℝ := 5 / 2 * Kboundary * (3 : ℝ) ^ (-(5 / 2 : ℝ))
    with hAboundDef
  set Kbudget : ℝ := max Aforce (max Amean Abound) with hKbudgetDef
  set Kdata : ℝ := (6 / 5 : ℝ) * (3 : ℝ) ^ (5 / 2 : ℝ) * Kbudget
    with hKdataDef
  have hKeps0 : 0 ≤ Keps := by rw [hKepsDef]; positivity
  have hKforce0 : 0 ≤ Kforce := by
    have := Section6ExcessDecay.fractionalHolderConst_nonneg d
    rw [hKforceDef]
    positivity
  have hKmean0 : 0 ≤ Kmean := by rw [hKmeanDef]; positivity
  have hKboundary0 : 0 ≤ Kboundary := by rw [hKboundaryDef]; positivity
  have hAforce0 : 0 ≤ Aforce := by rw [hAforceDef]; positivity
  have hAmean0 : 0 ≤ Amean := by rw [hAmeanDef]; positivity
  have hAbound0 : 0 ≤ Abound := by rw [hAboundDef]; positivity
  have hKbudget0 : 0 ≤ Kbudget := hAforce0.trans (by
    rw [hKbudgetDef]
    exact le_max_left _ _)
  have hKdata0 : 0 ≤ Kdata := by rw [hKdataDef]; positivity
  have hKdataCoeff :
      5 / 2 * Kdata * (3 : ℝ) ^ (-(5 / 2 : ℝ)) = 3 * Kbudget := by
    rw [hKdataDef]
    have hpow : (3 : ℝ) ^ (5 / 2 : ℝ) * (3 : ℝ) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
    calc
      5 / 2 * ((6 / 5 : ℝ) * (3 : ℝ) ^ (5 / 2 : ℝ) * Kbudget) *
          (3 : ℝ) ^ (-(5 / 2 : ℝ)) =
        3 * ((3 : ℝ) ^ (5 / 2 : ℝ) * (3 : ℝ) ^ (-(5 / 2 : ℝ))) *
          Kbudget := by ring
      _ = 3 * Kbudget := by rw [hpow]; ring
  set A0 : ℝ := Citer * ((k : ℝ) + 1) * ((k : ℝ) + 2) with hA0Def
  set P : ℝ := Citer * ((k : ℝ) + 1) + 3 * Citer * Keps + ratioRate d with hPDef
  have hP0 : 0 ≤ P := by
    have := ratioRate_nonneg d
    rw [hPDef]
    positivity
  obtain ⟨C1, Cabs, hC1, hCabs, habsorb⟩ :=
    Section6Holder.exists_holderLinearExponentialAbsorption A0 P hP0
  refine ⟨C1, C2, max Cabs 1, Kdata, hC1, hC2, le_max_right _ _, hKdata0, ?_⟩
  intro M hsmall alpha halpha hepsIcc hdelta heps8 hlam0 hlam1 L m hmL ω u h g
    hsol hg hh n hstop x hx ell hell hdeep y hygrid hy
  have hycube : y ∈ cube d (m : ℤ) := rowOne_centre_mem hy
  have hnm5 : (n : ℤ) ≤ (m : ℤ) - 5 :=
    base_scale_le_of_stopping M alpha _ _ step m n ω hstop
  obtain ⟨htoplt, htople⟩ := rowOne_base_lt_top hnm5 hell hdeep
  have hstopEll := rowOne_stopping_at_base M alpha _ _ step m n ell ω hstop hell
  obtain ⟨hctrlY, _hctrl0⟩ :=
    stoppedControls_pair M C1 C2 alpha step m ell ω hstopEll y hygrid hycube
  have hepsPos : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha := by
    rw [Section6Stopping.holderStoppingEpsilon]
    have hC2pos : (0 : ℝ) < C2 := by linarith
    positivity
  have hratio := stoppedRatio_row (L := L) M C1 C2 alpha step m ell (m - 5) ω
    (by omega) hmL (by omega) hlam0 hlam1 hepsPos hdelta y hycube hstopEll hygrid
  have hepsC2 : Section6Stopping.holderStoppingEpsilon C2 alpha ≤ C2⁻¹ := by
    rw [Section6Stopping.holderStoppingEpsilon]
    have hC2pos : (0 : ℝ) < C2 := by linarith
    have hsq : Real.sqrt (1 - alpha) ≤ 1 := by
      have h1 : (1 : ℝ) - alpha ≤ 1 := by linarith [halpha.1]
      simpa using Real.sqrt_le_sqrt h1
    have hinv : (0 : ℝ) ≤ C2⁻¹ := by positivity
    nlinarith only [hsq, hinv]
  have hcontr := hcontract (Section6Stopping.holderStoppingEpsilon C2 alpha)
    hepsPos hepsC2
  let ratioExponential := Real.exp (ratioRate d *
    Section6Stopping.holderStoppingLambda C1 alpha * ((m : ℝ) - (ell : ℝ)))
  have hout := hcamp M hsmall (Section6Stopping.holderStoppingEpsilon C2 alpha)
    hepsIcc (Section6Stopping.holderStoppingLambda C1 alpha) hlam0 hdelta heps8
    k hk ((3 : ℝ) ^ (-(1 / 4 : ℝ))) hthetaIoo hthetak hcontr
    L m ell (m - 5) htoplt htople hmL y hycube ω hctrlY.1 hctrlY.2
    ratioExponential (Real.exp_nonneg _) hratio u h g hsol hg hh
  dsimp only at hout
  let gap : ℝ := (m : ℝ) - (ell : ℝ)
  let lambda : ℝ := Section6Stopping.holderStoppingLambda C1 alpha
  let boundaryTop : ℝ :=
    if BoundaryTouches (truncatedCube d (m : ℤ) ((m - 5 : ℕ) : ℤ) y)
        (cube d (m : ℤ)) then 1 else 0
  let outsideIndicator : ℝ := if x ∈ cube d ((m : ℤ) - 1) then 0 else 1
  let forcing : ℝ := (tailCoefficientCubeAverage M L m ω)⁻¹ *
    holderSeminormOn (cube d (m : ℤ)) (1 / 2) g
  have hgap0 : 0 ≤ gap := by dsimp only [gap]; linarith
  have hratio1 : 1 ≤ ratioExponential := by
    have hx0 : 0 ≤ ratioRate d * lambda * gap := by
      exact mul_nonneg (mul_nonneg (ratioRate_nonneg d) hlam0) hgap0
    simpa only [ratioExponential, lambda, gap, Real.exp_zero] using
      Real.exp_le_exp.mpr hx0
  have hforcing0 : 0 ≤ forcing := by
    dsimp only [forcing]
    exact mul_nonneg (inv_nonneg.mpr (tailCoefficientCubeAverage_pos M L m ω).le)
      (Section6ExcessDecay.holderSeminormOn_nonneg hg)
  have hboundaryTop0 : 0 ≤ boundaryTop := by
    dsimp only [boundaryTop]
    split_ifs <;> norm_num
  have houtside0 : 0 ≤ outsideIndicator := by
    dsimp only [outsideIndicator]
    split_ifs <;> norm_num
  have hindicator : boundaryTop ≤ outsideIndicator := by
    dsimp only [boundaryTop, outsideIndicator]
    exact Section6Holder.boundaryIndicator_top_le_not_interior hy
      (by omega : (n : ℤ) ≤ ((m - 5 : ℕ) : ℤ)) (by omega)
  have hbudget := boundaryRowOne_dataBudget_le_fractionalInfinityNormOn
    (K := Kbudget) (Aforce := Aforce) (Amean := Amean) (Abound := Abound)
    (lambda := lambda) (gap := gap) (exponential := ratioExponential)
    (forcing := forcing) (boundaryIndicator := boundaryTop)
    (outsideIndicator := outsideIndicator) hh
    hKbudget0 hAmean0 hAbound0
    (by rw [hKbudgetDef]; apply le_max_left)
    (by rw [hKbudgetDef]; exact le_max_of_le_right (le_max_left _ _))
    (by rw [hKbudgetDef]; exact le_max_of_le_right (le_max_right _ _))
    hlam0 hlam1.le hgap0 hratio1 hforcing0 hboundaryTop0 houtside0 hindicator
  rw [← hKepsDef, ← hKforceDef, ← hKboundaryDef] at hout
  have hm5 : 5 ≤ m := by omega
  have htopCast : ((m - 5 : ℕ) : ℤ) = (m : ℤ) - 5 := by omega
  have htopReal : ((m - 5 : ℕ) : ℝ) = (m : ℝ) - 5 := by
    rw [Nat.cast_sub hm5]
    norm_num
  have hDbudget :
      5 / 2 * Kforce * (3 : ℝ) ^ (-(((m : ℝ) - ((m - 5 : ℕ) : ℝ)) / 2)) *
            ratioExponential *
            ((tailCoefficientCubeAverage M L m ω)⁻¹ *
              (3 : ℝ) ^ ((m : ℝ) / 2) *
              holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) +
          Kmean * (3 * Keps * lambda * (gap + 1)) *
              vectorSupNormOn (cube d (m : ℤ)) h.grad * boundaryTop +
          5 / 2 * Kboundary *
              (3 : ℝ) ^ (-(((m : ℝ) - ((m - 5 : ℕ) : ℝ)) / 2)) *
              ((3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad) * boundaryTop ≤
        3 * Kbudget * ((1 + lambda * gap) * ratioExponential) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) *
            (forcing + outsideIndicator *
              fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
                (1 / 2) h.grad)) := by
    rw [htopReal]
    have hgapFive : ((m : ℝ) - ((m : ℝ) - 5)) / 2 = (5 / 2 : ℝ) := by ring
    rw [hgapFive]
    rw [← hAforceDef, ← hAboundDef]
    calc
      Aforce * ratioExponential *
              ((tailCoefficientCubeAverage M L m ω)⁻¹ *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) +
            Kmean * (3 * Keps * lambda * (gap + 1)) *
                vectorSupNormOn (cube d (m : ℤ)) h.grad * boundaryTop +
            Abound * ((3 : ℝ) ^ ((m : ℝ) / 2) *
              holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad) * boundaryTop =
          Aforce * ratioExponential * ((3 : ℝ) ^ ((m : ℝ) / 2) * forcing) +
            Amean * lambda * (gap + 1) *
              (vectorSupNormOn (cube d (m : ℤ)) h.grad * boundaryTop) +
            Abound * ((3 : ℝ) ^ ((m : ℝ) / 2) *
              (holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad *
                boundaryTop)) := by
            rw [hAmeanDef]
            dsimp only [forcing]
            ring
      _ ≤ _ := hbudget
  let Aexp : ℝ := Real.exp (Citer * ((k : ℝ) + 1) *
      ((k : ℝ) + 2 + lambda * gap) +
    Citer * (3 * Keps * lambda * (gap + 1)))
  let exponential : ℝ := (1 + lambda * gap) * ratioExponential
  refine ⟨Aexp, exponential, Real.exp_nonneg _, ?_, ?_, ?_⟩
  · dsimp only [exponential]
    have hlinear1 : 1 ≤ 1 + lambda * gap :=
      le_add_of_nonneg_right (mul_nonneg hlam0 hgap0)
    calc
      1 ≤ ratioExponential := hratio1
      _ ≤ (1 + lambda * gap) * ratioExponential := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hlinear1 (by positivity : 0 ≤ ratioExponential)
  ·
    have hstep := expAbar_mul_linearRatio_le (Keps := Keps)
      (Cratio := ratioRate d) (Cabs := Cabs) (gap := gap) (k := (k : ℝ))
      (Citer := Citer) (alpha := alpha) (C1 := C1) hCiter.le (ratioRate_nonneg d)
      hgap0 (Nat.cast_nonneg k) halpha hC1
      (by
        intro a ha gp hgp
        rw [← hA0Def, ← hPDef]
        exact habsorb a ha gp hgp)
    dsimp only [Aexp, exponential]
    rw [show lambda = C1⁻¹ * (1 - alpha) by
      dsimp only [lambda]; rw [Section6Stopping.holderStoppingLambda]]
    dsimp only [ratioExponential, gap, lambda]
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by norm_num) _)
  · have houtBudget :
        (3 : ℝ) ^ (-(ell : ℤ)) *
              normalizedL2On (truncatedCube d (m : ℤ) (ell : ℤ) y)
                (fun p => u.toFun p -
                  averageOn (truncatedCube d (m : ℤ) (ell : ℤ) y) u.toFun) ≤
          Aexp * ((3 : ℝ) ^ (-((m - 5 : ℕ) : ℤ)) *
                normalizedL2On (truncatedCube d (m : ℤ) ((m - 5 : ℕ) : ℤ) y)
                  (fun p => u.toFun p - averageOn
                    (truncatedCube d (m : ℤ) ((m - 5 : ℕ) : ℤ) y) u.toFun) +
              3 * Kbudget * exponential *
                ((3 : ℝ) ^ ((m : ℝ) / 2) *
                  (forcing + outsideIndicator *
                    fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
                      (1 / 2) h.grad))) := by
      dsimp only [Aexp, exponential]
      apply hout.trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact add_le_add (le_refl _) (by
        simpa only [gap, lambda, boundaryTop, ratioExponential] using hDbudget)
    rw [← rpow_neg_natCast_eq_zpow ell, ← rpow_neg_natCast_eq_zpow (m - 5),
      htopReal, htopCast] at houtBudget
    dsimp only [forcing] at houtBudget
    rw [tailCoefficientCubeAverage_eq_tailAverage_cube] at houtBudget
    dsimp only [outsideIndicator] at houtBudget
    rw [hKdataCoeff]
    by_cases hinterior : x ∈ cube d ((m : ℤ) - 1)
    · simpa only [ite_eq_left hinterior, zero_mul, add_zero] using houtBudget
    · simpa only [ite_eq_right hinterior, one_mul] using houtBudget

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary
