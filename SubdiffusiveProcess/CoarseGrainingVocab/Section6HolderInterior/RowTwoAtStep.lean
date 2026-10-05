module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoAbsorb
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoForcingLeg
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoGateBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoOscLegFull
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoScaledBudget

@[expose] public section

/-!
# Frozen row 2 for the interior anchor

The second frozen interior row, conditional only on
`InteriorHolderExcessDecayInput`.

The chain is  on the interior branch:

1. the frozen base point `x ∈ cu_{m-1}` gets a scale-`n` grid centre `z` **of
   `cu_{m-1}`** (`Section6Holder.exists_holderGridCentre` read at scale `m-1`),
   so every proved estimate whose binder is `z ∈ cu_{m-1}` applies verbatim;
2. a good scale `gate ∈ [n+4, n+4+K]` is selected in the window `[n+6, n+6+K]`
   above the base (`RowTwoGateScale`), `K = ⌈lambda(m-n)⌉` being the failure
   budget; the six-scale offset is what Step 6 costs between its good event and
   its conclusion;
3. interior Step 6 at `gate`, transported down to the base scale
   (`RowTwoGateBudget`);
4. the scalar split of the budget (`EnergyRowScalar`) into an oscillation leg and
   a forcing leg (`RowTwoScaledBudget`);
5. the oscillation leg through the printed Campanato family and the top-window
   energy (`RowTwoOscLegFull`), the forcing leg through the Besov/Hölder
   embedding (`RowTwoForcingLeg`);
6. a single exponential absorption (`RowTwoAbsorb`), with `C₁ ≥ 2` — which is
   what keeps `lambda ≤ 1/4`, hence the selection window inside the domain.

The deterministic margin `step` must exceed `21`: the two selections consume
`2K + 11` scales above the base and `K ≤ lambda(m-n) + 1 ≤ (m-n)/4 + 1`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization Homogenization.Book Homogenization.Book.Ch03

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **Frozen row 2 for the interior anchor.** -/
theorem exists_interiorRowTwoAtStep (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d) :
    ∃ (C1 C2 Crow : ℝ), 2 ≤ C1 ∧ C1 ≤ C2 ∧ 0 ≤ Crow ∧
      ∀ step : ℕ, 21 ≤ step →
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
      ∀ L m : ℕ, m ≤ L →
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (cube d (m : ℤ)) u g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
      ∀ n : ℕ,
        (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
      ∀ x : Vec d, x ∈ cube d ((m : ℤ) - 1) →
        vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
            (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
              u.grad p) ≤
          Crow * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
            (vectorNormalizedL2On (cube d (m : ℤ))
                (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
                  u.grad p) +
              (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) := by
  classical
  obtain ⟨C2min, A0osc, Posc, Kpre, hC2min, hA0osc, hPosc, hKpre, hosc⟩ :=
    exists_interiorRowTwoOscLeg d hExcess
  obtain ⟨Kb, hKb, hgateBudget⟩ := exists_interiorRowTwoGateBudget d
  have hr0 : (0 : ℝ) ≤ ratioRate d := ratioRate_nonneg d
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hdlog0 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := by positivity
  set A0f : ℝ := A0osc + 3 * (d : ℝ) * Real.log 3 with hA0fDef
  set Pf : ℝ := Posc + ratioRate d + (d : ℝ) * Real.log 3 with hPfDef
  have hPf0 : 0 ≤ Pf := by rw [hPfDef]; linarith
  obtain ⟨C1abs, Cabs, hC1abs, hCabs, habsorb⟩ :=
    Section6Holder.exists_holderExponentialAbsorption A0f Pf hPf0
  refine ⟨max C1abs 2, max C2min (max C1abs 2),
    Real.sqrt ((81 : ℝ) ^ d * Kb) * (Kpre + rowTwoForcingConst d) * Cabs,
    le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ Real.sqrt ((81 : ℝ) ^ d * Kb) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ Kpre + rowTwoForcingConst d := by
      have := rowTwoForcingConst_nonneg d
      linarith
    have := hCabs.le
    positivity
  intro step hstep21 M hsmall alpha halpha hepsIcc hdelta
    L m hmL omega u g hsol hg n hstop x hx
  set C1 : ℝ := max C1abs 2 with hC1Def
  set C2 : ℝ := max C2min C1 with hC2Def
  set lam : ℝ := Section6Stopping.holderStoppingLambda C1 alpha with hlamDef
  have hC12 : (2 : ℝ) ≤ C1 := le_max_right _ _
  have hC1C2 : C1 ≤ C2 := le_max_right _ _
  have hC2ge : C2min ≤ C2 := le_max_left _ _
  have hC2one : (1 : ℝ) ≤ C2 := by linarith
  have ha0 : (0 : ℝ) ≤ 1 - alpha := by linarith [halpha.2]
  have ha2 : (1 : ℝ) - alpha ≤ 1 / 2 := by linarith [halpha.1]
  have hC1pos : (0 : ℝ) < C1 := by linarith
  have hlam0 : 0 ≤ lam := by
    rw [hlamDef, Section6Stopping.holderStoppingLambda]
    have : (0 : ℝ) ≤ C1⁻¹ := by positivity
    exact mul_nonneg this ha0
  -- the absorption at the enlarged `C₁`
  have habsorbC1 := holderExponentialAbsorption_mono hPf0 hC1abs
    (le_max_left C1abs 2) habsorb
  -- the gap
  have hgapZ : ((step : ℤ) + 5) ≤ (m : ℤ) - (n : ℤ) :=
    gap_ge_step_of_stopping M alpha _ _ step m n omega hstop
  have hgapN : n + 26 ≤ m := by omega
  have hgapR : (26 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have h : (n : ℝ) + 26 ≤ (m : ℝ) := by exact_mod_cast hgapN
    linarith
  have hgapR0 : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by linarith
  -- `lambda ≤ 1/4`, from `C₁ ≥ 2`
  have hlamQuarter : lam ≤ 1 / 4 := by
    rw [hlamDef, Section6Stopping.holderStoppingLambda]
    have hC12 : (2 : ℝ) ≤ C1 := le_max_right _ _
    have hinv : C1⁻¹ ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      exact inv_anti₀ (by norm_num) hC12
    have hinv0 : (0 : ℝ) ≤ C1⁻¹ := by positivity
    have ha : (0 : ℝ) ≤ 1 - alpha := by linarith [halpha.2]
    have ha2 : (1 : ℝ) - alpha ≤ 1 / 2 := by linarith [halpha.1]
    nlinarith only [hinv, hinv0, ha, ha2]
  have hlam1 : lam < 1 := by linarith
  -- the two remaining stopping-parameter conditions, from `2 ≤ C₁ ≤ C₂`
  have heps8 : Section6Stopping.holderStoppingEpsilon C2 alpha ^ 8 ≤ lam := by
    rw [hlamDef, Section6Stopping.holderStoppingLambda,
      Section6Stopping.holderStoppingEpsilon]
    have hC2pos : (0 : ℝ) < C2 := by linarith
    have hsq : Real.sqrt (1 - alpha) ^ 8 = (1 - alpha) ^ 4 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt ha0]
    have hexp : (C2⁻¹ * Real.sqrt (1 - alpha)) ^ 8 = (C2⁻¹) ^ 8 * (1 - alpha) ^ 4 := by
      rw [mul_pow, hsq]
    rw [hexp]
    have hinvC2 : (0 : ℝ) ≤ C2⁻¹ := by positivity
    have hinvC2one : C2⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right; linarith
    have h8 : (C2⁻¹) ^ 8 ≤ C2⁻¹ := by
      calc (C2⁻¹) ^ 8 ≤ (C2⁻¹) ^ 1 :=
            pow_le_pow_of_le_one hinvC2 hinvC2one (by norm_num)
        _ = C2⁻¹ := pow_one _
    have hmono : C2⁻¹ ≤ C1⁻¹ := inv_anti₀ hC1pos hC1C2
    have h1 : (C2⁻¹) ^ 8 ≤ C1⁻¹ := by linarith
    have ha1 : (1 : ℝ) - alpha ≤ 1 := by linarith
    have h2 : (1 - alpha) ^ 4 ≤ (1 - alpha) := by
      calc (1 - alpha) ^ 4 ≤ (1 - alpha) ^ 1 :=
            pow_le_pow_of_le_one ha0 ha1 (by norm_num)
        _ = 1 - alpha := pow_one _
    have hpow0 : (0 : ℝ) ≤ (1 - alpha) ^ 4 := by positivity
    have hinvC10 : (0 : ℝ) ≤ C1⁻¹ := by positivity
    calc (C2⁻¹) ^ 8 * (1 - alpha) ^ 4 ≤ C1⁻¹ * (1 - alpha) ^ 4 :=
          mul_le_mul_of_nonneg_right h1 hpow0
      _ ≤ C1⁻¹ * (1 - alpha) := mul_le_mul_of_nonneg_left h2 hinvC10
  -- the failure budget `K`
  set K : ℕ := ⌈lam * ((m : ℝ) - (n : ℝ))⌉₊ with hKDef
  have hKlow : lam * ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) := by
    rw [hKDef]; exact Nat.le_ceil _
  have hKup : (K : ℝ) < lam * ((m : ℝ) - (n : ℝ)) + 1 := by
    rw [hKDef]
    exact Nat.ceil_lt_add_one (mul_nonneg hlam0 hgapR0)
  have hKub : (K : ℝ) ≤ lam * ((m : ℝ) - (n : ℝ)) + 1 := le_of_lt hKup
  have hroom : 1 + lam * ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) + 1 := by linarith
  have hroomBigR : (n : ℝ) + 2 * (K : ℝ) + 11 < (m : ℝ) := by
    have h1 : lam * ((m : ℝ) - (n : ℝ)) ≤ 1 / 4 * ((m : ℝ) - (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hlamQuarter hgapR0
    linarith
  have hroomBig : n + 2 * K + 11 < m := by exact_mod_cast hroomBigR
  -- the grid centre inside `cu_{m-1}`
  have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  obtain ⟨z, hzgrid, hzc, hdist⟩ := Section6Holder.exists_holderGridCentre
    (d := d) (m := m - 1) (n := n) (x := x) (by rw [hm1]; exact hx) (by omega)
  rw [hm1] at hzc
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_mem_cube_sub_one hzc
  have hxm : x ∈ cube d (m : ℤ) := mem_cube_of_mem_cube_sub_one hx
  -- the gate scale
  obtain ⟨gate, hngate, hgateK, hgood⟩ := exists_interiorRowTwoGateScale M C1 C2
    alpha step m n K omega z hzgrid hzm hstop hC2one halpha.1 (by omega)
    (by rw [← hlamDef]; linarith)
  -- Step 6 at the gate scale
  have hsIcc : (interiorFractionalOrder).1 ∈
      Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) := by
    rw [interiorFractionalOrder_val]
    refine ⟨?_, le_rfl⟩
    have hS : Section6Stopping.holderStoppingS = 1 / 32 := rfl
    rw [hS] at hsmall
    linarith
  have hbudget := hgateBudget M hsIcc L m n gate hmL hngate (by omega) x z omega
    hxm hzc hdist hgood u g hsol hg
  -- the two legs
  have hsigmaPos : 0 < tailAverage M L (gate + 2) omega
      (translatedCube d ((gate : ℤ) + 2) z) := by
    rw [show ((gate : ℤ) + 2) = ((gate + 2 : ℕ) : ℤ) from by push_cast; ring]
    exact tailAverage_translatedCube_pos M L (gate + 2) omega z
  have hOscLeg := hosc C2 hC2ge M hsmall C1 alpha halpha hepsIcc hdelta heps8
    hlam0 hlam1
    step L m n gate K hmL omega z x hzgrid hzc hxm hdist hstop hngate hgateK
    (by rw [← hlamDef]; exact hKub) (by rw [← hlamDef]; exact hroom) hroomBig
    u g hsol hg
  have hForceLeg := interiorRowTwo_forcingLeg M C1 C2 alpha step m n gate L omega
    z x hzgrid hzm hxm hstop (by omega) (by omega) (by omega) hmL hlam0 hlam1
    (holderStoppingEpsilon_nonneg (by linarith)) hdelta g hg
  -- nonnegativity bookkeeping
  have hEg0 : 0 ≤ vectorNormalizedL2On (cube d (m : ℤ))
      (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) • u.grad p) :=
    Real.sqrt_nonneg _
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hbeq : tailCoefficientCubeAverage M L m omega =
      tailAverage M L m omega (cube d (m : ℤ)) :=
    tailCoefficientCubeAverage_eq_tailAverage_cube M L m omega
  have hDa0 : 0 ≤ (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
      (3 : ℝ) ^ ((m : ℝ) / 2) * holderSeminormOn (cube d (m : ℤ)) (1 / 2) g := by
    have h1 : (0 : ℝ) ≤ (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) :=
      Real.rpow_nonneg (by rw [← hbeq]; exact hb.le) _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have h3 : 0 ≤ holderSeminormOn (cube d (m : ℤ)) (1 / 2) g :=
      Section6ExcessDecay.holderSeminormOn_nonneg hg
    positivity
  set Total : ℝ := vectorNormalizedL2On (cube d (m : ℤ))
        (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
          u.grad p) +
      (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
        (3 : ℝ) ^ ((m : ℝ) / 2) *
        holderSeminormOn (cube d (m : ℤ)) (1 / 2) g with hTotalDef
  have hT0 : (0 : ℝ) ≤ Total := by rw [hTotalDef]; exact add_nonneg hEg0 hDa0
  have hDaTotal : (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
      (3 : ℝ) ^ ((m : ℝ) / 2) *
      holderSeminormOn (cube d (m : ℤ)) (1 / 2) g ≤ Total := by
    rw [hTotalDef]; linarith
  have hB0 : (0 : ℝ) ≤ rowTwoForcingConst d * rowTwoRatioBound d C1 alpha m n :=
    mul_nonneg (rowTwoForcingConst_nonneg d)
      (rowTwoRatioBound_nonneg d C1 alpha m n)
  -- the conversion
  have hconv := interiorRowTwo_of_scaledBudget (d := d)
    (scaleTransferPrice_nonneg d ((gate : ℤ) - 4 - (n : ℤ))) hKb.le hsigmaPos
    (by simp only [interiorFractionalOrder_val]; norm_num)
    (Section6Iteration.normalizedL2On_nonneg _ _) ENNReal.toReal_nonneg
    hbudget (by rw [← mul_assoc] at hOscLeg; exact hOscLeg)
    (hForceLeg.trans (mul_le_mul_of_nonneg_left hDaTotal hB0))
  -- the absorption
  set wgt : ℝ := lam * ((m : ℝ) - (n : ℝ) + 1) with hwgtDef
  have hwgt0 : 0 ≤ wgt := by rw [hwgtDef]; positivity
  refine rowTwo_absorb_arith (Real.sqrt_nonneg _) hT0
    (mul_nonneg hKpre (Real.exp_nonneg _))
    (mul_nonneg (rowTwoForcingConst_nonneg d)
      (rowTwoRatioBound_nonneg d C1 alpha m n))
    hconv (b := 3 * (d : ℝ) * Real.log 3 + ((d : ℝ) * Real.log 3) * wgt)
    (a := A0osc + (Posc + ratioRate d) * wgt) ?_ ?_ ?_ ?_
  · refine scaleTransferPrice_le_exp d (by omega) ?_
    rw [show (((gate : ℤ) - 4 - (n : ℤ) : ℤ) : ℝ) = (gate : ℝ) - 4 - (n : ℝ)
      from by push_cast; ring]
    have hgR : (gate : ℝ) ≤ (n : ℝ) + 4 + (K : ℝ) := by exact_mod_cast hgateK
    have hbase : (gate : ℝ) - 4 - (n : ℝ) + 2 ≤ wgt + 3 := by
      rw [hwgtDef]
      have : lam * ((m : ℝ) - (n : ℝ)) ≤ lam * ((m : ℝ) - (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam0
      linarith
    calc ((gate : ℝ) - 4 - (n : ℝ) + 2) * (d : ℝ) * Real.log 3
        = ((gate : ℝ) - 4 - (n : ℝ) + 2) * ((d : ℝ) * Real.log 3) := by ring
      _ ≤ (wgt + 3) * ((d : ℝ) * Real.log 3) :=
          mul_le_mul_of_nonneg_right hbase hdlog0
      _ = 3 * (d : ℝ) * Real.log 3 + ((d : ℝ) * Real.log 3) * wgt := by ring
  · refine mul_le_mul_of_nonneg_left ?_ hKpre
    refine Real.exp_le_exp.mpr ?_
    nlinarith only [hr0, hwgt0]
  · refine mul_le_mul_of_nonneg_left ?_ (rowTwoForcingConst_nonneg d)
    rw [rowTwoRatioBound]
    refine Real.exp_le_exp.mpr ?_
    have h1 : ratioRate d * lam * ((m : ℝ) - (n : ℝ)) ≤ ratioRate d * wgt := by
      rw [hwgtDef]
      calc ratioRate d * lam * ((m : ℝ) - (n : ℝ))
          = ratioRate d * (lam * ((m : ℝ) - (n : ℝ))) := by ring
        _ ≤ ratioRate d * (lam * ((m : ℝ) - (n : ℝ) + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ hr0
            exact mul_le_mul_of_nonneg_left (by linarith) hlam0
    nlinarith only [h1, hA0osc, hPosc, hwgt0]
  · have habs := habsorbC1 alpha halpha ((m : ℝ) - (n : ℝ)) hgapR0
    have heq : A0osc + (Posc + ratioRate d) * wgt +
        (3 * (d : ℝ) * Real.log 3 + ((d : ℝ) * Real.log 3) * wgt) =
        A0f + Pf * (C1⁻¹ * (1 - alpha)) * (((m : ℝ) - (n : ℝ)) + 1) := by
      rw [hA0fDef, hPfDef, hwgtDef, hlamDef,
        Section6Stopping.holderStoppingLambda]
      ring
    rw [heq]
    refine habs.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCabs.le
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have ha0 : (0 : ℝ) ≤ 1 - alpha := by linarith [halpha.2]
    nlinarith only [ha0, hgapR0]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
