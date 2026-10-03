module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GoodStoppingDepthTail
public import SubdiffusiveProcess.Frozen.Section6.DensityOfGoodScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GammaOneAssembly

@[expose] public section

/-!
# The Γ₁ tail of the cutoff-independent Hölder stopping scale

This closes, for the cutoff-independent carrier, the obligation recorded as
`UncutStoppingGammaOneTail`: the combined stopping scale
`measurableHolderStoppingScale` — which does not mention the cutoff at all, and
so serves every `J ≥ m` at once (the H7 reading, D-011/H7) — satisfies the
frozen Γ₁ bound.

The good-density half needs `DensityOfGoodScalesInput`, which is discharged here
by the PROVED anchor `SubdiffusiveProcess.Frozen.Section6.density_of_good_scales`.

The ingredients are all landed:

* the tail split
  `Section6Stopping.measure_measurableHolderStoppingScale_tail_le_add`;
* the error half `Section6Stopping.exists_errorStoppingDepth_tail`, made
  `ENNReal` by `TailBridge`;
* the good half `Section6Stopping.measure_goodStoppingDepth_tail_le_sum_exp`,
  collapsed by `GoodTailCollapse`;
* the exponent comparison and the two-halves assembly of `GammaOneAssembly`.

What this module supplies is the *choice of constant*: one `C` dominating the
error coefficient `C₁²·holderErrorSpatialCoeff²`, the good coefficient
`4·32⁶·C₁·C₂²·C_g`, the deterministic margin `step + 6`, the geometric prefactor
and the entry threshold, and large enough that the manuscript's α-window
`α ≤ 1 - C·δ·|log δ|^{1/2}` forces both smallness conditions and the
entropy-beating rate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The Γ₁ tail of the cutoff-independent Hölder stopping scale, at ladder
parameters `C1`, `C2` and deterministic margin `step`. -/
def UncutGammaOneTailAt (d : ℕ) (C C1 C2 : ℝ) (step : ℕ) : Prop :=
  ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ m k : ℕ, 0 < k →
        M.P.toMeasure {ω | k <
            Section6Stopping.measurableHolderStoppingScale M alpha
              (Section6Stopping.holderStoppingLambda C1 alpha)
              (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω} ≤
          ENNReal.ofReal (gammaOneRHS M C alpha k)

/-- **The cutoff-independent Γ₁ tail.** -/
theorem exists_uncutGammaOneTail (d : ℕ) [NeZero d] (step : ℕ) {C1 C2 : ℝ}
    (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ C : ℝ, 0 < C ∧ UncutGammaOneTailAt d C C1 C2 step := by
  classical
  have hDensity : Section6Stopping.DensityOfGoodScalesInput d :=
    SubdiffusiveProcess.Frozen.Section6.density_of_good_scales d
  obtain ⟨Ke, Ce, hKe, hCe, herrTail⟩ := exists_errorStoppingDepth_tail_ennreal d
  obtain ⟨Cg, hCg, hgoodTail⟩ :=
    Section6Stopping.measure_goodStoppingDepth_tail_le_sum_exp hDensity
  have hcoeffPos : 0 < Section6Stopping.holderErrorSpatialCoeff d Ce :=
    Section6Stopping.holderErrorSpatialCoeff_pos d Ce
  have hgammaPos : 0 < Section6Stopping.holderGammaOneGeometricConst :=
    Section6Stopping.holderGammaOneGeometricConst_pos
  have hlog3 : 0 ≤ (d : ℝ) * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg d) (Real.log_pos (by norm_num)).le
  set coeff : ℝ := Section6Stopping.holderErrorSpatialCoeff d Ce with hcoeffdef
  clear_value coeff
  have hC1pos : (0 : ℝ) < C1 := by linarith
  have hC2pos : (0 : ℝ) < C2 := by linarith
  set Berr : ℝ := C1 ^ 2 * coeff ^ 2 with hBerrdef
  set A : ℝ := 2 * (32 : ℝ) ^ 6 * C1 * C2 ^ 2 * Cg with hAdef
  set Bgood : ℝ := 2 * A with hBgooddef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hBerrPos : 0 < Berr := by rw [hBerrdef]; positivity
  have hBgoodPos : 0 < Bgood := by rw [hBgooddef]; linarith
  have hAle : A ≤ A * (2 * ((d : ℝ) * Real.log 3) + 3) := by nlinarith [hApos, hlog3]
  have hAle2 : A * (2 * ((d : ℝ) * Real.log 3) + 2) ≤
      A * (2 * ((d : ℝ) * Real.log 3) + 3) := by nlinarith [hApos]
  clear_value Berr A Bgood
  set C : ℝ := 1 + ((step : ℝ) + 6) + Berr + Bgood +
      2 * Section6Stopping.holderGammaOneGeometricConst + Ke + C1 * coeff +
      A * (2 * ((d : ℝ) * Real.log 3) + 3) with hCdef
  have hstep0 : (0 : ℝ) ≤ (step : ℝ) := Nat.cast_nonneg step
  have hKepos : (0 : ℝ) < Ke := by linarith
  have hprod : 0 < C1 * coeff := mul_pos hC1pos hcoeffPos
  have hlast : 0 < A * (2 * ((d : ℝ) * Real.log 3) + 3) := by
    apply mul_pos hApos; linarith
  have hCpos : 0 < C := by rw [hCdef]; linarith
  have hCone : (1 : ℝ) ≤ C := by rw [hCdef]; linarith
  have hCstep : (step : ℝ) + 6 ≤ C := by rw [hCdef]; linarith
  have hBerrC : Berr ≤ C := by rw [hCdef]; linarith
  have hBgoodC : Bgood ≤ C := by rw [hCdef]; linarith
  have hgammaC : Section6Stopping.holderGammaOneGeometricConst ≤ C / 2 := by
    rw [hCdef]; linarith
  have hKeC : Ke ≤ C := by rw [hCdef]; linarith
  have hcoeffC : C1 * coeff ≤ C := by rw [hCdef]; linarith
  have hrateC : A * (2 * ((d : ℝ) * Real.log 3) + 2) ≤ C := by
    rw [hCdef]; linarith
  have hAC : A ≤ C := by rw [hCdef]; linarith
  have hCgt : (1 : ℝ) < C := by rw [hCdef]; linarith
  clear_value C
  refine ⟨C, hCpos, ?_⟩
  intro M hdelta alpha halpha m k hk
  -- basic facts about the model parameters
  have hdelta0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hdelta1 : M.delta < 1 :=
    lt_of_le_of_lt hdelta (inv_lt_one_of_one_lt₀ hCgt)
  have hlogneg : Real.log M.delta < 0 := Real.log_neg hdelta0 hdelta1
  have habsPos : 0 < |Real.log M.delta| := abs_pos.mpr (ne_of_lt hlogneg)
  have hD : 0 < M.delta ^ 2 * |Real.log M.delta| := by positivity
  have hsqrtEq : |Real.log M.delta| ^ (1 / 2 : ℝ) = Real.sqrt |Real.log M.delta| :=
    (Real.sqrt_eq_rpow _).symm
  have hrootPos : 0 < Real.sqrt |Real.log M.delta| := Real.sqrt_pos.mpr habsPos
  have halphaLow : 1 / 2 ≤ alpha := halpha.1
  have halphaUp : alpha ≤ 1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) := halpha.2
  have hwindow : C * M.delta * Real.sqrt |Real.log M.delta| ≤ 1 - alpha := by
    rw [hsqrtEq] at halphaUp; linarith only [halphaUp]
  have hwindowPos : 0 < C * M.delta * Real.sqrt |Real.log M.delta| := by positivity
  have h1malphaPos : 0 < 1 - alpha := lt_of_lt_of_le hwindowPos hwindow
  have h1malphaHalf : 1 - alpha ≤ 1 / 2 := by linarith only [halphaLow]
  -- the square of the window bound
  have hsqroot : Real.sqrt |Real.log M.delta| ^ 2 = |Real.log M.delta| :=
    Real.sq_sqrt habsPos.le
  have hwindowSq : C ^ 2 * (M.delta ^ 2 * |Real.log M.delta|) ≤ (1 - alpha) ^ 2 := by
    have hbase : (C * M.delta * Real.sqrt |Real.log M.delta|) ^ 2 ≤ (1 - alpha) ^ 2 := by
      apply pow_le_pow_left₀ hwindowPos.le hwindow
    calc C ^ 2 * (M.delta ^ 2 * |Real.log M.delta|)
        = (C * M.delta * Real.sqrt |Real.log M.delta|) ^ 2 := by
          rw [mul_pow, mul_pow, hsqroot]; ring
      _ ≤ (1 - alpha) ^ 2 := hbase
  have hCsq : C ≤ C ^ 2 := by
    nlinarith only [mul_nonneg hCpos.le (sub_nonneg.mpr hCone)]
  -- the two stopping parameters
  set lam : ℝ := Section6Stopping.holderStoppingLambda C1 alpha with hlamdef
  set eps : ℝ := Section6Stopping.holderStoppingEpsilon C2 alpha with hepsdef
  have hlamEq : lam = C1⁻¹ * (1 - alpha) := by rw [hlamdef, Section6Stopping.holderStoppingLambda]
  have hepsEq : eps = C2⁻¹ * Real.sqrt (1 - alpha) := by
    rw [hepsdef, Section6Stopping.holderStoppingEpsilon]
  have hlamPos : 0 < lam := by rw [hlamEq]; positivity
  have hlamOne : lam ≤ 1 := by
    rw [hlamEq]
    have hinv : C1⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; exact hC1
    have hmul : C1⁻¹ * (1 - alpha) ≤ 1 * (1 - alpha) :=
      mul_le_mul_of_nonneg_right hinv h1malphaPos.le
    linarith only [hmul, h1malphaHalf]
  have hepsPos : 0 < eps := by
    rw [hepsEq]
    have : 0 < Real.sqrt (1 - alpha) := Real.sqrt_pos.mpr h1malphaPos
    positivity
  have hepsSq : eps ^ 2 = C2⁻¹ ^ 2 * (1 - alpha) := by
    rw [hepsEq, mul_pow, Real.sq_sqrt h1malphaPos.le]
  have hepsOne : eps ≤ 1 := by
    have hs1 : Real.sqrt (1 - alpha) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) - alpha ≤ 1 by linarith only [h1malphaHalf])
      simpa using h
    have hinv : C2⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; exact hC2
    rw [hepsEq]
    have := mul_le_mul hinv hs1 (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    linarith only [this]
  -- error-half hypotheses
  have hdeltaKe : M.delta ≤ Ke⁻¹ := by
    refine hdelta.trans ?_
    exact inv_anti₀ hKepos hKeC
  have hC1inv : (0 : ℝ) < C1⁻¹ := inv_pos.mpr hC1pos
  have hlamLow : coeff * M.delta * Real.sqrt |Real.log M.delta| ≤ lam := by
    have hkey : coeff ≤ C1⁻¹ * C := by
      rw [inv_mul_eq_div, le_div_iff₀ hC1pos]
      linarith only [hcoeffC]
    have hpos : (0 : ℝ) ≤ M.delta * Real.sqrt |Real.log M.delta| :=
      mul_nonneg hdelta0.le hrootPos.le
    rw [hlamEq]
    calc coeff * M.delta * Real.sqrt |Real.log M.delta|
        = coeff * (M.delta * Real.sqrt |Real.log M.delta|) := by ring
      _ ≤ (C1⁻¹ * C) * (M.delta * Real.sqrt |Real.log M.delta|) :=
          mul_le_mul_of_nonneg_right hkey hpos
      _ = C1⁻¹ * (C * M.delta * Real.sqrt |Real.log M.delta|) := by ring
      _ ≤ C1⁻¹ * (1 - alpha) := mul_le_mul_of_nonneg_left hwindow hC1inv.le
  -- good-half hypotheses
  have hsIoc : Section6Stopping.holderStoppingS ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [Section6Stopping.holderStoppingS]; constructor <;> norm_num
  have hs6 : Section6Stopping.holderStoppingS ^ (-6 : ℤ) = (32 : ℝ) ^ 6 := by
    rw [Section6Stopping.holderStoppingS]; norm_num
  have hAD : 2 * (32 : ℝ) ^ 6 * C1 * C2 ^ 2 * Cg * (M.delta ^ 2 * |Real.log M.delta|)
      ≤ (1 - alpha) ^ 2 := by
    have hkey : A * (M.delta ^ 2 * |Real.log M.delta|) ≤ (1 - alpha) ^ 2 := by
      calc A * (M.delta ^ 2 * |Real.log M.delta|)
          ≤ C ^ 2 * (M.delta ^ 2 * |Real.log M.delta|) :=
            mul_le_mul_of_nonneg_right (le_trans hAC hCsq) hD.le
        _ ≤ (1 - alpha) ^ 2 := hwindowSq
    rwa [hAdef] at hkey
  have hC2ne : C2 ≠ 0 := ne_of_gt hC2pos
  have hC1ne : C1 ≠ 0 := ne_of_gt hC1pos
  have hYne : (1 : ℝ) - alpha ≠ 0 := ne_of_gt h1malphaPos
  have hepsinv : eps⁻¹ ^ 2 = C2 ^ 2 * (1 - alpha)⁻¹ := by
    rw [inv_pow, hepsSq]
    field_simp
  have hgoodSmall : Cg * Section6Stopping.holderStoppingS ^ (-6 : ℤ) * eps⁻¹ ^ 2 *
      M.delta ^ 2 * |Real.log M.delta| ≤ lam / 2 := by
    have hnn : (0 : ℝ) ≤ (1 - alpha)⁻¹ / (2 * C1) :=
      div_nonneg (inv_nonneg.mpr h1malphaPos.le) (by linarith only [hC1pos])
    have hL : Cg * Section6Stopping.holderStoppingS ^ (-6 : ℤ) * eps⁻¹ ^ 2 *
        M.delta ^ 2 * |Real.log M.delta|
        = (2 * (32 : ℝ) ^ 6 * C1 * C2 ^ 2 * Cg *
            (M.delta ^ 2 * |Real.log M.delta|)) * ((1 - alpha)⁻¹ / (2 * C1)) := by
      rw [hs6, hepsinv]
      field_simp
    have hR : lam / 2 = (1 - alpha) ^ 2 * ((1 - alpha)⁻¹ / (2 * C1)) := by
      rw [hlamEq]
      field_simp
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right hAD hnn
  -- the collapse rate
  have hRate : 2 * ((d : ℝ) * Real.log 3) + 2 ≤
      Section6Stopping.holderStoppingS ^ 6 * eps ^ 2 * (lam / 2) /
        (Cg * M.delta ^ 2 * |Real.log M.delta|) := by
    have hrateEq : Section6Stopping.holderStoppingS ^ 6 * eps ^ 2 * (lam / 2) /
        (Cg * M.delta ^ 2 * |Real.log M.delta|)
        = (1 - alpha) ^ 2 / (A * (M.delta ^ 2 * |Real.log M.delta|)) := by
      rw [Section6Stopping.holderStoppingS, hepsSq, hlamEq, hAdef]
      field_simp
    have hApos' : (0 : ℝ) < 2 * (32 : ℝ) ^ 6 * C1 * C2 ^ 2 * Cg := by
      rw [← hAdef]; exact hApos
    rw [hrateEq, hAdef, le_div_iff₀ (mul_pos hApos' hD)]
    have hstepA : (2 * (32 : ℝ) ^ 6 * C1 * C2 ^ 2 * Cg) *
        (2 * ((d : ℝ) * Real.log 3) + 2) ≤ C ^ 2 := by
      have h1 : A * (2 * ((d : ℝ) * Real.log 3) + 2) ≤ C ^ 2 :=
        le_trans hrateC hCsq
      rwa [hAdef] at h1
    calc (2 * ((d : ℝ) * Real.log 3) + 2) *
          (2 * (32 : ℝ) ^ 6 * C1 * C2 ^ 2 * Cg * (M.delta ^ 2 * |Real.log M.delta|))
        = ((2 * (32 : ℝ) ^ 6 * C1 * C2 ^ 2 * Cg) *
            (2 * ((d : ℝ) * Real.log 3) + 2)) *
            (M.delta ^ 2 * |Real.log M.delta|) := by ring
      _ ≤ C ^ 2 * (M.delta ^ 2 * |Real.log M.delta|) :=
          mul_le_mul_of_nonneg_right hstepA hD.le
      _ ≤ (1 - alpha) ^ 2 := hwindowSq
  -- assemble
  refine measure_le_gammaOneRHS_of_parts M
    (Derr := fun ω => Section6Stopping.errorStoppingDepth M lam
      Section6Stopping.holderStoppingS m ω)
    (Dgood := fun ω => Section6Stopping.goodStoppingDepth M lam eps
      Section6Stopping.holderStoppingS m ω)
    hCstep hBerrPos hBerrC hBgoodPos hBgoodC hgammaC hD ?_ ?_ ?_
  · intro hkstep
    exact Section6Stopping.measure_measurableHolderStoppingScale_tail_le_add
      M alpha lam eps step m k hkstep
  · intro q hq
    have hraw := herrTail M hdeltaKe lam hlamLow q m hq
    have hexp : lam ^ 2 * max ((q : ℝ) - 1) 0 /
        (coeff ^ 2 * M.delta ^ 2 * |Real.log M.delta|)
        = (1 - alpha) ^ 2 * max ((q : ℝ) - 1) 0 /
          (Berr * (M.delta ^ 2 * |Real.log M.delta|)) := by
      rw [hlamEq, hBerrdef]
      field_simp
    rwa [hexp] at hraw
  · intro q
    by_cases hqm : q ≤ m
    · have hraw := hgoodTail M Section6Stopping.holderStoppingS lam eps hsIoc
        ⟨hlamPos, hlamOne⟩ ⟨hepsPos, hepsOne⟩ hgoodSmall q m
      have hcollapse := sum_entropy_ofReal_exp_le d (r :=
        Section6Stopping.holderStoppingS ^ 6 * eps ^ 2 * (lam / 2) /
          (Cg * M.delta ^ 2 * |Real.log M.delta|)) q m hqm hRate
      have hfinal := hraw.trans hcollapse
      have hexp : -(Section6Stopping.holderStoppingS ^ 6 * eps ^ 2 * (lam / 2) /
            (Cg * M.delta ^ 2 * |Real.log M.delta|) / 2) * (q : ℝ)
          = -((1 - alpha) ^ 2 * (q : ℝ) /
            (Bgood * (M.delta ^ 2 * |Real.log M.delta|))) := by
        rw [Section6Stopping.holderStoppingS, hepsSq, hlamEq, hBgooddef, hAdef]
        field_simp
      rwa [hexp] at hfinal
    · push_neg at hqm
      rw [goodStoppingDepth_tail_eq_empty M lam eps
        Section6Stopping.holderStoppingS m q (by omega)]
      simp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
