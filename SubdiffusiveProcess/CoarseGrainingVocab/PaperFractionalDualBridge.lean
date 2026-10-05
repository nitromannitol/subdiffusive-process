module

public import SubdiffusiveProcess.Vocab.PaperNegativeFractionalDual
public import Homogenization.Sobolev.Fractional.EuclideanWspCompletedDualExtension
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section

/-!
# The additive paper fractional dual versus the power-aggregated smooth dual

This file proves the norm comparison needed to place the paper's additive
test norm on `CoarseGraining`'s smooth-dual formulation.  The leading
`s ^ (1 / q)` normalization in the paper is retained exactly; consequently
the comparison has the explicit cost `s ^ (-1 / q)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization
open scoped ENNReal

noncomputable section

/-- The power-aggregated full fractional norm is bounded by the corresponding
additive norm before the paper's leading `s` normalization is inserted. -/
theorem cubeEuclideanWspFullENorm_le_additive {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (q : FiniteLpExponent) (F : Vec d → Vec d) :
    cubeEuclideanWspFullENorm Q s q F ≤
      (ENNReal.ofReal (cubeScaleFactor Q)) ^ (-s.1) *
          (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent F +
        cubeEuclideanWspESeminorm Q s q F := by
  let A : ℝ≥0∞ := (ENNReal.ofReal (cubeScaleFactor Q)) ^ (-s.1) *
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent F
  let S : ℝ≥0∞ := cubeEuclideanWspESeminorm Q s q F
  let t : ℝ := q.exponent.toReal
  have ht : 0 < t :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one q.one_lt)) q.lt_top.ne
  have ht1 : 1 ≤ t := by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono q.lt_top.ne q.one_lt.le
  have hbase : cubeEuclideanWspScalePowerWeight Q s q *
        ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent F) ^ t +
      (cubeEuclideanWspESeminorm Q s q F) ^ t = A ^ t + S ^ t := by
    dsimp [A, S, t, cubeEuclideanWspScalePowerWeight]
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le, ← ENNReal.rpow_mul]
  rw [cubeEuclideanWspFullENorm, hbase]
  calc
    (A ^ t + S ^ t) ^ t⁻¹ ≤ ((A + S) ^ t) ^ t⁻¹ :=
      ENNReal.rpow_le_rpow (ENNReal.add_rpow_le_rpow_add A S ht1)
        (inv_nonneg.mpr ht.le)
    _ = A + S := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]
    _ = _ := rfl

/-- **B10, test-norm form.**  The power-aggregated full norm is bounded by
the paper's additive full norm at the exact cost `s ^ (-1 / q)`. -/
theorem cubeEuclideanWspFullENorm_le_paperFractionalFullNorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (q : FiniteLpExponent)
    (F : Vec d → Vec d) :
    cubeEuclideanWspFullENorm Q s q F ≤
      (ENNReal.ofReal s.1) ^ (-(q.exponent.toReal)⁻¹) *
        paperFractionalFullNorm Q s q F := by
  let A : ℝ≥0∞ := (ENNReal.ofReal (cubeScaleFactor Q)) ^ (-s.1) *
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent F
  let S : ℝ≥0∞ := cubeEuclideanWspESeminorm Q s q F
  let t : ℝ := q.exponent.toReal
  let b : ℝ≥0∞ := ENNReal.ofReal s.1
  let c : ℝ≥0∞ := b ^ t⁻¹
  let K : ℝ≥0∞ := b ^ (-t⁻¹)
  have ht : 0 < t :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one q.one_lt)) q.lt_top.ne
  have hb0 : b ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr s.2.1
  have hbtop : b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hb1 : b ≤ 1 := ENNReal.ofReal_le_one.mpr s.2.2.le
  have hK1 : 1 ≤ K :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.ofReal_pos.mpr s.2.1) hb1 (neg_neg_of_pos (inv_pos.mpr ht))
  have hKc : K * c = 1 := by
    dsimp [K, c]
    rw [← ENNReal.rpow_add _ _ hb0 hbtop]
    simp
  have hAS : A + S ≤ K * (c * S + A) := by
    calc
      A + S ≤ K * A + K * (c * S) :=
        add_le_add (by simpa [mul_comm] using mul_le_mul_right hK1 A)
          (by rw [← mul_assoc, hKc, one_mul])
      _ = K * (c * S + A) := by ring
  calc
    cubeEuclideanWspFullENorm Q s q F ≤ A + S := by
      simpa only [A, S] using cubeEuclideanWspFullENorm_le_additive Q s q F
    _ ≤ K * (c * S + A) := hAS
    _ = _ := by rfl

/-- **B10, reverse test-norm form.**  The paper's additive norm is at most
twice the power-aggregated norm.  This direction has no `s` loss. -/
theorem paperFractionalFullNorm_le_two_mul_cubeEuclideanWspFullENorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (q : FiniteLpExponent)
    (F : Vec d → Vec d) :
    paperFractionalFullNorm Q s q F ≤
      2 * cubeEuclideanWspFullENorm Q s q F := by
  let A : ℝ≥0∞ := (ENNReal.ofReal (cubeScaleFactor Q)) ^ (-s.1) *
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent F
  let S : ℝ≥0∞ := cubeEuclideanWspESeminorm Q s q F
  let M : ℝ≥0∞ := cubeEuclideanWspFullENorm Q s q F
  let t : ℝ := q.exponent.toReal
  have ht : 0 < t :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one q.one_lt)) q.lt_top.ne
  have hbase : cubeEuclideanWspScalePowerWeight Q s q *
        ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent F) ^ t +
      (cubeEuclideanWspESeminorm Q s q F) ^ t = A ^ t + S ^ t := by
    dsimp [A, S, t, cubeEuclideanWspScalePowerWeight]
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le, ← ENNReal.rpow_mul]
  have hM : M = (A ^ t + S ^ t) ^ t⁻¹ := by
    dsimp [M]
    rw [cubeEuclideanWspFullENorm, hbase]
  have hA : A ≤ M := by
    rw [hM]
    calc
      A = (A ^ t) ^ t⁻¹ := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]
      _ ≤ (A ^ t + S ^ t) ^ t⁻¹ :=
        ENNReal.rpow_le_rpow (le_add_right le_rfl) (inv_nonneg.mpr ht.le)
  have hS : S ≤ M := by
    rw [hM]
    calc
      S = (S ^ t) ^ t⁻¹ := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]
      _ ≤ (A ^ t + S ^ t) ^ t⁻¹ :=
        ENNReal.rpow_le_rpow (le_add_left le_rfl) (inv_nonneg.mpr ht.le)
  have hc : (ENNReal.ofReal s.1) ^ t⁻¹ ≤ 1 :=
    ENNReal.rpow_le_one (ENNReal.ofReal_le_one.mpr s.2.2.le)
      (inv_nonneg.mpr ht.le)
  rw [paperFractionalFullNorm, paperFractionalSeminorm]
  change (ENNReal.ofReal s.1) ^ t⁻¹ * S + A ≤ 2 * M
  calc
    (ENNReal.ofReal s.1) ^ t⁻¹ * S + A ≤ S + A := by
      simpa [add_comm, mul_comm] using
        add_le_add_right (mul_le_mul_right hc S) A
    _ ≤ M + M := add_le_add hS hA
    _ = 2 * M := by ring

/-- The paper test norm is finite on every globally smooth test field. -/
theorem paperFractionalFullNorm_lt_top_of_smooth {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {q : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s q) :
    paperFractionalFullNorm Q s q h.toField < ⊤ := by
  rw [paperFractionalFullNorm, paperFractionalSeminorm]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg
        (inv_nonneg.mpr ENNReal.toReal_nonneg) ENNReal.ofReal_ne_top))
      h.toCubeEuclideanWspField.eSeminorm_lt_top
  · exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
        (ENNReal.ofReal_ne_zero_iff.mpr (cubeScaleFactor_pos' Q))
        ENNReal.ofReal_ne_top))
      h.toCubeEuclideanWspField.normalizedEuclideanLpENorm_lt_top

/-- **B10, dual form.**  The paper's additive smooth-test dual is controlled
by `CoarseGraining`'s power-norm smooth dual with the exact normalization
cost `s ^ (-1 / p')`.

The normalization step uses the public smooth graph.  It is the accessible
specialization of the private normalization argument in
`EuclideanWspSmoothDual.lean`; no duplicate wrapper is introduced. -/
theorem paperNegativeFractionalDual_le_smoothDual {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    paperNegativeFractionalDual Q s p F ≤
      (ENNReal.ofReal s.1) ^ (-(p.conjugate.exponent.toReal)⁻¹) *
        cubeEuclideanNegativeWspSmoothDualENorm Q s p F := by
  rw [paperNegativeFractionalDual]
  refine iSup_le fun h => ?_
  let N : ℝ≥0∞ := paperFractionalFullNorm Q s p.conjugate h.1.toField
  let K : ℝ≥0∞ := (ENNReal.ofReal s.1) ^ (-(p.conjugate.exponent.toReal)⁻¹)
  let T : ℝ≥0∞ := K * N
  let D : ℝ≥0∞ := cubeEuclideanNegativeWspSmoothDualENorm Q s p F
  have hN0 : N ≠ 0 := h.2
  have hNtop : N ≠ ⊤ := (paperFractionalFullNorm_lt_top_of_smooth h.1).ne
  have hK0 : K ≠ 0 := ne_of_gt
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr s.2.1) ENNReal.ofReal_ne_top)
  have hKtop : K ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero
    (ENNReal.ofReal_ne_zero_iff.mpr s.2.1) ENNReal.ofReal_ne_top
  have hT0 : T ≠ 0 := mul_ne_zero hK0 hN0
  have hTtop : T ≠ ⊤ := (ENNReal.mul_lt_top hKtop.lt_top hNtop.lt_top).ne
  let r : ℝ := T.toReal⁻¹
  have hrpos : 0 < r := inv_pos.mpr (ENNReal.toReal_pos hT0 hTtop)
  let hs : CubeEuclideanWspSmoothTest Q s p.conjugate := r • h.1
  have hr : ENNReal.ofReal r = T⁻¹ := by
    dsimp [r]
    rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hT0 hTtop),
      ENNReal.ofReal_toReal hTtop]
  have hM : cubeEuclideanWspFullENorm Q s p.conjugate h.1.toField ≤ T := by
    simpa only [T, K, N] using
      cubeEuclideanWspFullENorm_le_paperFractionalFullNorm Q s p.conjugate h.1.toField
  have hunit : cubeEuclideanWspFullENorm Q s p.conjugate hs.toField ≤ 1 := by
    rw [← CubeEuclideanWspSmoothTest.graph_enorm_eq_cubeEuclideanWspFullENorm hs,
      show CubeEuclideanWspSmoothTest.graph hs =
          r • CubeEuclideanWspSmoothTest.graph h.1 by
        exact CubeEuclideanWspSmoothTest.graph.map_smul r h.1,
      enorm_smul, CubeEuclideanWspSmoothTest.graph_enorm_eq_cubeEuclideanWspFullENorm h.1,
      Real.enorm_eq_ofReal hrpos.le, hr]
    calc
      T⁻¹ * cubeEuclideanWspFullENorm Q s p.conjugate h.1.toField ≤ T⁻¹ * T := by
        gcongr
      _ = 1 := ENNReal.inv_mul_cancel hT0 hTtop
  let hu : CubeEuclideanWspSmoothUnitTest Q s p.conjugate := ⟨hs, hunit⟩
  have hdual : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| ≤ D := by
    dsimp [D]
    exact le_iSup (fun u : CubeEuclideanWspSmoothUnitTest Q s p.conjugate =>
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F u.1|) hu
  have hpair : cubeEuclideanNormalizedSmoothPairing F hs =
      r * cubeEuclideanNormalizedSmoothPairing F h.1 := by
    change CubeEuclideanWspSmoothTest.pairingLinearMap F hs =
      r * CubeEuclideanWspSmoothTest.pairingLinearMap F h.1
    simpa only [smul_eq_mul] using
      (CubeEuclideanWspSmoothTest.pairingLinearMap F).map_smul r h.1
  have hscaled : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| =
      T⁻¹ * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1| := by
    rw [hpair, abs_mul, abs_of_pos hrpos, ENNReal.ofReal_mul hrpos.le, hr]
  apply (ENNReal.div_le_iff hN0 hNtop).mpr
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1| =
        T * (T⁻¹ * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1|) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hT0 hTtop, one_mul]
    _ = T * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| := by rw [hscaled]
    _ ≤ T * D := by gcongr
    _ = (K * D) * N := by simp only [T]; ring
    _ = ((ENNReal.ofReal s.1) ^ (-(p.conjugate.exponent.toReal)⁻¹) *
          cubeEuclideanNegativeWspSmoothDualENorm Q s p F) * N := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab
