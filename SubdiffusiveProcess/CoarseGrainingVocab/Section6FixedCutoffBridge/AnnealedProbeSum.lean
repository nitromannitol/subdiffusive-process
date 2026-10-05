module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.FiniteProbeReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.AnnealedResponseDecay

@[expose] public section

/-!
# The annealed bound for the finite probe sum

`FiniteProbeReduction.lean` dominates the Chapter 2 carrier's probe supremum by
the explicit finite sum `finiteProbeSum`, whose summands are `cutoffProbeForm`
values at the `d + d^2` directions `e i` and `e i + e j`.  This file computes
the *annealed* size of that sum.

Two ingredients:

* the probe form is a quadratic form (`cutoffProbeForm_eq_sum`), hence
  homogeneous of degree two, so a probe at an arbitrary direction is
  `vecNormSq` times a probe at a unit direction;
* `expectedJ_le_coarseContrast_sub_one` (the proved step 3) bounds the annealed
  unit probe by `abarScalarReadout * oneStepAnnealedDualReadout - 1`, which
  the contrast-index identity relates it with the
  Chapter 5 contrast index and `exists_annealed_contrast_decay_normalizedCutoffLaw`
  shows to decay algebraically.

The conclusion is the annealed input of the quenched estimate: on the centered
cube of scale `k`,

    `E[finiteProbeSum] ≤ 3 * d^2 * (contrast(k) - 1)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Homogeneity of the probe form -/

theorem cutoffProbeForm_smul (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {alpha : ℝ} (halpha : 0 < alpha) (R : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (t : ℝ) (v : Vec d) :
    cutoffProbeForm M L alpha R omega (t • v) =
      t ^ 2 * cutoffProbeForm M L alpha R omega v := by
  rw [cutoffProbeForm_eq_sum M L halpha R omega,
    cutoffProbeForm_eq_sum M L halpha R omega, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Elementary `vecNormSq` facts -/

theorem vecNormSq_single (i : Fin d) :
    vecNormSq (Pi.single i (1 : ℝ) : Vec d) = 1 := by
  classical
  rw [vecNormSq, vecDot]
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hl
    simp [hl]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem vecNormSq_add_le (u w : Vec d) :
    vecNormSq (u + w) ≤ 2 * vecNormSq u + 2 * vecNormSq w := by
  rw [vecNormSq, vecNormSq, vecNormSq, vecDot, vecDot, vecDot,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (u k - w k)]

theorem vecNormSq_single_add_le (i j : Fin d) :
    vecNormSq ((Pi.single i (1 : ℝ) : Vec d) +
      (Pi.single j (1 : ℝ) : Vec d)) ≤ 4 := by
  have h := vecNormSq_add_le (Pi.single i (1 : ℝ) : Vec d)
    (Pi.single j (1 : ℝ) : Vec d)
  rw [vecNormSq_single, vecNormSq_single] at h
  linarith

/-! ## The annealed probe bound -/

/-- The library coarse contrast at scale `k` is at least one. -/
theorem one_le_coarseContrast [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ) :
    1 ≤ abarScalarReadout M L k * oneStepAnnealedDualReadout M L k := by
  have halpha : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hu : 1 ≤ (ahom M L)⁻¹ * abarScalarReadout M L k := by
    rw [← inv_mul_cancel₀ halpha.ne']
    exact mul_le_mul_of_nonneg_left (ahom_le_abarScalarReadout M L k)
      (inv_nonneg.mpr halpha.le)
  have hv : 1 ≤ ahom M L * oneStepAnnealedDualReadout M L k := by
    rw [← mul_inv_cancel₀ halpha.ne']
    exact mul_le_mul_of_nonneg_left
      (ahom_inv_le_oneStepAnnealedDualReadout M L k) halpha.le
  have hprod : ((ahom M L)⁻¹ * abarScalarReadout M L k) *
      (ahom M L * oneStepAnnealedDualReadout M L k) =
        abarScalarReadout M L k * oneStepAnnealedDualReadout M L k := by
    field_simp
  nlinarith [hu, hv]

/-- The annealed probe form at a general direction, scaled by `vecNormSq`. -/
theorem integral_cutoffProbeForm_le [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ) (v : Vec d) :
    (∫ omega, cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega v
        ∂M.P.toMeasure) ≤
      vecNormSq v *
        (abarScalarReadout M L k * oneStepAnnealedDualReadout M L k - 1) := by
  have halpha : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hcontrast : 0 ≤
      abarScalarReadout M L k * oneStepAnnealedDualReadout M L k - 1 := by
    have := one_le_coarseContrast M L k
    linarith
  rcases eq_or_lt_of_le (vecNormSq_nonneg v) with hzero | hpos
  · -- `v = 0`: the probe form vanishes
    have hv0 : v = 0 := by
      funext i
      have hsum : ∑ k', v k' * v k' = 0 := hzero.symm
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k' _ => mul_self_nonneg (v k'))).1 hsum i (Finset.mem_univ i)
      exact mul_self_eq_zero.1 hall
    subst hv0
    have hsmul : ((0 : ℝ) • (0 : Vec d)) = (0 : Vec d) := by simp
    have hquad : ∀ omega, cutoffProbeForm M L (ahom M L)
        (originCube d (k : ℤ)) omega (0 : Vec d) = 0 := by
      intro omega
      have := cutoffProbeForm_smul M L halpha (originCube d (k : ℤ)) omega
        (0 : ℝ) (0 : Vec d)
      rw [hsmul] at this
      simpa using this
    simp only [hquad, integral_zero, ← hzero]
    simp
  · -- normalize `v`
    set t : ℝ := Real.sqrt (vecNormSq v) with ht
    have htpos : 0 < t := Real.sqrt_pos.2 hpos
    have htsq : t ^ 2 = vecNormSq v := Real.sq_sqrt (vecNormSq_nonneg v)
    set e : Vec d := t⁻¹ • v with he
    have hunit : vecNormSq e = 1 := by
      have : vecNormSq (t⁻¹ • v) = (t⁻¹) ^ 2 * vecNormSq v := by
        rw [vecNormSq, vecNormSq, vecDot, vecDot, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [he, this, ← htsq]
      field_simp
    have hve : v = t • e := by
      rw [he, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
    have hpt : ∀ omega,
        cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega v =
          vecNormSq v *
            cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega e := by
      intro omega
      calc cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega v
          = cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega (t • e) := by
            rw [← hve]
        _ = t ^ 2 * cutoffProbeForm M L (ahom M L)
              (originCube d (k : ℤ)) omega e :=
            cutoffProbeForm_smul M L halpha (originCube d (k : ℤ)) omega t e
        _ = vecNormSq v * cutoffProbeForm M L (ahom M L)
              (originCube d (k : ℤ)) omega e := by rw [htsq]
    simp only [hpt]
    rw [integral_const_mul]
    have hann : (∫ omega, cutoffProbeForm M L (ahom M L)
        (originCube d (k : ℤ)) omega e ∂M.P.toMeasure) ≤
        abarScalarReadout M L k * oneStepAnnealedDualReadout M L k - 1 :=
      expectedJ_le_coarseContrast_sub_one M L k e hunit
    exact mul_le_mul_of_nonneg_left hann (vecNormSq_nonneg v)

/-- **The annealed size of the finite probe sum.** -/
theorem integral_finiteProbeSum_le [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ) :
    (∫ omega, finiteProbeSum M L (ahom M L) (originCube d (k : ℤ)) omega
        ∂M.P.toMeasure) ≤
      3 * (d : ℝ) ^ 2 *
        (abarScalarReadout M L k * oneStepAnnealedDualReadout M L k - 1) := by
  classical
  have halpha : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hcontrast : 0 ≤
      abarScalarReadout M L k * oneStepAnnealedDualReadout M L k - 1 := by
    have := one_le_coarseContrast M L k
    linarith
  set C : ℝ := abarScalarReadout M L k * oneStepAnnealedDualReadout M L k - 1
    with hC
  have hint : ∀ v : Vec d,
      Integrable (fun omega => cutoffProbeForm M L (ahom M L)
        (originCube d (k : ℤ)) omega v) M.P.toMeasure := by
    intro v
    exact integrable_cutoffResponseOnCube M L _ _ _
  have hterm : ∀ i j : Fin d,
      (∫ omega, (1 / 2 : ℝ) *
          (cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
              ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
            cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
              (Pi.single i (1 : ℝ) : Vec d) +
            cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
              (Pi.single j (1 : ℝ) : Vec d)) ∂M.P.toMeasure) ≤ 3 * C := by
    intro i j
    have hadd12 : Integrable (fun omega =>
        cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
            (Pi.single i (1 : ℝ) : Vec d)) M.P.toMeasure :=
      (hint _).add (hint _)
    rw [integral_const_mul, integral_add hadd12 (hint _),
      integral_add (hint _) (hint _)]
    have h1 := integral_cutoffProbeForm_le M L k
      ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d))
    have h2 := integral_cutoffProbeForm_le M L k
      (Pi.single i (1 : ℝ) : Vec d)
    have h3 := integral_cutoffProbeForm_le M L k
      (Pi.single j (1 : ℝ) : Vec d)
    rw [vecNormSq_single] at h2 h3
    have h1' := h1.trans (mul_le_mul_of_nonneg_right
      (vecNormSq_single_add_le (d := d) i j) hcontrast)
    rw [← hC] at h1' h2 h3
    linarith
  have hsum : (∫ omega, finiteProbeSum M L (ahom M L)
      (originCube d (k : ℤ)) omega ∂M.P.toMeasure) ≤
      ∑ _i : Fin d, ∑ _j : Fin d, (3 * C) := by
    have hintij : ∀ i j : Fin d,
        Integrable (fun omega => (1 / 2 : ℝ) *
          (cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
              ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
            cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
              (Pi.single i (1 : ℝ) : Vec d) +
            cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
              (Pi.single j (1 : ℝ) : Vec d))) M.P.toMeasure :=
      fun i j => (((hint _).add (hint _)).add (hint _)).const_mul _
    have hinti : ∀ i : Fin d,
        Integrable (fun omega => ∑ j : Fin d, (1 / 2 : ℝ) *
          (cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
              ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
            cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
              (Pi.single i (1 : ℝ) : Vec d) +
            cutoffProbeForm M L (ahom M L) (originCube d (k : ℤ)) omega
              (Pi.single j (1 : ℝ) : Vec d))) M.P.toMeasure :=
      fun i => integrable_finsetSum _ fun j _ => hintij i j
    simp only [finiteProbeSum]
    rw [integral_finsetSum _ fun i _ => hinti i]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hintij i j]
    exact Finset.sum_le_sum fun j _ => hterm i j
  refine hsum.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
