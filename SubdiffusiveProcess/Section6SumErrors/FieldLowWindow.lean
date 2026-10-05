module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorWindow
@[expose] public section

/-!
# FieldLowWindow

Summing the pre-window field columns with separate old-shell and within-window distances gives an s^{-3} total scale.
-/

namespace SubdiffusiveProcess.Section6SumErrors
open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d
theorem sum_fieldLowScale_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hs : 0 < s) (hs1 : s / 8 ≤ 1) (n m : ℕ) :
    (∑ i ∈ Finset.range n, accumulatedFiniteFieldColumnScale M s n m i) ≤
      gammaTriangleConst 2 * fieldOneGammaDimScale M *
        (24 / (s / 8) ^ 3) := by
  have htri0 : 0 ≤ gammaTriangleConst 2 := gammaTriangleConst_pos.le
  let t : ℝ := s / 8
  let Q : ℝ := fieldOneGeometricBase t
  let F : ℕ → ℝ := fun q ↦ Q ^ q * ((q : ℝ) + 1)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hQ0 : 0 ≤ Q := by exact fieldOneGeometricBase_nonneg t
  have hQ1 : Q < 1 := fieldOneGeometricBase_lt_one ht
  have hnorm : ‖Q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hQ0]
  have hFsum : Summable F := by
    have hNQ : Summable fun q : ℕ ↦ (q : ℝ) * Q ^ q :=
      (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
    have hQsum : Summable fun q : ℕ ↦ Q ^ q :=
      summable_geometric_of_norm_lt_one hnorm
    convert hNQ.add hQsum using 1
    ext q
    unfold F
    ring
  have hF0 : ∀ q, 0 ≤ F q := fun q ↦ by
    unfold F
    positivity
  have hFbound : (∑' q, F q) ≤ 6 / t ^ 2 := by
    simpa only [F, Q] using!
      tsum_fieldOneGeometricBase_mul_succ_le ht hs1
  let G : ℕ → ℝ := fun q ↦ Q ^ q
  have hGsum : Summable G := summable_geometric_of_norm_lt_one hnorm
  have hG0 : ∀ q, 0 ≤ G q := fun q => pow_nonneg hQ0 q
  have hGbound : (∑' q, G q) ≤ 2 / t :=
    tsum_fieldOneGeometricBase_le ht hs1
  have hcolumn : ∀ i ∈ Finset.range n,
      accumulatedFiniteFieldColumnScale M s n m i ≤
        gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (F (n - i) * (∑' q, G q) + G (n - i) * (∑' q, F q)) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hfilter : (Finset.Icc n m).filter (fun k ↦ i ≤ k) =
        Finset.Icc n m := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    have hterm : ∀ k ∈ Finset.Icc n m,
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
            fieldOneCubeMajorantScale M i k ≤
          fieldOneGammaDimScale M * (F (n - i) * G (k - n) + G (n - i) * F (k - n)) := by
      intro k hk
      have hnk := (Finset.mem_Icc.mp hk).1
      have hik : i < k := lt_of_lt_of_le hin hnk
      have hscale0 := fieldOneCubeMajorantScale_le_sqrt M i i (k - i - 1)
      have hscale : fieldOneCubeMajorantScale M i k ≤
          fieldOneGammaDimScale M * Real.sqrt ((k - i : ℕ) : ℝ) := by
        simp only [fieldOneIndexDistance, sub_self, Int.natAbs_zero,
          zero_add] at hscale0
        have hidx : i + 1 + (k - i - 1) = k := by omega
        have hrad : k - i - 1 + 1 = k - i := by omega
        rw [hidx] at hscale0
        norm_num at hscale0
        have hradR : ((k - i - 1 : ℕ) : ℝ) + 1 = ((k - i : ℕ) : ℝ) := by
          exact_mod_cast hrad
        rw [hradR] at hscale0
        exact hscale0
      have hsqrt : Real.sqrt ((k - i : ℕ) : ℝ) ≤
          (((n - i : ℕ) : ℝ) + 1) + (((k - n : ℕ) : ℝ) + 1) := by
        have hki : 1 ≤ k - i := by omega
        have hsqrtSelf : Real.sqrt ((k - i : ℕ) : ℝ) ≤ (k - i : ℕ) := by
          rw [Real.sqrt_le_iff]
          constructor
          · positivity
          · have : (1 : ℝ) ≤ (k - i : ℕ) := by exact_mod_cast hki
            nlinarith
        have hsplit : k - i = (n - i) + (k - n) := by omega
        rw [hsplit] at hsqrtSelf
        rw [hsplit]
        push_cast at hsqrtSelf ⊢
        have hab : 0 ≤ ((n - i : ℕ) : ℝ) * ((k - n : ℕ) : ℝ) :=
          mul_nonneg (by positivity) (by positivity)
        nlinarith
      have hweight :
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) =
            Q ^ (n - i) * Q ^ (k - n) := by
        have hsplit : k - i = (n - i) + (k - n) := by omega
        rw [← Nat.cast_sub hik.le]
        rw [hsplit, Nat.cast_add]
        rw [show s / 8 = t by rfl]
        rw [show -t * (((n - i : ℕ) : ℝ) + ((k - n : ℕ) : ℝ)) =
          (-t * ((n - i : ℕ) : ℝ)) + (-t * ((k - n : ℕ) : ℝ)) by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        rw [show -t * ((n - i : ℕ) : ℝ) =
          -(t * ((n - i : ℕ) : ℝ)) by ring,
          show -t * ((k - n : ℕ) : ℝ) =
          -(t * ((k - n : ℕ) : ℝ)) by ring,
          fieldOne_qWeight_eq_pow, fieldOne_qWeight_eq_pow]
      rw [hweight]
      unfold F G
      have hD0 : 0 ≤ fieldOneGammaDimScale M := by
        unfold fieldOneGammaDimScale
        have hlog : 0 < 1 + Real.log 2 := by
          have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          linarith
        exact mul_nonneg
          (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
          (mul_nonneg (Real.rpow_nonneg hlog.le _) M.shellPrefix.delta_pos.le)
      calc
        _ ≤ (Q ^ (n - i) * Q ^ (k - n)) *
            (fieldOneGammaDimScale M * Real.sqrt ((k - i : ℕ) : ℝ)) := by
          gcongr
        _ ≤ (Q ^ (n - i) * Q ^ (k - n)) *
            (fieldOneGammaDimScale M *
              ((((n - i : ℕ) : ℝ) + 1) + (((k - n : ℕ) : ℝ) + 1))) := by
          gcongr
        _ = _ := by ring
    unfold accumulatedFiniteFieldColumnScale
    rw [hfilter]
    have hsumPoint := Finset.sum_le_sum fun k hk ↦ hterm k hk
    have hinnerF := sum_Icc_sub_le_tsum hF0 hFsum (n := n) (m := m)
    have hinnerG := sum_Icc_sub_le_tsum hG0 hGsum (n := n) (m := m)
    have hD0 : 0 ≤ fieldOneGammaDimScale M := by
      unfold fieldOneGammaDimScale
      have hlog : 0 < 1 + Real.log 2 := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith
      exact mul_nonneg
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (mul_nonneg (Real.rpow_nonneg hlog.le _) M.shellPrefix.delta_pos.le)
    calc
      gammaTriangleConst 2 *
          ∑ k ∈ Finset.Icc n m,
            (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
              fieldOneCubeMajorantScale M i k ≤
        gammaTriangleConst 2 *
          ∑ k ∈ Finset.Icc n m,
            fieldOneGammaDimScale M * (F (n - i) * G (k - n) + G (n - i) * F (k - n)) := by
          exact mul_le_mul_of_nonneg_left hsumPoint gammaTriangleConst_pos.le
      _ = gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (F (n - i) * (∑ k ∈ Finset.Icc n m, G (k - n)) +
            G (n - i) * (∑ k ∈ Finset.Icc n m, F (k - n))) := by
        simp only [mul_add, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (F (n - i) * (∑' q, G q) + G (n - i) * (∑' q, F q)) := by
        gcongr
      _ = _ := by ring
  have hsumColumns := Finset.sum_le_sum hcolumn
  have hreverseF := sum_range_reverse_le_tsum n hF0 hFsum
  have hreverseG := sum_range_reverse_le_tsum n hG0 hGsum
  have htri0 : 0 ≤ gammaTriangleConst 2 := gammaTriangleConst_pos.le
  have hD0 : 0 ≤ fieldOneGammaDimScale M := by
    unfold fieldOneGammaDimScale
    have hlog : 0 < 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.rpow_nonneg hlog.le _) M.shellPrefix.delta_pos.le)
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (F (n - i) * (∑' q, G q) + G (n - i) * (∑' q, F q)) := hsumColumns
    _ = gammaTriangleConst 2 * fieldOneGammaDimScale M *
        ((∑ i ∈ Finset.range n, F (n - i)) * (∑' q, G q) +
          (∑ i ∈ Finset.range n, G (n - i)) * (∑' q, F q)) := by
      simp only [mul_add, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ gammaTriangleConst 2 * fieldOneGammaDimScale M *
        ((∑' q, F q) * (∑' q, G q) + (∑' q, G q) * (∑' q, F q)) := by
      gcongr
    _ ≤ gammaTriangleConst 2 * fieldOneGammaDimScale M *
        ((6 / t ^ 2) * (2 / t) + (2 / t) * (6 / t ^ 2)) := by
      gcongr
    _ = _ := by
      rw [show t = s / 8 by rfl]
      ring

theorem isBigO_fieldLowWindow {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Homogenization.Vec d) {s : ℝ}
    (hs : 0 < s) (hs1 : s / 8 ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (accumulatedFiniteFieldLowWindow z s n m)
      (gammaTriangleConst 2 *
        (gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (24 / (s / 8) ^ 3))) := by
  by_cases hn : n = 0
  · subst n
    have hbase := (isBigOWith_gammaTwo_accumulatedFiniteFieldColumn
      M z s (n := 0) (m := m) (i := 0) (by omega) (by omega)).const_mul
        (c := 0) (by norm_num)
    have hzero : IsBigO M.P.toMeasure (gammaSigma 2)
        (fun _ : Sample d ↦ (0 : ℝ)) 0 := by simpa [IsBigO] using! hbase
    have hfun : accumulatedFiniteFieldLowWindow z s 0 m =
        (fun _ : Sample d ↦ (0 : ℝ)) := by
      funext omega
      simp [accumulatedFiniteFieldLowWindow]
    rw [hfun]
    exact hzero.mono_scale (by
      have htri := gammaTriangleConst_pos (σ := 2)
      have hD : 0 ≤ fieldOneGammaDimScale M := by
        unfold fieldOneGammaDimScale
        have hlog : 0 < 1 + Real.log 2 := by
          have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          linarith
        exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
          (mul_nonneg (Real.rpow_nonneg hlog.le _) M.shellPrefix.delta_pos.le)
      positivity)
  · let X : ℕ → Sample d → ℝ := fun i ↦ accumulatedFiniteFieldColumn z s n m i
    let a : ℕ → ℝ := fun i ↦ accumulatedFiniteFieldColumnScale M s n m i
    have hsum := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := M.P.toMeasure) (Finset.range n) (X := X) (a := a) (σ := 2)
      (by norm_num) (Finset.nonempty_range_iff.mpr hn)
      (fun i hi ↦ by
        have hin : i < n := Finset.mem_range.mp hi
        exact accumulatedFiniteFieldColumnScale_pos M s hnm
          (hin.le.trans hnm))
      (fun i hi ↦ by
        have hin : i < n := Finset.mem_range.mp hi
        have hcol := isBigOWith_gammaTwo_accumulatedFiniteFieldColumn
          M z s hnm (hin.le.trans hnm)
        have hnonneg : ∀ omega,
            0 ≤ accumulatedFiniteFieldColumn z s n m i omega := by
          intro omega
          unfold accumulatedFiniteFieldColumn
          exact Finset.sum_nonneg fun k _ ↦
            mul_nonneg (Real.rpow_nonneg (by norm_num) _)
              (fieldOneCubeMajorant_nonneg i k _)
        simpa only [X, a, IsBigO, abs_of_nonneg (hnonneg _)] using! hcol)
      (fun i _ ↦ (measurable_accumulatedFiniteFieldColumn_shellSigma
        z s n m i).mono (shellSigma_le i) le_rfl)
    have hsum' : IsBigO M.P.toMeasure (gammaSigma 2)
        (accumulatedFiniteFieldLowWindow z s n m)
        (gammaTriangleConst 2 * ∑ i ∈ Finset.range n, a i) := by
      simpa only [accumulatedFiniteFieldLowWindow, X] using! hsum
    refine hsum'.mono_scale ?_
    have hscale := sum_fieldLowScale_le M hs hs1 n m
    exact mul_le_mul_of_nonneg_left (by simpa only [a] using! hscale)
      gammaTriangleConst_pos.le


end
end SubdiffusiveProcess.Section6SumErrors
