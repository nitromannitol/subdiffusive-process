module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorFieldWindow

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Subadditivity of the square root. -/
theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- Nonnegativity of the dimension/model factor, extracted from the landed
proofs where it is re-derived inline. -/
theorem fieldOneGammaDimScale_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    0 ≤ fieldOneGammaDimScale M := by
  unfold fieldOneGammaDimScale
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    (mul_nonneg (Real.rpow_nonneg hlog.le _) M.shellPrefix.delta_pos.le)

/-- The sharp deterministic bound for the total pre-window column scale:
`≍ delta * (s / 8) ^ (-5 / 2)`, against the landed `(s / 8) ^ (-4)`. -/
def sharpFieldLowColumnScaleSum {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) : ℝ :=
  gammaTriangleConst 2 * fieldOneGammaDimScale M *
    (32 * (Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹ * (s / 8)⁻¹)

theorem sharpFieldLowColumnScaleSum_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ} (hs : 0 < s) :
    0 ≤ sharpFieldLowColumnScaleSum M s := by
  unfold sharpFieldLowColumnScaleSum
  have ht : (0 : ℝ) < s / 8 := by positivity
  have hD := fieldOneGammaDimScale_nonneg M
  have htri := gammaTriangleConst_pos (σ := 2)
  have : (0 : ℝ) ≤ 32 * (Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹ * (s / 8)⁻¹ := by
    positivity
  exact mul_nonneg (mul_nonneg htri.le hD) this

/-- Sharpened form of
`Section6Stopping.sum_accumulatedFiniteFieldColumnScale_low_le`: the pre-window
column scales sum to `≍ delta * (s / 8) ^ (-5 / 2)` rather than
`(s / 8) ^ (-4)`.  The only change from the landed proof is that
`√(q + j)` is split by subadditivity instead of by `(q + 1) * (j + 1)`. -/
theorem sum_accumulatedFiniteFieldColumnScale_low_le_sharp {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hs : 0 < s) (hs1 : s / 8 ≤ 1) (n m : ℕ) :
    (∑ i ∈ Finset.range n, accumulatedFiniteFieldColumnScale M s n m i) ≤
      sharpFieldLowColumnScaleSum M s := by
  set t : ℝ := s / 8 with ht_def
  set Q : ℝ := fieldOneGeometricBase t with hQ_def
  set P : ℕ → ℝ := fun q ↦ Q ^ q with hP_def
  set G : ℕ → ℝ := fun q ↦ Q ^ q * Real.sqrt ((q : ℝ) + 1) with hG_def
  have ht : 0 < t := by rw [ht_def]; positivity
  have hQ0 : 0 ≤ Q := fieldOneGeometricBase_nonneg t
  have hQ1 : Q < 1 := fieldOneGeometricBase_lt_one ht
  have hnorm : ‖Q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hQ0]
  have hPsum : Summable P := summable_geometric_of_norm_lt_one hnorm
  have hGsum : Summable G := summable_geom_mul_sqrt hQ0 hQ1
  have hP0 : ∀ q, 0 ≤ P q := fun q ↦ by rw [hP_def]; positivity
  have hG0 : ∀ q, 0 ≤ G q := fun q ↦ by rw [hG_def]; positivity
  have hTP0 : 0 ≤ ∑' q, P q := tsum_nonneg hP0
  have hTG0 : 0 ≤ ∑' q, G q := tsum_nonneg hG0
  have hPbound : (∑' q, P q) ≤ 2 / t := tsum_fieldOneGeometricBase_le ht hs1
  have hGbound : (∑' q, G q) ≤ 8 * (Real.sqrt t)⁻¹ * t⁻¹ :=
    tsum_fieldOneGeometricBase_mul_sqrt_le ht hs1
  have hD0 : 0 ≤ fieldOneGammaDimScale M := fieldOneGammaDimScale_nonneg M
  have htri0 : 0 ≤ gammaTriangleConst 2 := gammaTriangleConst_pos.le
  -- The per-column bound, with the sharp square-root split.
  have hcolumn : ∀ i ∈ Finset.range n,
      accumulatedFiniteFieldColumnScale M s n m i ≤
        gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (G (n - i) * (∑' q, P q) + P (n - i) * (∑' q, G q)) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hfilter : (Finset.Icc n m).filter (fun k ↦ i ≤ k) = Finset.Icc n m := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    have hterm : ∀ k ∈ Finset.Icc n m,
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
            fieldOneCubeMajorantScale M i k ≤
          fieldOneGammaDimScale M *
            (G (n - i) * P (k - n) + P (n - i) * G (k - n)) := by
      intro k hk
      have hnk := (Finset.mem_Icc.mp hk).1
      have hik : i < k := lt_of_lt_of_le hin hnk
      have hsplit : k - i = (n - i) + (k - n) := by omega
      -- the landed cube-majorant square-root bound
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
      -- THE SHARP STEP: subadditivity of `√`, not `√x ≤ x ≤ (q+1)(j+1)`.
      have hsqrt : Real.sqrt ((k - i : ℕ) : ℝ) ≤
          Real.sqrt (((n - i : ℕ) : ℝ) + 1) +
            Real.sqrt (((k - n : ℕ) : ℝ) + 1) := by
        rw [hsplit, Nat.cast_add]
        refine (sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)).trans ?_
        exact add_le_add (Real.sqrt_le_sqrt (by linarith))
          (Real.sqrt_le_sqrt (by linarith))
      have hweight :
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) =
            Q ^ (n - i) * Q ^ (k - n) := by
        rw [← Nat.cast_sub hik.le]
        rw [hsplit, Nat.cast_add]
        rw [show s / 8 = t from ht_def.symm]
        rw [show -t * (((n - i : ℕ) : ℝ) + ((k - n : ℕ) : ℝ)) =
          (-t * ((n - i : ℕ) : ℝ)) + (-t * ((k - n : ℕ) : ℝ)) by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        rw [show -t * ((n - i : ℕ) : ℝ) = -(t * ((n - i : ℕ) : ℝ)) by ring,
          show -t * ((k - n : ℕ) : ℝ) = -(t * ((k - n : ℕ) : ℝ)) by ring,
          fieldOne_qWeight_eq_pow, fieldOne_qWeight_eq_pow]
      rw [hweight]
      have hpow0 : (0 : ℝ) ≤ Q ^ (n - i) * Q ^ (k - n) :=
        mul_nonneg (pow_nonneg hQ0 _) (pow_nonneg hQ0 _)
      calc
        Q ^ (n - i) * Q ^ (k - n) * fieldOneCubeMajorantScale M i k
            ≤ Q ^ (n - i) * Q ^ (k - n) *
              (fieldOneGammaDimScale M * Real.sqrt ((k - i : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hscale hpow0
        _ ≤ Q ^ (n - i) * Q ^ (k - n) *
              (fieldOneGammaDimScale M *
                (Real.sqrt (((n - i : ℕ) : ℝ) + 1) +
                  Real.sqrt (((k - n : ℕ) : ℝ) + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ hpow0
          exact mul_le_mul_of_nonneg_left hsqrt hD0
        _ = fieldOneGammaDimScale M *
              (G (n - i) * P (k - n) + P (n - i) * G (k - n)) := by
          rw [hP_def, hG_def]; ring
    unfold accumulatedFiniteFieldColumnScale
    rw [hfilter]
    have hsumPoint := Finset.sum_le_sum fun k hk ↦ hterm k hk
    have hinnerP := sum_Icc_sub_le_tsum hP0 hPsum (n := n) (m := m)
    have hinnerG := sum_Icc_sub_le_tsum hG0 hGsum (n := n) (m := m)
    have hrepack : (∑ k ∈ Finset.Icc n m,
        fieldOneGammaDimScale M *
          (G (n - i) * P (k - n) + P (n - i) * G (k - n))) =
        (fieldOneGammaDimScale M * G (n - i)) *
            (∑ k ∈ Finset.Icc n m, P (k - n)) +
          (fieldOneGammaDimScale M * P (n - i)) *
            (∑ k ∈ Finset.Icc n m, G (k - n)) := by
      calc
        (∑ k ∈ Finset.Icc n m,
            fieldOneGammaDimScale M *
              (G (n - i) * P (k - n) + P (n - i) * G (k - n)))
            = ∑ k ∈ Finset.Icc n m,
                ((fieldOneGammaDimScale M * G (n - i)) * P (k - n) +
                  (fieldOneGammaDimScale M * P (n - i)) * G (k - n)) :=
          Finset.sum_congr rfl (fun k _ ↦ by ring)
        _ = (∑ k ∈ Finset.Icc n m,
              (fieldOneGammaDimScale M * G (n - i)) * P (k - n)) +
            (∑ k ∈ Finset.Icc n m,
              (fieldOneGammaDimScale M * P (n - i)) * G (k - n)) :=
          Finset.sum_add_distrib
        _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc
      gammaTriangleConst 2 *
          ∑ k ∈ Finset.Icc n m,
            (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
              fieldOneCubeMajorantScale M i k
          ≤ gammaTriangleConst 2 *
            ∑ k ∈ Finset.Icc n m,
              fieldOneGammaDimScale M *
                (G (n - i) * P (k - n) + P (n - i) * G (k - n)) :=
        mul_le_mul_of_nonneg_left hsumPoint htri0
      _ = gammaTriangleConst 2 *
            ((fieldOneGammaDimScale M * G (n - i)) *
                (∑ k ∈ Finset.Icc n m, P (k - n)) +
              (fieldOneGammaDimScale M * P (n - i)) *
                (∑ k ∈ Finset.Icc n m, G (k - n))) := by rw [hrepack]
      _ ≤ gammaTriangleConst 2 *
            ((fieldOneGammaDimScale M * G (n - i)) * (∑' q, P q) +
              (fieldOneGammaDimScale M * P (n - i)) * (∑' q, G q)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) htri0
        · exact mul_le_mul_of_nonneg_left hinnerP
            (mul_nonneg hD0 (hG0 _))
        · exact mul_le_mul_of_nonneg_left hinnerG
            (mul_nonneg hD0 (hP0 _))
      _ = _ := by ring
  -- Sum the columns.
  have hsumColumns := Finset.sum_le_sum hcolumn
  have hreverseP := sum_range_reverse_le_tsum n hP0 hPsum
  have hreverseG := sum_range_reverse_le_tsum n hG0 hGsum
  have houter : (∑ i ∈ Finset.range n,
      gammaTriangleConst 2 * fieldOneGammaDimScale M *
        (G (n - i) * (∑' q, P q) + P (n - i) * (∑' q, G q))) =
      (gammaTriangleConst 2 * fieldOneGammaDimScale M * (∑' q, P q)) *
          (∑ i ∈ Finset.range n, G (n - i)) +
        (gammaTriangleConst 2 * fieldOneGammaDimScale M * (∑' q, G q)) *
          (∑ i ∈ Finset.range n, P (n - i)) := by
    calc
      (∑ i ∈ Finset.range n,
          gammaTriangleConst 2 * fieldOneGammaDimScale M *
            (G (n - i) * (∑' q, P q) + P (n - i) * (∑' q, G q)))
          = ∑ i ∈ Finset.range n,
              ((gammaTriangleConst 2 * fieldOneGammaDimScale M *
                  (∑' q, P q)) * G (n - i) +
                (gammaTriangleConst 2 * fieldOneGammaDimScale M *
                  (∑' q, G q)) * P (n - i)) :=
        Finset.sum_congr rfl (fun i _ ↦ by ring)
      _ = (∑ i ∈ Finset.range n,
            (gammaTriangleConst 2 * fieldOneGammaDimScale M *
              (∑' q, P q)) * G (n - i)) +
          (∑ i ∈ Finset.range n,
            (gammaTriangleConst 2 * fieldOneGammaDimScale M *
              (∑' q, G q)) * P (n - i)) := Finset.sum_add_distrib
      _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hcoefP : 0 ≤ gammaTriangleConst 2 * fieldOneGammaDimScale M * (∑' q, P q) :=
    mul_nonneg (mul_nonneg htri0 hD0) hTP0
  have hcoefG : 0 ≤ gammaTriangleConst 2 * fieldOneGammaDimScale M * (∑' q, G q) :=
    mul_nonneg (mul_nonneg htri0 hD0) hTG0
  have hmain : (∑ i ∈ Finset.range n, accumulatedFiniteFieldColumnScale M s n m i) ≤
      gammaTriangleConst 2 * fieldOneGammaDimScale M *
        (2 * ((∑' q, P q) * (∑' q, G q))) := by
    refine hsumColumns.trans ?_
    rw [houter]
    have h1 := mul_le_mul_of_nonneg_left hreverseG hcoefP
    have h2 := mul_le_mul_of_nonneg_left hreverseP hcoefG
    have := add_le_add h1 h2
    refine this.trans (le_of_eq ?_)
    ring
  refine hmain.trans ?_
  unfold sharpFieldLowColumnScaleSum
  have hprod : (∑' q, P q) * (∑' q, G q) ≤
      (2 / t) * (8 * (Real.sqrt t)⁻¹ * t⁻¹) := by
    have hG0' : (0 : ℝ) ≤ 8 * (Real.sqrt t)⁻¹ * t⁻¹ := by positivity
    exact mul_le_mul hPbound hGbound hTG0 (by positivity)
  have hcoef : 0 ≤ gammaTriangleConst 2 * fieldOneGammaDimScale M :=
    mul_nonneg htri0 hD0
  have hstep : gammaTriangleConst 2 * fieldOneGammaDimScale M *
      (2 * ((∑' q, P q) * (∑' q, G q))) ≤
      gammaTriangleConst 2 * fieldOneGammaDimScale M *
        (2 * ((2 / t) * (8 * (Real.sqrt t)⁻¹ * t⁻¹))) := by
    refine mul_le_mul_of_nonneg_left ?_ hcoef
    linarith
  refine hstep.trans (le_of_eq ?_)
  rw [← ht_def]
  field_simp
  ring

/-- The field-low window is `Gamma`-two at the sharp scale
`≍ delta * s ^ (-5 / 2)`.  Mirrors
`Section6Stopping.isBigO_accumulatedFiniteFieldLowWindow`, replacing only the
final `mono_scale` input. -/
theorem isBigO_accumulatedFiniteFieldLowWindow_sharp {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d) {s : ℝ}
    (hs : 0 < s) (hs1 : s / 8 ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (accumulatedFiniteFieldLowWindow z s n m)
      (gammaTriangleConst 2 * sharpFieldLowColumnScaleSum M s) := by
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
    refine hzero.mono_scale ?_
    exact mul_nonneg gammaTriangleConst_pos.le
      (sharpFieldLowColumnScaleSum_nonneg M hs)
  · let X : ℕ → Sample d → ℝ := fun i ↦ accumulatedFiniteFieldColumn z s n m i
    let a : ℕ → ℝ := fun i ↦ accumulatedFiniteFieldColumnScale M s n m i
    have hsum := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := M.P.toMeasure) (Finset.range n) (X := X) (a := a) (σ := 2)
      (by norm_num) (Finset.nonempty_range_iff.mpr hn)
      (fun i hi ↦ by
        have hin : i < n := Finset.mem_range.mp hi
        exact accumulatedFiniteFieldColumnScale_pos M s hnm (hin.le.trans hnm))
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
    have hscale := sum_accumulatedFiniteFieldColumnScale_low_le_sharp M hs hs1 n m
    exact mul_le_mul_of_nonneg_left (by simpa only [a] using! hscale)
      gammaTriangleConst_pos.le

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
