import SubdiffusiveProcess.Static.CubeMassAffine
import SubdiffusiveProcess.Static.CutoffMacroscopicEnergyGrowth

/-! # Integer windows and the geometric cost of a Hölder stopping radius -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The literal truncated cube is a truncated sup-norm ball. -/
theorem harmonic_truncatedCube_eq_ball {d : ℕ} (k n : ℤ) (x : Vec d) :
    truncatedCube d k n x = Metric.ball x ((3 : ℝ)^n / 2) ∩ cube d k := by
  unfold truncatedCube translatedCube cube
  rw [originCube_eq_ball]
  congr 1
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hv
  · intro hy
    refine ⟨y-x, ?_, by simp⟩
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hy

/-- A radius has an enclosing integer window with side at most six times
its radius truncated below one. -/
theorem harmonic_enclosing_window {R : ℝ} (_hR : 0 < R) :
    ∃ n : ℕ, 2 * R ≤ (3 : ℝ)^n ∧ (3 : ℝ)^n ≤ 6 * max R 1 := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (le_max_right (2*R) 1) (by norm_num : (1 : ℝ)<3)
  refine ⟨n+1, (le_max_left (2*R) 1).trans hn'.le, ?_⟩
  rw [pow_succ]
  have hm : max (2*R) 1 ≤ 2 * max R 1 := by
    apply max_le
    · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
    · have := le_max_right R 1
      linarith
  nlinarith only [hn, hm]

/-- The stopped integer-window growth and whole-domain energy imply a
literal all-radius budget, with a geometric moment paying the stopping scale. -/
theorem harmonic_stopped_ball_budget {d : ℕ} (hd : 2 ≤ d) (k X : ℕ)
    (e : Vec d → ℝ≥0∞) {D : ℝ} (hD : 0 ≤ D)
    (hwhole : ∫⁻ y in cube d (k : ℤ), e y ≤ ENNReal.ofReal (D*((3 : ℝ)^k)^d))
    (hwindow : ∀ n : ℕ, (n : ℤ) ≤ (k : ℤ) - (X : ℤ) →
      ∀ x ∈ cube d (k : ℤ), ∫⁻ y in truncatedCube d (k : ℤ) (n : ℤ) x, e y ≤
        ENNReal.ofReal (D * (3 : ℝ)^((k : ℝ)/4) * ((3 : ℝ)^n)^((d : ℝ)-1/4)))
    (x : Vec d) (hx : x ∈ cube d (k : ℤ)) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y in Metric.ball x R ∩ cube d (k : ℤ), e y ≤
      ENNReal.ofReal (D * (3 : ℝ)^((k : ℝ)/4) *
        (6 : ℝ)^((d : ℝ)-1/4) * (3 : ℝ)^((d : ℝ)*(X : ℝ)) *
        (max R 1)^((d : ℝ)-1/4)) := by
  let a : ℝ := (d : ℝ)-1/4
  have ha : 0 ≤ a := by
    dsimp only [a]
    have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hmax : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcost : 1 ≤ (3 : ℝ)^((d : ℝ)*(X : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  obtain ⟨n, hRn, hnR⟩ := harmonic_enclosing_window hR
  by_cases hn : (n : ℤ) ≤ (k : ℤ) - (X : ℤ)
  · refine (lintegral_mono_set (show Metric.ball x R ∩ cube d (k : ℤ) ⊆
        truncatedCube d (k : ℤ) (n : ℤ) x from ?_)).trans
        ((hwindow n hn x hx).trans (ENNReal.ofReal_le_ofReal ?_))
    · rw [harmonic_truncatedCube_eq_ball]
      exact Set.inter_subset_inter_left _ (Metric.ball_subset_ball (by
        rw [zpow_natCast]; linarith))
    · have hpow : ((3 : ℝ)^n)^a ≤ (6 : ℝ)^a*(max R 1)^a := by
        rw [← Real.mul_rpow (by norm_num) hmax.le]
        exact Real.rpow_le_rpow (by positivity) hnR ha
      have hD' : 0 ≤ D * (3 : ℝ)^((k : ℝ)/4) := by positivity
      calc
        _ ≤ D * (3 : ℝ)^((k : ℝ)/4) * ((6 : ℝ)^a*(max R 1)^a) :=
          mul_le_mul_of_nonneg_left hpow hD'
        _ ≤ _ := by
          have hp : 0 ≤ D * (3 : ℝ)^((k : ℝ)/4) * (6 : ℝ)^a * (max R 1)^a := by positivity
          simpa only [one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm, a] using
            mul_le_mul_of_nonneg_left hcost hp
  · have hk : k ≤ n+X := by omega
    have hscale : (3 : ℝ)^k ≤ 6 * max R 1 * (3 : ℝ)^X := by
      calc
        _ ≤ (3 : ℝ)^(n+X) := pow_le_pow_right₀ (by norm_num) hk
        _ = (3 : ℝ)^n*(3 : ℝ)^X := pow_add _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right hnR (by positivity)
    have hXcost : ((3 : ℝ)^X)^a ≤ (3 : ℝ)^((d : ℝ)*(X : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp only [a]
      nlinarith [Nat.cast_nonneg (α := ℝ) X]
    have hpow : ((3 : ℝ)^k)^a ≤
        (6 : ℝ)^a * (max R 1)^a * (3 : ℝ)^((d : ℝ)*(X : ℝ)) := by
      calc
        _ ≤ (6 * max R 1 * (3 : ℝ)^X)^a := Real.rpow_le_rpow (by positivity) hscale ha
        _ = (6 : ℝ)^a*(max R 1)^a*((3 : ℝ)^X)^a := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hmax.le]
        _ ≤ _ := mul_le_mul_of_nonneg_left hXcost (by positivity)
    have hidentity : ((3 : ℝ)^k)^d = (3 : ℝ)^((k : ℝ)/4) * ((3 : ℝ)^k)^a := by
      rw [← Real.rpow_natCast (3 : ℝ) k, ← Real.rpow_mul_natCast (by norm_num),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
      dsimp only [a]
      ring
    refine (lintegral_mono_set Set.inter_subset_right).trans
      (hwhole.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [hidentity, ← mul_assoc]
    have hb := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ D*(3 : ℝ)^((k : ℝ)/4) by positivity)
    simpa only [mul_assoc, mul_left_comm, mul_comm, a] using hb

end SubdiffusiveProcess.Static
