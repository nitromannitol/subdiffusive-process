module

public import SubdiffusiveProcess.Analysis.PolynomialGeometricTail
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

/-! Two small depth fractions make a retained-bank error and a discarded-tail
error simultaneously summable on polynomial-geometric catalogues. This is
scalar rate arithmetic and does not assert any stochastic comparison.
-/
open scoped ENNReal BigOperators
namespace SubdiffusiveProcess

/-- Retained and spatial depths can be chosen in order with strict entropy margins. -/
theorem exists_two_depth_rates (D g a c : ℝ) (hD : 0 ≤ D) (hg : 0 ≤ g)
    (ha : 0 < a) (hc : 0 < c) :
    ∃ u v : ℝ, (0 < u ∧ u < 1 / 4) ∧ (0 < v ∧ v < 1 / 4) ∧
      D * u + g * v < c / 4 ∧ g * v < a * u / 2 := by
  let u : ℝ := min (1 / 8) (c / (8 * (D + 1)))
  have hu : 0 < u := lt_min (by norm_num) (div_pos hc (by positivity))
  have hu1 : u < 1 / 4 := (min_le_left _ _).trans_lt (by norm_num)
  have hub : 8 * (D + 1) * u ≤ c := by
    have hh := (le_div_iff₀ (show (0 : ℝ) < 8 * (D + 1) by positivity)).mp
      (min_le_right (1 / 8) (c / (8 * (D + 1))))
    nlinarith only [hh]
  let v : ℝ := min (1 / 8) (min (c / (8 * (g + 1))) (a * u / (4 * (g + 1))))
  have hv : 0 < v := lt_min (by norm_num) (lt_min
    (div_pos hc (by positivity)) (div_pos (mul_pos ha hu) (by positivity)))
  have hv1 : v < 1 / 4 := (min_le_left _ _).trans_lt (by norm_num)
  have hvc : 8 * (g + 1) * v ≤ c := by
    have hquot : v ≤ c / (8 * (g + 1)) :=
      (min_le_right (1 / 8) _).trans (min_le_left _ _)
    have hh := (le_div_iff₀ (show (0 : ℝ) < 8 * (g + 1) by positivity)).mp
      hquot
    nlinarith only [hh]
  have hva : 4 * (g + 1) * v ≤ a * u := by
    have hquot : v ≤ a * u / (4 * (g + 1)) :=
      (min_le_right (1 / 8) _).trans (min_le_right _ _)
    have hh := (le_div_iff₀ (show (0 : ℝ) < 4 * (g + 1) by positivity)).mp
      hquot
    nlinarith only [hh]
  refine ⟨u, v, ⟨hu, hu1⟩, ⟨hv, hv1⟩, ?_, ?_⟩
  · nlinarith only [hub, hvc, hu, hv]
  · nlinarith only [hva, hv, mul_pos ha hu]

/-- The retained-bank exponential loses only a fixed factor when depths are rounded down. -/
theorem retained_depth_rate_le (D c u : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (N : ℕ) :
    (3 : ℝ) ^ (D * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ) - c * (⌊(N : ℝ) / 2⌋₊ : ℝ)) ≤
      (3 : ℝ) ^ (D + c) * (3 : ℝ) ^ ((D * u - c / 2) * N) := by
  have hH := Nat.floor_le (mul_nonneg hu (Nat.cast_nonneg (α := ℝ) N))
  have hK := Nat.lt_floor_add_one ((N : ℝ) / 2)
  rw [← Real.rpow_add (show (0 : ℝ) < 3 by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith only [mul_le_mul_of_nonneg_left hH hD,
    mul_le_mul_of_nonneg_left hK.le hc]

/-- Rounding the retained depth upward in the tail improves its exponential decay. -/
theorem discarded_depth_rate_le (a u : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    (3 : ℝ) ^ (-a * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ)) ≤
      (3 : ℝ) ^ ((-a * u) * N) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hH := Nat.lt_floor_add_one (u * N)
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith only [mul_le_mul_of_nonneg_left hH.le ha]

/-- A polynomial-geometric catalogue preserves both strict two-depth decay margins. -/
theorem two_depth_mesh_tsum_ne_top (k : ℕ → ℕ) (b : ℕ)
    (C A D g a c u v : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hD : 0 ≤ D) (hc : 0 ≤ c) (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hret : g * v + D * u - c / 2 < 0) (htail : g * v - a * u < 0)
    (hcard : ∀ N, (k N : ℝ) ≤ C * ((N : ℝ) + 1) ^ b * (3 : ℝ) ^ ((g * v) * N)) :
    (∑' N : ℕ, (k N : ℝ≥0∞) * ENNReal.ofReal (A *
      ((3 : ℝ) ^ (D * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ) - c * (⌊(N : ℝ) / 2⌋₊ : ℝ)) +
        (3 : ℝ) ^ (-a * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ))))) ≠ ⊤ := by
  let f : ℕ → ℝ := fun N => (k N : ℝ) * (A *
    ((3 : ℝ) ^ (D * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ) - c * (⌊(N : ℝ) / 2⌋₊ : ℝ)) +
      (3 : ℝ) ^ (-a * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ))))
  have hf0 N : 0 ≤ f N := by dsimp only [f]; positivity
  have hdom N : f N ≤ C * A * ((3 : ℝ) ^ (D + c) *
      (((N : ℝ) + 1) ^ b * (3 : ℝ) ^ ((g * v + D * u - c / 2) * N)) +
      ((N : ℝ) + 1) ^ b * (3 : ℝ) ^ ((g * v - a * u) * N)) := by
    have hr := retained_depth_rate_le D c u hD hc hu N
    have ht := discarded_depth_rate_le a u ha N
    have hstep := mul_le_mul (hcard N) (mul_le_mul_of_nonneg_left (add_le_add hr ht) hA)
      (by positivity) (by positivity)
    refine hstep.trans_eq ?_
    rw [mul_add, mul_add]
    have h1 : (3 : ℝ) ^ ((g * v) * N) * (3 : ℝ) ^ ((D * u - c / 2) * N) =
        (3 : ℝ) ^ ((g * v + D * u - c / 2) * N) := by
      rw [← Real.rpow_add (show (0 : ℝ) < 3 by norm_num)]
      congr 1
      ring
    have h2 : (3 : ℝ) ^ ((g * v) * N) * (3 : ℝ) ^ ((-a * u) * N) =
        (3 : ℝ) ^ ((g * v - a * u) * N) := by
      rw [← Real.rpow_add (show (0 : ℝ) < 3 by norm_num)]
      congr 1
      ring
    rw [← h1, ← h2]
    ring
  have hsum : Summable f := Summable.of_nonneg_of_le hf0 hdom
    ((((summable_shifted_pow_mul_triadic b hret).mul_left ((3 : ℝ) ^ (D + c))).add
      (summable_shifted_pow_mul_triadic b htail)).mul_left (C * A))
  have heq N : (k N : ℝ≥0∞) * ENNReal.ofReal (A *
      ((3 : ℝ) ^ (D * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ) - c * (⌊(N : ℝ) / 2⌋₊ : ℝ)) +
        (3 : ℝ) ^ (-a * ((⌊u * N⌋₊ + 1 : ℕ) : ℝ)))) = ENNReal.ofReal (f N) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) (k N))]
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hsum]
  exact ENNReal.ofReal_ne_top

end SubdiffusiveProcess
