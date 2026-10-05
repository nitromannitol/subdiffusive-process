module

public import SubdiffusiveProcess.Probability.PrefixMeshAllowance

@[expose] public section

/-! Simultaneous bounds for two real prefix banks on a growing mesh.
Outer-measure tail bounds suffice; measurable covers handle arbitrary chosen
versions of the prefix limits. This file does not supply those tail bounds.
-/
open MeasureTheory Set
open scoped ENNReal Topology

namespace SubdiffusiveProcess

/-- Exponential tails give one affine allowance for both prefix banks on every mesh. -/
theorem ae_prefix_bound_on_mesh
    {Omega Pos : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (k : ℕ → ℕ) (d b : ℕ) (Ccount Ctail A xi lam : ℝ)
    (hCcount : 0 ≤ Ccount) (hCtail : 0 ≤ Ctail)
    (hA : 0 < A) (hxi : 0 < xi)
    (hrate : (d : ℝ) * Real.log 3 < A * xi)
    (hcard : ∀ n : ℕ, (k n : ℝ) ≤
      Ccount * ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ ((d : ℝ) * n))
    (entry : ∀ n : ℕ, Fin (k n) → Pos)
    (V : Pos → Bool → ℕ → Omega → ℝ)
    (htail : ∀ pos (m : ℕ), 1 ≤ m → ∀ tag,
      mu {omega | lam * (m : ℝ) < V pos tag m omega} ≤
        ENNReal.ofReal (Ctail * Real.exp (-A * (m : ℝ)))) :
    ∀ᵐ omega ∂mu, ∃ B0 : ℝ, 0 < B0 ∧
      ∀ (n : ℕ) (i : Fin (k n)) (m : ℕ), xi * (n : ℝ) + B0 ≤ (m : ℝ) →
        ∀ tag, V (entry n i) tag m omega ≤ lam * (m : ℝ) := by
  classical
  let bad : ∀ n : ℕ, Fin (k n) → ℕ → Set Omega := fun n i m =>
    if m = 0 then ∅ else
      {omega | lam * (m : ℝ) < V (entry n i) false m omega} ∪
      {omega | lam * (m : ℝ) < V (entry n i) true m omega}
  have hbad n i m : mu (bad n i m) ≤
      ENNReal.ofReal ((2 * Ctail) * Real.exp (-A * (m : ℝ))) := by
    by_cases hm : m = 0
    · simp only [bad, ite_eq_left hm, measure_empty]
      exact zero_le
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hn : 0 ≤ Ctail * Real.exp (-A * (m : ℝ)) :=
        mul_nonneg hCtail (Real.exp_pos _).le
      calc
        mu (bad n i m) ≤
            mu {omega | lam * (m : ℝ) < V (entry n i) false m omega} +
            mu {omega | lam * (m : ℝ) < V (entry n i) true m omega} := by
          simp only [bad, ite_eq_right hm]
          exact measure_union_le _ _
        _ ≤ ENNReal.ofReal (Ctail * Real.exp (-A * (m : ℝ))) +
            ENNReal.ofReal (Ctail * Real.exp (-A * (m : ℝ))) :=
          add_le_add (htail _ m hm1 false) (htail _ m hm1 true)
        _ = ENNReal.ofReal ((2 * Ctail) * Real.exp (-A * (m : ℝ))) := by
          rw [← ENNReal.ofReal_add hn hn]
          congr 1
          ring
  have hcommon := exists_common_prefix_allowance mu k d b Ccount (2 * Ctail) A xi
    hCcount (mul_nonneg (by norm_num) hCtail) hA hxi hrate hcard
    (fun n i m => toMeasurable mu (bad n i m))
    (fun n i m => measurableSet_toMeasurable mu (bad n i m))
    (fun n i m => by rw [measure_toMeasurable]; exact hbad n i m)
  filter_upwards [hcommon] with omega homega
  obtain ⟨B0, hB0, hB⟩ := homega
  refine ⟨B0, hB0, ?_⟩
  intro n i m hm tag
  have hm0 : m ≠ 0 := by
    intro heq
    rw [heq, Nat.cast_zero] at hm
    have hn := mul_nonneg hxi.le (Nat.cast_nonneg (α := ℝ) n)
    linarith only [hn, hB0, hm]
  have hnot : omega ∉ bad n i m := fun h =>
    hB n i m hm (subset_toMeasurable mu (bad n i m) h)
  simp only [bad, ite_eq_right hm0, mem_union, not_or] at hnot
  cases tag
  · exact le_of_not_gt hnot.1
  · exact le_of_not_gt hnot.2

end SubdiffusiveProcess
