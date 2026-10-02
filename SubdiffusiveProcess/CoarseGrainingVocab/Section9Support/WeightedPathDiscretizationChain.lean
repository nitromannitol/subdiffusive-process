/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedPathDiscretizationGeometry




set_option autoImplicit false

open Set Homogenization MeasureTheory MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-- A uniform time partition of `[a,b]` whose consecutive samples of a
continuous path differ by less than `eps` in every coordinate. -/
theorem exists_uniform_partition (p : ContinuousPath (Vec d)) (a b : ℝ≥0)
    (hab : a ≤ b) {eps : ℝ} (heps : 0 < eps) :
    ∃ (M : ℕ) (u : ℕ → ℝ≥0), u 0 = a ∧ u M = b ∧ Monotone u ∧
      (∀ m i, |p (u m) i - p (u (m + 1)) i| < eps) := by
  classical
  have hcpt : IsCompact (Set.Icc a b) := isCompact_Icc
  have huc : UniformContinuousOn (⇑p) (Set.Icc a b) :=
    hcpt.uniformContinuousOn_of_continuous p.continuous.continuousOn
  obtain ⟨delta, hdelta, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc eps heps
  set e : ℝ≥0 := Real.toNNReal (delta / 2) with he
  have hecoe : (e : ℝ) = delta / 2 := Real.coe_toNNReal _ (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_ge (((b : ℝ) - (a : ℝ)) / (delta / 2))
  have hMb : (b : ℝ) ≤ (a : ℝ) + (M : ℝ) * (delta / 2) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < delta / 2)).mp hM
    linarith
  set u : ℕ → ℝ≥0 := fun m => min b (a + (m : ℝ≥0) * e) with hu
  have hucoe : ∀ m : ℕ, ((u m : ℝ≥0) : ℝ) = min (b : ℝ) ((a : ℝ) + (m : ℝ) * (delta / 2)) := by
    intro m
    simp only [hu, NNReal.coe_min, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, hecoe]
  have hmonoU : Monotone u := by
    intro m n hmn
    refine min_le_min le_rfl (add_le_add le_rfl ?_)
    have hcast : ((m : ℝ≥0)) ≤ (n : ℝ≥0) := by exact_mod_cast hmn
    exact mul_le_mul_of_nonneg_right hcast (zero_le e)
  have hmem : ∀ m : ℕ, u m ∈ Set.Icc a b := by
    intro m
    refine ⟨?_, min_le_left _ _⟩
    exact le_min hab (le_add_of_nonneg_right (zero_le _))
  have hu0 : u 0 = a := by
    simp only [hu, Nat.cast_zero, zero_mul, add_zero]
    exact min_eq_right hab
  have huM : u M = b := by
    refine min_eq_left ?_
    have : (b : ℝ) ≤ ((a + (M : ℝ≥0) * e : ℝ≥0) : ℝ) := by
      simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, hecoe] using hMb
    exact_mod_cast this
  refine ⟨M, u, hu0, huM, hmonoU, fun m i => ?_⟩
  have hstep : ((u (m + 1) : ℝ≥0) : ℝ) - ((u m : ℝ≥0) : ℝ) ≤ delta / 2 := by
    rw [hucoe, hucoe]
    push_cast
    rcases min_cases (b : ℝ) ((a : ℝ) + (m : ℝ) * (delta / 2)) with ⟨hc, _⟩ | ⟨hc, _⟩
    · rw [hc]
      have := min_le_left (b : ℝ) ((a : ℝ) + ((m : ℝ) + 1) * (delta / 2))
      linarith
    · rw [hc]
      have := min_le_right (b : ℝ) ((a : ℝ) + ((m : ℝ) + 1) * (delta / 2))
      nlinarith
  have hdist : dist (u (m + 1)) (u m) < delta := by
    rw [NNReal.dist_eq, abs_of_nonneg (by
      have := hmonoU (Nat.le_succ m)
      exact sub_nonneg.mpr (by exact_mod_cast this))]
    linarith
  have hp := hmod (u (m + 1)) (hmem (m + 1)) (u m) (hmem m) hdist
  have hcoord : dist (p (u (m + 1)) i) (p (u m) i) < eps :=
    lt_of_le_of_lt (dist_le_pi_dist (p (u (m + 1))) (p (u m)) i) hp
  rw [Real.dist_eq, abs_sub_comm] at hcoord
  exact hcoord

/-- The fine-grid walk attached to a continuous crossing: a `1`-step lattice
walk whose middle quarters carry the samples and whose endpoints are the cubes
of `p a` and `p b`. -/
theorem exists_sampled_grid_walk {r : ℝ} (hr : 0 < r) (Q : Lattice d → Cube d)
    (hQc : ∀ k : Lattice d, (Q k).1 = (gridCube d r k).1)
    (hQs : ∀ k : Lattice d, r ≤ (Q k).2 ∧ (Q k).2 ≤ 3 * r)
    (p : ContinuousPath (Vec d)) (a b : ℝ≥0) (hab : a ≤ b) :
    ∃ (M : ℕ) (k : ℕ → Lattice d) (u : ℕ → ℝ≥0),
      u 0 = a ∧ u M = b ∧ Monotone u ∧
      (∀ m, m < M → latticeDist (k m) (k (m + 1)) ≤ 1) ∧
      (∀ m, m ≤ M → p (u m) ∈ middleQuarter (Q (k m))) ∧
      p a ∈ cubeSet (Q (k 0)) ∧ p b ∈ cubeSet (Q (k M)) := by
  classical
  obtain ⟨M, u, hu0, huM, hmonoU, hstep⟩ :=
    exists_uniform_partition p a b hab (by positivity : (0 : ℝ) < r / 32)
  have hcentre : ∀ (m : Lattice d) (i : Fin d), (Q m).1 i = r / 8 * (m i : ℝ) := by
    intro m i
    simpa [gridCube] using congrFun (hQc m) i
  set k : ℕ → Lattice d := fun m => (exists_grid_near hr (p (u m))).choose with hk
  have hkspec : ∀ m i, |p (u m) i - r / 8 * ((k m) i : ℝ)| ≤ r / 16 :=
    fun m => (exists_grid_near hr (p (u m))).choose_spec
  have hquarter : ∀ m, p (u m) ∈ middleQuarter (Q (k m)) := by
    intro m
    refine mem_centeredAxisCube.mpr fun i => ?_
    rw [hcentre]
    have h1 := hkspec m i
    have h2 := (hQs (k m)).1
    have : r / 16 < (Q (k m)).2 / 4 / 2 := by linarith
    linarith [h1]
  have hcube : ∀ m, p (u m) ∈ cubeSet (Q (k m)) := by
    intro m
    refine mem_centeredAxisCube.mpr fun i => ?_
    rw [hcentre]
    have h1 := hkspec m i
    have h2 := (hQs (k m)).1
    have : r / 16 < (Q (k m)).2 / 2 := by linarith
    linarith [h1]
  refine ⟨M, k, u, hu0, huM, hmonoU, ?_, fun m _ => hquarter m, ?_, ?_⟩
  · intro m _
    exact latticeDist_le_one_of_grid_near hr (hkspec m) (hkspec (m + 1)) (hstep m)
  · rw [← hu0]; exact hcube 0
  · rw [← huM]; exact hcube M

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
