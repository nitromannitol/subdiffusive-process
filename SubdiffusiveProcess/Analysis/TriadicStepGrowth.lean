module

public import SubdiffusiveProcess.Analysis.TriadicFractionalIncrement
public import SubdiffusiveProcess.Geometry.GrowthBoundary
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

theorem triadicStepIncrement_memLp_and_eLpNorm_sq_le_fractionalKernel
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (ν : Measure (SpatialCoordinates d)) (hν : IsFiniteMeasure ν)
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Q), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 →
        ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t))
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hrsmall : r / 3 ≤ 1)
    (hparent : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Q))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    let Δ : SpatialCoordinates d → ℝ := fun x =>
      ∑ k : OddGridIndex d 1,
        (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)).indicator
          (fun _ => averageOn
              (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) f -
            averageOn (centeredCube z r hr : Set (SpatialCoordinates d)) f) x
    MemLp Δ 2 ν ∧
      eLpNorm Δ 2 ν ^ (2 : ℕ) ≤
        ENNReal.ofReal
          ((K * (r / 3) ^ t) * (((r / 3) ^ d) * (r ^ d))⁻¹) *
          (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
            (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
                ENNReal.ofReal ((f y - f x) ^ 2) /
                  (ENNReal.ofReal
                    (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^
                      ((d : ℝ) + 1)) := by
  classical
  letI := hν
  dsimp only
  let a : OddGridIndex d 1 → ℝ := fun k =>
    averageOn (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) f -
      averageOn (centeredCube z r hr : Set (SpatialCoordinates d)) f
  let S : OddGridIndex d 1 → Set (SpatialCoordinates d) := fun k =>
    (oddGridCell z r hr 1 k : Set (SpatialCoordinates d))
  let Δ : SpatialCoordinates d → ℝ := fun x =>
    ∑ k : OddGridIndex d 1, (S k).indicator (fun _ => a k) x
  change MemLp Δ 2 ν ∧
      eLpNorm Δ 2 ν ^ (2 : ℕ) ≤
        ENNReal.ofReal
          ((K * (r / 3) ^ t) * (((r / 3) ^ d) * (r ^ d))⁻¹) *
          (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
            (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
                ENNReal.ofReal ((f y - f x) ^ 2) /
                  (ENNReal.ofReal
                    (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^
                      ((d : ℝ) + 1))
  have hmass : ∀ k : OddGridIndex d 1,
      ν.real (S k) ≤ K * (r / 3) ^ t := by
    intro k
    have hcenter : oddGridCenter z r 1 k ∈
        (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      apply oddGridCell_subset z hr 1 k
      have hcell : (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) =
          Metric.ball (oddGridCenter z r 1 k)
            ((r / (2 * (1 : ℝ) + 1)) / 2) := by
        ext x
        norm_num [oddGridCell, centeredCube]
      rw [hcell]
      exact Metric.mem_ball_self (by positivity)
    have hglobal : oddGridCenter z r 1 k ∈
        closure (Homogenization.openCubeSet Q) := hparent hcenter
    have hsub : S k ⊆ Metric.ball (oddGridCenter z r 1 k) (r / 3) := by
      intro x hx
      have hx' : dist x (oddGridCenter z r 1 k) <
          (r / (2 * (1 : ℝ) + 1)) / 2 := by
        rw [show S k = (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) by rfl,
          show (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) =
            Metric.ball (oddGridCenter z r 1 k)
              ((r / (2 * (1 : ℝ) + 1)) / 2) by
            ext y
            norm_num [oddGridCell, centeredCube]] at hx
        exact (Metric.mem_ball.mp hx)
      rw [Metric.mem_ball]
      norm_num at hx' ⊢
      linarith
    have hbound : ν (S k) ≤ ENNReal.ofReal (K * (r / 3) ^ t) := by
      apply (measure_mono hsub).trans
      exact hgrowth _ hglobal _ (by positivity) hrsmall
    calc
      ν.real (S k) ≤ ν.real (Metric.ball (oddGridCenter z r 1 k) (r / 3)) :=
        measureReal_mono hsub
      _ = (ν (Metric.ball (oddGridCenter z r 1 k) (r / 3))).toReal := rfl
      _ ≤ (ENNReal.ofReal (K * (r / 3) ^ t)).toReal :=
        ENNReal.toReal_mono (by simp)
          (hgrowth _ hglobal _ (by positivity) hrsmall)
      _ = K * (r / 3) ^ t := by
        rw [ENNReal.toReal_ofReal]
        positivity
  have hconst : ∀ k : OddGridIndex d 1,
      MemLp ((S k).indicator (fun _ => a k)) 2 ν := by
    intro k
    apply memLp_indicator_const
    · exact (oddGridCell z r hr 1 k).isOpen.measurableSet
    · exact Or.inr (by finiteness)
  have hmem : MemLp Δ 2 ν := by
    simpa [Δ] using
      (memLp_finset_sum (Finset.univ : Finset (OddGridIndex d 1))
        (fun k hk => hconst k))
  refine ⟨hmem, ?_⟩
  have he : eLpNorm Δ 2 ν ^ (2 : ℕ) =
      ∫⁻ x, ‖Δ x‖ₑ ^ (2 : ℝ) ∂ν := by
    convert eLpNorm_nnreal_pow_eq_lintegral (f := Δ) (p := (2 : NNReal))
      (by norm_num) hmem.aestronglyMeasurable using 1 <;> norm_num
  rw [he]
  have hnorm : ∀ x, ‖Δ x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (Δ x ^ 2) := by
    intro x
    rw [← ofReal_norm_eq_enorm, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (norm_nonneg (Δ x)) 2]
    congr 1
    rw [Real.norm_eq_abs, sq_abs]
  rw [show (fun x => ‖Δ x‖ₑ ^ (2 : ℝ)) =
      (fun x => ENNReal.ofReal (Δ x ^ 2)) by funext x; exact hnorm x]
  have hpoint : ∀ x, ENNReal.ofReal (Δ x ^ 2) =
      ∑ k : OddGridIndex d 1,
        (S k).indicator (fun _ => ENNReal.ofReal (a k ^ 2)) x := by
    intro x
    by_cases hx : ∃ k : OddGridIndex d 1, x ∈ S k
    · obtain ⟨k, hk⟩ := hx
      have hΔ : Δ x = a k := by
        change (∑ l : OddGridIndex d 1,
          (S l).indicator (fun _ => a l) x) = a k
        rw [Finset.sum_eq_single k]
        · simp [Set.indicator_of_mem hk]
        · intro l hl hlk
          have hnot : x ∉ S l := by
            intro hlx
            have hdj : Disjoint (S l) (S k) := by
              simpa [S] using oddGridCell_pairwiseDisjoint z hr 1 hlk
            exact Set.disjoint_left.1 hdj hlx hk
          simp [Set.indicator_of_notMem hnot]
        · intro hk'
          simp at hk'
      have hsum : (∑ l : OddGridIndex d 1,
          (S l).indicator (fun _ => ENNReal.ofReal (a l ^ 2)) x) =
          ENNReal.ofReal (a k ^ 2) := by
        rw [Finset.sum_eq_single k]
        · simp [Set.indicator_of_mem hk]
        · intro l hl hlk
          have hnot : x ∉ S l := by
            intro hlx
            have hdj : Disjoint (S l) (S k) := by
              simpa [S] using oddGridCell_pairwiseDisjoint z hr 1 hlk
            exact Set.disjoint_left.1 hdj hlx hk
          simp [Set.indicator_of_notMem hnot]
        · intro hk'
          simp at hk'
      rw [hΔ, hsum]
    · have hnone : ∀ k : OddGridIndex d 1, x ∉ S k := by
        intro k hk
        exact hx ⟨k, hk⟩
      have hΔ : Δ x = 0 := by
        change (∑ k : OddGridIndex d 1,
          (S k).indicator (fun _ => a k) x) = 0
        apply Finset.sum_eq_zero
        intro k hk
        simp [Set.indicator_of_notMem (hnone k)]
      rw [hΔ]
      simp [hnone]
  rw [show (fun x => ENNReal.ofReal (Δ x ^ 2)) =
      (fun x => ∑ k : OddGridIndex d 1,
        (S k).indicator (fun _ => ENNReal.ofReal (a k ^ 2)) x) by
        funext x; exact hpoint x]
  rw [lintegral_finset_sum (Finset.univ : Finset (OddGridIndex d 1))]
  · have hterm : ∀ k : OddGridIndex d 1,
        ENNReal.ofReal (a k ^ 2) * ν (S k) =
          ENNReal.ofReal (ν.real (S k) * |a k| ^ 2) := by
      intro k
      calc
        ENNReal.ofReal (a k ^ 2) * ν (S k) =
            ENNReal.ofReal (a k ^ 2) * ENNReal.ofReal (ν.real (S k)) := by
          rw [measureReal_def, ENNReal.ofReal_toReal]
          finiteness
        _ = ENNReal.ofReal (ν.real (S k) * a k ^ 2) := by
          rw [mul_comm, ← ENNReal.ofReal_mul measureReal_nonneg]
        _ = ENNReal.ofReal (ν.real (S k) * |a k| ^ 2) := by
          rw [sq_abs]
    have hM : 0 ≤ K * (r / 3) ^ t := by
      exact mul_nonneg hK (Real.rpow_nonneg (by positivity) _)
    have hfrac :=
      ofReal_sum_triadic_child_mass_mul_average_sub_average_sq_le_fractional_kernel
        (hd := hd) (z := z) (r := r) (M := K * (r / 3) ^ t)
        hr hM ν f hf hmass
    calc
      (∑ k : OddGridIndex d 1,
          ∫⁻ (x : SpatialCoordinates d),
            (S k).indicator (fun _ => ENNReal.ofReal (a k ^ 2)) x ∂ν) =
          ∑ k : OddGridIndex d 1,
            ENNReal.ofReal (a k ^ 2) * ν (S k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact lintegral_indicator_const
          (by simpa [S] using (oddGridCell z r hr 1 k).isOpen.measurableSet) _
      _ = ∑ k : OddGridIndex d 1,
          ENNReal.ofReal (ν.real (S k) * |a k| ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k
      _ = ENNReal.ofReal (∑ k : OddGridIndex d 1,
          ν.real (S k) * |a k| ^ 2) := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro k hk
        exact mul_nonneg measureReal_nonneg (sq_nonneg _)
      _ ≤ _ := hfrac
  · intro k hk
    simpa [S] using
      (measurable_const.indicator (oddGridCell z r hr 1 k).isOpen.measurableSet)

end SubdiffusiveProcess
