import SubdiffusiveProcess.Analysis.GlobalTriadicAverages
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanControlReduction
import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra
import Mathlib.Topology.UniformSpace.HeineCantor

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess

private theorem averageOn_close_of_continuousOn
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (f : SpatialCoordinates d → ℝ)
    (hf : ContinuousOn f (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ k : OddGridIndex d (triadicHalf n),
        x ∈ (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)) →
          |averageOn (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)) f - f x| < ε := by
  let K : Set (SpatialCoordinates d) := closure (centeredCube z r hr : Set (SpatialCoordinates d))
  have hK : IsCompact K := (centeredCube_isBounded z hr).isCompact_closure
  have hU : UniformContinuousOn f K := hK.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.mp hU (ε / 2) (half_pos hε)
  have hside : Filter.Tendsto (fun n : ℕ => r / (2 * (triadicHalf n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ)
      (by norm_num : 0 ≤ (1 / 3 : ℝ)) (by norm_num : (1 / 3 : ℝ) < 1)
    have hmul := (tendsto_const_nhds (x := r)).mul hp
    simpa [triadic_denominator, div_eq_mul_inv, one_div, inv_pow] using hmul
  filter_upwards [hside.eventually (Iio_mem_nhds hδ)] with n hn k hxk
  have hxK : x ∈ K := subset_closure hx
  have hcellK : ∀ y ∈ (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)), y ∈ K := by
    intro y hy
    exact subset_closure (oddGridCell_subset z hr (triadicHalf n) k hy)
  have hclose : ∀ y ∈ (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)),
      |f y - f x| < ε / 2 := by
    intro y hy
    have hxy : dist y x < r / (2 * (triadicHalf n : ℝ) + 1) := by
      let c := oddGridCenter z r (triadicHalf n) k
      have hyc : dist y c < (r / (2 * (triadicHalf n : ℝ) + 1)) / 2 := by
        change dist y (oddGridCenter z r (triadicHalf n) k) <
          (r / (2 * (triadicHalf n : ℝ) + 1)) / 2 at hy
        simpa [c] using hy
      have hxc : dist x c < (r / (2 * (triadicHalf n : ℝ) + 1)) / 2 := by
        change dist x (oddGridCenter z r (triadicHalf n) k) <
          (r / (2 * (triadicHalf n : ℝ) + 1)) / 2 at hxk
        simpa [c] using hxk
      calc
        dist y x ≤ dist y c + dist c x := dist_triangle y c x
        _ < (r / (2 * (triadicHalf n : ℝ) + 1)) / 2 +
            (r / (2 * (triadicHalf n : ℝ) + 1)) / 2 := add_lt_add hyc (by simpa [dist_comm] using hxc)
        _ = r / (2 * (triadicHalf n : ℝ) + 1) := by ring
    have hxy' : dist y x < δ := lt_trans hxy hn
    have hfx := hcont y (hcellK y hy) x hxK hxy'
    simpa [Real.dist_eq, abs_sub_comm] using hfx
  let U : Set (SpatialCoordinates d) := oddGridCell z r hr (triadicHalf n) k
  have hUm : MeasurableSet U := (oddGridCell z r hr (triadicHalf n) k).isOpen.measurableSet
  have hUtop : volume U ≠ ⊤ := by
    rw [oddGridCell_volume]
    exact ENNReal.ofReal_ne_top
  have hUpos : 0 < (volume U).toReal := by
    dsimp [U]
    change 0 < volume.real (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d))
    rw [oddGridCell_volume_real]
    positivity
  have hfK : IntegrableOn f K volume := hf.integrableOn_compact hK
  have hfU : IntegrableOn f U volume := hfK.mono_set (fun y hy => subset_closure (oddGridCell_subset z hr (triadicHalf n) k hy))
  have hupper : averageOn U f ≤ f x + ε / 2 := by
    apply Homogenization.volumeAverage_le_of_le_on hUm hfU hUpos.ne'
    intro y hy
    have := (abs_lt.mp (hclose y hy)).2
    dsimp [U] at hy
    linarith
  have hnegU : IntegrableOn (fun y => -f y) U volume := hfU.neg
  have hnegupper : averageOn U (fun y => -f y) ≤ -(f x - ε / 2) := by
    apply Homogenization.volumeAverage_le_of_le_on hUm hnegU hUpos.ne'
    intro y hy
    have := (abs_lt.mp (hclose y hy)).1
    dsimp [U] at hy
    linarith
  have hneg : averageOn U (fun y => -f y) = -averageOn U f := by
    unfold averageOn Homogenization.volumeAverage
    rw [MeasureTheory.integral_neg]
    ring
  have hbound : |averageOn U f - f x| ≤ ε / 2 := by
    rw [abs_le]
    constructor
    · rw [← neg_le_neg_iff]
      rw [hneg] at hnegupper
      linarith
    · linarith
  dsimp [U] at hbound
  exact lt_of_le_of_lt hbound (half_lt_self hε)

theorem globalTriadicAverages_tendsto_ae_of_continuousOn
    {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (ν : Measure (SpatialCoordinates d))
    (hplanes : ∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0)
    (f : SpatialCoordinates d → ℝ)
    (hf : ContinuousOn f
      (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) :
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  ∀ᵐ x ∂ν, Filter.Tendsto (fun n => E n x) Filter.atTop
    (nhds ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator f x)) := by
  dsimp only
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  change ∀ᵐ x ∂ν, Filter.Tendsto (fun n => E n x) Filter.atTop
    (nhds ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator f x))
  have hgood : ∀ᵐ x ∂ν, ∀ m : ℕ,
      x ∉ ⋃ i : Fin d, ⋃ q : Fin (2 * triadicHalf m + 2),
        triadicFaceSet z r (triadicHalf m) i q := by
    apply ae_all_iff.2
    intro m
    apply ae_iff.2
    rw [show {x : SpatialCoordinates d |
        ¬ x ∉ ⋃ i : Fin d, ⋃ q : Fin (2 * triadicHalf m + 2),
          triadicFaceSet z r (triadicHalf m) i q} =
        ⋃ i : Fin d, ⋃ q : Fin (2 * triadicHalf m + 2),
          triadicFaceSet z r (triadicHalf m) i q by
      ext x
      simp]
    exact triadicFaceSet_union_null z hr (triadicHalf m) ν hplanes
  filter_upwards [hgood] with x hx
  by_cases hxroot : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
  · have hcells : ∀ n : ℕ, ∃ k : OddGridIndex d (triadicHalf n),
        x ∈ (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)) := by
      intro n
      apply mem_triadicCell_of_mem_cube_of_not_face z hr (triadicHalf n) x hxroot
      intro i q hq
      exact hx n (by
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨q, hq⟩⟩)
    choose k hk using hcells
    have hE : ∀ n : ℕ, E n x =
        averageOn (oddGridCell z r hr (triadicHalf n) (k n) : Set (SpatialCoordinates d)) f := by
      intro n
      dsimp [E]
      exact sum_indicator_triadicCell_eq z hr (triadicHalf n) x
        (fun j => averageOn
          (oddGridCell z r hr (triadicHalf n) j : Set (SpatialCoordinates d)) f)
        (k n) (hk n)
    have hlim : Filter.Tendsto (fun n : ℕ => E n x) Filter.atTop (nhds (f x)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
        (averageOn_close_of_continuousOn z hr f hf x hxroot hε)
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq, hE n]
      exact hN n hn (k n) (hk n)
    simpa [Set.indicator_of_mem hxroot] using hlim
  · have hzero : ∀ n : ℕ, E n x = 0 := by
      intro n
      dsimp [E]
      exact sum_indicator_triadicCell_eq_zero_of_not_mem_root z hr
        (triadicHalf n) x (fun j => averageOn
          (oddGridCell z r hr (triadicHalf n) j : Set (SpatialCoordinates d)) f) hxroot
    have hlim : Filter.Tendsto (fun n : ℕ => E n x) Filter.atTop (nhds 0) := by
      simpa [hzero] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
        Filter.atTop (nhds 0))
    simpa [Set.indicator_of_notMem hxroot] using hlim

end SubdiffusiveProcess
