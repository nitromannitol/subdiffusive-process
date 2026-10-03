module

public import SubdiffusiveProcess.Paper.in_represented_bounds_seq_collar_count

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff

noncomputable section
namespace Paper

/-- The diameter of a closed grid cell is its side length in the coordinate metric. -/
theorem aux_in_represented_bounds_seq_collar_profile_diameter
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (k : OddGridIndex d m) (x y : SpatialCoordinates d)
    (hx : x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)))
    (hy : y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d))) :
    dist x y ≤ R / (2 * (m : ℝ) + 1) := by
  rw [dist_pi_le_iff (by positivity : 0 ≤ R / (2 * (m : ℝ) + 1))]
  intro i
  rw [Real.dist_eq]
  have hx' := aux_cutoffs_closed_cell_coordinate z R hR m k x hx i
  have hy' := aux_cutoffs_closed_cell_coordinate z R hR m k y hy i
  calc
    |x i - y i| ≤ |x i - oddGridCenter z R m k i| +
        |oddGridCenter z R m k i - y i| := abs_sub_le _ _ _
    _ ≤ R / (2 * (m : ℝ) + 1) := by
      rw [abs_sub_comm (oddGridCenter z R m k i)]
      simp only [oddGridCenter]
      linarith

/-- Harmonic interpolation on a finer grid preserves the exact collar thresholds.
Its energy is the sum of the actual Dirichlet minima on transition cells. -/
theorem in_represented_bounds_seq_collar_profile
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (J : ℕ) (r : ℝ) (hr : 0 < r) (hmesh : R / (3 : ℝ) ^ J ≤ r / 2)
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a) (hapos : ∀ x, 0 < a x)
    (phi : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hsmooth : ContDiff ℝ ∞ phi.toFun) (hcompact : HasCompactSupport phi.toFun)
    (hsupport : tsupport phi.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hrange : ∀ x, 0 ≤ phi.toFun x ∧ phi.toFun x ≤ 1)
    (hzero : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r / 2 →
        phi.toFun x = 0)
    (hone : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      5 * r / 2 ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        phi.toFun x = 1) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ w.toH1Function.toFun x ∧ w.toH1Function.toFun x ≤ 1) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
          w.toH1Function.toFun x = 0) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          w.toH1Function.toFun x = 1) ∧
      (∀ k : OddGridIndex d (triadicHalf J),
        IsWeaklyHarmonicOn a
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k)) ∧
        HasZeroTraceDifferenceOn
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k))
          (phi.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k))) ∧
      energy a (centeredCube z R hR : Set (SpatialCoordinates d)) w.toH1Function ≤
        ∑ k ∈ aux_in_represented_bounds_seq_collar_count_indices z R hR (triadicHalf J) phi.toFun,
          cellDirichletInfimum a
            (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
            (phi.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k)) := by
  classical
  obtain ⟨w, hwcont, hwrange, hwharm, hwen, hwconst, hwpart⟩ :=
    aux_lem_cutoffs_mesh_package hd z R hR J a ha hapos phi hsmooth hcompact hsupport hrange
  have hdiam (k : OddGridIndex d (triadicHalf J)) (x y : SpatialCoordinates d)
      (hx : x ∈ closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)))
      (hy : y ∈ closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))) :
      dist x y ≤ r / 2 := by
    have h := aux_in_represented_bounds_seq_collar_profile_diameter z R hR (triadicHalf J) k x y hx hy
    rw [triadic_denominator] at h
    exact h.trans hmesh
  refine ⟨w, hwcont, hwrange, ?_, ?_, hwharm, ?_⟩
  · intro x hx hxd
    obtain ⟨k, hxk⟩ := aux_lem_cutoffs_holder_exists_cell z hR (triadicHalf J) hx
    apply (hwconst k 0 ?_).1 x hxk
    intro y hy
    apply hzero y (subset_closure (oddGridCell_subset z hR (triadicHalf J) k hy))
    have hdist := hdiam k y x (subset_closure hy) hxk
    have hi := Metric.infDist_le_infDist_add_dist (x := y) (y := x)
      (s := (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ)
    linarith
  · intro x hx hxd
    obtain ⟨k, hxk⟩ := aux_lem_cutoffs_holder_exists_cell z hR (triadicHalf J) hx
    apply (hwconst k 1 ?_).1 x hxk
    intro y hy
    apply hone y (subset_closure (oddGridCell_subset z hR (triadicHalf J) k hy))
    have hdist := hdiam k x y hxk (subset_closure hy)
    have hi := Metric.infDist_le_infDist_add_dist (x := x) (y := y)
      (s := (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ)
    linarith
  · let I := aux_in_represented_bounds_seq_collar_count_indices z R hR (triadicHalf J) phi.toFun
    have hzeroE : ∀ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf J))), k ∉ I →
        energy a (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k)) = 0 := by
      intro k _ hk
      have hnot : ¬ (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
          {x | 0 < phi.toFun x ∧ phi.toFun x < 1}).Nonempty := by
        simpa [I, aux_in_represented_bounds_seq_collar_count_indices] using hk
      rcases aux_lem_cutoffs_nontransition_const z hR (triadicHalf J) k phi.toFun
        hsmooth.continuous hrange hnot with h0 | h1
      · exact aux_lem_cutoffs_energy_zero _ a _
          (hwconst k 0 (fun y hy => h0 y (subset_closure hy))).2
      · exact aux_lem_cutoffs_energy_zero _ a _
          (hwconst k 1 (fun y hy => h1 y (subset_closure hy))).2
    rw [hwpart, ← Finset.sum_subset (Finset.subset_univ I) hzeroE]
    exact le_of_eq (Finset.sum_congr rfl fun k _ => hwen k)

end Paper
