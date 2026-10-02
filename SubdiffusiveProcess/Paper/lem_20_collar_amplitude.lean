import SubdiffusiveProcess.Geometry.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess

namespace Paper



/- The existing argument works for every positive collar radius. -/
theorem aux_lem_20_collar_amplitude_all_radii
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (alpha : ℝ) (halpha_lower : 1 / 2 < alpha) (halpha_upper : alpha < 1)
    (KN fNorm : ℝ) (hKN : 1 ≤ KN) (hfNorm : 0 ≤ fNorm)
    (uc : SpatialCoordinates d → ℝ)
    (hcontinuous : ContinuousOn uc
      (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hboundary : ∀ x : SpatialCoordinates d,
      x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)) → uc x = 0)
    (hholder : ∀ x y : SpatialCoordinates d,
      x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
      y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
      |uc x - uc y| ≤ KN * fNorm * dist x y ^ alpha)
    (r : ℝ) (hr : 0 < r) :
    ∀ x : SpatialCoordinates d,
      x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r →
      |uc x| ≤ KN * fNorm * (3 * r) ^ alpha := by
  have hdpos : 0 < d := by omega
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hdpos
  letI : Inhabited (Fin d) := ⟨⟨0, hdpos⟩⟩
  intro x hx hcollar
  have hne : (centeredCube z R hR : Set (SpatialCoordinates d)) ≠ Set.univ := by
    intro hcube
    apply NormedSpace.unbounded_univ ℝ (SpatialCoordinates d)
    rw [← hcube]
    exact centeredCube_isBounded z hR
  obtain ⟨y, hyfront, hdist⟩ :=
    exists_mem_frontier_infDist_compl_eq_dist hx hne
  have hdist_le : dist x y ≤ 3 * r := by
    rw [← hdist]
    exact hcollar
  have halpha_nonneg : 0 ≤ alpha := by
    exact (by norm_num : (0 : ℝ) ≤ 1 / 2).trans halpha_lower.le
  have hrpow : dist x y ^ alpha ≤ (3 * r) ^ alpha :=
    Real.rpow_le_rpow dist_nonneg hdist_le halpha_nonneg
  calc
    |uc x| = |uc x - uc y| := by simp [hboundary y hyfront]
    _ ≤ KN * fNorm * dist x y ^ alpha :=
      hholder x y (subset_closure hx) (frontier_subset_closure hyfront)
    _ ≤ KN * fNorm * (3 * r) ^ alpha :=
      mul_le_mul_of_nonneg_left hrpow (mul_nonneg (zero_le_one.trans hKN) hfNorm)

theorem lem_20_collar_amplitude
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (alpha : ℝ) (halpha_lower : 1 / 2 < alpha) (halpha_upper : alpha < 1)
    (KN fNorm : ℝ) (hKN : 1 ≤ KN) (hfNorm : 0 ≤ fNorm)
    (uc : SpatialCoordinates d → ℝ)
    (hcontinuous : ContinuousOn uc
      (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hboundary : ∀ x : SpatialCoordinates d,
      x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)) → uc x = 0)
    (hholder : ∀ x y : SpatialCoordinates d,
      x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
      y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
      |uc x - uc y| ≤ KN * fNorm * dist x y ^ alpha)
    (r : ℝ) (hr : 0 < r) (hr_upper : r ≤ 1) :
    ∀ x : SpatialCoordinates d,
      x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r →
      |uc x| ≤ KN * fNorm * (3 * r) ^ alpha := by
  exact aux_lem_20_collar_amplitude_all_radii d hd z R hR alpha halpha_lower halpha_upper
    KN fNorm hKN hfNorm uc hcontinuous hboundary hholder r hr

end Paper
