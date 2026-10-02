import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.BoundaryEnergy
import SubdiffusiveProcess.Paper.lem_even_fold_construction
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

noncomputable section
namespace Paper




lemma aux_lem_even_energy_transport_sector_subset
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P J : Finset (Fin d)) (hJ : J ⊆ I) :
    coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
        (centeredCube w r hr : Set (SpatialCoordinates d)) ⊆
      (foldedCube w r hr I P : Set (SpatialCoordinates d)) := by
  intro x hx
  rw [centeredCube_eq_pi] at hx
  change x ∈ Set.pi Set.univ (fun j =>
    if j ∈ I then
      (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
        else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
    else Set.Ioo (w j - r / 2) (w j + r / 2))
  intro j hj
  have hxj := hx j (Set.mem_univ j)
  by_cases hI : j ∈ I
  · by_cases hP : j ∈ P
    · dsimp
      rw [if_pos hI, if_pos hP]
      by_cases hJ' : j ∈ J
      · have hxj' : w j - r / 2 < coordinateReflection
            (foldedCubeCenter w r I P) J x j ∧
            coordinateReflection (foldedCubeCenter w r I P) J x j < w j + r / 2 := hxj
        rw [coordinateReflection, if_pos hJ'] at hxj'
        simp [foldedCubeCenter, hI, hP] at hxj'
        constructor <;> linarith
      · have hxj' : w j - r / 2 < coordinateReflection
            (foldedCubeCenter w r I P) J x j ∧
            coordinateReflection (foldedCubeCenter w r I P) J x j < w j + r / 2 := hxj
        rw [coordinateReflection, if_neg hJ'] at hxj'
        constructor <;> linarith
    · dsimp
      rw [if_pos hI, if_neg hP]
      by_cases hJ' : j ∈ J
      · have hxj' : w j - r / 2 < coordinateReflection
            (foldedCubeCenter w r I P) J x j ∧
            coordinateReflection (foldedCubeCenter w r I P) J x j < w j + r / 2 := hxj
        rw [coordinateReflection, if_pos hJ'] at hxj'
        simp [foldedCubeCenter, hI, hP] at hxj'
        constructor <;> linarith
      · have hxj' : w j - r / 2 < coordinateReflection
            (foldedCubeCenter w r I P) J x j ∧
            coordinateReflection (foldedCubeCenter w r I P) J x j < w j + r / 2 := hxj
        rw [coordinateReflection, if_neg hJ'] at hxj'
        constructor <;> linarith
  · dsimp
    rw [if_neg hI]
    have hJ' : j ∉ J := fun h => hI (hJ h)
    have hxj' : w j - r / 2 < coordinateReflection
          (foldedCubeCenter w r I P) J x j ∧
          coordinateReflection (foldedCubeCenter w r I P) J x j < w j + r / 2 := hxj
    rw [coordinateReflection, if_neg hJ'] at hxj'
    exact hxj'

lemma aux_lem_even_energy_transport_sector_disjoint
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P J K : Finset (Fin d)) (hJ : J ⊆ I) (hK : K ⊆ I) (hJK : J ≠ K) :
    Disjoint
      (coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
        (centeredCube w r hr : Set (SpatialCoordinates d)))
      (coordinateReflection (foldedCubeCenter w r I P) K ⁻¹'
        (centeredCube w r hr : Set (SpatialCoordinates d))) := by
  rw [Set.disjoint_left]
  intro x hxJ hxK
  have hex : ∃ j, (j ∈ J ∧ j ∉ K) ∨ (j ∈ K ∧ j ∉ J) := by
    by_contra h
    apply hJK
    apply Finset.Subset.antisymm
    · intro j hj
      by_contra hjK
      exact h ⟨j, Or.inl ⟨hj, hjK⟩⟩
    · intro j hj
      by_contra hjJ
      exact h ⟨j, Or.inr ⟨hj, hjJ⟩⟩
  rcases hex with ⟨j, hJKj | hKJj⟩
  · have hxJj := (hxJ : coordinateReflection (foldedCubeCenter w r I P) J x ∈
        (centeredCube w r hr : Set (SpatialCoordinates d)))
    have hxKj := (hxK : coordinateReflection (foldedCubeCenter w r I P) K x ∈
        (centeredCube w r hr : Set (SpatialCoordinates d)))
    rw [centeredCube_eq_pi] at hxJj hxKj
    have hjI : j ∈ I := hJ hJKj.1
    have hxJj' := hxJj j (Set.mem_univ j)
    have hxKj' := hxKj j (Set.mem_univ j)
    by_cases hP : j ∈ P
    · have hz : foldedCubeCenter w r I P j = w j + r / 2 := by
        simp [foldedCubeCenter, hjI, hP]
      have hJval : coordinateReflection (foldedCubeCenter w r I P) J x j =
          2 * foldedCubeCenter w r I P j - x j := by
        simp [coordinateReflection, hJKj.1]
      have hKval : coordinateReflection (foldedCubeCenter w r I P) K x j = x j := by
        simp [coordinateReflection, hJKj.2]
      rw [hJval] at hxJj'
      rw [hKval] at hxKj'
      simp only [Set.mem_Ioo] at hxJj' hxKj'
      linarith
    · have hz : foldedCubeCenter w r I P j = w j - r / 2 := by
        simp [foldedCubeCenter, hjI, hP]
      have hJval : coordinateReflection (foldedCubeCenter w r I P) J x j =
          2 * foldedCubeCenter w r I P j - x j := by
        simp [coordinateReflection, hJKj.1]
      have hKval : coordinateReflection (foldedCubeCenter w r I P) K x j = x j := by
        simp [coordinateReflection, hJKj.2]
      rw [hJval] at hxJj'
      rw [hKval] at hxKj'
      simp only [Set.mem_Ioo] at hxJj' hxKj'
      linarith
  · have hxJj := (hxJ : coordinateReflection (foldedCubeCenter w r I P) J x ∈
        (centeredCube w r hr : Set (SpatialCoordinates d)))
    have hxKj := (hxK : coordinateReflection (foldedCubeCenter w r I P) K x ∈
        (centeredCube w r hr : Set (SpatialCoordinates d)))
    rw [centeredCube_eq_pi] at hxJj hxKj
    have hjI : j ∈ I := hK hKJj.1
    have hxJj' := hxJj j (Set.mem_univ j)
    have hxKj' := hxKj j (Set.mem_univ j)
    by_cases hP : j ∈ P
    · have hz : foldedCubeCenter w r I P j = w j + r / 2 := by
        simp [foldedCubeCenter, hjI, hP]
      have hJval : coordinateReflection (foldedCubeCenter w r I P) J x j = x j := by
        simp [coordinateReflection, hKJj.2]
      have hKval : coordinateReflection (foldedCubeCenter w r I P) K x j =
          2 * foldedCubeCenter w r I P j - x j := by
        simp [coordinateReflection, hKJj.1]
      rw [hJval] at hxJj'
      rw [hKval] at hxKj'
      simp only [Set.mem_Ioo] at hxJj' hxKj'
      linarith
    · have hz : foldedCubeCenter w r I P j = w j - r / 2 := by
        simp [foldedCubeCenter, hjI, hP]
      have hJval : coordinateReflection (foldedCubeCenter w r I P) J x j = x j := by
        simp [coordinateReflection, hKJj.2]
      have hKval : coordinateReflection (foldedCubeCenter w r I P) K x j =
          2 * foldedCubeCenter w r I P j - x j := by
        simp [coordinateReflection, hKJj.1]
      rw [hJval] at hxJj'
      rw [hKval] at hxKj'
      simp only [Set.mem_Ioo] at hxJj' hxKj'
      linarith

lemma aux_lem_even_energy_transport_sector_cover_point
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P : Finset (Fin d)) (x : SpatialCoordinates d)
    (hx : x ∈ (foldedCube w r hr I P : Set (SpatialCoordinates d)))
    (hneq : ∀ j ∈ I, x j ≠ foldedCubeCenter w r I P j) :
    ∃ J : Finset (Fin d), J ⊆ I ∧
      x ∈ coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
        (centeredCube w r hr : Set (SpatialCoordinates d)) := by
  classical
  let z := foldedCubeCenter w r I P
  let J : Finset (Fin d) := I.filter
    (fun j => (j ∈ P ∧ z j < x j) ∨ (j ∉ P ∧ x j < z j))
  have hJsub : J ⊆ I := by
    exact Finset.filter_subset _ _
  refine ⟨J, hJsub, ?_⟩
  rw [centeredCube_eq_pi]
  intro j hj
  have hxj := hx j (Set.mem_univ j)
  by_cases hI : j ∈ I
  · have hneqj : x j ≠ z j := by
      intro h
      apply hneq j hI
      simpa [z] using h
    by_cases hP : j ∈ P
    · by_cases hJ : j ∈ J
      · have hJ' := (Finset.mem_filter.mp hJ).2
        have hzlt : z j < x j := by
          rcases hJ' with h | h
          · exact h.2
          · exact (h.1 hP).elim
        have hxj' := hxj
        simp [hI, hP] at hxj'
        have hyj : coordinateReflection z J x j = 2 * z j - x j := by
          simp [coordinateReflection, hJ]
        rw [hyj]
        have hz : z j = w j + r / 2 := by
          simp [z, foldedCubeCenter, hI, hP]
        change w j - r / 2 < 2 * z j - x j ∧ 2 * z j - x j < w j + r / 2
        constructor <;> linarith [hxj'.1, hxj'.2, hz]
      · have hnJ : ¬ ((j ∈ P ∧ z j < x j) ∨ (j ∉ P ∧ x j < z j)) := by
          intro h
          exact hJ (Finset.mem_filter.mpr ⟨hI, h⟩)
        have hxlt : x j < z j := by
          rcases lt_or_gt_of_ne hneqj with h | h
          · exact h
          · exfalso
            exact hnJ (Or.inl ⟨hP, h⟩)
        have hxj' := hxj
        simp [hI, hP] at hxj'
        have hyj : coordinateReflection z J x j = x j := by
          simp [coordinateReflection, hJ]
        rw [hyj]
        have hz : z j = w j + r / 2 := by
          simp [z, foldedCubeCenter, hI, hP]
        change w j - r / 2 < x j ∧ x j < w j + r / 2
        exact ⟨hxj'.1, by linarith [hxlt, hz]⟩
    · by_cases hJ : j ∈ J
      · have hJ' := (Finset.mem_filter.mp hJ).2
        have hxlt : x j < z j := by
          rcases hJ' with h | h
          · exact (hP h.1).elim
          · exact h.2
        have hxj' := hxj
        simp [hI, hP] at hxj'
        have hyj : coordinateReflection z J x j = 2 * z j - x j := by
          simp [coordinateReflection, hJ]
        rw [hyj]
        have hz : z j = w j - r / 2 := by
          simp [z, foldedCubeCenter, hI, hP]
        change w j - r / 2 < 2 * z j - x j ∧ 2 * z j - x j < w j + r / 2
        constructor <;> linarith [hxj'.1, hxj'.2, hz]
      · have hnJ : ¬ ((j ∈ P ∧ z j < x j) ∨ (j ∉ P ∧ x j < z j)) := by
          intro h
          exact hJ (Finset.mem_filter.mpr ⟨hI, h⟩)
        have hzlt : z j < x j := by
          rcases lt_or_gt_of_ne hneqj with h | h
          · exfalso
            exact hnJ (Or.inr ⟨hP, h⟩)
          · exact h
        have hxj' := hxj
        simp [hI, hP] at hxj'
        have hyj : coordinateReflection z J x j = x j := by
          simp [coordinateReflection, hJ]
        rw [hyj]
        have hz : z j = w j - r / 2 := by
          simp [z, foldedCubeCenter, hI, hP]
        change w j - r / 2 < x j ∧ x j < w j + r / 2
        exact ⟨by linarith [hzlt, hz], hxj'.2⟩
  · have hJ : j ∉ J := by
      intro h
      exact hI (hJsub h)
    have hxj' := hxj
    simp [hI] at hxj'
    have hyj : coordinateReflection z J x j = x j := by
      simp [coordinateReflection, hJ]
    rw [hyj]
    exact hxj'

lemma aux_lem_even_energy_transport_sector_fold
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P J : Finset (Fin d)) (hJ : J ⊆ I) (x : SpatialCoordinates d)
    (hx : x ∈ coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
      (centeredCube w r hr : Set (SpatialCoordinates d))) :
    coordinateFold (foldedCubeCenter w r I P) I P x =
      coordinateReflection (foldedCubeCenter w r I P) J x := by
  rw [centeredCube_eq_pi] at hx
  funext j
  have hxj := hx j (Set.mem_univ j)
  by_cases hI : j ∈ I
  · by_cases hP : j ∈ P
    · by_cases hJ' : j ∈ J
      · have hRj : w j - r / 2 < coordinateReflection
            (foldedCubeCenter w r I P) J x j ∧
            coordinateReflection (foldedCubeCenter w r I P) J x j < w j + r / 2 := hxj
        rw [coordinateReflection, if_pos hJ'] at hRj
        rw [coordinateFold, if_pos hI]
        simp only [coordinateReflectionSign, if_pos hP]
        have hz : foldedCubeCenter w r I P j = w j + r / 2 := by
          simp [foldedCubeCenter, hI, hP]
        have hxgt : foldedCubeCenter w r I P j < x j := by linarith [hRj.2, hz]
        rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hxgt))]
        simp only [coordinateReflection, if_pos hJ']
        ring
      · have hRj : w j - r / 2 < coordinateReflection
            (foldedCubeCenter w r I P) J x j ∧
            coordinateReflection (foldedCubeCenter w r I P) J x j < w j + r / 2 := hxj
        rw [coordinateReflection, if_neg hJ'] at hRj
        rw [coordinateFold, if_pos hI]
        simp only [coordinateReflectionSign, if_pos hP]
        have hz : foldedCubeCenter w r I P j = w j + r / 2 := by
          simp [foldedCubeCenter, hI, hP]
        have hxlt : x j < foldedCubeCenter w r I P j := by linarith [hRj.2, hz]
        rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxlt))]
        simp only [coordinateReflection, if_neg hJ']
        ring
    · by_cases hJ' : j ∈ J
      · have hRj : w j - r / 2 < coordinateReflection
            (foldedCubeCenter w r I P) J x j ∧
            coordinateReflection (foldedCubeCenter w r I P) J x j < w j + r / 2 := hxj
        rw [coordinateReflection, if_pos hJ'] at hRj
        rw [coordinateFold, if_pos hI]
        simp only [coordinateReflectionSign, if_neg hP]
        have hz : foldedCubeCenter w r I P j = w j - r / 2 := by
          simp [foldedCubeCenter, hI, hP]
        have hxlt : x j < foldedCubeCenter w r I P j := by linarith [hRj.2, hz]
        rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxlt))]
        simp only [coordinateReflection, if_pos hJ']
        ring
      · have hRj : w j - r / 2 < coordinateReflection
            (foldedCubeCenter w r I P) J x j ∧
            coordinateReflection (foldedCubeCenter w r I P) J x j < w j + r / 2 := hxj
        rw [coordinateReflection, if_neg hJ'] at hRj
        rw [coordinateFold, if_pos hI]
        simp only [coordinateReflectionSign, if_neg hP]
        have hz : foldedCubeCenter w r I P j = w j - r / 2 := by
          simp [foldedCubeCenter, hI, hP]
        have hxgt : foldedCubeCenter w r I P j < x j := by linarith [hRj.1, hz]
        rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hxgt))]
        simp only [coordinateReflection, if_neg hJ']
        ring
  · have hJ' : j ∉ J := fun h => hI (hJ h)
    rw [coordinateFold, if_neg hI]
    simp only [coordinateReflection, if_neg hJ']

lemma aux_lem_even_energy_transport_partition
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P : Finset (Fin d)) (f : SpatialCoordinates d → ℝ)
    (hf : Integrable f (volume.restrict
      (foldedCube w r hr I P : Set (SpatialCoordinates d))))
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B) :
    (∫ x in (foldedCube w r hr I P : Set (SpatialCoordinates d)),
        B.indicator f x) =
      ∑ J ∈ I.powerset,
        ∫ x in coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
          (centeredCube w r hr : Set (SpatialCoordinates d)), B.indicator f x := by
  let U : Set (SpatialCoordinates d) := centeredCube w r hr
  let z : SpatialCoordinates d := foldedCubeCenter w r I P
  have hsubset : ∀ J ∈ I.powerset,
      coordinateReflection z J ⁻¹' U ⊆
        (foldedCube w r hr I P : Set (SpatialCoordinates d)) := by
    intro J hJ
    exact aux_lem_even_energy_transport_sector_subset d w r hr I P J
      (Finset.mem_powerset.mp hJ)
  have hmeas : ∀ J : Finset (Fin d), MeasurableSet (coordinateReflection z J ⁻¹' U) := by
    intro J
    exact (centeredCube w r hr).isOpen.measurableSet.preimage
      (coordinateReflection_isometry z J).continuous.measurable
  have hpair : Set.Pairwise (↑I.powerset)
      (fun J K => Disjoint (coordinateReflection z J ⁻¹' U)
        (coordinateReflection z K ⁻¹' U)) := by
    intro J hJ K hK hJK
    exact aux_lem_even_energy_transport_sector_disjoint d w r hr I P J K
      (Finset.mem_powerset.mp hJ) (Finset.mem_powerset.mp hK) hJK
  have h0 : ∀ j : Fin d, ∀ᵐ x : SpatialCoordinates d ∂volume,
      x j ≠ foldedCubeCenter w r I P j := by
    intro j
    rw [ae_iff]
    simpa only [not_not] using
      (Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) j
        (foldedCubeCenter w r I P j))
  have hne : ∀ᵐ x : SpatialCoordinates d ∂volume.restrict
      (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      ∀ j : Fin d, x j ≠ foldedCubeCenter w r I P j := by
    apply ae_all_iff.mpr
    intro j
    exact ae_restrict_of_ae (h0 j)
  have hc : ∀ᵐ x ∂volume.restrict
      (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      x ∈ ⋃ J ∈ I.powerset, coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
        (centeredCube w r hr : Set (SpatialCoordinates d)) := by
    filter_upwards [hne, ae_restrict_mem (foldedCube w r hr I P).isOpen.measurableSet]
      with x hne hx
    obtain ⟨J, hJ, hxJ⟩ :=
      aux_lem_even_energy_transport_sector_cover_point d w r hr I P x hx
        (fun j _ => hne j)
    exact Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2
      ⟨Finset.mem_powerset.mpr hJ, hxJ⟩⟩
  rw [ae_restrict_iff' (foldedCube w r hr I P).isOpen.measurableSet] at hc
  have heq : (foldedCube w r hr I P : Set (SpatialCoordinates d)) =ᵐ[volume]
      ⋃ J ∈ I.powerset, coordinateReflection z J ⁻¹' U := by
    filter_upwards [hc] with x hx
    apply propext
    constructor
    · exact hx
    · intro hu
      rcases Set.mem_iUnion.1 hu with ⟨J, hu⟩
      rcases Set.mem_iUnion.1 hu with ⟨hJ, hxJ⟩
      exact hsubset J hJ hxJ
  rw [setIntegral_congr_set heq]
  rw [integral_biUnion_finset I.powerset]
  · intro J hJ
    exact hmeas J
  · exact hpair
  · intro J hJ
    exact (hf.mono_measure (Measure.restrict_mono (hsubset J hJ) le_rfl)).indicator hB

lemma aux_lem_even_energy_transport_sector_energy_ae
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P J : Finset (Fin d)) (hJ : J ⊆ I)
    (a : PositiveCoefficient (centeredCube w r hr))
    (v : weakSobolevGraph (centeredCube w r hr))
    (af : PositiveCoefficient (foldedCube w r hr I P))
    (vf : weakSobolevGraph (foldedCube w r hr I P))
    (ha : ((af.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
      fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)))
    (hg : (∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
        sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) j x =
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r I P j then -1 else 1)
           else 1) *
            sobolevGradient (v : SobolevData (centeredCube w r hr)) j
              (coordinateFold (foldedCubeCenter w r I P) I P x)))
    (j : Fin d) :
    ∀ᵐ x ∂volume.restrict
      (coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
        (centeredCube w r hr : Set (SpatialCoordinates d))),
      af.val x *
          (sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) j x) ^ 2 =
        a.val (coordinateReflection (foldedCubeCenter w r I P) J x) *
          (sobolevGradient (v : SobolevData (centeredCube w r hr)) j
            (coordinateReflection (foldedCubeCenter w r I P) J x)) ^ 2 := by
  have hsec : coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
      (centeredCube w r hr : Set (SpatialCoordinates d)) ⊆
      (foldedCube w r hr I P : Set (SpatialCoordinates d)) := by
    exact aux_lem_even_energy_transport_sector_subset d w r hr I P J hJ
  have hha := ae_mono (Measure.restrict_mono hsec le_rfl) ha
  have hhg := ae_mono (Measure.restrict_mono hsec le_rfl) (hg j)
  have hmeas : MeasurableSet (coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
      (centeredCube w r hr : Set (SpatialCoordinates d))) :=
    (centeredCube w r hr).isOpen.measurableSet.preimage
      (coordinateReflection_isometry (foldedCubeCenter w r I P) J).continuous.measurable
  filter_upwards [hha, hhg, ae_restrict_mem hmeas] with x hha hhg hxs
  have hfold := aux_lem_even_energy_transport_sector_fold d w r hr I P J hJ x hxs
  rw [hha, hhg, hfold]
  have hq :
      (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) ^ 2 = 1 := by
    by_cases hI : j ∈ I
    · rw [if_pos hI, mul_pow, coordinateReflectionSign_sq]
      by_cases hxj : x j < foldedCubeCenter w r I P j <;> simp [hxj]
    · simp [hI]
  rw [show ((if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) *
        sobolevGradient (v : SobolevData (centeredCube w r hr)) j
          (coordinateReflection (foldedCubeCenter w r I P) J x)) ^ 2 =
      (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) ^ 2 *
        (sobolevGradient (v : SobolevData (centeredCube w r hr)) j
          (coordinateReflection (foldedCubeCenter w r I P) J x)) ^ 2 by ring,
    hq, one_mul]

lemma aux_lem_even_energy_transport_sector_energy_integral
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P J : Finset (Fin d)) (hJ : J ⊆ I)
    (f g : SpatialCoordinates d → ℝ)
    (hfg : ∀ᵐ x ∂volume.restrict
      (coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
        (centeredCube w r hr : Set (SpatialCoordinates d))),
      f x = g (coordinateReflection (foldedCubeCenter w r I P) J x))
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (hBs : ∀ K : Finset (Fin d), K ⊆ I →
      coordinateReflection (foldedCubeCenter w r I P) K ⁻¹' B = B) :
    (∫ x in coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
        (centeredCube w r hr : Set (SpatialCoordinates d)), B.indicator f x) =
      ∫ y in (centeredCube w r hr : Set (SpatialCoordinates d)), B.indicator g y := by
  let U : Set (SpatialCoordinates d) := centeredCube w r hr
  let z : SpatialCoordinates d := foldedCubeCenter w r I P
  have hmp := (coordinateReflection_measurePreserving z J).restrict_preimage
    (centeredCube w r hr).isOpen.measurableSet
  have hBmem : ∀ y : SpatialCoordinates d, y ∈ B ↔ coordinateReflection z J y ∈ B := by
    intro y
    exact (Set.ext_iff.mp (hBs J hJ) y).symm
  calc
    (∫ x in coordinateReflection z J ⁻¹' U, B.indicator f x) =
        ∫ x in coordinateReflection z J ⁻¹' U,
          B.indicator (fun x => g (coordinateReflection z J x)) x := by
      apply integral_congr_ae
      filter_upwards [hfg] with x hx
      by_cases hBx : x ∈ B
      · simp only [Set.indicator_of_mem hBx]
        rw [hx]
      · simp only [Set.indicator_of_notMem hBx]
    _ = ∫ x in coordinateReflection z J ⁻¹' U,
          B.indicator g (coordinateReflection z J x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hBx : x ∈ B
      · have hRx : coordinateReflection z J x ∈ B := (hBmem x).mp hBx
        simp only [Set.indicator_of_mem hBx, Set.indicator_of_mem hRx]
      · have hRx : coordinateReflection z J x ∉ B := by
          intro hRx
          exact hBx ((hBmem x).mpr hRx)
        simp only [Set.indicator_of_notMem hBx, Set.indicator_of_notMem hRx]
    _ = ∫ y in U, B.indicator g y := by
      simpa [U] using
        hmp.integral_comp (coordinateReflectionEquiv z J).toHomeomorph.measurableEmbedding
          (fun y => B.indicator g y)
theorem lem_even_energy_transport
  (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
  (I P : Finset (Fin d))
  (a : PositiveCoefficient (centeredCube w r hr))
  (v : weakSobolevGraph (centeredCube w r hr))
  (af : PositiveCoefficient (foldedCube w r hr I P))
  (vf : weakSobolevGraph (foldedCube w r hr I P))
  (ha : ((af.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
    fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)))
  (hg : (∀ j : Fin d,
    ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) j x =
        (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) *
          sobolevGradient (v : SobolevData (centeredCube w r hr)) j
            (coordinateFold (foldedCubeCenter w r I P) I P x))) :
  ∀ (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B),
    (∀ J : Finset (Fin d), J ⊆ I →
      coordinateReflection (foldedCubeCenter w r I P) J ⁻¹' B = B) →
    localGradientEnergy af hB
        (sobolevGradient (vf : SobolevData (foldedCube w r hr I P))) =
      2 ^ I.card *
        localGradientEnergy a (hB.inter (centeredCube w r hr).isOpen.measurableSet)
          (sobolevGradient (v : SobolevData (centeredCube w r hr))) := by
  intro B hB hBs
  let U : Set (SpatialCoordinates d) := centeredCube w r hr
  let fF : Fin d → SpatialCoordinates d → ℝ := fun i x =>
    af.val x * (sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) i x) ^ 2
  let fO : Fin d → SpatialCoordinates d → ℝ := fun i x =>
    a.val x * (sobolevGradient (v : SobolevData (centeredCube w r hr)) i x) ^ 2
  have hfF : ∀ i : Fin d,
      Integrable (fF i) (volume.restrict
        (foldedCube w r hr I P : Set (SpatialCoordinates d))) := by
    intro i
    have hi := integrable_weighted_inner
      (μ := volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)))
      (E := ℝ) af.val
      (sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) i)
      (sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) i)
    simpa [fF, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using hi
  have htransport : ∀ i : Fin d,
      (∫ x in B, fF i x ∂volume.restrict
        (foldedCube w r hr I P : Set (SpatialCoordinates d))) =
        (2 : ℝ) ^ I.card *
          (∫ y in U, B.indicator (fO i) y ∂volume) := by
    intro i
    have hsector : ∀ J : Finset (Fin d), J ⊆ I →
        (∫ x in coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
            (centeredCube w r hr : Set (SpatialCoordinates d)), B.indicator (fF i) x) =
          ∫ y in (centeredCube w r hr : Set (SpatialCoordinates d)),
            B.indicator (fO i) y := by
      intro J hJ
      exact aux_lem_even_energy_transport_sector_energy_integral d w r hr I P J hJ
        (fF i) (fO i)
        (aux_lem_even_energy_transport_sector_energy_ae d w r hr I P J hJ
          a v af vf ha hg i)
        B hB hBs
    calc
      (∫ x in B, fF i x ∂volume.restrict
          (foldedCube w r hr I P : Set (SpatialCoordinates d))) =
          ∫ x in (foldedCube w r hr I P : Set (SpatialCoordinates d)),
            B.indicator (fF i) x := by
        calc
          (∫ x in B, fF i x ∂volume.restrict
              (foldedCube w r hr I P : Set (SpatialCoordinates d))) =
              ∫ x, B.indicator (fF i) x ∂volume.restrict
                (foldedCube w r hr I P : Set (SpatialCoordinates d)) :=
            (integral_indicator hB).symm
          _ = ∫ x in (foldedCube w r hr I P : Set (SpatialCoordinates d)),
              B.indicator (fF i) x := rfl
      _ = ∑ J ∈ I.powerset,
          ∫ x in coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
            (centeredCube w r hr : Set (SpatialCoordinates d)), B.indicator (fF i) x :=
        aux_lem_even_energy_transport_partition d w r hr I P (fF i) (hfF i) B hB
      _ = ∑ J ∈ I.powerset,
          ∫ y in (centeredCube w r hr : Set (SpatialCoordinates d)),
            B.indicator (fO i) y := by
        apply Finset.sum_congr rfl
        intro J hJ
        exact hsector J (Finset.mem_powerset.mp hJ)
      _ = (2 : ℝ) ^ I.card * (∫ y in U, B.indicator (fO i) y ∂volume) := by
        rw [Finset.sum_const, Finset.card_powerset]
        simp [nsmul_eq_mul, U]
  have hOrig : ∀ i : Fin d,
      (∫ y in U, B.indicator (fO i) y ∂volume) =
        ∫ y in B ∩ U, fO i y ∂volume.restrict U := by
    intro i
    have hset : (fun y : SpatialCoordinates d => y ∈ B) =ᵐ[volume.restrict U]
        (fun y => y ∈ (B ∩ U : Set (SpatialCoordinates d))) := by
      filter_upwards [ae_restrict_mem (centeredCube w r hr).isOpen.measurableSet]
        with y hy
      apply propext
      constructor
      · intro hBy
        exact ⟨hBy, hy⟩
      · intro hBy
        exact hBy.1
    calc
      (∫ y in U, B.indicator (fO i) y ∂volume) =
          ∫ y, B.indicator (fO i) y ∂volume.restrict U := rfl
      _ = ∫ y in B, fO i y ∂volume.restrict U := integral_indicator hB
      _ = ∫ y in B ∩ U, fO i y ∂volume.restrict U :=
        setIntegral_congr_set hset
  have hsum :
      (∑ i : Fin d, ∫ x in B, fF i x ∂volume.restrict
        (foldedCube w r hr I P : Set (SpatialCoordinates d))) =
      (2 : ℝ) ^ I.card *
        ∑ i : Fin d, ∫ y in B ∩ U, fO i y ∂volume.restrict U := by
    calc
      (∑ i : Fin d, ∫ x in B, fF i x ∂volume.restrict
          (foldedCube w r hr I P : Set (SpatialCoordinates d))) =
          ∑ i : Fin d, (2 : ℝ) ^ I.card *
            (∫ y in U, B.indicator (fO i) y ∂volume) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact htransport i
      _ = (2 : ℝ) ^ I.card *
            ∑ i : Fin d, ∫ y in U, B.indicator (fO i) y ∂volume := by
        exact (Finset.mul_sum (s := Finset.univ)
          (f := fun i : Fin d => ∫ y in U, B.indicator (fO i) y ∂volume)
          ((2 : ℝ) ^ I.card)).symm
      _ = (2 : ℝ) ^ I.card *
            ∑ i : Fin d, ∫ y in B ∩ U, fO i y ∂volume.restrict U := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        exact hOrig i
  rw [localGradientEnergy_eq_integral af hB,
    localGradientEnergy_eq_integral a
      (hB.inter (centeredCube w r hr).isOpen.measurableSet)]
  simpa [fF, fO, U] using hsum

end Paper
