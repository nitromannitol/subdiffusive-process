import SubdiffusiveProcess.Section10.InitialSimplexPackingCounting
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.CellDilation




namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Finite coverage by half-open cubes yields the open-packing remainder
bound, because all the finitely many discarded grid faces are null. -/
theorem packingRemainder_volume_le_sum {U : Set (Vec d)}
    (S T : Finset (TriadicCube d))
    (hcover : U ⊆ (⋃ Q ∈ S, cubeSet Q) ∪ ⋃ Q ∈ T, cubeSet Q) :
    (volume (packingRemainder U S openCubeSet)).toReal ≤
      ∑ Q ∈ T, (volume (cubeSet Q)).toReal := by
  classical
  have hsub : packingRemainder U S openCubeSet ⊆
      (⋃ Q ∈ S, cubeBoundary Q) ∪ ⋃ Q ∈ T, cubeSet Q := by
    intro x hx
    obtain ⟨hxU, hxnot⟩ := hx
    rcases hcover hxU with hxS | hxT
    · obtain ⟨Q, hQS, hxQ⟩ := Set.mem_iUnion₂.mp hxS
      exact Or.inl (Set.mem_iUnion₂.mpr ⟨Q, hQS, hxQ,
        fun hxopen => hxnot (Set.mem_iUnion₂.mpr ⟨Q, hQS, hxopen⟩)⟩)
    · exact Or.inr hxT
  have hnull : volume (⋃ Q ∈ S, cubeBoundary Q) = 0 := by
    apply le_antisymm _ (zero_le _)
    simpa only [volume_cubeBoundary_eq_zero, Finset.sum_const_zero] using
      (measure_biUnion_finset_le (μ := volume) S cubeBoundary)
  have hmeasure : volume (packingRemainder U S openCubeSet) ≤
      ∑ Q ∈ T, volume (cubeSet Q) := by
    calc
      _ ≤ volume ((⋃ Q ∈ S, cubeBoundary Q) ∪ ⋃ Q ∈ T, cubeSet Q) := measure_mono hsub
      _ ≤ volume (⋃ Q ∈ S, cubeBoundary Q) + volume (⋃ Q ∈ T, cubeSet Q) :=
        measure_union_le _ _
      _ = volume (⋃ Q ∈ T, cubeSet Q) := by rw [hnull, zero_add]
      _ ≤ _ := measure_biUnion_finset_le T cubeSet
  have hfinite : (∑ Q ∈ T, volume (cubeSet Q)) ≠ ⊤ := by
    exact (ENNReal.sum_lt_top.mpr fun Q _ => volume_cubeSet_lt_top Q).ne
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [ENNReal.toReal_sum (fun Q _ => (volume_cubeSet_lt_top Q).ne)] at hreal
  exact hreal

theorem initialSimplex_volume_scale (ell : ℕ) (pi : Equiv.Perm (Fin d)) :
    (volume (initialSimplex ell pi).openCarrier).toReal =
      ((3 : ℝ) ^ ell) ^ d * (volume (initialSimplex 0 pi).openCarrier).toReal := by
  have heq : Kuhn.dilateKuhnCell ell 0 0 (initialSimplex 0 pi) = initialSimplex ell pi := by
    simp [Kuhn.dilateKuhnCell, initialSimplex, originCube, Pi.zero_def]
  have h := Kuhn.volume_toReal_openCarrier_dilateKuhnCell
    (k := ell) (R := 0) (c := (0 : Fin d → ℤ)) (V := initialSimplex 0 pi) (by rfl)
  simpa only [heq, zpow_natCast] using h

/-- A dimension-only finite normalization constant. No exact simplex-volume
formula is required: the finite sum bounds each permutation's inverse volume. -/
def initialSimplexVolumeNormalization (d : ℕ) : ℝ :=
  ∑ pi : Equiv.Perm (Fin d), (volume (initialSimplex 0 pi).openCarrier).toReal⁻¹

theorem initialSimplexVolumeNormalization_nonneg (d : ℕ) :
    0 ≤ initialSimplexVolumeNormalization d := by
  apply Finset.sum_nonneg
  intro pi _
  exact inv_nonneg.mpr ENNReal.toReal_nonneg

theorem initialSimplex_inverse_volume_le (pi : Equiv.Perm (Fin d)) :
    (volume (initialSimplex 0 pi).openCarrier).toReal⁻¹ ≤
      initialSimplexVolumeNormalization d := by
  classical
  unfold initialSimplexVolumeNormalization
  exact Finset.single_le_sum (fun pi _ =>
    inv_nonneg.mpr (ENNReal.toReal_nonneg (a := volume (initialSimplex 0 pi).openCarrier)))
    (Finset.mem_univ pi)

theorem descendant_initialSimplex_volume_fraction {ell n : ℕ}
    (pi : Equiv.Perm (Fin d)) {Q : TriadicCube d}
    (hQ : Q ∈ descendantsAtDepth (originCube d (ell : ℤ)) n) :
    (volume (openCubeSet Q)).toReal / (volume (initialSimplex ell pi).openCarrier).toReal =
      ((3 : ℝ) ^ n)⁻¹ ^ d * (volume (initialSimplex 0 pi).openCarrier).toReal⁻¹ := by
  have hvol : (volume (initialSimplex 0 pi).openCarrier).toReal ≠ 0 :=
    (volume_toReal_pos (kuhnCellDomain (initialSimplex 0 pi))).ne'
  rw [volume_openCubeSet_toReal, cubeVolume, cubeScaleFactor_descendant_eq_div_pow hQ,
    cubeScaleFactor_originCube, zpow_natCast, initialSimplex_volume_scale, div_pow]
  have hthree : (3 : ℝ) ^ ell ≠ 0 := by positivity
  have hthree' : (3 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  rw [← mul_pow]
  simp [hthree']

theorem gridCount_volume_factor (hd : 1 ≤ d) (n : ℕ) :
    ((3 : ℝ) ^ (d - 1)) ^ n * ((3 : ℝ) ^ n)⁻¹ ^ d = (1 / 3 : ℝ) ^ n := by
  have heq : d = (d - 1) + 1 := by omega
  have hthree : (3 : ℝ) ^ n ≠ 0 := by positivity
  calc
    _ = ((3 : ℝ) ^ n) ^ (d - 1) * ((3 : ℝ) ^ n)⁻¹ ^ ((d - 1) + 1) := by
      rw [pow_right_comm]
      conv_rhs => rw [← heq]
    _ = ((3 : ℝ) ^ n)⁻¹ := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hthree]
      simp
    _ = _ := by simp [one_div, inv_pow]

/-- The only quantitative interface needed from a future alternative counter:
cardinality of unresolved cubes, before any normalization or energy. -/
theorem unresolved_volume_fraction_le (hd : 1 ≤ d) (ell n : ℕ)
    (pi : Equiv.Perm (Fin d)) :
    (∑ Q ∈ initialSimplexUnresolved ell pi n, (volume (cubeSet Q)).toReal) /
      (volume (initialSimplex ell pi).openCarrier).toReal ≤
        (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d * (1 / 3 : ℝ) ^ n := by
  classical
  rw [Finset.sum_div]
  have hsum : (∑ Q ∈ initialSimplexUnresolved ell pi n,
      (volume (cubeSet Q)).toReal / (volume (initialSimplex ell pi).openCarrier).toReal) =
      ((initialSimplexUnresolved ell pi n).card : ℝ) *
        (((3 : ℝ) ^ n)⁻¹ ^ d * (volume (initialSimplex 0 pi).openCarrier).toReal⁻¹) := by
    calc
      _ = ∑ _Q ∈ initialSimplexUnresolved ell pi n,
          ((3 : ℝ) ^ n)⁻¹ ^ d * (volume (initialSimplex 0 pi).openCarrier).toReal⁻¹ := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [← volume_openCubeSet_eq_volume_cubeSet]
        exact descendant_initialSimplex_volume_fraction pi (mem_unresolvedAtDepth.mp hQ).1
      _ = _ := by simp
  rw [hsum]
  have hcard : ((initialSimplexUnresolved ell pi n).card : ℝ) ≤
      (d : ℝ) ^ 2 * ((3 : ℝ) ^ (d - 1)) ^ n := by
    exact_mod_cast initialSimplexUnresolved_card_le ell n pi
  calc
    _ ≤ ((d : ℝ) ^ 2 * ((3 : ℝ) ^ (d - 1)) ^ n) *
        (((3 : ℝ) ^ n)⁻¹ ^ d * initialSimplexVolumeNormalization d) := by
      gcongr
      exact initialSimplex_inverse_volume_le pi
    _ = _ := by
      calc
        _ = (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d *
            (((3 : ℝ) ^ (d - 1)) ^ n * ((3 : ℝ) ^ n)⁻¹ ^ d) := by ring
        _ = _ := by rw [gridCount_volume_factor hd]

def initialSimplexPackingConstant (d : ℕ) : ℝ :=
  1 + ((3 : ℝ) ^ d + 1) * (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d

theorem initialSimplexPackingConstant_one_le (d : ℕ) :
    1 ≤ initialSimplexPackingConstant d := by
  unfold initialSimplexPackingConstant
  have hN := initialSimplexVolumeNormalization_nonneg d
  have hterm : 0 ≤ ((3 : ℝ) ^ d + 1) * (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d := by positivity
  linarith

theorem initialSimplexPackingConstant_depth_le (d : ℕ) :
    (3 : ℝ) ^ d * (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d ≤
      initialSimplexPackingConstant d := by
  unfold initialSimplexPackingConstant
  have hN := initialSimplexVolumeNormalization_nonneg d
  have hnn : 0 ≤ (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d := mul_nonneg (sq_nonneg _) hN
  nlinarith

theorem initialSimplexPackingConstant_remainder_le (d : ℕ) :
    (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d ≤ initialSimplexPackingConstant d := by
  unfold initialSimplexPackingConstant
  have hN := initialSimplexVolumeNormalization_nonneg d
  have hnn : 0 ≤ (3 : ℝ) ^ d * (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d := by positivity
  nlinarith

theorem initialSimplexPacking_atDepth_fraction_le (hd : 1 ≤ d) (ell : ℕ)
    (pi : Equiv.Perm (Fin d)) (i : ℕ) (hi : 0 < i) :
    (∑ Q ∈ maximalContainedAtDepth (originCube d (ell : ℤ))
      (initialSimplex ell pi).openCarrier i,
      (volume (openCubeSet Q)).toReal / (volume (initialSimplex ell pi).openCarrier).toReal) ≤
        initialSimplexPackingConstant d * (1 / 3 : ℝ) ^ i := by
  classical
  let S := maximalContainedAtDepth (originCube d (ell : ℤ)) (initialSimplex ell pi).openCarrier i
  have hsum : (∑ Q ∈ S, (volume (openCubeSet Q)).toReal /
      (volume (initialSimplex ell pi).openCarrier).toReal) =
      (S.card : ℝ) * (((3 : ℝ) ^ i)⁻¹ ^ d *
        (volume (initialSimplex 0 pi).openCarrier).toReal⁻¹) := by
    calc
      _ = ∑ _Q ∈ S, ((3 : ℝ) ^ i)⁻¹ ^ d *
          (volume (initialSimplex 0 pi).openCarrier).toReal⁻¹ := by
        apply Finset.sum_congr rfl
        intro Q hQ
        exact descendant_initialSimplex_volume_fraction pi
          (mem_maximalContainedAtDepth.mp hQ).1
      _ = _ := by simp
  change (∑ Q ∈ S, _) ≤ _
  rw [hsum]
  have hcard : (S.card : ℝ) ≤ (3 : ℝ) ^ d * (d : ℝ) ^ 2 *
      ((3 : ℝ) ^ (d - 1)) ^ i := by
    exact_mod_cast initialSimplexPacking_atDepth_card_le ell pi i hi
  calc
    _ ≤ ((3 : ℝ) ^ d * (d : ℝ) ^ 2 * ((3 : ℝ) ^ (d - 1)) ^ i) *
        (((3 : ℝ) ^ i)⁻¹ ^ d * initialSimplexVolumeNormalization d) := by
      gcongr
      exact initialSimplex_inverse_volume_le pi
    _ = ((3 : ℝ) ^ d * (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d) *
        (1 / 3 : ℝ) ^ i := by
      calc
        _ = ((3 : ℝ) ^ d * (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d) *
          (((3 : ℝ) ^ (d - 1)) ^ i * ((3 : ℝ) ^ i)⁻¹ ^ d) := by ring
        _ = _ := by rw [gridCount_volume_factor hd]
    _ ≤ _ := mul_le_mul_of_nonneg_right (initialSimplexPackingConstant_depth_le d)
      (pow_nonneg (by norm_num) i)

theorem initialSimplexPacking_depth_fraction (hd : 1 ≤ d) (ell : ℕ)
    (pi : Equiv.Perm (Fin d)) (i : ℕ) :
    (∑ Q ∈ (initialSimplexPackingCubes ell pi).filter
      (fun Q => initialSimplexPackingDepth ell Q = i),
      (volume (openCubeSet Q)).toReal / (volume (initialSimplex ell pi).openCarrier).toReal) ≤
        initialSimplexPackingConstant d * (1 / 3 : ℝ) ^ i := by
  classical
  by_cases hi : 1 ≤ i ∧ i ≤ ell
  · have hfilter := maximalContainedPacking_filter_depth
      (originCube d (ell : ℤ)) (initialSimplex ell pi).openCarrier ell i hi.1 hi.2
    change (∑ Q ∈ (maximalContainedPacking _ _ ell).filter
      (fun Q => packingCubeDepth (originCube d (ell : ℤ)) Q = i), _) ≤ _
    rw [hfilter]
    exact initialSimplexPacking_atDepth_fraction_le hd ell pi i hi.1
  · have hempty : (initialSimplexPackingCubes ell pi).filter
        (fun Q => initialSimplexPackingDepth ell Q = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      obtain ⟨hQP, hdepth⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hp, hl, -⟩ := initialSimplexPacking_depth_bounds hQP
      exact hi (by omega)
    rw [hempty, Finset.sum_empty]
    exact mul_nonneg (le_trans (by norm_num) (initialSimplexPackingConstant_one_le d))
      (pow_nonneg (by norm_num) i)

theorem initialSimplexPacking_remainder_fraction (hd : 2 ≤ d) (ell : ℕ)
    (pi : Equiv.Perm (Fin d)) :
    (volume (packingRemainder (initialSimplex ell pi).openCarrier
      (initialSimplexPackingCubes ell pi) openCubeSet)).toReal /
      (volume (initialSimplex ell pi).openCarrier).toReal ≤
        initialSimplexPackingConstant d * (1 / 3 : ℝ) ^ ell := by
  have hraw := packingRemainder_volume_le_sum (initialSimplexPackingCubes ell pi)
    (initialSimplexUnresolved ell pi ell) (initialSimplexPacking_cover hd ell pi)
  calc
    _ ≤ (∑ Q ∈ initialSimplexUnresolved ell pi ell, (volume (cubeSet Q)).toReal) /
        (volume (initialSimplex ell pi).openCarrier).toReal :=
      div_le_div_of_nonneg_right hraw ENNReal.toReal_nonneg
    _ ≤ (d : ℝ) ^ 2 * initialSimplexVolumeNormalization d * (1 / 3 : ℝ) ^ ell :=
      unresolved_volume_fraction_le (by omega) ell ell pi
    _ ≤ _ := mul_le_mul_of_nonneg_right (initialSimplexPackingConstant_remainder_le d)
      (pow_nonneg (by norm_num) ell)



def initialSimplexCubePacking_geometry (hd : 2 ≤ d) (ell : ℕ)
    (pi : Equiv.Perm (Fin d)) :
    InitialSimplexCubePacking ell pi (initialSimplexPackingConstant d) := by
  by_cases hz : ell = 0
  · subst ell
    exact initialSimplexCubePacking_zero pi (initialSimplexPackingConstant_one_le d)
  · exact {
  cubes := initialSimplexPackingCubes ell pi
  depth := initialSimplexPackingDepth ell
  depth_pos Q hQ := (initialSimplexPacking_depth_bounds hQ).1
  depth_le Q hQ := (initialSimplexPacking_depth_bounds hQ).2.1
  scale_eq Q hQ := (initialSimplexPacking_depth_bounds hQ).2.2
  subset Q hQ := initialSimplexPacking_subset hQ
  disjoint := initialSimplexPacking_disjoint ell pi
  depth_fraction := initialSimplexPacking_depth_fraction (by omega) ell pi
  remainder_fraction := initialSimplexPacking_remainder_fraction hd ell pi }

/-- D1a's complete geometric supplier, with K depending only on dimension. -/
theorem exists_initialSimplexCubePacking (d : ℕ) (hd : 2 ≤ d) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (ell : ℕ) (pi : Equiv.Perm (Fin d)),
      Nonempty (InitialSimplexCubePacking ell pi K) := by
  exact ⟨initialSimplexPackingConstant d, initialSimplexPackingConstant_one_le d,
    fun ell pi => ⟨initialSimplexCubePacking_geometry hd ell pi⟩⟩

end
end SubdiffusiveProcess.Section10
