module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.OscillatoryOnCell

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book Filter
open scoped BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-! ## Counting is volume, for a family of congruent cells -/

/-- The volume of a union of cells of one depth is the sum of their
volumes. -/
theorem volume_oneStepRetainedOpenSet_toReal_eq_sum
    {Q : TriadicCube d} {m : ℕ} {T : Finset (TriadicCube d)}
    (hT : T ⊆ descendantsAtDepth Q m) :
    (volume (oneStepRetainedOpenSet T)).toReal = ∑ R ∈ T, cubeVolume R := by
  classical
  have hdisj : (T : Set (TriadicCube d)).PairwiseDisjoint
      (fun R ↦ openCubeSet R) := by
    intro R hR S hS hRS
    exact pairwiseDisjoint_openCubeSet_descendantsAtDepth Q m
      (hT (by simpa using hR)) (hT (by simpa using hS)) hRS
  have hmeas : ∀ R ∈ T, MeasurableSet (openCubeSet R) := fun R _ ↦
    measurableSet_openCubeSet R
  have hunion : volume (oneStepRetainedOpenSet T) =
      ∑ R ∈ T, volume (openCubeSet R) := by
    unfold oneStepRetainedOpenSet
    exact measure_biUnion_finset hdisj hmeas
  rw [hunion]
  rw [ENNReal.toReal_sum (fun R _ ↦ (volume_openCubeSet_lt_top R).ne)]
  exact Finset.sum_congr rfl fun R _ ↦ volume_openCubeSet_toReal R

/-- The full descendant family at one depth exhausts the parent's volume. -/
theorem sum_cubeVolume_descendantsAtDepth
    (Q : TriadicCube d) (m : ℕ) :
    ∑ R ∈ descendantsAtDepth Q m, cubeVolume R = cubeVolume Q := by
  classical
  have hbase := volume_oneStepRetainedOpenSet_toReal_eq_sum
    (Q := Q) (m := m) (T := descendantsAtDepth Q m) (fun R hR ↦ hR)
  have haeUnion : oneStepRetainedOpenSet (descendantsAtDepth Q m) =ᵐ[volume]
      ⋃ R ∈ ((descendantsAtDepth Q m : Finset (TriadicCube d)) :
        Set (TriadicCube d)), cubeSet R :=
    EventuallyEqSet.biUnion (descendantsAtDepth Q m).finite_toSet
      fun R _hR ↦ (cubeSet_ae_eq_openCubeSet R).symm
  have hcover : (⋃ R ∈ ((descendantsAtDepth Q m : Finset (TriadicCube d)) :
      Set (TriadicCube d)), cubeSet R) = cubeSet Q :=
    (cubeSet_eq_iUnion_descendantsAtDepth Q m).symm
  have hvol : volume (oneStepRetainedOpenSet (descendantsAtDepth Q m)) =
      volume (openCubeSet Q) := by
    rw [measure_congr haeUnion, hcover]
    exact measure_congr (cubeSet_ae_eq_openCubeSet Q)
  rw [← hbase, hvol, volume_openCubeSet_toReal]

/-- **Counting is volume.**  For a subfamily of one depth, the cardinality
fraction equals the normalized volume of the union. -/
theorem card_div_card_eq_inv_cubeVolume_mul_volume
    {Q : TriadicCube d} {m : ℕ} {T : Finset (TriadicCube d)}
    (hT : T ⊆ descendantsAtDepth Q m) :
    ((T.card : ℝ)) / ((descendantsAtDepth Q m).card : ℝ) =
      (cubeVolume Q)⁻¹ * (volume (oneStepRetainedOpenSet T)).toReal := by
  classical
  obtain ⟨R₀, hR₀⟩ := descendantsAtDepth_nonempty Q m
  have hvolR₀ : 0 < cubeVolume R₀ := cubeVolume_pos R₀
  have hTsum : ∑ R ∈ T, cubeVolume R = (T.card : ℝ) * cubeVolume R₀ := by
    rw [Finset.sum_congr rfl
      (fun R hR ↦ cubeVolume_eq_of_mem_descendantsAtDepth (hT hR) hR₀)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hDsum : ((descendantsAtDepth Q m).card : ℝ) * cubeVolume R₀ =
      cubeVolume Q := by
    rw [← sum_cubeVolume_descendantsAtDepth Q m]
    rw [Finset.sum_congr rfl
      (fun R hR ↦ cubeVolume_eq_of_mem_descendantsAtDepth hR hR₀)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcardD : (0 : ℝ) < ((descendantsAtDepth Q m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q m)
  rw [volume_oneStepRetainedOpenSet_toReal_eq_sum hT, hTsum, ← hDsum]
  field_simp

/-! ## The discarded cells lie in the discarded strip -/

/-- Cells of the family that are outside a subfamily are disjoint from that
subfamily's open set. -/
theorem oneStepRetainedOpenSet_subset_diff
    {Q : TriadicCube d} {m : ℕ} {covered T : Finset (TriadicCube d)}
    (hcov : covered ⊆ descendantsAtDepth Q m)
    (hT : T ⊆ descendantsAtDepth Q m) (hdisj : ∀ R ∈ T, R ∉ covered) :
    oneStepRetainedOpenSet T ⊆
      openCubeSet Q \ oneStepRetainedOpenSet covered := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨R, hxR⟩
  rcases Set.mem_iUnion.mp hxR with ⟨hR, hxR⟩
  have hRmem : R ∈ T := by simpa using hR
  refine ⟨openCubeSet_subset_of_mem_descendantsAtDepth (hT hRmem) hxR, ?_⟩
  intro hxcov
  rcases Set.mem_iUnion.mp hxcov with ⟨S, hxS⟩
  rcases Set.mem_iUnion.mp hxS with ⟨hS, hxS⟩
  have hSmem : S ∈ covered := by simpa using hS
  have hne : R ≠ S := fun hRS ↦ hdisj R hRmem (hRS ▸ hSmem)
  exact Set.disjoint_left.mp
    (pairwiseDisjoint_openCubeSet_descendantsAtDepth Q m (hT hRmem)
      (hcov hSmem) hne) hxR hxS

/-! ## The uncovered fraction -/

/-- **The uncovered-fraction bound.**  Any covered family containing the
committed retained source cells leaves at most an
`oneStepRetainedBoundaryFraction` share of the source cells. -/
theorem card_sdiff_div_card_le_oneStepRetainedBoundaryFraction
    {K n : ℕ} {delta : ℝ} {N : ℕ}
    (hsource : oneStepLocalizationScale n delta ≤ K)
    (hhalf : oneStepRetainedBoundaryThickness (d := d) (K : ℤ)
      (oneStepLocalizationScale n delta : ℤ) N ≤ 1 / 2)
    (covered : Finset (TriadicCube d))
    (hret : oneStepRetainedSourceCells (d := d) (K : ℤ)
      (oneStepLocalizationScale n delta : ℤ) N ⊆ covered) :
    ((((oneStepSourceCells d K n delta) \ covered).card : ℝ)) /
        ((oneStepSourceCells d K n delta).card : ℝ) ≤
      oneStepRetainedBoundaryFraction (d := d) (K : ℤ)
        (oneStepLocalizationScale n delta : ℤ) N := by
  classical
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  set m : ℕ := K - oneStepLocalizationScale n delta with hm
  set src : Finset (TriadicCube d) := oneStepSourceCells d K n delta with hsrc
  have hsrcD : src = descendantsAtDepth Q m := rfl
  set T : Finset (TriadicCube d) := src \ covered with hTdef
  have hTsub : T ⊆ descendantsAtDepth Q m := by
    rw [← hsrcD]
    exact Finset.sdiff_subset
  -- the committed retained family sits inside the source cells
  have hretD : oneStepRetainedSourceCells (d := d) (K : ℤ)
      (oneStepLocalizationScale n delta : ℤ) N ⊆ descendantsAtDepth Q m := by
    intro R hR
    have hscale := (mem_oneStepRetainedSourceCells_iff.mp hR).1
    have hle : (oneStepLocalizationScale n delta : ℤ) ≤ (K : ℤ) := by
      exact_mod_cast hsource
    rw [descendantsAtScale_eq_descendantsAtDepth Q (by simpa [hQ, originCube]
      using hle)] at hscale
    have htoNat : Int.toNat (Q.scale - (oneStepLocalizationScale n delta : ℤ))
        = m := by
      simp only [hQ, originCube, hm]
      omega
    rwa [htoNat] at hscale
  have hdisjT : ∀ R ∈ T, R ∉ oneStepRetainedSourceCells (d := d) (K : ℤ)
      (oneStepLocalizationScale n delta : ℤ) N := by
    intro R hR hmem
    exact (Finset.mem_sdiff.mp hR).2 (hret hmem)
  have hsubset := oneStepRetainedOpenSet_subset_diff (Q := Q) (m := m)
    hretD hTsub hdisjT
  -- volume of the discarded strip
  have hstrip : (cubeVolume Q)⁻¹ *
      (volume (openCubeSet Q \ oneStepRetainedOpenSet
        (oneStepRetainedSourceCells (d := d) (K : ℤ)
          (oneStepLocalizationScale n delta : ℤ) N))).toReal ≤
      oneStepRetainedBoundaryFraction (d := d) (K : ℤ)
        (oneStepLocalizationScale n delta : ℤ) N := by
    have hle : (oneStepLocalizationScale n delta : ℤ) ≤ (K : ℤ) := by
      exact_mod_cast hsource
    have hbase := inv_cubeVolume_mul_integral_diff_retained_le_boundaryFraction
      (d := d) hle hhalf (fun _ ↦ (1 : ℝ)) 1
      (integrableOn_const
        (by
          refine ne_top_of_le_ne_top ?_
            (measure_mono (cubeBoundaryLayer_subset_cubeSet _ _))
          rw [measure_congr (cubeSet_ae_eq_openCubeSet _)]
          exact (volume_openCubeSet_lt_top _).ne)
        (by simp))
      (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
      (Filter.Eventually.of_forall fun _ ↦ le_rfl)
    simpa only [one_mul, setIntegral_const, smul_eq_mul, Measure.real,
      mul_one] using hbase
  -- assemble
  have hvolmono : (volume (oneStepRetainedOpenSet T)).toReal ≤
      (volume (openCubeSet Q \ oneStepRetainedOpenSet
        (oneStepRetainedSourceCells (d := d) (K : ℤ)
          (oneStepLocalizationScale n delta : ℤ) N))).toReal := by
    refine ENNReal.toReal_mono ?_ (measure_mono hsubset)
    exact ne_top_of_le_ne_top (volume_openCubeSet_lt_top Q).ne
      (measure_mono Set.sdiff_subset)
  have hcardeq := card_div_card_eq_inv_cubeVolume_mul_volume
    (Q := Q) (m := m) (T := T) hTsub
  rw [hsrcD, hTdef] at *
  refine le_trans (le_of_eq hcardeq) (le_trans ?_ hstrip)
  exact mul_le_mul_of_nonneg_left hvolmono
    (inv_nonneg.mpr (cubeVolume_pos Q).le)

/-! ## The `frac` sequence -/

/-- The bound that `BoundaryLayer.lean` consumes: the retained boundary
fraction wherever it is meaningful, and the trivial bound `1` elsewhere. -/
def uncoveredFractionBound (d n : ℕ) (delta : ℝ) (N : ℕ) (K : ℕ) : ℝ := by
  classical
  exact if oneStepLocalizationScale n delta ≤ K ∧
      oneStepRetainedBoundaryThickness (d := d) (K : ℤ)
        (oneStepLocalizationScale n delta : ℤ) N ≤ 1 / 2 then
    oneStepRetainedBoundaryFraction (d := d) (K : ℤ)
      (oneStepLocalizationScale n delta : ℤ) N
  else 1

/-- **The bound vanishes.**  Both side conditions hold for large `K`, where
the sequence is the committed retained boundary fraction. -/
theorem tendsto_uncoveredFractionBound_zero (d n : ℕ) (delta : ℝ) (N : ℕ) :
    Tendsto (uncoveredFractionBound d n delta N) atTop (nhds 0) := by
  classical
  have hthick := tendsto_oneStepRetainedBoundaryThickness_zero (d := d)
    (oneStepLocalizationScale n delta : ℤ) N
  have hthickEv : ∀ᶠ K : ℕ in atTop,
      oneStepRetainedBoundaryThickness (d := d) (K : ℤ)
        (oneStepLocalizationScale n delta : ℤ) N ≤ 1 / 2 :=
    hthick.eventually_le_const (by norm_num)
  have hscaleEv : ∀ᶠ K : ℕ in atTop, oneStepLocalizationScale n delta ≤ K :=
    eventually_atTop.2 ⟨oneStepLocalizationScale n delta, fun K hK ↦ hK⟩
  refine Tendsto.congr' ?_
    (tendsto_oneStepRetainedBoundaryFraction_zero (d := d)
      (oneStepLocalizationScale n delta : ℤ) N)
  filter_upwards [hthickEv, hscaleEv] with K hK1 hK2
  unfold uncoveredFractionBound
  rw [ite_eq_left ⟨hK2, hK1⟩]

/-- **The uncovered fraction, in the exact shape `BoundaryLayer.lean`
consumes.** -/
theorem card_sdiff_div_card_le_uncoveredFractionBound
    (d n : ℕ) (delta : ℝ) (N : ℕ)
    (covered : ℕ → Finset (TriadicCube d))
    (K : ℕ)
    (hret : oneStepRetainedSourceCells (d := d) (K : ℤ)
      (oneStepLocalizationScale n delta : ℤ) N ⊆ covered K) :
    ((((oneStepSourceCells d K n delta) \ covered K).card : ℝ)) /
        ((oneStepSourceCells d K n delta).card : ℝ) ≤
      uncoveredFractionBound d n delta N K := by
  classical
  by_cases hK : oneStepLocalizationScale n delta ≤ K ∧
      oneStepRetainedBoundaryThickness (d := d) (K : ℤ)
        (oneStepLocalizationScale n delta : ℤ) N ≤ 1 / 2
  · unfold uncoveredFractionBound
    rw [ite_eq_left hK]
    exact card_sdiff_div_card_le_oneStepRetainedBoundaryFraction
      hK.1 hK.2 (covered K) hret
  · unfold uncoveredFractionBound
    rw [ite_eq_right hK]
    have hcard : (0 : ℝ) < ((oneStepSourceCells d K n delta).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr
        (oneStepSourceCells_nonempty d K n delta)
    rw [div_le_one hcard]
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
