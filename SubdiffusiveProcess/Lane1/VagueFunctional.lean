module

public import SubdiffusiveProcess.Lane1.TestIntegralCauchy
public import SubdiffusiveProcess.Lane1.WeightedIndep

@[expose] public section

/-!
# Convergence of every test integral

From the convergence of the countably many cube masses, the test integral
`∫ f dmu_N` converges for EVERY compactly supported continuous `f`.  The
uniform mass bound the Cauchy argument needs is free: a convergent sequence is
bounded, so the mass of one big cube is bounded along the cutoffs, and the
tiles used by the step bound are disjoint inside it.
-/

open Filter MeasureTheory

open scoped CompactlySupported ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- The tiles of a generation whose index lies in the box of radius `R` are
contained in the cube of side `2 (R + 3)`. -/
theorem tileIndices_subset_bigCube {d : ℕ} {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    (⋃ k ∈ tileIndices d R j, triadicTile j k) ⊆
      (centeredCube (0 : SpatialCoordinates d) (2 * (R + 4))
        (by linarith) : Set (SpatialCoordinates d)) := by
  classical
  have ht : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  have ht1 : (3 : ℝ) ^ (-(j : ℤ)) ≤ 1 := three_zpow_neg_le_one j
  have hdt : (R / (3 : ℝ) ^ (-(j : ℤ))) * (3 : ℝ) ^ (-(j : ℤ)) = R :=
    div_mul_cancel₀ R (ne_of_gt ht)
  have hce : (⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) < R / (3 : ℝ) ^ (-(j : ℤ)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  intro x hx
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨k, hk, hxk⟩ := hx
  rw [tileIndices, Fintype.mem_piFinset] at hk
  rw [mem_triadicTile_iff] at hxk
  rw [centeredCube_coe_eq_ball]
  refine Metric.mem_ball.mpr ?_
  have hhalf : 2 * (R + 4) / 2 = R + 4 := by ring
  rw [hhalf]
  refine lt_of_le_of_lt ((dist_pi_le_iff (by linarith : (0 : ℝ) ≤ R + 3)).mpr ?_)
    (by linarith)
  intro i
  have hki := hk i
  rw [Finset.mem_Icc] at hki
  obtain ⟨h1, h2⟩ := hxk i
  have hkub : ((k i : ℤ) : ℝ) ≤ (⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1 := by
    have h := hki.2
    have hcast : (((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ + 1 : ℤ)) : ℝ)
        = (⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1 := by push_cast; ring
    rw [← hcast]
    exact_mod_cast h
  have hklb : -((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1) ≤ ((k i : ℤ) : ℝ) := by
    have h := hki.1
    have hcast : ((-(⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ + 1 : ℤ)) : ℝ)
        = -((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1) := by push_cast; ring
    rw [← hcast]
    exact_mod_cast h
  have hlowmul : -((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1) * (3 : ℝ) ^ (-(j : ℤ))
      ≤ ((k i : ℤ) : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) :=
    mul_le_mul_of_nonneg_right hklb ht.le
  have hupmul : (((k i : ℤ) : ℝ) + 1) * (3 : ℝ) ^ (-(j : ℤ))
      ≤ ((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 2) * (3 : ℝ) ^ (-(j : ℤ)) :=
    mul_le_mul_of_nonneg_right (by linarith) ht.le
  have hexp1 : ((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 2) * (3 : ℝ) ^ (-(j : ℤ))
      < (R / (3 : ℝ) ^ (-(j : ℤ)) + 3) * (3 : ℝ) ^ (-(j : ℤ)) :=
    mul_lt_mul_of_pos_right (by linarith) ht
  have hexp2 : (R / (3 : ℝ) ^ (-(j : ℤ)) + 3) * (3 : ℝ) ^ (-(j : ℤ))
      = R + 3 * (3 : ℝ) ^ (-(j : ℤ)) := by
    rw [add_mul, hdt]
  have hexp3 : -((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1) * (3 : ℝ) ^ (-(j : ℤ))
      > -((R / (3 : ℝ) ^ (-(j : ℤ)) + 2) * (3 : ℝ) ^ (-(j : ℤ))) := by
    have := mul_lt_mul_of_pos_right
      (show (⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1 < R / (3 : ℝ) ^ (-(j : ℤ)) + 2
        by linarith) ht
    linarith
  have hexp4 : (R / (3 : ℝ) ^ (-(j : ℤ)) + 2) * (3 : ℝ) ^ (-(j : ℤ))
      = R + 2 * (3 : ℝ) ^ (-(j : ℤ)) := by
    rw [add_mul, hdt]
  have hzero : (0 : SpatialCoordinates d) i = 0 := rfl
  rw [Real.dist_eq, hzero, sub_zero, abs_le]
  constructor
  · linarith [hlowmul, h1, hexp3, hexp4, ht1]
  · linarith [hupmul, h2, hexp1, hexp2, ht1]

/-- **Every test integral converges.**  From the convergence of the countably
many tile-cube masses and of one big cube mass per integer radius, the test
integral converges for every compactly supported continuous `f`. -/
theorem chaos_vague_functional
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d)
    (hcube : ∀ (j : ℕ) (k : Fin d → ℤ), ∃ L : ℝ, Tendsto (fun N =>
      ((weightedChaosCutoff M H N omega)
        ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
          (zpow_neg_pos j)) : Set (SpatialCoordinates d))).toReal)
      atTop (nhds L))
    (hbig : ∀ n : ℕ, ∃ L : ℝ, Tendsto (fun N =>
      ((weightedChaosCutoff M H N omega)
        ((centeredCube (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 4))
          (by positivity)) : Set (SpatialCoordinates d))).toReal)
      atTop (nhds L)) :
    ∀ f : C_c(SpatialCoordinates d, ℝ),
      ∃ L : ℝ, Tendsto (fun N => ∫ x, f x ∂(weightedChaosCutoff M H N omega))
        atTop (nhds L) := by
  classical
  intro f
  have hfc : Continuous (f : SpatialCoordinates d → ℝ) := map_continuous f
  have hcs : HasCompactSupport (f : SpatialCoordinates d → ℝ) := f.hasCompactSupport
  obtain ⟨R0, hR0⟩ := hcs.isBounded.subset_closedBall (0 : SpatialCoordinates d)
  obtain ⟨R, hRn⟩ := exists_nat_ge (max R0 0)
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have hRsub : tsupport (f : SpatialCoordinates d → ℝ) ⊆
      Metric.closedBall (0 : SpatialCoordinates d) (R : ℝ) :=
    hR0.trans (Metric.closedBall_subset_closedBall
      (le_trans (le_max_left _ _) hRn))
  have hsupp : ∀ x, (R : ℝ) < dist x (0 : SpatialCoordinates d) → f x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport ?_
    intro hmem
    exact absurd (Metric.mem_closedBall.mp (hRsub hmem)) (not_le.mpr hx)
  set bigCube : Set (SpatialCoordinates d) :=
    ((centeredCube (0 : SpatialCoordinates d) (2 * ((R : ℝ) + 4))
      (by positivity)) : Set (SpatialCoordinates d)) with hbigdef
  -- finiteness and absolute continuity of the cutoff measures
  have hfinbig : ∀ N : ℕ, (weightedChaosCutoff M H N omega) bigCube ≠ ⊤ := by
    intro N
    haveI := weightedChaosCutoff_isLocallyFinite M H N omega
    rw [hbigdef, centeredCube_coe_eq_ball]
    exact (measure_ball_lt_top).ne
  have hac : ∀ N : ℕ, weightedChaosCutoff M H N omega ≪ volume := by
    intro N
    rw [weightedChaosCutoff]
    exact withDensity_absolutelyContinuous _ _
  have hint : ∀ N : ℕ,
      Integrable (f : SpatialCoordinates d → ℝ)
        (weightedChaosCutoff M H N omega) := by
    intro N
    haveI := weightedChaosCutoff_isLocallyFinite M H N omega
    exact hfc.integrable_of_hasCompactSupport hcs
  -- the uniform mass bound is free: a convergent sequence is bounded
  obtain ⟨Lbig, hLbig⟩ := hbig R
  obtain ⟨Cm0, hCm0⟩ := hLbig.bddAbove_range
  set Cm : ℝ := max Cm0 1 with hCmdef
  have hCmpos : (0 : ℝ) < Cm := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCmle : ∀ N : ℕ,
      ((weightedChaosCutoff M H N omega) bigCube).toReal ≤ Cm := by
    intro N
    refine le_trans (hCm0 ?_) (le_max_left _ _)
    exact Set.mem_range_self N
  have hsubbig : ∀ (j : ℕ), ∀ k ∈ tileIndices d (R : ℝ) j,
      triadicTile j k ⊆ bigCube := by
    intro j k hk x hx
    exact tileIndices_subset_bigCube hRnn j (Set.mem_biUnion hk hx)
  have hfinN : ∀ (N j : ℕ), ∀ k ∈ tileIndices d (R : ℝ) j,
      (weightedChaosCutoff M H N omega) (triadicTile j k) ≠ ⊤ := by
    intro N j k hk
    exact ne_top_of_le_ne_top (hfinbig N) (measure_mono (hsubbig j k hk))
  have hCmass : ∀ (N j : ℕ),
      ∑ k ∈ tileIndices d (R : ℝ) j,
        ((weightedChaosCutoff M H N omega) (triadicTile j k)).toReal ≤ Cm := by
    intro N j
    have hunion : (weightedChaosCutoff M H N omega)
        (⋃ k ∈ tileIndices d (R : ℝ) j, triadicTile j k)
        = ∑ k ∈ tileIndices d (R : ℝ) j,
          (weightedChaosCutoff M H N omega) (triadicTile j k) :=
      measure_biUnion_finset (fun k _ l _ hkl => triadicTile_disjoint j hkl)
        (fun k _ => measurableSet_triadicTile j k)
    have hsum : ∑ k ∈ tileIndices d (R : ℝ) j,
        ((weightedChaosCutoff M H N omega) (triadicTile j k)).toReal
        = ((weightedChaosCutoff M H N omega)
            (⋃ k ∈ tileIndices d (R : ℝ) j, triadicTile j k)).toReal := by
      rw [hunion, ENNReal.toReal_sum (fun k hk => hfinN N j k hk)]
    rw [hsum]
    refine le_trans (ENNReal.toReal_mono (hfinbig N) ?_) (hCmle N)
    exact measure_mono (tileIndices_subset_bigCube hRnn j)
  exact test_integral_cauchy (fun N => weightedChaosCutoff M H N omega) hac
    (f : SpatialCoordinates d → ℝ) hfc hcs hint (R : ℝ) hRnn hsupp Cm hCmpos
    hCmass hfinN (fun j k => hcube j k)

end SubdiffusiveProcess
