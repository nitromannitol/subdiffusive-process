module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.Cells

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

open Homogenization Filter Set Topology

noncomputable section

variable {d : ℕ}

/-! ## Local-coordinate form of the two cube realizations -/

private theorem cubeScaleFactor_pos (Q : TriadicCube d) : 0 < cubeScaleFactor Q :=
  zpow_pos (by norm_num) _

private theorem mem_cubeSet_iff_localCoordinate {Q : TriadicCube d} {x : Vec d} :
    x ∈ cubeSet Q ↔
      ∀ i : Fin d,
        -(1 / 2 : ℝ) * cubeScaleFactor Q ≤ triadicLocalCoordinate Q x i ∧
          triadicLocalCoordinate Q x i < (1 / 2 : ℝ) * cubeScaleFactor Q := by
  simp only [cubeSet, Set.mem_setOf_eq, triadicLocalCoordinate]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

private theorem mem_openCubeSet_iff_localCoordinate {Q : TriadicCube d} {x : Vec d} :
    x ∈ openCubeSet Q ↔
      ∀ i : Fin d,
        -(1 / 2 : ℝ) * cubeScaleFactor Q < triadicLocalCoordinate Q x i ∧
          triadicLocalCoordinate Q x i < (1 / 2 : ℝ) * cubeScaleFactor Q := by
  simp only [openCubeSet, Set.mem_setOf_eq, triadicLocalCoordinate]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

private theorem continuous_localCoordinate (Q : TriadicCube d) (k : Fin d) :
    Continuous fun x : Vec d => triadicLocalCoordinate Q x k :=
  (continuous_apply k).sub continuous_const

/-! ## The closed cell is closed -/



theorem isClosed_closedCarrier (T : KuhnCell d) : IsClosed T.closedCarrier := by
  have hEq : T.closedCarrier =
      Metric.closedBall (cubeCenter T.supportCube) (cubeRadius T.supportCube) ∩
        ⋂ i : Fin d, ⋂ j : Fin d,
          {x : Vec d | i.val ≤ j.val →
            triadicLocalCoordinate T.supportCube x (T.order i) ≤
              triadicLocalCoordinate T.supportCube x (T.order j)} := by
    ext x
    simp only [KuhnCell.closedCarrier, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter]
  rw [hEq]
  refine Metric.isClosed_closedBall.inter ?_
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : i.val ≤ j.val
  · have hset :
        {x : Vec d | i.val ≤ j.val →
            triadicLocalCoordinate T.supportCube x (T.order i) ≤
              triadicLocalCoordinate T.supportCube x (T.order j)} =
          {x : Vec d |
            triadicLocalCoordinate T.supportCube x (T.order i) ≤
              triadicLocalCoordinate T.supportCube x (T.order j)} := by
      ext x; simp [hij]
    rw [hset]
    exact isClosed_le (continuous_localCoordinate T.supportCube (T.order i))
      (continuous_localCoordinate T.supportCube (T.order j))
  · have hset :
        {x : Vec d | i.val ≤ j.val →
            triadicLocalCoordinate T.supportCube x (T.order i) ≤
              triadicLocalCoordinate T.supportCube x (T.order j)} = Set.univ := by
      ext x; simp [hij]
    rw [hset]
    exact isClosed_univ

theorem closure_openCarrier_subset_closedCarrier (T : KuhnCell d) :
    closure T.openCarrier ⊆ T.closedCarrier :=
  (isClosed_closedCarrier T).closure_subset_iff.mpr T.openCarrier_subset_closedCarrier

/-! ## The half-open cell is inside the closure of the open cell -/

/-- **Every point of the half-open cell is a limit of interior points.**  The
contraction towards the explicit interior point whose local coordinates are
proportional to the cell's own order sends the half-open cell into the open
one; letting the contraction parameter tend to zero gives the claim. -/
theorem carrier_subset_closure_openCarrier (T : KuhnCell d) :
    T.carrier ⊆ closure T.openCarrier := by
  intro x hx
  set Q : TriadicCube d := T.supportCube with hQ
  set s : ℝ := cubeScaleFactor Q with hs'
  have hs : 0 < s := cubeScaleFactor_pos Q
  -- the local coordinates of an explicit interior point
  set ell : Fin d → ℝ :=
    fun k => s * ((T.order.symm k).val : ℝ) / (4 * ((d : ℝ) + 1)) with hell
  have hdpos : (0 : ℝ) < 4 * ((d : ℝ) + 1) := by positivity
  have hell_nonneg : ∀ k, 0 ≤ ell k := by
    intro k
    rw [hell]
    positivity
  have hell_lt : ∀ k, ell k < s / 4 := by
    intro k
    have hrank : (((T.order.symm k).val : ℝ)) < (d : ℝ) + 1 := by
      have := (T.order.symm k).isLt
      have : (((T.order.symm k).val : ℝ)) < (d : ℝ) := by exact_mod_cast this
      linarith
    rw [hell, div_lt_iff₀ hdpos]
    nlinarith [hs, hrank]
  have hell_mono : ∀ i j : Fin d, i.val < j.val → ell (T.order i) < ell (T.order j) := by
    intro i j hij
    have hlt : ((i.val : ℝ)) < (j.val : ℝ) := by exact_mod_cast hij
    rw [hell]
    simp only [Equiv.symm_apply_apply]
    rw [div_lt_div_iff_of_pos_right hdpos]
    nlinarith [hs, hlt]
  -- the interior point itself
  set z : Vec d := fun i => (Q.index i : ℝ) * s + ell i with hz
  have hzloc : ∀ i, triadicLocalCoordinate Q z i = ell i := by
    intro i
    simp only [triadicLocalCoordinate, hz, ← hs']
    ring
  -- the contraction
  set y : ℝ → Vec d := fun t => x + t • (z - x) with hy
  have hyloc : ∀ (t : ℝ) (i : Fin d),
      triadicLocalCoordinate Q (y t) i =
        (1 - t) * triadicLocalCoordinate Q x i + t * ell i := by
    intro t i
    have : y t i = x i + t * (z i - x i) := by
      simp [hy, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [triadicLocalCoordinate, this, hz]
    ring
  -- the local coordinates of `x`
  have hxcube : x ∈ cubeSet Q := hx.1
  have hxbox := mem_cubeSet_iff_localCoordinate.mp hxcube
  have hxmono : ∀ i j : Fin d, i.val ≤ j.val →
      triadicLocalCoordinate Q x (T.order i) ≤ triadicLocalCoordinate Q x (T.order j) := by
    intro i j hij
    have := hx.2
    rw [this]
    exact Tuple.monotone_sort (triadicLocalCoordinate T.supportCube x) hij
  -- the contracted point lies in the open cell
  have hmem : ∀ t : ℝ, 0 < t → t ≤ 1 → y t ∈ T.openCarrier := by
    intro t ht0 ht1
    rw [KuhnCell.mem_openCarrier_iff]
    constructor
    · rw [mem_openCubeSet_iff_localCoordinate]
      intro i
      have hb := hxbox i
      have hl0 := hell_nonneg i
      have hl1 := hell_lt i
      rw [hyloc t i]
      constructor
      · have h1 : 0 ≤ (1 - t) * (triadicLocalCoordinate Q x i + s / 2) :=
          mul_nonneg (by linarith) (by linarith [hb.1])
        have h2 : 0 < t * (ell i + s / 2) := mul_pos ht0 (by linarith)
        linarith
      · have h1 : 0 ≤ (1 - t) * (s / 2 - triadicLocalCoordinate Q x i) :=
          mul_nonneg (by linarith) (by linarith [hb.2])
        have h2 : 0 < t * (s / 2 - ell i) := mul_pos ht0 (by linarith)
        linarith
    · intro i j hij
      have h1 : 0 ≤ (1 - t) *
          (triadicLocalCoordinate Q x (T.order j) -
            triadicLocalCoordinate Q x (T.order i)) :=
        mul_nonneg (by linarith) (by linarith [hxmono i j hij.le])
      have h2 : 0 < t * (ell (T.order j) - ell (T.order i)) :=
        mul_pos ht0 (by linarith [hell_mono i j hij])
      rw [hyloc t (T.order i), hyloc t (T.order j)]
      linarith
  -- let the contraction parameter tend to zero
  refine mem_closure_of_tendsto (f := fun n : ℕ => y (1 / ((n : ℝ) + 1)))
    (b := atTop) ?_ ?_
  · have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => x + (1 / ((n : ℝ) + 1)) • (z - x)) atTop
        (nhds (x + (0 : ℝ) • (z - x))) :=
      (h0.smul_const (z - x)).const_add x
    simpa [hy] using h1
  · refine Filter.Eventually.of_forall fun n => ?_
    refine hmem _ (by positivity) ?_
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-! ## An interior point determines the order -/

/-- Two cells with the same support cube whose closed and open realizations
share a point carry the same order.  A point of the open cell has pairwise
distinct local coordinates, so a weakly monotone order is strictly monotone,
and both orders are then `Tuple.sort` of those coordinates. -/
theorem order_eq_of_mem_closedCarrier_of_mem_openCarrier {V T : KuhnCell d}
    (hVT : V.supportCube = T.supportCube) {x : Vec d}
    (hxV : x ∈ V.closedCarrier) (hxT : x ∈ T.openCarrier) : V.order = T.order := by
  set f : Fin d → ℝ := fun k => triadicLocalCoordinate T.supportCube x k with hf
  -- the open cell forces the printed strict chain
  have hstrict : ∀ i j : Fin d, i.val < j.val → f (T.order i) < f (T.order j) :=
    (KuhnCell.mem_openCarrier_iff.mp hxT).2
  -- hence pairwise distinct coordinates
  have hinj : ∀ a b : Fin d, a ≠ b → f a ≠ f b := by
    intro a b hab
    obtain ⟨a', rfl⟩ : ∃ a', T.order a' = a := ⟨T.order.symm a, T.order.apply_symm_apply a⟩
    obtain ⟨b', rfl⟩ : ∃ b', T.order b' = b := ⟨T.order.symm b, T.order.apply_symm_apply b⟩
    have hne : a' ≠ b' := fun h => hab (congrArg T.order h)
    rcases lt_or_gt_of_ne (fun h : a'.val = b'.val => hne (Fin.ext h)) with h | h
    · exact ne_of_lt (hstrict a' b' h)
    · exact ne_of_gt (hstrict b' a' h)
  -- `T.order` sorts `f`
  have hTsort : T.order = Tuple.sort f :=
    (T.openCarrier_subset_carrier hxT).2
  -- so does `V.order`
  have hVmono : ∀ i j : Fin d, i.val ≤ j.val → f (V.order i) ≤ f (V.order j) := by
    intro i j hij
    have := hxV.2 i j hij
    rw [hVT] at this
    exact this
  have hVsort : V.order = Tuple.sort f := by
    refine (Tuple.eq_sort_iff (f := f) (σ := V.order)).2 ⟨?_, ?_⟩
    · intro i j hij
      exact hVmono i j hij
    · intro i j hij heq
      exact absurd heq (hinj _ _ fun h => absurd (V.order.injective h) (ne_of_lt hij))
  rw [hTsort, hVsort]

/-! ## The mesh -/



theorem exists_triadicSubMesh (U : KuhnCell d) (R : ℕ) :
    ∃ S : Finset (KuhnCell d),
      (∀ T ∈ S, T.supportCube.scale = U.supportCube.scale - (R : ℤ)) ∧
      (∀ T ∈ S, T.openCarrier ⊆ U.openCarrier) ∧
      U.openCarrier ⊆ ⋃ T ∈ (S : Set (KuhnCell d)), T.carrier := by
  classical
  set Q : TriadicCube d := U.supportCube with hQ
  set j : ℤ := Q.scale - (R : ℤ) with hj'
  have hj : j ≤ Q.scale := by omega
  refine ⟨(triadicSimplexPartition Q j).filter (fun T => T.openCarrier ⊆ U.openCarrier),
    ?_, ?_, ?_⟩
  · intro T hT
    exact supportCube_scale_eq_of_mem_triadicSimplexPartition hj (Finset.mem_filter.mp hT).1
  · intro T hT
    exact (Finset.mem_filter.mp hT).2
  · intro x hx
    have hxcube : x ∈ cubeSet Q :=
      openCubeSet_subset_cubeSet Q (U.openCarrier_subset_openCubeSet hx)
    rw [cubeSet_eq_iUnion_triadicSimplexPartition Q hj] at hxcube
    obtain ⟨T, hT, hxT⟩ := by simpa only [Set.mem_iUnion] using hxcube
    obtain ⟨V, hV, hTV⟩ :=
      triadicSimplexPartition_refines_openCarrier Q (le_refl Q.scale) hj hT
    -- the coarse parent has the support cube of `U`
    have hVQ : V.supportCube = Q := by
      have hmem : V.supportCube ∈ descendantsAtScale Q Q.scale :=
        mem_triadicSimplexPartition_iff.mp hV
      rw [descendantsAtScale_self, Finset.mem_singleton] at hmem
      exact hmem
    -- and, because it meets the interior of `U`, the order of `U`
    have hxVclosed : x ∈ V.closedCarrier :=
      closure_openCarrier_subset_closedCarrier V
        (closure_mono hTV (carrier_subset_closure_openCarrier T hxT))
    have hVU : V = U := by
      have horder : V.order = U.order :=
        order_eq_of_mem_closedCarrier_of_mem_openCarrier (hVQ.trans hQ) hxVclosed hx
      cases V with
      | mk QV piV =>
          cases U with
          | mk QU piU =>
              simp only at hVQ horder hQ
              simp only [KuhnCell.mk.injEq]
              exact ⟨hVQ.trans hQ, horder⟩
    refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨?_, hxT⟩⟩
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hT, ?_⟩)
    rw [← hVU]
    exact hTV

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn
