module

public import SubdiffusiveProcess.Model.G2Observable

@[expose] public section

/-!
# Measurability of the unit-cube regularity observable

The gradient Lipschitz seminorm is reduced to a countable dense family of
distinct pairs.  Continuity then identifies that countable supremum with the
literal all-pairs supremum.
-/




namespace SubdiffusiveProcess.Model.PotentialField

open Homogenization Topology

noncomputable section

variable {d : ℕ}

private abbrev UnitPoint (d : ℕ) :=
  {x : Vec d // x ∈ openCubeSet (originCube d 0)}

private abbrev DistinctPair (d : ℕ) :=
  {p : UnitPoint d × UnitPoint d // p.1 ≠ p.2}

private def valueAtIndex (g : PotentialField d) : Option (UnitPoint d) → ℝ
  | none => 0
  | some x => |g x.1|

private def derivAtIndex (g : PotentialField d) : Option (UnitPoint d) → ℝ
  | none => 0
  | some x => ‖deriv g x.1‖

private def ratioAtIndex (g : PotentialField d) : Option (DistinctPair d) → ℝ
  | none => 0
  | some p =>
      dist (deriv g p.val.fst.val) (deriv g p.val.snd.val) /
        dist p.val.fst.val p.val.snd.val

private theorem unitPoint_mem_closedBall (x : UnitPoint d) :
    x.1 ∈ Metric.closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0)) := by
  apply Metric.ball_subset_closedBall
  rw [ball_cubeCenter_eq_openCubeSet]
  exact x.2

private theorem valueAtIndex_range_bddAbove (g : PotentialField d) :
    BddAbove (Set.range (valueAtIndex g)) := by
  let K : Set (Vec d) := Metric.closedBall
    (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
  obtain ⟨C, hC⟩ := (isCompact_closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))).exists_bound_of_continuousOn
        g.1.1.continuous.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
      exact (hC x.1 (unitPoint_mem_closedBall x)).trans (le_max_right _ _)

private theorem derivAtIndex_range_bddAbove (g : PotentialField d) :
    BddAbove (Set.range (derivAtIndex g)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))).exists_bound_of_continuousOn
        (continuous_norm.comp (deriv g).continuous).continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
      have h := hC x.1 (unitPoint_mem_closedBall x)
      have h' : ‖deriv g x.1‖ ≤ C := by
        simpa only [Function.comp_apply, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)] using h
      exact h'.trans (le_max_right _ _)

private theorem ratioAtIndex_range_bddAbove (g : PotentialField d) :
    BddAbove (Set.range (ratioAtIndex g)) := by
  let K : Set (Vec d) := Metric.closedBall
    (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
  obtain ⟨C, hC⟩ := g.2.2 K (isCompact_closedBall _ _)
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some p =>
      have hxy : p.val.fst.val ≠ p.val.snd.val :=
        fun h ↦ p.property (Subtype.ext h)
      have hdist : 0 < dist p.val.fst.val p.val.snd.val := dist_pos.mpr hxy
      have hLip := hC.dist_le_mul p.val.fst.val
        (unitPoint_mem_closedBall p.val.fst) p.val.snd.val
        (unitPoint_mem_closedBall p.val.snd)
      exact ((div_le_iff₀ hdist).2 hLip).trans (le_max_right _ _)

theorem unitCubeValueNorm_nonneg (g : PotentialField d) :
    0 ≤ unitCubeValueNorm g := by
  exact le_csSup (valueAtIndex_range_bddAbove g) ⟨none, rfl⟩

/-- Point evaluation is controlled by the unit-cube value observable. -/
theorem abs_apply_le_unitCubeValueNorm (g : PotentialField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    |g x| ≤ unitCubeValueNorm g := by
  exact le_csSup (valueAtIndex_range_bddAbove g) ⟨some ⟨x, hx⟩, rfl⟩

theorem unitCubeDerivNorm_nonneg (g : PotentialField d) :
    0 ≤ unitCubeDerivNorm g := by
  exact le_csSup (derivAtIndex_range_bddAbove g) ⟨none, rfl⟩

theorem unitCubeDerivLipschitzSeminorm_nonneg (g : PotentialField d) :
    0 ≤ unitCubeDerivLipschitzSeminorm g := by
  exact le_csSup (ratioAtIndex_range_bddAbove g) ⟨none, rfl⟩

private theorem valueAtIndex_continuous (o : Option (UnitPoint d)) :
    Continuous (fun g : PotentialField d ↦ valueAtIndex g o) := by
  cases o with
  | none => exact continuous_const
  | some x => exact continuous_abs.comp (continuous_eval x.1)

private theorem derivAtIndex_continuous (o : Option (UnitPoint d)) :
    Continuous (fun g : PotentialField d ↦ derivAtIndex g o) := by
  cases o with
  | none => exact continuous_const
  | some x => exact continuous_norm.comp (continuous_eval_deriv x.1)

private theorem ratioAtIndex_continuous (o : Option (DistinctPair d)) :
    Continuous (fun g : PotentialField d ↦ ratioAtIndex g o) := by
  cases o with
  | none => exact continuous_const
  | some p =>
      apply Continuous.div
      · exact (continuous_eval_deriv p.val.fst.val).dist
          (continuous_eval_deriv p.val.snd.val)
      · exact continuous_const
      · intro _g
        exact dist_ne_zero.mpr (fun h ↦ p.property (Subtype.ext h))

private theorem ratioOnPair_continuous (g : PotentialField d) :
    Continuous (fun p : DistinctPair d ↦ ratioAtIndex g (some p)) := by
  apply Continuous.div
  · apply Continuous.dist
    · exact (deriv g).continuous.comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    · exact (deriv g).continuous.comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
  · exact (continuous_subtype_val.comp
      (continuous_fst.comp continuous_subtype_val)).dist
        (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))
  · intro p
    exact dist_ne_zero.mpr (fun h ↦ p.property (Subtype.ext h))

private noncomputable def densePairs (d : ℕ) : Set (DistinctPair d) :=
  Classical.choose (TopologicalSpace.exists_countable_dense (DistinctPair d))

private theorem densePairs_countable (d : ℕ) : (densePairs d).Countable :=
  (Classical.choose_spec
    (TopologicalSpace.exists_countable_dense (DistinctPair d))).1

private theorem dense_densePairs (d : ℕ) : Dense (densePairs d) :=
  (Classical.choose_spec
    (TopologicalSpace.exists_countable_dense (DistinctPair d))).2

private def denseRatioAtIndex (g : PotentialField d) :
    Option (densePairs d) → ℝ
  | none => 0
  | some p => ratioAtIndex g (some p.1)

private theorem denseRatioAtIndex_range_bddAbove (g : PotentialField d) :
    BddAbove (Set.range (denseRatioAtIndex g)) := by
  obtain ⟨C, hC⟩ := ratioAtIndex_range_bddAbove g
  refine ⟨C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact hC ⟨none, rfl⟩
  | some p => exact hC ⟨some p.1, rfl⟩

private theorem sSup_denseRatio_eq (g : PotentialField d) :
    sSup (Set.range (denseRatioAtIndex g)) =
      sSup (Set.range (ratioAtIndex g)) := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, ⟨none, rfl⟩⟩
    · rintro r ⟨o, rfl⟩
      apply le_csSup (ratioAtIndex_range_bddAbove g)
      cases o with
      | none => exact ⟨none, rfl⟩
      | some p => exact ⟨some p.1, rfl⟩
  · apply csSup_le
    · exact ⟨0, ⟨none, rfl⟩⟩
    · rintro r ⟨o, rfl⟩
      cases o with
      | none =>
          exact le_csSup (denseRatioAtIndex_range_bddAbove g) ⟨none, rfl⟩
      | some p =>
          let c := sSup (Set.range (denseRatioAtIndex g))
          let q : DistinctPair d → ℝ := fun z ↦ ratioAtIndex g (some z)
          have hclosed : IsClosed (q ⁻¹' Set.Iic c) :=
            isClosed_Iic.preimage (ratioOnPair_continuous g)
          have hsubset : densePairs d ⊆ q ⁻¹' Set.Iic c := by
            intro z hz
            exact le_csSup (denseRatioAtIndex_range_bddAbove g)
              ⟨some ⟨z, hz⟩, rfl⟩
          have hclosure := closure_minimal hsubset hclosed
          rw [(dense_densePairs d).closure_eq] at hclosure
          exact hclosure (Set.mem_univ p)

private theorem denseRatioAtIndex_continuous (o : Option (densePairs d)) :
    Continuous (fun g : PotentialField d ↦ denseRatioAtIndex g o) := by
  cases o with
  | none => exact continuous_const
  | some p => exact ratioAtIndex_continuous (some p.1)

theorem unitCubeValueNorm_lowerSemicontinuous :
    LowerSemicontinuous (unitCubeValueNorm : PotentialField d → ℝ) := by
  have h := lowerSemicontinuous_ciSup
    (fun g : PotentialField d ↦ valueAtIndex_range_bddAbove g)
    (fun o ↦ (valueAtIndex_continuous o).lowerSemicontinuous)
  simpa only [unitCubeValueNorm, iSup] using! h

theorem unitCubeDerivNorm_lowerSemicontinuous :
    LowerSemicontinuous (unitCubeDerivNorm : PotentialField d → ℝ) := by
  have h := lowerSemicontinuous_ciSup
    (fun g : PotentialField d ↦ derivAtIndex_range_bddAbove g)
    (fun o ↦ (derivAtIndex_continuous o).lowerSemicontinuous)
  simpa only [unitCubeDerivNorm, iSup] using! h

theorem unitCubeValueNorm_measurable :
    Measurable (unitCubeValueNorm : PotentialField d → ℝ) :=
  unitCubeValueNorm_lowerSemicontinuous.measurable

theorem unitCubeDerivNorm_measurable :
    Measurable (unitCubeDerivNorm : PotentialField d → ℝ) :=
  unitCubeDerivNorm_lowerSemicontinuous.measurable

theorem unitCubeDerivLipschitzSeminorm_measurable :
    Measurable (unitCubeDerivLipschitzSeminorm : PotentialField d → ℝ) := by
  let : Countable (densePairs d) := densePairs_countable d
  have h : Measurable (fun g : PotentialField d ↦
      ⨆ o : Option (densePairs d), denseRatioAtIndex g o) :=
    Measurable.iSup fun o ↦ (denseRatioAtIndex_continuous o).measurable
  have heq : (fun g : PotentialField d ↦
      ⨆ o : Option (densePairs d), denseRatioAtIndex g o) =
      unitCubeDerivLipschitzSeminorm := by
    funext g
    simpa only [iSup, unitCubeDerivLipschitzSeminorm] using! sSup_denseRatio_eq g
  rwa [heq] at h

theorem g2Observable_nonneg (g : PotentialField d) :
    0 ≤ g2Observable g :=
  add_nonneg
    (add_nonneg (unitCubeValueNorm_nonneg g) (unitCubeDerivNorm_nonneg g))
    (unitCubeDerivLipschitzSeminorm_nonneg g)

/-- Point evaluation on the unit cube is controlled by the full `(g2)`
observable. -/
theorem abs_apply_le_g2Observable (g : PotentialField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    |g x| ≤ g2Observable g := by
  calc
    |g x| ≤ unitCubeValueNorm g := abs_apply_le_unitCubeValueNorm g hx
    _ ≤ g2Observable g := by
      unfold g2Observable
      exact (le_add_of_nonneg_right (unitCubeDerivNorm_nonneg g)).trans
        (le_add_of_nonneg_right (unitCubeDerivLipschitzSeminorm_nonneg g))

theorem g2Observable_measurable :
    Measurable (g2Observable : PotentialField d → ℝ) :=
  (unitCubeValueNorm_measurable.add unitCubeDerivNorm_measurable).add
    unitCubeDerivLipschitzSeminorm_measurable

/-! ### Pointwise readouts of the three unit-cube observables

The value readout is `abs_apply_le_unitCubeValueNorm` above; these are the two
missing siblings, together with the three comparisons against the packaged
`(g2)` observable. -/

/-- Pointwise gradient control by the unit-cube gradient observable. -/
theorem norm_deriv_le_unitCubeDerivNorm (g : PotentialField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    ‖deriv g x‖ ≤ unitCubeDerivNorm g :=
  le_csSup (derivAtIndex_range_bddAbove g) ⟨some ⟨x, hx⟩, rfl⟩

/-- Pairwise gradient control by the unit-cube gradient Lipschitz seminorm. -/
theorem dist_deriv_le_unitCubeDerivLipschitzSeminorm_mul (g : PotentialField d)
    {x y : Vec d} (hx : x ∈ openCubeSet (originCube d 0))
    (hy : y ∈ openCubeSet (originCube d 0)) :
    dist (deriv g x) (deriv g y) ≤
      unitCubeDerivLipschitzSeminorm g * dist x y := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hne : (⟨x, hx⟩ : UnitPoint d) ≠ ⟨y, hy⟩ := fun h ↦ hxy (Subtype.ext_iff.mp h)
    have hle : dist (deriv g x) (deriv g y) / dist x y ≤
        unitCubeDerivLipschitzSeminorm g :=
      le_csSup (ratioAtIndex_range_bddAbove g)
        ⟨some ⟨(⟨x, hx⟩, ⟨y, hy⟩), hne⟩, rfl⟩
    exact (div_le_iff₀ hd).mp hle

/-- The norm version of `dist_deriv_le_unitCubeDerivLipschitzSeminorm_mul`. -/
theorem norm_deriv_sub_deriv_le_unitCubeDerivLipschitzSeminorm_mul
    (g : PotentialField d) {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0))
    (hy : y ∈ openCubeSet (originCube d 0)) :
    ‖deriv g x - deriv g y‖ ≤ unitCubeDerivLipschitzSeminorm g * ‖x - y‖ := by
  simpa only [dist_eq_norm] using
    dist_deriv_le_unitCubeDerivLipschitzSeminorm_mul g hx hy

theorem unitCubeValueNorm_le_g2Observable (g : PotentialField d) :
    unitCubeValueNorm g ≤ g2Observable g := by
  unfold g2Observable
  have h₁ := unitCubeDerivNorm_nonneg g
  have h₂ := unitCubeDerivLipschitzSeminorm_nonneg g
  linarith

theorem unitCubeDerivNorm_le_g2Observable (g : PotentialField d) :
    unitCubeDerivNorm g ≤ g2Observable g := by
  unfold g2Observable
  have h₁ := unitCubeValueNorm_nonneg g
  have h₂ := unitCubeDerivLipschitzSeminorm_nonneg g
  linarith

theorem unitCubeDerivLipschitzSeminorm_le_g2Observable (g : PotentialField d) :
    unitCubeDerivLipschitzSeminorm g ≤ g2Observable g := by
  unfold g2Observable
  have h₁ := unitCubeValueNorm_nonneg g
  have h₂ := unitCubeDerivNorm_nonneg g
  linarith

/-- Pointwise gradient control by the full `(g2)` observable. -/
theorem norm_deriv_le_g2Observable (g : PotentialField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    ‖deriv g x‖ ≤ g2Observable g :=
  (norm_deriv_le_unitCubeDerivNorm g hx).trans (unitCubeDerivNorm_le_g2Observable g)

/-- Pairwise gradient control by the full `(g2)` observable. -/
theorem norm_deriv_sub_deriv_le_g2Observable_mul (g : PotentialField d)
    {x y : Vec d} (hx : x ∈ openCubeSet (originCube d 0))
    (hy : y ∈ openCubeSet (originCube d 0)) :
    ‖deriv g x - deriv g y‖ ≤ g2Observable g * ‖x - y‖ :=
  (norm_deriv_sub_deriv_le_unitCubeDerivLipschitzSeminorm_mul g hx hy).trans
    (mul_le_mul_of_nonneg_right (unitCubeDerivLipschitzSeminorm_le_g2Observable g)
      (norm_nonneg _))

end

end SubdiffusiveProcess.Model.PotentialField
