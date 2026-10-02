import SubdiffusiveProcess.Analysis.CoordinateFaceIntegration

open MeasureTheory Filter Set Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess


/-- Pairs near a face: the second point is nearer that face, and tangentially nearby. -/
def cubeFacePatch {d : ℕ} (lam : ℝ) (upper : Bool) (i : Fin d)
    (x : SpatialCoordinates d) : Set (SpatialCoordinates d) :=
  Set.pi Set.univ fun j =>
    if j = i then
      if upper then Ioo (1 / 2 - lam * cubeFaceDistance upper i x) (1 / 2)
      else Ioo (-(1 / 2)) (-(1 / 2) + lam * cubeFaceDistance upper i x)
    else Ioo (max (-(1 / 2)) (x j - cubeFaceDistance upper i x))
      (min (1 / 2) (x j + cubeFaceDistance upper i x))

/-- The face weight with the fractional boundary exponent. -/
def cubeFaceWeight {d : ℕ} (s : ℝ) (upper : Bool) (i : Fin d)
    (x : SpatialCoordinates d) : ℝ≥0∞ :=
  ENNReal.ofReal (cubeFaceDistance upper i x) ^ (-(2 * s))

def cubeFaceWeightedIntegral {d : ℕ} (s : ℝ) (upper : Bool) (i : Fin d)
    (f : SpatialCoordinates d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in cubeExtensionBox d, ENNReal.ofReal (f x ^ 2) * cubeFaceWeight s upper i x

/-- Unnormalized fractional energy on the unit cube. -/
def unitCubeFractionalEnergy {d : ℕ} (s : ℝ) (f : SpatialCoordinates d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in cubeExtensionBox d, ∫⁻ y in cubeExtensionBox d, cubeFractionalKernel s f x y

theorem cubeFaceDistance_pos_lt_one {d : ℕ} (upper : Bool) (i : Fin d)
    {x : SpatialCoordinates d} (hx : x ∈ cubeExtensionBox d) :
    0 < cubeFaceDistance upper i x ∧ cubeFaceDistance upper i x < 1 := by
  have h := hx i (Set.mem_univ i)
  change -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 at h
  cases upper <;> simp only [cubeFaceDistance, Bool.false_eq_true, if_false, if_true] <;>
    constructor <;> linarith [h.1, h.2]

theorem measurable_cubeFaceWeight {d : ℕ} (s : ℝ) (upper : Bool) (i : Fin d) :
    Measurable (cubeFaceWeight s upper i) := by
  cases upper <;> unfold cubeFaceWeight cubeFaceDistance <;> simp only [if_true, if_false,
    Bool.false_eq_true] <;> fun_prop

theorem measurableSet_cubeFacePatch {d : ℕ} (lam : ℝ) (upper : Bool) (i : Fin d)
    (x : SpatialCoordinates d) : MeasurableSet (cubeFacePatch lam upper i x) := by
  apply MeasurableSet.univ_pi
  intro j
  split_ifs <;> exact measurableSet_Ioo

theorem measurableSet_cubeFacePatch_relation {d : ℕ} (lam : ℝ) (upper : Bool) (i : Fin d) :
    MeasurableSet {p : SpatialCoordinates d × SpatialCoordinates d |
      p.2 ∈ cubeFacePatch lam upper i p.1} := by
  simp only [cubeFacePatch, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const]
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  cases upper <;> by_cases hji : j = i <;>
    simp only [hji, if_true, if_false, Bool.false_eq_true, cubeFaceDistance,
      Set.mem_Ioo, setOf_and]
  all_goals
    exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))

theorem cubeFacePatch_subset {d : ℕ} (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (upper : Bool) (i : Fin d) {x : SpatialCoordinates d} (hx : x ∈ cubeExtensionBox d) :
    cubeFacePatch lam upper i x ⊆ cubeExtensionBox d := by
  intro y hy j _
  have hj := hy j (Set.mem_univ j)
  have hδ := cubeFaceDistance_pos_lt_one upper i hx
  have hmul : lam * cubeFaceDistance upper i x ≤ 1 :=
    (mul_le_of_le_one_left hδ.1.le hlam1).trans hδ.2.le
  change y j ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)
  by_cases hji : j = i
  · subst j
    cases upper <;> simp only [cubeFacePatch, if_true, if_false, Bool.false_eq_true,
      Set.mem_Ioo] at hj
    all_goals exact ⟨by linarith [hj.1, hj.2], by linarith [hj.1, hj.2]⟩
  · simp only [hji, if_false, Set.mem_Ioo] at hj
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hj.1,
      lt_of_lt_of_le hj.2 (min_le_left _ _)⟩

theorem cubeFacePatch_volume_ge {d : ℕ} (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (upper : Bool) (i : Fin d) {x : SpatialCoordinates d} (hx : x ∈ cubeExtensionBox d) :
    ENNReal.ofReal lam * ENNReal.ofReal (cubeFaceDistance upper i x) ^ d ≤
      volume (cubeFacePatch lam upper i x) := by
  let delta := cubeFaceDistance upper i x
  have hdelt : 0 < delta ∧ delta < 1 := cubeFaceDistance_pos_lt_one upper i hx
  unfold cubeFacePatch
  rw [volume_pi_pi]
  calc
    ENNReal.ofReal lam * ENNReal.ofReal delta ^ d =
        ∏ j : Fin d, (if j = i then ENNReal.ofReal lam else 1) * ENNReal.ofReal delta := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro j _
      by_cases hji : j = i
      · subst j
        simp only [if_true]
        cases upper <;> simp only [Bool.false_eq_true, if_false, if_true]
        all_goals
          rw [Real.volume_Ioo]
          rw [← ENNReal.ofReal_mul hlam0.le]
          apply ENNReal.ofReal_le_ofReal
          change lam * delta ≤ _
          dsimp only [delta]
          linarith
      · simp only [hji, if_false, one_mul, Real.volume_Ioo]
        apply ENNReal.ofReal_le_ofReal
        have hj := hx j (Set.mem_univ j)
        change -(1 / 2 : ℝ) < x j ∧ x j < 1 / 2 at hj
        change delta ≤ min (1 / 2) (x j + delta) - max (-(1 / 2)) (x j - delta)
        rw [min_def, max_def]
        split_ifs <;> linarith [hj.1, hj.2, hdelt.1, hdelt.2]

theorem euclideanDist_le_of_mem_cubeFacePatch {d : ℕ} (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) (upper : Bool) (i : Fin d) {x y : SpatialCoordinates d}
    (hx : x ∈ cubeExtensionBox d) (hy : y ∈ cubeFacePatch lam upper i x) :
    euclideanDist x y ≤ (d : ℝ) * cubeFaceDistance upper i x := by
  have hdelta := cubeFaceDistance_pos_lt_one upper i hx
  have hnorm : ‖x - y‖ ≤ cubeFaceDistance upper i x := by
    apply (pi_norm_le_iff_of_nonneg hdelta.1.le).mpr
    intro j
    change |x j - y j| ≤ cubeFaceDistance upper i x
    apply abs_le.mpr
    have hj := hy j (Set.mem_univ j)
    by_cases hji : j = i
    · subst j
      have hn : 0 < cubeFaceDistance upper i y ∧
          cubeFaceDistance upper i y < lam * cubeFaceDistance upper i x := by
        cases upper <;> simp only [if_true, if_false, Bool.false_eq_true,
          Set.mem_Ioo, cubeFaceDistance] at hj ⊢
        all_goals exact ⟨by linarith [hj.1, hj.2], by linarith [hj.1, hj.2]⟩
      have hxrel : x i = if upper then 1 / 2 - cubeFaceDistance upper i x
          else cubeFaceDistance upper i x - 1 / 2 := by
        cases upper <;> simp [cubeFaceDistance]
      have hyrel : y i = if upper then 1 / 2 - cubeFaceDistance upper i y
          else cubeFaceDistance upper i y - 1 / 2 := by
        cases upper <;> simp [cubeFaceDistance]
      have hmul : lam * cubeFaceDistance upper i x ≤ cubeFaceDistance upper i x :=
        mul_le_of_le_one_left hdelta.1.le hlam1
      cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] at hxrel hyrel
      all_goals constructor <;> linarith [hn.1, hn.2]
    · simp only [hji, if_false, Set.mem_Ioo] at hj
      have hlow := lt_of_le_of_lt (le_max_right _ _) hj.1
      have hupp := lt_of_lt_of_le hj.2 (min_le_right _ _)
      constructor <;> linarith
  exact (euclideanNorm_le_dimension_mul_norm (x - y)).trans
    (mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg d))

theorem cubeFacePatch_normal_condition {d : ℕ} (lam : ℝ) (upper : Bool) (i : Fin d)
    {x y : SpatialCoordinates d} (hy : y ∈ cubeFacePatch lam upper i x) :
    0 < cubeFaceDistance upper i y ∧
      cubeFaceDistance upper i y < lam * cubeFaceDistance upper i x := by
  have hj := hy i (Set.mem_univ i)
  cases upper <;> simp only [cubeFacePatch, if_true, if_false, Bool.false_eq_true,
    Set.mem_Ioo, cubeFaceDistance] at hj ⊢
  all_goals exact ⟨by linarith [hj.1, hj.2], by linarith [hj.1, hj.2]⟩

theorem volume_cubeFacePatch_incoming_slice_le {n : ℕ} (lam : ℝ) (upper : Bool)
    (i : Fin (n + 1)) (y : SpatialCoordinates (n + 1)) (t : ℝ) (ht : 0 < t) :
    volume {z : SpatialCoordinates n | z ∈ cubeExtensionBox n ∧
      y ∈ cubeFacePatch lam upper i (cubeFaceInsert upper i t z)} ≤
        ENNReal.ofReal ((2 * t) ^ n) := by
  let S : Set (SpatialCoordinates n) := Set.pi Set.univ fun j =>
    Ioo (y (i.succAbove j) - t) (y (i.succAbove j) + t)
  have hsub : {z : SpatialCoordinates n | z ∈ cubeExtensionBox n ∧
      y ∈ cubeFacePatch lam upper i (cubeFaceInsert upper i t z)} ⊆ S := by
    intro z hz j _
    have hj := hz.2 (i.succAbove j) (Set.mem_univ _)
    simp only [Fin.succAbove_ne, if_false, cubeFaceDistance_insert] at hj
    simp only [cubeFaceInsert, Fin.insertNth_apply_succAbove, Set.mem_Ioo] at hj
    have hlow := lt_of_le_of_lt (le_max_right _ _) hj.1
    have hupp := lt_of_lt_of_le hj.2 (min_le_right _ _)
    constructor <;> linarith
  calc
    _ ≤ volume S := measure_mono hsub
    _ = ENNReal.ofReal ((2 * t) ^ n) := by
      rw [volume_pi_pi]
      have heq : ∀ j : Fin n,
          volume (Ioo (y (i.succAbove j) - t) (y (i.succAbove j) + t)) =
            ENNReal.ofReal (2 * t) := by
        intro j
        rw [Real.volume_Ioo]
        congr 1
        ring
      simp_rw [heq]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [ENNReal.ofReal_pow (by positivity)]

end SubdiffusiveProcess
