import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRefinedIntersection
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszStoppingGeneric




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- The repaired graph joins cells with near selected parents. -/
def repairedStoppingGraph :
    SimpleGraph (RefinedStoppingCell failure omega base) :=
  SimpleGraph.fromRel fun q p ↦
    StoppingCubesNear (refinedStoppingFailureCube q)
      (refinedStoppingFailureCube p)

omit [NeZero d] in
theorem repairedStoppingGraph_adj_iff
    (q p : RefinedStoppingCell failure omega base) :
    repairedStoppingGraph.Adj q p ↔ q ≠ p ∧
      StoppingCubesNear (refinedStoppingFailureCube q)
        (refinedStoppingFailureCube p) := by
  rw [repairedStoppingGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hnear | hnear⟩
    · exact ⟨hne, hnear⟩
    · exact ⟨hne, (stoppingCubesNear_comm _ _).mpr hnear⟩
  · rintro ⟨hne, hnear⟩
    exact ⟨hne, Or.inl hnear⟩

omit [NeZero d] in
/-- Intersecting refined cells are adjacent in the repaired graph. -/
theorem repairedStoppingGraph_adj_of_inter_nonempty
    {q p : RefinedStoppingCell failure omega base} (hne : q ≠ p)
    (hinter :
      (translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p) (refinedStoppingCenter p)).Nonempty) :
    repairedStoppingGraph.Adj q p :=
  (repairedStoppingGraph_adj_iff q p).mpr
    ⟨hne, stoppingCubesNear_of_refinedStoppingCell_inter_nonempty hinter⟩

/-- Near selected parents have one of five relative scales. -/
theorem repairedStoppingGraph_scale_window
    {q p : RefinedStoppingCell failure omega base}
    (hadj : repairedStoppingGraph.Adj q p) :
    -(2 : ℤ) ≤ (refinedStoppingFailureCube p).scale -
        (refinedStoppingFailureCube q).scale ∧
      (refinedStoppingFailureCube p).scale -
        (refinedStoppingFailureCube q).scale ≤ 2 := by
  have hnear := (repairedStoppingGraph_adj_iff q p).mp hadj |>.2
  have habs := abs_scale_sub_le_two_of_repairedStoppingCube_near
    failure omega hnear
  change |(refinedStoppingFailureCube q).scale -
    (refinedStoppingFailureCube p).scale| ≤ 2 at habs
  rw [abs_le] at habs
  constructor <;> omega

/-- The side of either near parent is at most nine times the other's side. -/
theorem cubeScaleFactor_le_nine_mul_of_repairedStoppingGraph_adj
    {q p : RefinedStoppingCell failure omega base}
    (hadj : repairedStoppingGraph.Adj q p) :
    cubeScaleFactor (refinedStoppingFailureCube q) ≤
      9 * cubeScaleFactor (refinedStoppingFailureCube p) := by
  have hwindow := repairedStoppingGraph_scale_window hadj
  have hscale : (refinedStoppingFailureCube q).scale ≤
      (refinedStoppingFailureCube p).scale + 2 := by omega
  have hpow := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hscale
  calc
    cubeScaleFactor (refinedStoppingFailureCube q) ≤
        (3 : ℝ) ^ ((refinedStoppingFailureCube p).scale + 2) := hpow
    _ = 9 * cubeScaleFactor (refinedStoppingFailureCube p) := by
      rw [cubeScaleFactor, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
      ring

/-- Nearness gives a fixed real coordinate window after normalizing by the
neighbor's side length. -/
theorem repairedStoppingGraph_normalized_index_sub_le
    {q p : RefinedStoppingCell failure omega base}
    (hadj : repairedStoppingGraph.Adj q p) (i : Fin d) :
    |((refinedStoppingFailureCube p).index i : ℝ) -
        cubeCenter (refinedStoppingFailureCube q) i /
          cubeScaleFactor (refinedStoppingFailureCube p)| ≤ 90 := by
  let Q := refinedStoppingFailureCube q
  let P := refinedStoppingFailureCube p
  have hnear := (repairedStoppingGraph_adj_iff q p).mp hadj |>.2
  have hPpos : 0 < cubeScaleFactor P := zpow_pos (by norm_num) _
  have hQle : cubeScaleFactor Q ≤ 9 * cubeScaleFactor P :=
    cubeScaleFactor_le_nine_mul_of_repairedStoppingGraph_adj hadj
  have hmax : max (cubeScaleFactor Q) (cubeScaleFactor P) ≤
      9 * cubeScaleFactor P := by
    rw [max_le_iff]
    exact ⟨hQle, by nlinarith⟩
  have hmax0 : 0 ≤ max (cubeScaleFactor Q) (cubeScaleFactor P) :=
    (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale).le.trans
      (le_max_left _ _)
  have hcoord : dist (cubeCenter Q i) (cubeCenter P i) ≤
      10 * max (cubeScaleFactor Q) (cubeScaleFactor P) := by
    exact (dist_pi_le_iff (mul_nonneg (by norm_num) hmax0)).mp hnear i
  have hcoord' : |cubeCenter P i - cubeCenter Q i| ≤
      90 * cubeScaleFactor P := by
    rw [Real.dist_eq, abs_sub_comm] at hcoord
    calc
      |cubeCenter P i - cubeCenter Q i| ≤
          10 * max (cubeScaleFactor Q) (cubeScaleFactor P) := hcoord
      _ ≤ 10 * (9 * cubeScaleFactor P) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ = 90 * cubeScaleFactor P := by ring
  have hcenterP : cubeCenter P i =
      (P.index i : ℝ) * cubeScaleFactor P := rfl
  rw [hcenterP] at hcoord'
  rw [abs_le] at hcoord'
  change |(P.index i : ℝ) - cubeCenter Q i / cubeScaleFactor P| ≤ 90
  rw [abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add]
    apply (div_le_iff₀ hPpos).2
    nlinarith [hcoord'.1]
  · rw [sub_le_iff_le_add]
    have hmul : ((P.index i : ℝ) - 90) * cubeScaleFactor P ≤
        cubeCenter Q i := by
      nlinarith [hcoord'.2]
    have hdiv := (le_div_iff₀ hPpos).2 hmul
    linarith

/-- Each coordinate of a neighboring triadic index lies in a fixed integer
window around the floor of the normalized reference center. -/
theorem repairedStoppingGraph_index_window
    {q p : RefinedStoppingCell failure omega base}
    (hadj : repairedStoppingGraph.Adj q p) (i : Fin d) :
    -(90 : ℤ) ≤ (refinedStoppingFailureCube p).index i -
        ⌊cubeCenter (refinedStoppingFailureCube q) i /
          cubeScaleFactor (refinedStoppingFailureCube p)⌋ ∧
      (refinedStoppingFailureCube p).index i -
        ⌊cubeCenter (refinedStoppingFailureCube q) i /
          cubeScaleFactor (refinedStoppingFailureCube p)⌋ < 92 := by
  let a := cubeCenter (refinedStoppingFailureCube q) i /
    cubeScaleFactor (refinedStoppingFailureCube p)
  have hnorm := repairedStoppingGraph_normalized_index_sub_le hadj i
  have hfloorLe : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
  have haLt : a < (⌊a⌋ : ℝ) + 1 := by
    exact_mod_cast Int.lt_floor_add_one a
  have hlowerReal : (-(90 : ℤ) : ℝ) ≤
      (((refinedStoppingFailureCube p).index i - ⌊a⌋ : ℤ) : ℝ) := by
    rw [Int.cast_sub]
    rw [abs_le] at hnorm
    dsimp only [a] at hnorm hfloorLe haLt ⊢
    linarith
  have hupperReal :
      (((refinedStoppingFailureCube p).index i - ⌊a⌋ : ℤ) : ℝ) < 92 := by
    rw [Int.cast_sub]
    rw [abs_le] at hnorm
    dsimp only [a] at hnorm hfloorLe haLt ⊢
    linarith
  exact ⟨by exact_mod_cast hlowerReal, by exact_mod_cast hupperReal⟩

/-- Finite code space for a neighbor: relative scale, normalized parent
index, and half-grid offset. -/
def RepairedStoppingNeighborCode (d : ℕ) :=
  Fin 5 × (Fin d → Fin 182) × StoppingHalfGridOffset d

noncomputable instance : Fintype (RepairedStoppingNeighborCode d) := by
  dsimp only [RepairedStoppingNeighborCode]
  infer_instance

/-- Encode one graph neighbor into the fixed dimension-only code space. -/
def repairedStoppingNeighborCode
    (q : RefinedStoppingCell failure omega base) :
    repairedStoppingGraph.neighborSet q → RepairedStoppingNeighborCode d :=
  fun p ↦
    let hwindow := repairedStoppingGraph_scale_window p.2
    let delta := (refinedStoppingFailureCube p.1).scale -
      (refinedStoppingFailureCube q).scale
    let scaleCode : Fin 5 :=
      ⟨(delta + 2).toNat, by
        have h0 : 0 ≤ delta + 2 := by omega
        have h5 : delta + 2 < 5 := by omega
        rw [Int.toNat_lt (by omega)]
        exact_mod_cast h5⟩
    let indexCode : Fin d → Fin 182 := fun i ↦
      let z := (refinedStoppingFailureCube p.1).index i -
        ⌊cubeCenter (refinedStoppingFailureCube q) i /
          cubeScaleFactor (refinedStoppingFailureCube p.1)⌋ + 90
      let hz := repairedStoppingGraph_index_window p.2 i
      ⟨z.toNat, by
        have h0 : 0 ≤ z := by omega
        have h182 : z < 182 := by omega
        rw [Int.toNat_lt (by omega)]
        exact_mod_cast h182⟩
    (scaleCode, indexCode, p.1.2)

/-- The fixed neighbor code is injective. -/
theorem repairedStoppingNeighborCode_injective
    (q : RefinedStoppingCell failure omega base) :
    Function.Injective (repairedStoppingNeighborCode q) := by
  rintro ⟨p, hp⟩ ⟨r, hr⟩ hcode
  have hpWindow := repairedStoppingGraph_scale_window hp
  have hrWindow := repairedStoppingGraph_scale_window hr
  have hscaleCode := congrArg (fun c : RepairedStoppingNeighborCode d ↦ c.1) hcode
  have hscale : (refinedStoppingFailureCube p).scale =
      (refinedStoppingFailureCube r).scale := by
    dsimp only [repairedStoppingNeighborCode] at hscaleCode
    simp only [Fin.mk.injEq] at hscaleCode
    have hp0 : 0 ≤ (refinedStoppingFailureCube p).scale -
        (refinedStoppingFailureCube q).scale + 2 := by omega
    have hr0 : 0 ≤ (refinedStoppingFailureCube r).scale -
        (refinedStoppingFailureCube q).scale + 2 := by omega
    omega
  have hoffset : p.2 = r.2 := by
    exact congrArg (fun c : RepairedStoppingNeighborCode d ↦ c.2.2) hcode
  have hindexCode := congrArg (fun c : RepairedStoppingNeighborCode d ↦ c.2.1) hcode
  have hindex : (refinedStoppingFailureCube p).index =
      (refinedStoppingFailureCube r).index := by
    funext i
    have hi := congrFun hindexCode i
    dsimp only [repairedStoppingNeighborCode] at hi
    simp only [Fin.mk.injEq] at hi
    have hpz := repairedStoppingGraph_index_window hp i
    have hrz := repairedStoppingGraph_index_window hr i
    have hp0 : 0 ≤ (refinedStoppingFailureCube p).index i -
        ⌊cubeCenter (refinedStoppingFailureCube q) i /
          cubeScaleFactor (refinedStoppingFailureCube p)⌋ + 90 := by omega
    have hr0 : 0 ≤ (refinedStoppingFailureCube r).index i -
        ⌊cubeCenter (refinedStoppingFailureCube q) i /
          cubeScaleFactor (refinedStoppingFailureCube r)⌋ + 90 := by omega
    have hfactor : cubeScaleFactor (refinedStoppingFailureCube p) =
        cubeScaleFactor (refinedStoppingFailureCube r) := by
      unfold cubeScaleFactor
      exact congrArg (fun s : ℤ ↦ (3 : ℝ) ^ s) hscale
    have hfloor :
        ⌊cubeCenter (refinedStoppingFailureCube q) i /
            cubeScaleFactor (refinedStoppingFailureCube p)⌋ =
          ⌊cubeCenter (refinedStoppingFailureCube q) i /
            cubeScaleFactor (refinedStoppingFailureCube r)⌋ := by
      rw [hfactor]
    rw [hfloor] at hi
    omega
  have hcube : refinedStoppingFailureCube p = refinedStoppingFailureCube r := by
    exact congrArg₂ TriadicCube.mk hscale hindex
  have hparent : p.1 = r.1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hcube
  apply Subtype.ext
  exact Prod.ext hparent hoffset

/-- The repaired graph is locally finite. -/
noncomputable instance repairedStoppingGraphLocallyFinite
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ) :
    (repairedStoppingGraph (failure := failure) (omega := omega)
      (base := base)).LocallyFinite := fun q ↦
  Fintype.ofInjective (repairedStoppingNeighborCode q)
    (repairedStoppingNeighborCode_injective q)

/-- Explicit dimension-only degree bound for the repaired graph. -/
def repairedStoppingDegreeBound (d : ℕ) : ℕ :=
  5 * 182 ^ d * 7 ^ d

/-- Every repaired graph degree obeys the explicit dimension-only bound. -/
theorem card_repairedStoppingGraph_neighborFinset_le
    (q : RefinedStoppingCell failure omega base) :
    (repairedStoppingGraph.neighborFinset q).card ≤
      repairedStoppingDegreeBound d := by
  have hcard := Fintype.card_le_of_injective
    (repairedStoppingNeighborCode q)
    (repairedStoppingNeighborCode_injective q)
  rw [SimpleGraph.neighborFinset_def, Set.toFinset_card]
  simpa only [RepairedStoppingNeighborCode, repairedStoppingDegreeBound,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    card_stoppingHalfGridOffset, mul_assoc] using hcard

omit [NeZero d] in
/-- Two distinct refined cells with meeting enlargements are adjacent in the
repaired graph. -/
theorem repairedStoppingGraph_adj_of_enlargements_inter_nonempty
    {q p : RefinedStoppingCell failure omega base} (hne : q ≠ p)
    (hinter :
      (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p + 1)
          (refinedStoppingCenter p)).Nonempty) :
    repairedStoppingGraph.Adj q p :=
  (repairedStoppingGraph_adj_iff q p).mpr
    ⟨hne, stoppingCubesNear_of_refinedStoppingCell_enlargements_inter_nonempty
      hinter⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
