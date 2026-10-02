import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionLaminarRepair
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionHalfGridCover




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- The finite half-grid offset set used over each selected cube. -/
def StoppingHalfGridOffset (d : ℕ) :=
  {k : Fin d → ℤ // k ∈ gridNeighbours d (0 : Fin d → ℤ)}

instance : Fintype (StoppingHalfGridOffset d) := by
  dsimp only [StoppingHalfGridOffset]
  infer_instance

instance : DecidableEq (StoppingHalfGridOffset d) := by
  dsimp only [StoppingHalfGridOffset]
  infer_instance

instance : Encodable (StoppingHalfGridOffset d) := Fintype.toEncodable _

@[simp]
theorem card_stoppingHalfGridOffset (d : ℕ) :
    Fintype.card (StoppingHalfGridOffset d) = 7 ^ d := by
  let e : StoppingHalfGridOffset d ≃
      {k // k ∈ gridNeighbours d (0 : Fin d → ℤ)} := Equiv.refl _
  calc
    Fintype.card (StoppingHalfGridOffset d) =
        Fintype.card {k // k ∈ gridNeighbours d (0 : Fin d → ℤ)} :=
      Fintype.card_congr e
    _ = (gridNeighbours d (0 : Fin d → ℤ)).card := Fintype.card_coe _
    _ = 7 ^ d := card_gridNeighbours d 0

/-- A repaired cube paired with one of its finite half-grid offsets. -/
def RefinedStoppingCell
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ) :=
  RepairedStoppingCube failure omega base × StoppingHalfGridOffset d

instance (failure : TriadicCube d → Set Omega) (omega : Omega) :
    Countable (RefinedStoppingCell failure omega base) := by
  dsimp only [RefinedStoppingCell]
  infer_instance

instance (failure : TriadicCube d → Set Omega) (omega : Omega) :
    DecidableEq (RefinedStoppingCell failure omega base) := by
  exact Classical.decEq _

instance (failure : TriadicCube d → Set Omega) (omega : Omega) :
    Encodable (RefinedStoppingCell failure omega base) := by
  exact Encodable.ofCountable _

/-- The selected triadic cube carrying the failure-event provenance. -/
def refinedStoppingFailureCube
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (q : RefinedStoppingCell failure omega base) : TriadicCube d :=
  q.1.1.1

/-- Scale of a refined cell. -/
def refinedStoppingScale
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (q : RefinedStoppingCell failure omega base) : ℤ :=
  q.1.1.1.scale

/-- Center of a refined cell on the relative half-grid of its selected cube. -/
def refinedStoppingCenter
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (q : RefinedStoppingCell failure omega base) : Vec d :=
  stoppingRelativeGridCentre q.1.1.1.scale (cubeCenter q.1.1.1) q.2.1

@[simp]
theorem refinedStoppingScale_eq_failureCube
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (q : RefinedStoppingCell failure omega base) :
    refinedStoppingScale q = (refinedStoppingFailureCube q).scale :=
  rfl

/-- A half-open triadic cube lies in its centered threefold enlargement. -/
theorem cubeSet_subset_centered_succ_translatedCube (Q : TriadicCube d) :
    cubeSet Q ⊆ translatedCube d (Q.scale + 1) (cubeCenter Q) := by
  intro x hx
  rw [translatedCube_eq_metricBall, Metric.mem_ball]
  have hdist : dist x (cubeCenter Q) ≤ cubeRadius Q :=
    Metric.mem_closedBall.mp (cubeSet_subset_closedBall Q hx)
  have hradius : cubeRadius Q < cubeRadius (originCube d (Q.scale + 1)) := by
    unfold cubeRadius cubeScaleFactor
    change 1 / 2 * (3 : ℝ) ^ Q.scale < 1 / 2 * (3 : ℝ) ^ (Q.scale + 1)
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    have hpow : 0 < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) Q.scale
    nlinarith
  exact hdist.trans_lt hradius

/-- The finite half-grid refinement covers all of space whenever the repaired
maximal cubes do. -/
theorem iUnion_refinedStoppingCell_eq_univ [NeZero d]
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1) :
    (⋃ q : RefinedStoppingCell failure omega base,
      translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q)) =
      (Set.univ : Set (Vec d)) := by
  apply Set.eq_univ_of_forall
  intro x
  have hcover := iUnion_cubeSet_repairedStoppingCube_eq_univ
    failure omega hinitial hrepair
  obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcover x)
  have hxEnlarged := cubeSet_subset_centered_succ_translatedCube Q.1.1 hxQ
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp
    (translatedCube_succ_subset_stoppingRelativeGridNeighbours
      d Q.1.1.scale (cubeCenter Q.1.1) hxEnlarged)
  let offset : StoppingHalfGridOffset d := ⟨k, hk⟩
  exact Set.mem_iUnion.mpr ⟨(Q, offset), hxk⟩

/-- Every refined cell carries the good-event conclusion of its selected
failure cube. -/
theorem not_mem_failure_refinedStoppingFailureCube
    (failure : TriadicCube d → Set Omega) {omega : Omega}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (q : RefinedStoppingCell failure omega base) :
    omega ∉ failure (refinedStoppingFailureCube q) :=
  not_mem_failure_of_stoppingRepairGenerated hfinite q.1.1.2

/-- Any property implied by non-failure transfers to every refined cell. -/
theorem refinedStoppingCell_property_of_not_mem_failure
    (failure : TriadicCube d → Set Omega) {omega : Omega}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (Good : TriadicCube d → Prop)
    (hgood : ∀ Q, omega ∉ failure Q → Good Q)
    (q : RefinedStoppingCell failure omega base) :
    Good (refinedStoppingFailureCube q) :=
  hgood _ (not_mem_failure_refinedStoppingFailureCube failure hfinite q)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
