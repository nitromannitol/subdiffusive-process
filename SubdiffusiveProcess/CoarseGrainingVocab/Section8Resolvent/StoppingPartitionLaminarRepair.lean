module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionMaximalLaminar

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- Two cubes are geometrically near when their centers are within ten larger
side lengths.  The fixed factor safely contains the half-grid refinements used
below and is dimension-independent for the `Vec d` sup metric. -/
def StoppingCubesNear (Q R : TriadicCube d) : Prop :=
  dist (cubeCenter Q) (cubeCenter R) ≤
    10 * max (cubeScaleFactor Q) (cubeScaleFactor R)

theorem stoppingCubesNear_comm (Q R : TriadicCube d) :
    StoppingCubesNear Q R ↔ StoppingCubesNear R Q := by
  rw [StoppingCubesNear, StoppingCubesNear, dist_comm, max_comm]

/-- Inductive parent closure of the maximal initial laminar family. -/
inductive StoppingRepairGenerated
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ) :
    TriadicCube d → Prop
  | initial (Q : MaximalInitialStoppingCube failure omega base) :
      StoppingRepairGenerated failure omega base Q.1.1
  | parent {Q R : TriadicCube d}
      (hQ : StoppingRepairGenerated failure omega base Q)
      (hR : StoppingRepairGenerated failure omega base R)
      (hnear : StoppingCubesNear Q R) (hscale : Q.scale + 2 < R.scale) :
      StoppingRepairGenerated failure omega base (parentCube Q)

/-- Carrier of all cubes generated during parent replacement. -/
def StoppingRepairCube
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ) :=
  {Q : TriadicCube d // StoppingRepairGenerated failure omega base Q}

instance (failure : TriadicCube d → Set Omega) (omega : Omega) :
    Countable (StoppingRepairCube failure omega base) := by
  dsimp only [StoppingRepairCube]
  infer_instance



def IsMaximalStoppingRepairCube
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ)
    (Q : StoppingRepairCube failure omega base) : Prop :=
  ∀ R : StoppingRepairCube failure omega base,
    cubeSet Q.1 ⊆ cubeSet R.1 → cubeSet R.1 ⊆ cubeSet Q.1

/-- The repaired stopping-cell carrier. -/
def RepairedStoppingCube
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ) :=
  {Q : StoppingRepairCube failure omega base //
    IsMaximalStoppingRepairCube failure omega base Q}

instance (failure : TriadicCube d → Set Omega) (omega : Omega) :
    Countable (RepairedStoppingCube failure omega base) := by
  dsimp only [RepairedStoppingCube]
  infer_instance



theorem StoppingRepairGenerated.exists_candidate_ancestor
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    {Q : TriadicCube d}
    (hQ : StoppingRepairGenerated failure omega base Q) :
    ∃ (P : StoppingBaseCube d base) (k : ℕ),
      Q = ancestorCube k (triadicStoppingCandidate failure omega P) := by
  induction hQ with
  | initial S =>
      obtain ⟨P, hP⟩ := S.1.2
      exact ⟨P, 0, by simpa only [ancestorCube_zero] using hP.symm⟩
  | parent hQ _ _ _ ihQ _ =>
      obtain ⟨P, k, hk⟩ := ihQ
      refine ⟨P, k + 1, ?_⟩
      rw [ancestorCube_succ, ← hk]

/-- Parent replacement never lowers the base scale. -/
theorem base_le_scale_of_stoppingRepairGenerated
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    {Q : TriadicCube d}
    (hQ : StoppingRepairGenerated failure omega base Q) :
    base ≤ Q.scale := by
  obtain ⟨P, k, rfl⟩ := hQ.exists_candidate_ancestor
  rw [ancestorCube_scale]
  exact (base_le_triadicStoppingCandidate_scale failure omega P).trans
    (le_add_of_nonneg_right (Int.natCast_nonneg k))



theorem not_mem_failure_of_stoppingRepairGenerated
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    {Q : TriadicCube d}
    (hQ : StoppingRepairGenerated failure omega base Q) :
    omega ∉ failure Q := by
  obtain ⟨P, k, rfl⟩ := hQ.exists_candidate_ancestor
  exact not_mem_failure_ancestor_triadicStoppingCandidate failure (hfinite P) k



theorem exists_repairedStoppingCube_mem [NeZero d]
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hlocal : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    {x : Vec d}
    (hx : ∃ Q : StoppingRepairCube failure omega base, x ∈ cubeSet Q.1) :
    ∃ Q : RepairedStoppingCube failure omega base, x ∈ cubeSet Q.1.1 := by
  let through : Set (StoppingRepairCube failure omega base) :=
    {Q | x ∈ cubeSet Q.1}
  have hfinite : through.Finite := hlocal.point_finite x
  have hnonempty : through.Nonempty := hx
  obtain ⟨Q, hQ, hmax⟩ :=
    through.exists_max_image (fun R ↦ R.1.scale) hfinite hnonempty
  have hQmax : IsMaximalStoppingRepairCube failure omega base Q := by
    intro R hQR
    have hxR : x ∈ cubeSet R.1 := hQR hQ
    have hscale : R.1.scale ≤ Q.1.scale := hmax R hxR
    exact cubeSet_subset_of_le_of_mem_of_mem hscale hxR hQ
  exact ⟨⟨Q, hQmax⟩, hQ⟩



theorem iUnion_cubeSet_repairedStoppingCube_eq_univ [NeZero d]
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1) :
    (⋃ Q : RepairedStoppingCube failure omega base, cubeSet Q.1.1) =
      (Set.univ : Set (Vec d)) := by
  apply Set.eq_univ_of_forall
  intro x
  have hcover := iUnion_cubeSet_maximalInitialStoppingCube_eq_univ
    failure omega hinitial
  obtain ⟨Q, hQ⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcover x)
  obtain ⟨R, hR⟩ := exists_repairedStoppingCube_mem failure omega hrepair
    ⟨⟨Q.1.1, StoppingRepairGenerated.initial Q⟩, hQ⟩
  exact Set.mem_iUnion.mpr ⟨R, hR⟩



theorem locallyFinite_repairedStoppingCube
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1) :
    LocallyFinite fun Q : RepairedStoppingCube failure omega base ↦
      cubeSet Q.1.1 :=
  hrepair.comp_injective Subtype.val_injective

/-- Distinct repaired maximal cubes are disjoint. -/
theorem pairwiseDisjoint_repairedStoppingCube [NeZero d]
    (failure : TriadicCube d → Set Omega) (omega : Omega) :
    (Set.univ : Set (RepairedStoppingCube failure omega base)).PairwiseDisjoint
      (fun Q ↦ cubeSet Q.1.1) := by
  intro Q _ R _ hQR
  rcases cubeSet_subset_or_disjoint Q.1.1 R.1.1 with hsub | hsub | hdisjoint
  · have hback := Q.2 R.1 hsub
    exact (hQR (Subtype.ext (Subtype.ext
      (eq_of_cubeSet_subset_subset hsub hback)))).elim
  · have hback := R.2 Q.1 hsub
    exact (hQR (Subtype.ext (Subtype.ext
      (eq_of_cubeSet_subset_subset hback hsub)))).elim
  · exact hdisjoint

/-- Parent closure forces nearby repaired cubes to differ by at most two
triadic scales. -/
theorem repairedStoppingCube_scale_le_add_two_of_near [NeZero d]
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    {Q R : RepairedStoppingCube failure omega base}
    (hnear : StoppingCubesNear Q.1.1 R.1.1) :
    Q.1.1.scale ≤ R.1.1.scale + 2 := by
  by_contra hnot
  have hgap : R.1.1.scale + 2 < Q.1.1.scale := by omega
  let P : StoppingRepairCube failure omega base :=
    ⟨parentCube R.1.1,
      StoppingRepairGenerated.parent R.1.2 Q.1.2
        ((stoppingCubesNear_comm Q.1.1 R.1.1).mp hnear) hgap⟩
  have hsub : cubeSet R.1.1 ⊆ cubeSet P.1 :=
    cubeSet_subset_cubeSet_parentCube R.1.1
  have hback : cubeSet P.1 ⊆ cubeSet R.1.1 := R.2 P hsub
  have heq : parentCube R.1.1 = R.1.1 :=
    eq_of_cubeSet_subset_subset hback hsub
  have hscale := congrArg TriadicCube.scale heq
  simp only [parentCube_scale] at hscale
  omega

/-- Symmetric scale comparability: nearby repaired cells differ by at most a
factor `9` in side length. -/
theorem abs_scale_sub_le_two_of_repairedStoppingCube_near [NeZero d]
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    {Q R : RepairedStoppingCube failure omega base}
    (hnear : StoppingCubesNear Q.1.1 R.1.1) :
    |Q.1.1.scale - R.1.1.scale| ≤ 2 := by
  have hQR := repairedStoppingCube_scale_le_add_two_of_near
    failure omega hnear
  have hRQ := repairedStoppingCube_scale_le_add_two_of_near
    failure omega ((stoppingCubesNear_comm Q.1.1 R.1.1).mp hnear)
  rw [abs_le]
  constructor <;> omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
