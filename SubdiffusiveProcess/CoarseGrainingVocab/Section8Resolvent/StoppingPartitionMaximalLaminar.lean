import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionTriadicFailureHeight
import Mathlib.Topology.Compactness.LocallyFinite




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- The range of the initial stopping-cube map, with duplicates removed. -/
def InitialStoppingCube (failure : TriadicCube d → Set Omega)
    (omega : Omega) (base : ℤ) :=
  Set.range (triadicStoppingCandidate (base := base) failure omega)

instance (failure : TriadicCube d → Set Omega) (omega : Omega) :
    Countable (InitialStoppingCube failure omega base) :=
  by infer_instance

/-- A cube in the initial range is maximal for set inclusion. -/
def IsMaximalInitialStoppingCube
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ)
    (Q : InitialStoppingCube failure omega base) : Prop :=
  ∀ R : InitialStoppingCube failure omega base,
    cubeSet Q.1 ⊆ cubeSet R.1 → cubeSet R.1 ⊆ cubeSet Q.1

/-- Carrier of the maximal laminar selection. -/
def MaximalInitialStoppingCube
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ) :=
  {Q : InitialStoppingCube failure omega base //
    IsMaximalInitialStoppingCube failure omega base Q}

instance (failure : TriadicCube d → Set Omega) (omega : Omega) :
    Countable (MaximalInitialStoppingCube failure omega base) :=
  by
    dsimp only [MaximalInitialStoppingCube]
    infer_instance

/-- Passing from base-cube indices to the duplicate-free candidate range
preserves local finiteness. -/
theorem locallyFinite_initialStoppingCube
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hlocal : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q)) :
    LocallyFinite fun Q : InitialStoppingCube failure omega base ↦ cubeSet Q.1 := by
  let toInitial : StoppingBaseCube d base →
      InitialStoppingCube failure omega base := fun Q ↦
    ⟨triadicStoppingCandidate failure omega Q, ⟨Q, rfl⟩⟩
  have hsurjective : Function.Surjective toInitial := by
    rintro ⟨R, ⟨Q, hQ⟩⟩
    subst R
    exact ⟨Q, rfl⟩
  apply LocallyFinite.of_comp_surjective hsurjective
  simpa only [Function.comp_apply, toInitial] using hlocal

/-- Mutual containment determines a positive-dimensional triadic cube. -/
theorem eq_of_cubeSet_subset_subset [NeZero d] {Q R : TriadicCube d}
    (hQR : cubeSet Q ⊆ cubeSet R) (hRQ : cubeSet R ⊆ cubeSet Q) :
    Q = R := by
  have hvolume : volume (cubeSet Q) = volume (cubeSet R) :=
    le_antisymm (measure_mono hQR) (measure_mono hRQ)
  have hcubes : cubeVolume Q = cubeVolume R := by
    rw [← volume_cubeSet_toReal, ← volume_cubeSet_toReal, hvolume]
  have hscale : Q.scale = R.scale := by
    rw [cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale] at hcubes
    rcases lt_trichotomy Q.scale R.scale with hlt | heq | hgt
    · have hbase : (3 : ℝ) ^ Q.scale < (3 : ℝ) ^ R.scale :=
        zpow_lt_zpow_right₀ (by norm_num) hlt
      have hpow := pow_lt_pow_left₀ hbase
        (le_of_lt (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
        (NeZero.ne d)
      exact (ne_of_lt hpow hcubes).elim
    · exact heq
    · have hbase : (3 : ℝ) ^ R.scale < (3 : ℝ) ^ Q.scale :=
        zpow_lt_zpow_right₀ (by norm_num) hgt
      have hpow := pow_lt_pow_left₀ hbase
        (le_of_lt (zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale))
        (NeZero.ne d)
      exact (ne_of_lt hpow hcubes.symm).elim
  exact eq_of_scale_eq_of_mem_of_mem hscale
    (cubeCenter_mem_cubeSet Q) (hQR (cubeCenter_mem_cubeSet Q))

/-- A locally finite initial family has a maximal member through every point
which lies in one of its cubes. -/
theorem exists_maximalInitialStoppingCube_mem [NeZero d]
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hlocal : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    {x : Vec d}
    (hx : ∃ Q : InitialStoppingCube failure omega base, x ∈ cubeSet Q.1) :
    ∃ Q : MaximalInitialStoppingCube failure omega base, x ∈ cubeSet Q.1 := by
  let initialLocal := locallyFinite_initialStoppingCube failure omega hlocal
  let through : Set (InitialStoppingCube failure omega base) :=
    {Q | x ∈ cubeSet Q.1}
  have hfinite : through.Finite := initialLocal.point_finite x
  have hnonempty : through.Nonempty := hx
  obtain ⟨Q, hQ, hmax⟩ :=
    through.exists_max_image (fun R ↦ R.1.scale) hfinite hnonempty
  have hQmax : IsMaximalInitialStoppingCube failure omega base Q := by
    intro R hQR
    have hxR : x ∈ cubeSet R.1 := hQR hQ
    have hscale : R.1.scale ≤ Q.1.scale := hmax R hxR
    exact cubeSet_subset_of_le_of_mem_of_mem hscale hxR hQ
  exact ⟨⟨Q, hQmax⟩, hQ⟩

/-- The maximal initial cubes cover all of space. -/
theorem iUnion_cubeSet_maximalInitialStoppingCube_eq_univ [NeZero d]
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hlocal : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q)) :
    (⋃ Q : MaximalInitialStoppingCube failure omega base, cubeSet Q.1.1) =
      (Set.univ : Set (Vec d)) := by
  apply Set.eq_univ_of_forall
  intro x
  let Q0 : StoppingBaseCube d base := ⟨cubeAt base x, cubeAt_scale base x⟩
  have hbase : x ∈ cubeSet Q0.1 := mem_cubeSet_cubeAt base x
  have hcandidate : x ∈ cubeSet (triadicStoppingCandidate failure omega Q0) :=
    cubeSet_subset_triadicStoppingCandidate failure omega Q0 hbase
  obtain ⟨Q, hQ⟩ := exists_maximalInitialStoppingCube_mem failure omega hlocal
    ⟨⟨triadicStoppingCandidate failure omega Q0, ⟨Q0, rfl⟩⟩, hcandidate⟩
  exact Set.mem_iUnion.mpr ⟨Q, hQ⟩

/-- The selected maximal family remains locally finite. -/
theorem locallyFinite_maximalInitialStoppingCube
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hlocal : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q)) :
    LocallyFinite fun Q : MaximalInitialStoppingCube failure omega base ↦
      cubeSet Q.1.1 := by
  have hinitial := locallyFinite_initialStoppingCube failure omega hlocal
  exact hinitial.comp_injective Subtype.val_injective

/-- Distinct cubes in the maximal selection are disjoint. -/
theorem pairwiseDisjoint_maximalInitialStoppingCube [NeZero d]
    (failure : TriadicCube d → Set Omega) (omega : Omega) :
    (Set.univ : Set (MaximalInitialStoppingCube failure omega base)).PairwiseDisjoint
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

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
