import SubdiffusiveProcess.Lane4.Carriers
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension

open MeasureTheory TopologicalSpace Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section
namespace Paper

lemma aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_insert_isometry
    (n : ℕ) (i : Fin (n + 1)) (c : ℝ) :
    Isometry (fun y : SpatialCoordinates n =>
      @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y) := by
  intro x y
  simp only [edist_pi_def, Finset.sup_univ_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun b => ?_
    obtain rfl | h := eq_or_ne b i
    · simp
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
      simpa using (le_iSup (fun b : Fin n => edist (x b) (y b)) j)
  · refine iSup_le fun b => ?_
    exact le_iSup_of_le (i.succAbove b) (by simp)

lemma aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_map_restrict_insert
    (n : ℕ) (i : Fin (n + 1)) (c : ℝ) (U : Set (SpatialCoordinates n)) :
    Measure.map (fun y : SpatialCoordinates n =>
        @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y)
      (volume.restrict U) =
      (MeasureTheory.Measure.hausdorffMeasure (n : ℝ)).restrict
        ((fun y : SpatialCoordinates n =>
          @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y) '' U) := by
  let f : SpatialCoordinates n → SpatialCoordinates (n + 1) := fun y =>
    @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y
  have hf : Isometry f :=
    aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_insert_isometry n i c
  have hfm : Measurable f := hf.continuous.measurable
  have hH : MeasureTheory.Measure.hausdorffMeasure (n : ℝ) =
      (volume : Measure (SpatialCoordinates n)) := by
    simpa only [Fintype.card_fin] using
      (MeasureTheory.hausdorffMeasure_pi_real (ι := Fin n))
  refine Measure.ext fun s hs => ?_
  have hpre : MeasurableSet (f ⁻¹' s) := hs.preimage hfm
  rw [Measure.map_apply hfm hs, Measure.restrict_apply hpre, Measure.restrict_apply hs]
  have himage : f '' (f ⁻¹' s ∩ U) = s ∩ (f '' U) := by
    ext z
    constructor
    · rintro ⟨y, ⟨hy, hyU⟩, rfl⟩
      exact ⟨hy, ⟨y, hyU, rfl⟩⟩
    · rintro ⟨hz, y, hyU, rfl⟩
      exact ⟨y, ⟨hz, hyU⟩, rfl⟩
  calc
    volume (f ⁻¹' s ∩ U) =
        MeasureTheory.Measure.hausdorffMeasure (n : ℝ) (f ⁻¹' s ∩ U) := by
      rw [hH]
    _ = MeasureTheory.Measure.hausdorffMeasure (n : ℝ) (f '' (f ⁻¹' s ∩ U)) := by
      symm
      exact hf.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg n)) _
    _ = MeasureTheory.Measure.hausdorffMeasure (n : ℝ) (s ∩ (f '' U)) := by
      rw [himage]

lemma aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_null_isometric_image
    {m d p : ℕ} (hmd : m < d) (f : SpatialCoordinates m → SpatialCoordinates p)
    (hf : Isometry f) (U : Set (SpatialCoordinates m)) :
    MeasureTheory.Measure.hausdorffMeasure (d : ℝ) (f '' U) = 0 := by
  have hzero : MeasureTheory.Measure.hausdorffMeasure (d : ℝ) =
      (0 : Measure (SpatialCoordinates m)) := by
    apply Real.hausdorffMeasure_of_finrank_lt
    simpa [Module.finrank_fin_fun] using hmd
  rw [hf.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg d)) U, hzero]
  rfl

lemma aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_double_insert_isometry
    (m : ℕ) (i : Fin (m + 2)) (k : Fin (m + 1)) (c d : ℝ) :
    Isometry (fun z : SpatialCoordinates m =>
      @Fin.insertNth (m + 1) (fun _ : Fin (m + 2) => ℝ) i c
        (@Fin.insertNth m (fun _ : Fin (m + 1) => ℝ) k d z)) := by
  exact
    (aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_insert_isometry
      (m + 1) i c).comp
      (aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_insert_isometry
        m k d)

lemma aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_double_face_cover
    (m : ℕ) (i j : Fin (m + 2)) (k : Fin (m + 1))
    (hk : i.succAbove k = j) (c d : ℝ) :
    {x : SpatialCoordinates (m + 2) | x i = c ∧ x j = d} ⊆
      (fun z : SpatialCoordinates m =>
        @Fin.insertNth (m + 1) (fun _ : Fin (m + 2) => ℝ) i c
          (@Fin.insertNth m (fun _ : Fin (m + 1) => ℝ) k d z)) ''
        (Set.univ : Set (SpatialCoordinates m)) := by
  intro x hx
  let y : SpatialCoordinates (m + 1) := i.removeNth x
  have hy : y k = d := by
    dsimp [y]
    change x (i.succAbove k) = d
    rw [hk]
    exact hx.2
  have houter :
      @Fin.insertNth (m + 1) (fun _ : Fin (m + 2) => ℝ) i c y = x := by
    simpa [y, hx.1] using (Fin.insertNth_self_removeNth i x)
  have hinner :
      @Fin.insertNth m (fun _ : Fin (m + 1) => ℝ) k d (k.removeNth y) = y := by
    simpa [hy] using (Fin.insertNth_self_removeNth k y)
  refine ⟨k.removeNth y, Set.mem_univ _, ?_⟩
  dsimp
  rw [hinner, houter]

lemma aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_closed_face_image
    (m : ℕ) (i : Fin (m + 1)) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (fun y : SpatialCoordinates m =>
        @Fin.insertNth m (fun _ : Fin (m + 1) => ℝ) i c y) ''
      (Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) 1)) =
      {x : SpatialCoordinates (m + 1) | x i = c} ∩
        Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨by simp, ?_⟩
    rw [Set.mem_pi]
    simp only [Set.mem_univ, true_implies]
    refine i.forall_iff_succAbove.2 ⟨?_, ?_⟩
    · simpa using hc
    intro k
    simpa using (Set.mem_pi.mp hy) k (Set.mem_univ k)
  · rintro ⟨hxi, hx⟩
    let y : SpatialCoordinates m := i.removeNth x
    have hy : y ∈ Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) 1) := by
      rw [Set.mem_pi]
      intro k hk
      exact (Set.mem_pi.mp hx) (i.succAbove k) (Set.mem_univ _)
    refine ⟨y, hy, ?_⟩
    change @Fin.insertNth m (fun _ : Fin (m + 1) => ℝ) i c (i.removeNth x) = x
    rw [← hxi]
    exact Fin.insertNth_self_removeNth i x

lemma aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_unit_cube_eq_pi_Ioo
    (d : ℕ) :
    (unitNeumannCube d : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (0 : ℝ) 1) := by
  unfold unitNeumannCube
  rw [centeredCube_eq_pi]
  · congr 1
    funext i
    norm_num

lemma aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_unit_cube_frontier_faces
    (m : ℕ) :
    frontier (unitNeumannCube (m + 2) : Set (SpatialCoordinates (m + 2))) =
      ⋃ i : Fin (m + 2),
        ((fun y : SpatialCoordinates (m + 1) =>
            @Fin.insertNth (m + 1) (fun _ : Fin (m + 2) => ℝ) i (1 : ℝ) y) ''
            Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1) ∪
          (fun y : SpatialCoordinates (m + 1) =>
            @Fin.insertNth (m + 1) (fun _ : Fin (m + 2) => ℝ) i (0 : ℝ) y) ''
            Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1)) := by
  have hQ : (unitNeumannCube (m + 2) : Set (SpatialCoordinates (m + 2))) =
      Set.pi Set.univ (fun _ : Fin (m + 2) => Set.Ioo (0 : ℝ) 1) :=
    aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_unit_cube_eq_pi_Ioo _
  have hcl : closure (unitNeumannCube (m + 2) : Set (SpatialCoordinates (m + 2))) =
      Set.pi Set.univ (fun _ : Fin (m + 2) => Set.Icc (0 : ℝ) 1) := by
    rw [hQ, closure_pi_set]
    congr 1
    funext i
    rw [closure_Ioo]
    norm_num
  have hcoord : frontier (unitNeumannCube (m + 2) : Set (SpatialCoordinates (m + 2))) =
      ⋃ i : Fin (m + 2),
        (({x : SpatialCoordinates (m + 2) | x i = (1 : ℝ)} ∩
            Set.pi Set.univ (fun _ : Fin (m + 2) => Set.Icc (0 : ℝ) 1)) ∪
          ({x : SpatialCoordinates (m + 2) | x i = (0 : ℝ)} ∩
            Set.pi Set.univ (fun _ : Fin (m + 2) => Set.Icc (0 : ℝ) 1))) := by
    rw [frontier, hcl, (unitNeumannCube (m + 2)).isOpen.interior_eq, hQ]
    ext x
    simp only [mem_diff, mem_pi, mem_univ, true_implies, mem_iUnion, mem_union,
      mem_inter_iff, mem_setOf_eq, mem_Icc, mem_Ioo]
    constructor
    · rintro ⟨hx, hnot⟩
      by_cases hi : ∀ i : Fin (m + 2), 0 < x i ∧ x i < 1
      · exact False.elim (hnot hi)
      · push_neg at hi
        obtain ⟨i, hi⟩ := hi
        by_cases hlow : 0 < x i
        · have heq : x i = 1 := le_antisymm (hx i).2 (hi hlow)
          exact ⟨i, Or.inl ⟨heq, hx⟩⟩
        · have heq : x i = 0 := le_antisymm (le_of_not_gt hlow) (hx i).1
          exact ⟨i, Or.inr ⟨heq, hx⟩⟩
    · rintro ⟨i, hi⟩
      rcases hi with ⟨hxi, hx⟩ | ⟨hxi, hx⟩
      · refine ⟨hx, ?_⟩
        intro hinterior
        linarith [hxi, (hinterior i).2]
      · refine ⟨hx, ?_⟩
        intro hinterior
        linarith [hxi, (hinterior i).1]
  rw [hcoord]
  congr 1
  funext i
  rw [aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_closed_face_image
        (m + 1) i 1 (by norm_num),
    aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_closed_face_image
        (m + 1) i 0 (by norm_num)]

lemma aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_coordinate_faces_aedisjoint
    (m : ℕ) (i j : Fin (m + 2)) (hij : i ≠ j) (c d : ℝ)
    (F G : Set (SpatialCoordinates (m + 2)))
    (hF : ∀ x ∈ F, x i = c) (hG : ∀ x ∈ G, x j = d) :
    MeasureTheory.AEDisjoint
      (MeasureTheory.Measure.hausdorffMeasure (m + 1 : ℝ)) F G := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  let g : SpatialCoordinates m → SpatialCoordinates (m + 2) := fun z =>
    @Fin.insertNth (m + 1) (fun _ : Fin (m + 2) => ℝ) i c
      (@Fin.insertNth m (fun _ : Fin (m + 1) => ℝ) k d z)
  have hg : Isometry g := by
    exact aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_double_insert_isometry
      m i k c d
  have hsubset : F ∩ G ⊆ g '' (Set.univ : Set (SpatialCoordinates m)) := by
    intro x hx
    simpa [g] using
      (aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_double_face_cover
        m i j k hk c d ⟨hF x hx.1, hG x hx.2⟩)
  change (MeasureTheory.Measure.hausdorffMeasure (m + 1 : ℝ)) (F ∩ G) = 0
  apply MeasureTheory.measure_mono_null hsubset
  convert (aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_null_isometric_image
      (Nat.lt_succ_self m) g hg Set.univ) using 1 <;> norm_num

lemma aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_closed_open_cube_ae_eq
    (m : ℕ) :
    (Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1)) =ᵐ[volume]
      Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Ioo (0 : ℝ) 1) := by
  apply MeasureTheory.ae_eq_set.2
  constructor
  · have hzero (i : Fin (m + 1)) (c : ℝ) :
        volume {x : SpatialCoordinates (m + 1) | x i = c} = 0 := by
      rw [MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_hyperplane
        (fun _ : Fin (m + 1) => (volume : Measure ℝ)) i c
    have hsubset :
        (Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1)) \
          (Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Ioo (0 : ℝ) 1)) ⊆
        ⋃ i : Fin (m + 1),
          ({x : SpatialCoordinates (m + 1) | x i = (0 : ℝ)} ∪
            {x : SpatialCoordinates (m + 1) | x i = (1 : ℝ)}) := by
      intro x hx
      have hxC : ∀ i : Fin (m + 1), 0 ≤ x i ∧ x i ≤ 1 := by
        intro i
        exact (Set.mem_pi.mp hx.1) i (Set.mem_univ i)
      have hxnot : ¬ ∀ i : Fin (m + 1), 0 < x i ∧ x i < 1 := by
        intro h
        exact hx.2 (Set.mem_pi.2 fun i _ => h i)
      push_neg at hxnot
      obtain ⟨i, hi⟩ := hxnot
      by_cases hlow : 0 < x i
      · have heq : x i = 1 := le_antisymm (hxC i).2 (hi hlow)
        exact Set.mem_iUnion.2 ⟨i, Or.inr heq⟩
      · have heq : x i = 0 := le_antisymm (le_of_not_gt hlow) (hxC i).1
        exact Set.mem_iUnion.2 ⟨i, Or.inl heq⟩
    apply MeasureTheory.measure_mono_null hsubset
    apply MeasureTheory.measure_iUnion_null
    intro i
    exact MeasureTheory.measure_union_null (hzero i 0) (hzero i 1)
  · apply MeasureTheory.measure_mono_null
    · intro x hx
      exfalso
      apply hx.2
      exact Set.mem_pi.2 fun i _ =>
        ⟨le_of_lt ((Set.mem_pi.mp hx.1) i (Set.mem_univ i) |>.1),
          le_of_lt ((Set.mem_pi.mp hx.1) i (Set.mem_univ i) |>.2)⟩
    · exact MeasureTheory.measure_empty

/-- Statement-only fine child: exact decomposition of the concrete Hausdorff
frontier measure into the inserted coordinate-face measures. The codimension-two
edge nullity is part of this conclusion. -/
theorem lane4_neumann_boundary_identity_frontier_hn_decomposition
    (n : ℕ) (hn : 1 ≤ n) :
    let Q : Opens (SpatialCoordinates (n + 1)) := unitNeumannCube (n + 1)
    let Qface : Opens (SpatialCoordinates n) := unitNeumannCube n
    let μface : Measure (SpatialCoordinates n) :=
      volume.restrict (Qface : Set (SpatialCoordinates n))
    let muBoundary : Measure (SpatialCoordinates (n + 1)) :=
      (MeasureTheory.Measure.hausdorffMeasure (n : ℝ)).restrict
        (frontier (Q : Set (SpatialCoordinates (n + 1))))
    muBoundary =
      ∑ i : Fin (n + 1),
        (Measure.map (fun y : SpatialCoordinates n =>
            @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (1 : ℝ) y) μface +
          Measure.map (fun y : SpatialCoordinates n =>
            @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (0 : ℝ) y) μface) := by
  cases n with
  | zero => omega
  | succ m =>
    dsimp
    let H : Measure (SpatialCoordinates (m + 2)) :=
      MeasureTheory.Measure.hausdorffMeasure (m + 1 : ℝ)
    let C : Set (SpatialCoordinates (m + 1)) :=
      Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1)
    let U : Set (SpatialCoordinates (m + 1)) :=
      Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Ioo (0 : ℝ) 1)
    let f : Fin (m + 2) → ℝ → SpatialCoordinates (m + 1) → SpatialCoordinates (m + 2) :=
      fun i c y => @Fin.insertNth (m + 1) (fun _ : Fin (m + 2) => ℝ) i c y
    let F : Fin (m + 2) → ℝ → Set (SpatialCoordinates (m + 2)) :=
      fun i c => f i c '' C
    have hfront :
        frontier (unitNeumannCube (m + 2) : Set (SpatialCoordinates (m + 2))) =
          ⋃ i : Fin (m + 2), F i 1 ∪ F i 0 := by
      simpa [F, f, C] using
        (aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_unit_cube_frontier_faces m)
    have hunit :
        (unitNeumannCube (m + 1) : Set (SpatialCoordinates (m + 1))) = U := by
      simpa [U, aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_unit_cube_eq_pi_Ioo]
    have hH : H = MeasureTheory.Measure.hausdorffMeasure (m + 1 : ℝ) := rfl
    have hFcoord (i : Fin (m + 2)) (c : ℝ) (x : SpatialCoordinates (m + 2))
        (hx : x ∈ F i c) : x i = c := by
      rcases hx with ⟨y, hy, rfl⟩
      simp [F, f]
    have hFmeas (i : Fin (m + 2)) (c : ℝ)
        (hc : c ∈ Set.Icc (0 : ℝ) 1) : MeasurableSet (F i c) := by
      have hface :=
        aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_closed_face_image
          (m + 1) i c hc
      have hclosed : IsClosed
          (Set.pi Set.univ (fun _ : Fin (m + 2) => Set.Icc (0 : ℝ) 1)) :=
        isClosed_set_pi (fun _ _ => isClosed_Icc)
      have hcoordclosed : IsClosed {x : SpatialCoordinates (m + 2) | x i = c} :=
        isClosed_singleton.preimage (continuous_apply i)
      rw [show F i c =
          {x : SpatialCoordinates (m + 2) | x i = c} ∩
            Set.pi Set.univ (fun _ : Fin (m + 2) => Set.Icc (0 : ℝ) 1) by
        simpa [F, f, C] using hface]
      exact (hcoordclosed.inter hclosed).measurableSet
    have hnull (i j : Fin (m + 2)) (hij : i ≠ j) (c d : ℝ)
        (hc : c ∈ Set.Icc (0 : ℝ) 1) (hd : d ∈ Set.Icc (0 : ℝ) 1) :
        H (F i c ∩ F j d) = 0 := by
      have h :=
        aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_coordinate_faces_aedisjoint
          m i j hij c d (F i c) (F j d)
          (hFcoord i c) (hFcoord j d)
      convert h using 1 <;> norm_num
    have hsame (i : Fin (m + 2)) : Disjoint (F i 1) (F i 0) := by
      refine Set.disjoint_left.2 ?_
      intro x hx1 hx0
      have h1 := hFcoord i 1 x hx1
      have h0 := hFcoord i 0 x hx0
      linarith
    have hAed : Pairwise (fun i j : Fin (m + 2) =>
        MeasureTheory.AEDisjoint H (F i 1 ∪ F i 0) (F j 1 ∪ F j 0)) := by
      intro i j hij
      have hcover : (F i 1 ∪ F i 0) ∩ (F j 1 ∪ F j 0) ⊆
          (((F i 1 ∩ F j 1) ∪ (F i 1 ∩ F j 0)) ∪
            (F i 0 ∩ F j 1)) ∪ (F i 0 ∩ F j 0) := by
        intro x hx
        simp only [mem_union, mem_inter_iff] at hx ⊢
        aesop
      change H ((F i 1 ∪ F i 0) ∩ (F j 1 ∪ F j 0)) = 0
      apply MeasureTheory.measure_mono_null hcover
      apply MeasureTheory.measure_union_null
      · apply MeasureTheory.measure_union_null
        · apply MeasureTheory.measure_union_null
          · exact hnull i j hij 1 1 (by norm_num) (by norm_num)
          · exact hnull i j hij 1 0 (by norm_num) (by norm_num)
        · exact hnull i j hij 0 1 (by norm_num) (by norm_num)
      · exact hnull i j hij 0 0 (by norm_num) (by norm_num)
    have hAmeas (i : Fin (m + 2)) :
        NullMeasurableSet (F i 1 ∪ F i 0) H :=
      ((hFmeas i 1 (by norm_num)).union (hFmeas i 0 (by norm_num))).nullMeasurableSet
    have hclosed :
        H.restrict (frontier (unitNeumannCube (m + 2) : Set (SpatialCoordinates (m + 2)))) =
          ∑ i : Fin (m + 2), (H.restrict (F i 1) + H.restrict (F i 0)) := by
      apply Measure.ext
      intro s hs
      calc
        (H.restrict (frontier (unitNeumannCube (m + 2) :
            Set (SpatialCoordinates (m + 2)))) ) s =
            (H.restrict (⋃ i : Fin (m + 2), F i 1 ∪ F i 0)) s := by rw [hfront]
        _ = ∑' i : Fin (m + 2), (H.restrict (F i 1 ∪ F i 0)) s :=
          MeasureTheory.Measure.restrict_iUnion_apply_ae hAed hAmeas hs
        _ = (∑ i : Fin (m + 2), (H.restrict (F i 1) + H.restrict (F i 0))) s := by
          rw [tsum_fintype]
          rw [Measure.finset_sum_apply]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Measure.restrict_union (hsame i) (hFmeas i 0 (by norm_num))]
    have hCU : volume.restrict C = volume.restrict U := by
      apply Measure.restrict_congr_set
      simpa [C, U] using
        (aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_closed_open_cube_ae_eq m)
    have hmapC (i : Fin (m + 2)) (c : ℝ) :
        Measure.map (f i c) (volume.restrict C) = H.restrict (F i c) := by
      simpa [H, F, f] using
        (aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_map_restrict_insert
          (m + 1) i c C)
    have hmapU (i : Fin (m + 2)) (c : ℝ) :
        Measure.map (f i c) (volume.restrict U) =
          H.restrict (f i c '' U) := by
      simpa [H, f] using
        (aux_lane4_neumann_boundary_identity_frontier_hn_decomposition_map_restrict_insert
          (m + 1) i c U)
    have hrestrict_face (i : Fin (m + 2)) (c : ℝ) :
        H.restrict (F i c) = H.restrict (f i c '' U) := by
      calc
        H.restrict (F i c) = Measure.map (f i c) (volume.restrict C) := (hmapC i c).symm
        _ = Measure.map (f i c) (volume.restrict U) := by rw [hCU]
        _ = H.restrict (f i c '' U) := hmapU i c
    have hopen :
        H.restrict (frontier (unitNeumannCube (m + 2) : Set (SpatialCoordinates (m + 2)))) =
          ∑ i : Fin (m + 2),
            (Measure.map (f i 1) (volume.restrict U) +
              Measure.map (f i 0) (volume.restrict U)) := by
      calc
        H.restrict (frontier (unitNeumannCube (m + 2) : Set (SpatialCoordinates (m + 2)))) =
            ∑ i : Fin (m + 2), (H.restrict (F i 1) + H.restrict (F i 0)) := hclosed
        _ = ∑ i : Fin (m + 2),
            (Measure.map (f i 1) (volume.restrict U) +
              Measure.map (f i 0) (volume.restrict U)) := by
          congr 1
          funext i
          rw [hrestrict_face i 1, hrestrict_face i 0]
          rw [← hmapU i 1, ← hmapU i 0]
    simpa [H, f, hunit] using hopen

end Paper

