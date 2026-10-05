module

public import MarkovProcess.Parameterized.ContinuousProcessProperties
public import MarkovProcess.Trajectory.FellerFiniteMarginals
public import SubdiffusiveProcess.Main.DiffusionPath
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalAttachment
theorem pa_prefix_bound
    (I : Finset DenseTime) :
    ∃ n, SubMarkovKernelSemigroup.denseTimePhysicalSet I ⊆
      SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro t ht
      simp only [SubMarkovKernelSemigroup.denseTimePhysicalSet,
        Finset.map_empty, Finset.notMem_empty] at ht
  | @insert a I ha ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨max n (DenseTime.enumeration.symm a + 1), ?_⟩
      intro t ht
      rw [SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at ht
      obtain ⟨r, hr, rfl⟩ := ht
      rw [SubMarkovKernelSemigroup.denseTimePhysicalPrefix, Finset.mem_map]
      refine ⟨r, ?_, rfl⟩
      rw [CountableEnumeration.mem_prefix_iff]
      rw [Finset.mem_insert] at hr
      rcases hr with rfl | hr
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
      · have hmem : DenseTime.castOrderEmbedding r ∈
            SubMarkovKernelSemigroup.denseTimePhysicalSet I := by
          rw [SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
          exact ⟨r, hr, rfl⟩
        have hprefix := hn hmem
        rw [SubMarkovKernelSemigroup.denseTimePhysicalPrefix, Finset.mem_map] at hprefix
        obtain ⟨r', hr', heq⟩ := hprefix
        have hrr' : r = r' := DenseTime.castOrderEmbedding.injective heq.symm
        subst r'
        rw [CountableEnumeration.mem_prefix_iff] at hr'
        exact Nat.lt_of_lt_of_le hr' (le_max_left _ _)

theorem pa_finiteDense
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (default : DiffusionPath d)
    (hsupport : Kernel.IsSupportedOnContinuousPaths
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory P hP
        DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding))
    (I : Finset DenseTime) :
    (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
        (fun path (t : SubMarkovKernelSemigroup.denseTimePhysicalSet I) ↦ path t) =
      SubMarkovKernelSemigroup.finiteSetKernel P
        (SubMarkovKernelSemigroup.denseTimePhysicalSet I) := by
  classical
  obtain ⟨n, hsubset⟩ :=
    pa_prefix_bound I
  let equiv : Fin n ≃
      SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n :=
    Equiv.ofBijective
      (fun i ↦ ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration i), by
        rw [SubMarkovKernelSemigroup.denseTimePhysicalPrefix, Finset.mem_map]
        exact ⟨DenseTime.enumeration i, by
          rw [CountableEnumeration.mem_prefix_iff, DenseTime.enumeration.symm_apply_apply]
          exact i.isLt, rfl⟩⟩)
      ⟨by
        intro i j hij
        apply Fin.ext
        apply DenseTime.enumeration.injective
        apply DenseTime.castOrderEmbedding.injective
        exact congrArg Subtype.val hij,
       by
        intro t
        have ht := t.property
        change t.val ∈ (CountableEnumeration.prefix DenseTime.enumeration n).map
          DenseTime.castOrderEmbedding.toEmbedding at ht
        rw [Finset.mem_map] at ht
        obtain ⟨r, hr, hrt⟩ := ht
        let i : Fin n := ⟨DenseTime.enumeration.symm r, by
          rw [CountableEnumeration.mem_prefix_iff] at hr
          exact hr⟩
        refine ⟨i, Subtype.ext ?_⟩
        change DenseTime.castOrderEmbedding (DenseTime.enumeration i) = t
        rw [show DenseTime.enumeration i = r by
          exact DenseTime.enumeration.apply_symm_apply r]
        exact hrt⟩
  let prefixPath : (Fin n → SpatialCoordinates d) →
      SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n → SpatialCoordinates d :=
    fun path t ↦ path (equiv.symm t)
  have hleft :
      prefixPath ∘
          (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix DenseTime.enumeration n ∘
            ContinuousPath.denseRestriction) =
        (fun path (t : SubMarkovKernelSemigroup.denseTimePhysicalPrefix
          DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding n) ↦ path t) := by
    funext path t
    change path (DenseTime.castOrderEmbedding
      (DenseTime.enumeration (equiv.symm t))) = path t
    exact congrArg path (congrArg Subtype.val (equiv.apply_symm_apply t))
  have hright :
      prefixPath ∘ SubMarkovKernelSemigroup.denseTimePrefixReindex DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n = id := by
    funext path t
    change path (equiv (equiv.symm t)) = path t
    rw [equiv.apply_symm_apply]
  have hprefixPath_meas : Measurable prefixPath :=
    measurable_pi_iff.mpr fun t =>
      measurable_pi_apply (X := fun _ => SpatialCoordinates d) (equiv.symm t)
  have hrestrictPrefix_meas : Measurable
      (Finset.restrict₂ (π := fun _ ↦ SpatialCoordinates d) hsubset ∘ prefixPath) :=
    (Finset.measurable_restrict₂ (X := fun _ ↦ SpatialCoordinates d) hsubset).comp
      hprefixPath_meas
  have htraj_meas : Measurable
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix
          DenseTime.enumeration n ∘ ContinuousPath.denseRestriction) :=
    (SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix
      (α := SpatialCoordinates d) DenseTime.enumeration n).comp
      ContinuousPath.measurable_denseRestriction
  have hreindex_meas : Measurable
      (SubMarkovKernelSemigroup.denseTimePrefixReindex DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n) :=
    SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex
      (α := SpatialCoordinates d) DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n
  let kappa := SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory P hP
    DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding
  have hback :
      (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
          ContinuousPath.denseRestriction = kappa := by
    exact Kernel.IsSupportedOnContinuousPaths.map_denseRestriction kappa hsupport default
  have hpref :
      (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
          (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix DenseTime.enumeration n ∘
            ContinuousPath.denseRestriction) =
        SubMarkovKernelSemigroup.denseTimePrefixKernel P DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n := by
    rw [Kernel.map_comp_right]
    · rw [hback]
      exact SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_prefix P hP
        DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding n
    · exact ContinuousPath.measurable_denseRestriction
    · exact SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix
        (α := SpatialCoordinates d) DenseTime.enumeration n
  have hfun :
      (fun path : DiffusionPath d ↦
        fun t : SubMarkovKernelSemigroup.denseTimePhysicalSet I ↦ path t) =
      Finset.restrict₂ (π := fun _ ↦ SpatialCoordinates d) hsubset ∘
        (fun path : DiffusionPath d ↦
          fun t : SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding n ↦ path t) := by
    rfl
  have hphysical :
      (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
          (fun path (t : SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding n) ↦ path t) =
        SubMarkovKernelSemigroup.finiteSetKernel P
          (SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding n) := by
    rw [← hleft, Kernel.map_comp_right]
    · rw [hpref, SubMarkovKernelSemigroup.denseTimePrefixKernel_eq_map,
        ← Kernel.map_comp_right]
      · rw [hright, Kernel.map_id]
      · exact SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex
          (α := SpatialCoordinates d) DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n
      · exact hprefixPath_meas
    · exact htraj_meas
    · exact hprefixPath_meas
  rw [hfun, Kernel.map_comp_right]
  · rw [hphysical]
    exact (hP.finiteSetKernel_map_restrict₂ P hsubset).symm
  · apply measurable_pi_iff.mpr
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) (t : NNReal)
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ SpatialCoordinates d) hsubset

theorem pa_fdd
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup)
    (default : DiffusionPath d)
    (hsupport : Kernel.IsSupportedOnContinuousPaths
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory P hP
        DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding))
    (I : Finset NNReal) :
    (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
        (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel P I := by
  classical
  obtain ⟨q, hq⟩ := exists_denseTime_finset_seq_tendsto I
  let K := SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default
  have hmarkovK : IsMarkovKernel K := by infer_instance
  have hmarkovFinite : IsMarkovKernel (SubMarkovKernelSemigroup.finiteSetKernel P I) :=
    hP.isMarkovKernel_finiteSetKernel P I
  apply Kernel.map_finiteEvaluation_eq_of_integral_tendsto
    K hmarkovK
      (fun k ↦ SubMarkovKernelSemigroup.finiteDenseApproximationKernel P (q k))
      (SubMarkovKernelSemigroup.finiteSetKernel P I) hmarkovFinite
      (fun t : I ↦ (t : NNReal))
      (fun k t ↦ DenseTime.castOrderEmbedding (q k t)) hq
  · intro k
    let evalPhysical : DiffusionPath d →
        SubMarkovKernelSemigroup.finiteDenseApproximationPhysicalSet (q k) →
          SpatialCoordinates d := fun path t ↦ path t
    have hevalPhysical : Measurable evalPhysical := by
      rw [measurable_pi_iff]
      intro t
      exact ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) t
    have hcomp :
        SubMarkovKernelSemigroup.finiteDenseApproximationReindex (γ := SpatialCoordinates d)
            (q k) ∘ evalPhysical =
          ContinuousPath.finiteEvaluation
            (fun t : I ↦ DenseTime.castOrderEmbedding (q k t)) := by
      rfl
    rw [← hcomp, Kernel.map_comp_right]
    · have hrational := pa_finiteDense
        P hP default hsupport
        (SubMarkovKernelSemigroup.finiteDenseApproximationIndexSet (q k))
      change (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
          evalPhysical =
        SubMarkovKernelSemigroup.finiteSetKernel P
          (SubMarkovKernelSemigroup.finiteDenseApproximationPhysicalSet (q k)) at hrational
      rw [hrational]
      rfl
    · exact hevalPhysical
    · exact SubMarkovKernelSemigroup.measurable_finiteDenseApproximationReindex (q k)
  · intro x f
    exact hF.tendsto_integral_compactlySupported_finiteDenseApproximationKernel
      hP q hq f x

theorem pa_trajectory_congr
    {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
    [Nonempty alpha]
    (P Q : SubMarkovKernelSemigroup alpha) (hPQ : P = Q)
    (hP : P.IsConservative) (hQ : Q.IsConservative)
    (default : ContinuousPath alpha) :
    SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default =
      SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory Q hQ default := by
  subst Q
  rfl


end SubdiffusiveProcess.Section10.PhysicalAttachment
