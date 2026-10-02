import SubdiffusiveProcess.Paper.Support.KillingTestProbability
import SubdiffusiveProcess.Section9.KilledCommonParameterEvent
import SubdiffusiveProcess.Section9.RepresentedComparisonDraft
import SubdiffusiveProcess.Analysis.KilledOccupationParameters

/-! Supports: mfd_lem_killing.
The source application's common-event step. Its analytic continuity and
congruence inputs are internal properties of the produced unique minimizers;
they must be discharged by their actual construction in the principal.
-/
open Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Section9 SubdiffusiveProcess.Analysis
open scoped ENNReal NNReal LevyProkhorov
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_mfd_lem_killing_identify_common_parameters
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] [NeZero d] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (hin : in_crossing M H PN KN)
    (R : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      BilateralField d → C(SpatialCoordinates d, ℝ))
    (hpath : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps →
        Tendsto (fun N => (chaosSampleLaw M).toMeasure
          {omega | ∃ x ∈ B, eps ≤ pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
            (jointPathProbabilityMeasure K hK omega x)}) atTop (𝓝 0))
    (hprob : ∀ i lam, 0 < lam → ∀ f, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → (chaosSampleLaw M).toMeasure
        {omega | ∃ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
          eps ≤ |killedOccupationResolvent (determiningCube d i) KN N omega lam f x -
            R i lam f omega x|} ≤ ENNReal.ofReal rho)
    (hzero : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i lam, 0 < lam → ∀ f,
      ∀ x ∉ (determiningCube d i : Set (SpatialCoordinates d)), R i lam f omega x = 0)
    (hcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
      letI : CompactSpace (closure (determiningCube d i : Set (SpatialCoordinates d))) :=
        isCompact_iff_compactSpace.mp
          ((centeredCube_isBounded (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)).isCompact_closure)
      Continuous (fun a : Set.Ioi (0 : ℝ) ×
          C(closure (determiningCube d i : Set (SpatialCoordinates d)), ℝ) =>
        fun x : determiningCube d i =>
          R i a.1.1 (closedSourceExtension (determiningCube d i) a.2) omega x))
    (hcongr : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i lam, 0 < lam →
      ∀ f g : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      Set.EqOn f g (closure (determiningCube d i : Set (SpatialCoordinates d))) →
        Set.EqOn (R i lam f omega) (R i lam g omega)
          (determiningCube d i : Set (SpatialCoordinates d))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i lam, 0 < lam → ∀ f,
      ∀ x ∈ (determiningCube d i : Set (SpatialCoordinates d)),
        R i lam f omega x = killedOccupationResolvent (determiningCube d i)
          (fun _ => K) 0 omega lam f x := by
  classical
  letI (i : ℕ) : CompactSpace (closure (determiningCube d i : Set (SpatialCoordinates d))) :=
    isCompact_iff_compactSpace.mp
      ((centeredCube_isBounded (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)).isCompact_closure)
  letI : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  letI : IsMarkovKernel K := hK
  let X (i : ℕ) := Set.Ioi (0 : ℝ) ×
    C(closure (determiningCube d i : Set (SpatialCoordinates d)), ℝ)
  let Y (i : ℕ) := determiningCube d i → ℝ
  let A : ∀ i, BilateralField d → X i → Y i := fun i omega a x =>
    R i a.1.1 (closedSourceExtension (determiningCube d i) a.2) omega x
  let B : ∀ i, BilateralField d → X i → Y i := fun i omega a x =>
    SubdiffusiveProcess.KilledFeller.killedResolventScalar (determiningCube d i)
      (closedSourceExtension (determiningCube d i) a.2) a.1.1 (K (omega, x))
  have hcontinuous : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ i, Continuous (A i omega) ∧ Continuous (B i omega) := by
    filter_upwards [hcont] with omega hω i
    refine ⟨hω i, continuous_pi fun x => ?_⟩
    exact continuous_closedKilledResolventScalar (determiningCube d i)
      (determiningCube d i).isOpen (K (omega, x))
  have hpoint : ∀ i a, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      A i omega a = B i omega a := by
    intro i a
    have hz : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ x ∉ (determiningCube d i : Set (SpatialCoordinates d)),
          R i a.1.1 (BoundedContinuousFunction.const _ 1) omega x = 0 := by
      filter_upwards [hzero] with omega hω
      exact hω i a.1.1 a.1.2 _
    have hid := aux_mfd_lem_killing_identify_test_in_probability hd M H PN KN hKN K hK hin
      (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
      a.1.1 a.1.2 (closedSourceExtension (determiningCube d i) a.2)
      (R i a.1.1 (closedSourceExtension (determiningCube d i) a.2))
      (R i a.1.1 (BoundedContinuousFunction.const _ 1)) hpath
      (hprob i a.1.1 a.1.2 _) (hprob i a.1.1 a.1.2 _) hz
    filter_upwards [hid] with omega hω
    funext x
    exact (hω x x.2).trans (killedOccupationResolvent_eq_scalar _ _ _ _ _ _ _)
  have hae := SubdiffusiveProcess.Section9.ae_forall_eq_of_continuous_parameter
    (chaosSampleLaw M).toMeasure X Y A B hcontinuous hpoint
  filter_upwards [hae, hcongr] with omega hω hcω
  intro i lam hlam f x hx
  let flocal := f.toContinuousMap.restrict (closure (determiningCube d i : Set (SpatialCoordinates d)))
  have hs : Set.EqOn (closedSourceExtension (determiningCube d i) flocal) f
      (closure (determiningCube d i : Set (SpatialCoordinates d))) := by
    intro y hy
    exact closedSourceExtension_restrict _ _ ⟨y, hy⟩
  calc
    R i lam f omega x = R i lam (closedSourceExtension (determiningCube d i) flocal) omega x :=
      (hcω i lam hlam _ _ hs hx).symm
    _ = SubdiffusiveProcess.KilledFeller.killedResolventScalar (determiningCube d i)
        (closedSourceExtension (determiningCube d i) flocal) lam (K (omega, x)) :=
      congrFun (hω i (⟨lam, hlam⟩, flocal)) ⟨x, hx⟩
    _ = SubdiffusiveProcess.KilledFeller.killedResolventScalar (determiningCube d i) f lam (K (omega, x)) :=
      closedSourceExtension_scalar_eq _ _ _ _
    _ = killedOccupationResolvent (determiningCube d i) (fun _ => K) 0 omega lam f x :=
      (killedOccupationResolvent_eq_scalar (determiningCube d i) (fun _ => K) 0 omega lam f x).symm

end Paper
