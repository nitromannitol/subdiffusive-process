import SubdiffusiveProcess.Paper.Support.UniformResolventLifetime
import SubdiffusiveProcess.Paper.car_variational
import SubdiffusiveProcess.Analysis.KilledOccupationResolvent
import SubdiffusiveProcess.Section9.RepresentedComparisonDraft

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Section9 SubdiffusiveProcess.Analysis
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace Paper



theorem aux_mfd_prop_uniform_resolvent_finite_family
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN) :
    let RN := fun i N omega lam f => killedOccupationResolvent (determiningCube d i) KN N omega lam f
    ∃ uN : ∀ i, ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → killedSobolevGraph (determiningCube d i),
      (∀ i N lam f x, Measurable (fun omega => RN i N omega lam f x)) ∧
      (∀ i N omega lam, 0 < lam → ∀ f x, |RN i N omega lam f x| ≤ ‖f‖ / lam) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i N lam, 0 < lam → ∀ f,
        (RN i N omega lam f =ᵐ[volume.restrict (determiningCube d i : Set (SpatialCoordinates d))]
          (uN i N omega lam f).val.1) ∧
        (∀ w : killedSobolevGraph (determiningCube d i),
          sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N
            (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) (uN i N omega lam f).val w.val =
            ∫ x, (f x - lam * RN i N omega lam f x) * w.val.1 x
              ∂((cutoffSpeedMeasure M H omega N).restrict
                (closure (determiningCube d i : Set (SpatialCoordinates d))))) ∧
        sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N
          (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))
          (uN i N omega lam f).val (uN i N omega lam f).val ≤
          ‖f‖ ^ 2 * (((cutoffSpeedMeasure M H omega N).restrict
            (closure (determiningCube d i : Set (SpatialCoordinates d))))
            (determiningCube d i : Set (SpatialCoordinates d))).toReal / lam) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i N lam, 0 < lam → ∀ f,
        ∀ v : SpatialCoordinates d → ℝ, Continuous v →
          (v =ᵐ[volume.restrict (determiningCube d i : Set (SpatialCoordinates d))] RN i N omega lam f) →
          (∀ x ∉ (determiningCube d i : Set (SpatialCoordinates d)), v x = 0) →
          ∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), RN i N omega lam f x = v x) := by
  classical
  intro RN
  obtain ⟨L, hL, hlocal, hstrong⟩ := aux_mfd_prop_uniform_resolvent_lifetime hd M H hH PN KN hKN hin
  let K := fun N omega => (KN N).comap (fun x : SpatialCoordinates d => (omega, x))
    (measurable_const.prodMk measurable_id)
  have hK : ∀ N omega, IsMarkovKernel (K N omega) := by
    intro N omega
    haveI := hKN N
    exact inferInstance
  have hRN : ∀ i N omega lam f, RN i N omega lam f =
      aux_car_variational_hol_occupation (K N omega) (determiningCube d i) lam f :=
    fun _ _ _ _ _ => rfl
  have hu : ∀ i N omega lam f, ∃ u : killedSobolevGraph (determiningCube d i),
      LocalDiffusionData (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega) →
      0 < lam →
      (RN i N omega lam f =ᵐ[volume.restrict (determiningCube d i : Set (SpatialCoordinates d))] u.val.1) ∧
      (∀ w : killedSobolevGraph (determiningCube d i),
        sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N
          (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) u.val w.val =
          ∫ x, (f x - lam * RN i N omega lam f x) * w.val.1 x
            ∂((cutoffSpeedMeasure M H omega N).restrict
              (closure (determiningCube d i : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N
        (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) u.val u.val ≤
        ‖f‖ ^ 2 * (((cutoffSpeedMeasure M H omega N).restrict
          (closure (determiningCube d i : Set (SpatialCoordinates d))))
          (determiningCube d i : Set (SpatialCoordinates d))).toReal / lam := by
    intro i N omega lam f
    by_cases hgood : LocalDiffusionData (cutoffCoefficient M H omega N)
        (cutoffSpeedDensity M H omega N) (L N omega) ∧ 0 < lam
    · haveI := hK N omega
      obtain ⟨u, h1, h2⟩ := aux_car_variational_hol_weak_ident M H omega N (K N omega)
        (L N omega) (hL N omega) hgood.1.1 (rationalTriadicCenter d i)
        (rationalTriadicSide d i) (rationalTriadicSide_pos d i) lam hgood.2 f
      have hb := fun x (_ : x ∈ (determiningCube d i : Set (SpatialCoordinates d))) =>
        aux_car_variational_hol_occupation_bound (K N omega) (determiningCube d i) lam hgood.2 f x
      obtain ⟨hae, -, hweak, henergy⟩ := aux_car_variational_hfinite_of_weak_ident hd M H omega N
        (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
        lam hgood.2 f _ u h1 h2 hb
      exact ⟨u, fun _ _ => ⟨hae, hweak, henergy⟩⟩
    · exact ⟨0, fun hd' hl => (hgood ⟨hd', hl⟩).elim⟩
  choose uN huN using hu
  refine ⟨uN, ?_, ?_, ?_, ?_⟩
  · intro i N lam f x
    exact (aux_car_variational_occupation_measurable KN N (hKN N) (determiningCube d i) lam f).comp
      (measurable_id.prodMk measurable_const)
  · intro i N omega lam hlam f x
    haveI := hK N omega
    exact aux_car_variational_hol_occupation_bound (K N omega) (determiningCube d i) lam hlam f x
  · filter_upwards [hlocal] with omega hω i N lam hlam f
    exact huN i N omega lam f (hω N) hlam
  · filter_upwards [hlocal, hstrong] with omega hω hs i N lam hlam f v hv hae hv0
    haveI := hK N omega
    obtain ⟨pk, hkd, -⟩ := (hω N).2 (determiningCube d i)
      (determiningCube d i).isOpen (centeredCube_isBounded (rationalTriadicCenter d i)
        (rationalTriadicSide_pos d i))
    exact aux_prop_uniform_resolvent_point (determiningCube d i) (determiningCube d i).isOpen
      (centeredCube_isBounded (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))
      (K N omega) (L N omega) (hL N omega) (hs N) _ pk hkd lam hlam f
      (RN i N omega lam f) (fun _ => rfl) v hv hae hv0

end Paper
