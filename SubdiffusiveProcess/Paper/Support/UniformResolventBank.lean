module

public import SubdiffusiveProcess.Paper.Support.UniformResolventSelectedBank
public import SubdiffusiveProcess.Probability.UniformSubsequenceCriterion

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.Section9 SubdiffusiveProcess.Analysis
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_mfd_prop_uniform_resolvent_bank
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : CampanatoInput d) (Interp : CubeFractionalInterpolationInput d hd)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (q : ℝ) (hq : 1 ≤ q)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (A : aux_mfd_prop_uniform_resolvent_Inputs d hd M H KN epsilon q)
    :
      ∃ (R : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → BilateralField d → C(SpatialCoordinates d, ℝ))
        (B : ℕ → BilateralField d → ℝ),
        (∀ i, Measurable (B i) ∧ (∀ omega, 0 ≤ B i omega) ∧ MemLp (B i) (ENNReal.ofReal (q / 2)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i lam, 0 < lam → ∀ f, Measurable (R i lam f)) ∧
        (∀ i lam, 0 < lam → ∀ f, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N → (chaosSampleLaw M).toMeasure
            {omega | ∃ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), eps ≤
              |killedOccupationResolvent (determiningCube d i) KN N omega lam f x - R i lam f omega x|} ≤
              ENNReal.ofReal rho) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
          (∀ N lam, 0 < lam → ∀ f, ContinuousOn (killedOccupationResolvent (determiningCube d i) KN N omega lam f)
            (closure (determiningCube d i : Set (SpatialCoordinates d))) ∧
            ∀ x ∈ frontier (determiningCube d i : Set (SpatialCoordinates d)),
              killedOccupationResolvent (determiningCube d i) KN N omega lam f x = 0) ∧
          ∀ lam, 0 < lam → ∀ f,
            ((R i lam f omega : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (determiningCube d i : Set (SpatialCoordinates d))]
              ((A.O i omega).ustar lam f : SpatialCoordinates d → ℝ)) ∧
            (∀ x ∉ (determiningCube d i : Set (SpatialCoordinates d)), R i lam f omega x = 0) ∧
            (∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), |R i lam f omega x| ≤ ‖f‖ / lam) ∧
            (∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), |R i lam f omega x| ≤ B i omega * ‖f‖) ∧
            ∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), ∀ y ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
              |R i lam f omega x - R i lam f omega y| ≤ B i omega * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) := by
  classical
  let P := (chaosSampleLaw M).toMeasure
  obtain ⟨_, _, R, B, hB, hRm, _, hR⟩ := aux_mfd_prop_uniform_resolvent_selected_bank
    d hd Cp Interp epsilon hepsilon hepsilon' q hq M H KN A id (fun _ _ h => h)
  refine ⟨R, B, hB, hRm, ?_, hR⟩
  intro i lam hlam f
  apply SubdiffusiveProcess.Probability.uniform_probability_limit_of_subsequence P
    (closure (determiningCube d i : Set (SpatialCoordinates d)))
    (fun N omega => killedOccupationResolvent (determiningCube d i) KN N omega lam f)
    (fun omega x => R i lam f omega x)
  intro psi hpsi
  obtain ⟨phi, hphi, S, _, _, _, hSprob, hS⟩ := aux_mfd_prop_uniform_resolvent_selected_bank
    d hd Cp Interp epsilon hepsilon hepsilon' q hq M H KN A psi hpsi
  have heq : ∀ᵐ omega ∂P, ∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
      S i lam f omega x = R i lam f omega x := by
    filter_upwards [hS, hR] with omega hs hr
    exact aux_prop_uniform_resolvent_subsequence_bridge_eqOn_of_ae_eq
      (determiningCube d i) (closure (determiningCube d i : Set (SpatialCoordinates d)))
      (determiningCube d i).isOpen
      (aux_prop_uniform_resolvent_ident_cube_nonempty (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) rfl
      (S i lam f omega) (R i lam f omega) (S i lam f omega).continuous.continuousOn
      (R i lam f omega).continuous.continuousOn
      (((hs i).2 lam hlam f).1.trans (((hr i).2 lam hlam f).1.symm))
  refine ⟨phi, hphi, ?_⟩
  intro eps heps rho hrho
  obtain ⟨N0, hN0⟩ := hSprob i lam hlam f eps heps rho hrho
  refine ⟨N0, fun N hN => ?_⟩
  have hSets : {omega | ∃ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), eps ≤
        |killedOccupationResolvent (determiningCube d i) KN (psi (phi N)) omega lam f x - S i lam f omega x|} =ᵐ[P]
      {omega | ∃ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), eps ≤
        |killedOccupationResolvent (determiningCube d i) KN (psi (phi N)) omega lam f x - R i lam f omega x|} := by
    filter_upwards [heq] with omega hω
    apply propext
    constructor
    · rintro ⟨x, hx, hb⟩
      exact ⟨x, hx, by simpa only [hω x hx] using hb⟩
    · rintro ⟨x, hx, hb⟩
      exact ⟨x, hx, by simpa only [hω x hx] using hb⟩
  rw [← measure_congr hSets]
  exact hN0 N hN

end SubdiffusiveProcess.Paper
