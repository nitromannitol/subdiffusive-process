import SubdiffusiveProcess.Paper.in_common_scale_coupling
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane3.DeterministicEndpoints
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_represented_bounds
import SubdiffusiveProcess.Paper.in_represented_enum
import SubdiffusiveProcess.Paper.conv_represented_estimates
import SubdiffusiveProcess.Paper.thm_prop_affine_parameters
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Paper.lem_endpoints_support_1
import SubdiffusiveProcess.Paper.lem_endpoints_support_3
import SubdiffusiveProcess.Paper.lem_endpoints_support_8

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/--
Paper Lemma `mfd:lem-endpoints` (new paper line 9732): the endpoints `m = sup{a : aE ≤ F}` and `M = inf{a : F ≤ aE}`, taken over
the whole countable determining family of killed cubes, for two subsequential limit forms `E, F` of ONE represented sequence
(`in_joint_extracted_candidates`), are almost surely constant. The eq:mfd-26 comparison (`C0`, `hcomp`, `hnz`) is the
context of the sentence defining the endpoints. The proof is the paper's: measurability by variational duality on a countable
dense family, invariance under single-layer resampling (common positive weight, `prop_21`/`lem_sincos`), and the zero-one law
(`lem_endpoints_zero_one`).
-/
theorem lem_endpoints (d : ℕ) (hd : 2 ≤ d) :
    [NeZero d] →
    (I : Paper.in_J d) →
    (X : Paper.in_extension d hd I) →
    (Sob : Lane4.SobolevFoundationalInput d hd) →
    (Step : Paper.cutoff_good_scale_input d) →
    (MeyersMorrey : Lane4.SmallPerturbationInput d) →
    (Pin : Paper.in_poincare d hd I) →
    (D : Paper.lane4_deterministic_good_scale_input d) →
    (Cp : SubdiffusiveProcess.Lane4.CampanatoInput d) →
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality) →
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasBeurlingDenyLocality F.toClosedForm) →
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm) →
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasEnergyMeasure F) →
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) →
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        (hJoint :
          in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) →
        (Rm : Paper.in_responses d model) →
        (Sreg : Paper.in_6_16 d model) →
        (It : Paper.in_iteration d model I Sreg) →
        (hBounds : Paper.aux_lem_endpoints_bounds_pointwise d hd model H z r hr Sspace NE NF) →
        (hEnum : Paper.in_represented_enum d z r hr) →
        (@aux_lem_endpoints_catalogue d hd _ _ model H Ω _ P hJoint.1 field z r hr Sspace NE NF
          (aux_thm_prop_alpha d hd) (1 / 128)) →
        ∀ C0 : ℝ, 1 ≤ C0 →
        (∀ᵐ omega ∂P, aux_lem_endpoints_compare z r hr GE GF C0 omega) →
        (∀ᵐ omega ∂P, aux_lem_endpoints_nonzero z r hr GE omega) →
        ∃ cL cU : ℝ, ∀ᵐ omega ∂P,
          sSup (aux_lem_endpoints_lowerSet z r hr GE GF omega) = cL ∧
            sInf (aux_lem_endpoints_upperSet z r hr GE GF omega) = cU := by
  intro inst I X Sob Step MeyersMorrey Pin D Cp hES BD BDQ EM hcontract
  letI : NeZero d := inst
  obtain ⟨δ1, hδ1, hinv⟩ :=
    aux_lem_endpoints_support_8_endpoint_invariance d hd I X Sob Step MeyersMorrey Pin D Cp hES BD BDQ EM hcontract
  obtain ⟨δ2, hδ2, htr⟩ := lem_endpoints_support_8 d hd
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro _ _ model hmodel H Ω _ P field z r hr Sspace GN GE GF NE NF hJoint
    Rm Sreg It hBounds hEnum hCat C0 hC0 hcomp hnz
  obtain ⟨GNc, hGNc, hGNcMeas⟩ := aux_lem_endpoints_support_3_canonical_response d model H hJoint.2.2.2.1 z r hr Sspace
  exact htr model (hmodel.trans (min_le_right _ _)) H Ω P field z r hr Sspace GN GE GF NE NF
    hJoint C0 hC0 hcomp hnz GNc hGNc hGNcMeas
    (fun GEc GFc hc hdom => hinv model (hmodel.trans (min_le_left _ _)) H z r hr Sspace GNc GEc GFc
      NE NF hc (lem_endpoints_support_1 hd hBounds hc) hdom)

end Paper
