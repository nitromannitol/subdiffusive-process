import SubdiffusiveProcess.Paper.Support.UniformResolventFormObjects
import SubdiffusiveProcess.Paper.Support.UniformResolventFiniteFamily
import SubdiffusiveProcess.Paper.Support.UniformResolventCoercivityScale
import SubdiffusiveProcess.Paper.Support.UniformResolventHolderFamily
import SubdiffusiveProcess.Paper.Support.UniformResolventMaskedInverse
import SubdiffusiveProcess.Paper.Support.UniformResolventFractionalEvent
import SubdiffusiveProcess.Paper.Support.UniformResolventInverse
import SubdiffusiveProcess.Paper.Support.UniformResolventMeasure
import SubdiffusiveProcess.Geometry.EnclosingTriadicRegion
import SubdiffusiveProcess.Paper.inputs_J_witness
import SubdiffusiveProcess.Paper.inputs_poincare_witness
import SubdiffusiveProcess.Paper.inputs_extension_witness
import SubdiffusiveProcess.Paper.inputs_W_witness
import SubdiffusiveProcess.Paper.inputs_Cp_witness
import SubdiffusiveProcess.Paper.inputs_Sf_witness
import SubdiffusiveProcess.Paper.inputs_Interp_witness
import SubdiffusiveProcess.Paper.inputs_responses_witness
import SubdiffusiveProcess.Paper.inputs_regularity_witness
import SubdiffusiveProcess.Paper.inputs_iteration_witness

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Section9 SubdiffusiveProcess.Analysis
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- Internal data, produced from the standing paper hypotheses below. -/
structure aux_mfd_prop_uniform_resolvent_Inputs
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (epsilon q : ℝ) where
  G : KilledInverseFamily d (BilateralField d)
  muFull : BilateralField d → Measure (SpatialCoordinates d)
  hGmeas : ∀ i, Measurable (G i)
  hmuMeas : Measurable muFull
  hGconv : ∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
    (fun N omega => volumeResponseOperator (determiningResponseSpace d i)
      (cutoffPositiveCoefficient M H omega N (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)))
    atTop (G i)
  hmu : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
    IsLocallyFiniteMeasure (muFull omega) ∧ (muFull omega).IsOpenPosMeasure ∧ NoAtoms (muFull omega) ∧
    ∀ i, muFull omega (frontier (determiningCube d i : Set (SpatialCoordinates d))) = 0
  Kmu : ℕ → BilateralField d → ℝ
  hKmuMeas : ∀ i, Measurable (Kmu i)
  hKmuMom : ∀ i, MemLp (Kmu i) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure
  Qroot : ℕ → Homogenization.TriadicCube d
  Region : ℕ → Set (SpatialCoordinates d)
  hRegion : ∀ i, Bornology.IsBounded (Region i)
  hroot : ∀ i, closure (determiningCube d i : Set (SpatialCoordinates d)) ⊆ closure (Homogenization.openCubeSet (Qroot i))
  hrootRegion : ∀ i, closure (Homogenization.openCubeSet (Qroot i)) ⊆ Region i
  hNeighborhood : ∀ i x, x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)) → Metric.ball x 1 ⊆ Region i
  hgrowth : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
    0 ≤ Kmu i omega ∧
    (∀ N x, x ∈ Region i → ∀ r, 0 < r → r ≤ 1 → cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
      ENNReal.ofReal (Kmu i omega * r ^ ((d : ℝ) - epsilon))) ∧
    ∀ x, x ∈ Region i → ∀ r, 0 < r → r ≤ 1 → muFull omega (Metric.ball x r) ≤
      ENNReal.ofReal (Kmu i omega * r ^ ((d : ℝ) - epsilon))
  Kcoer : ℕ → ℕ → BilateralField d → ℝ
  Khol : ℕ → ℕ → BilateralField d → ℝ
  Cbound : ℕ → ℝ
  hCbound : ∀ i, 0 ≤ Cbound i
  hKmeas : ∀ i N, Measurable (Kcoer i N) ∧ Measurable (Khol i N)
  hKnonneg : ∀ i N omega, 0 ≤ Kcoer i N omega ∧ 0 ≤ Khol i N omega
  hKmom : ∀ i N, MemLp (Kcoer i N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
    MemLp (Khol i N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure
  hKbound : ∀ i N, eLpNorm (Kcoer i N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i) ∧
    eLpNorm (Khol i N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)
  hcoer : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i N,
    ∀ v : killedSobolevGraph (determiningCube d i),
      (‖v.val.1‖ ^ 2 ≤ Kcoer i N omega *
        sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N (rationalTriadicCenter d i)
          (rationalTriadicSide_pos d i)) v.val v.val) ∧
      (globalFractionalSqNorm (3 / 4) ((determiningCube d i : Set (SpatialCoordinates d)).indicator (fun x => v.val.1 x)) ≤
        ENNReal.ofReal (Kcoer i N omega * sobolevCoefficientForm
          (cutoffPositiveCoefficient M H omega N (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) v.val v.val)) ∧
      ∃ v3 : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
          (rationalTriadicSide_pos d i) threeQuarterOrder,
        v3.val 0 = v.val.1 ∧ cubeFractionalL2Norm hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
          (rationalTriadicSide_pos d i) threeQuarterOrder v3 ^ 2 ≤
          Kcoer i N omega * sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N
            (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) v.val v.val
  hHolder : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i N,
    ∀ F : SpatialCoordinates d → ℝ, Measurable F → ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ (determiningCube d i : Set (SpatialCoordinates d)), |F x| ≤ MF) →
    ∀ v : killedSobolevGraph (determiningCube d i),
      (∀ w : killedSobolevGraph (determiningCube d i),
        sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N (rationalTriadicCenter d i)
          (rationalTriadicSide_pos d i)) v.val w.val = ∫ x in (determiningCube d i : Set (SpatialCoordinates d)), F x * w.val.1 x) →
      ∃ vc : C(SpatialCoordinates d, ℝ), (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (determiningCube d i : Set (SpatialCoordinates d))] vc ∧
        (∀ x ∉ (determiningCube d i : Set (SpatialCoordinates d)), vc x = 0) ∧
        ∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), ∀ y ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
          |vc x - vc y| ≤ Khol i N omega * MF * dist x y ^ (1 / 2 : ℝ)
  lift : ∀ i omega (u : DomainL2 (determiningCube d i)), (limitFormEnergy (G i omega) u).toENNReal ≠ ∞ →
    CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i) halfFractionalOrder
  hlift : ∀ i omega u hu, (lift i omega u hu).val 0 = u
  O : ∀ i omega, aux_mfd_prop_uniform_resolvent_FormObjects hd (rationalTriadicCenter d i)
    (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
    ((muFull omega).restrict (closure (determiningCube d i : Set (SpatialCoordinates d))))
  hForm : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
    aux_mfd_prop_uniform_resolvent_FormSpec hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
      (rationalTriadicSide_pos d i) (G i omega)
      ((muFull omega).restrict (closure (determiningCube d i : Set (SpatialCoordinates d))))
      (Kmu i omega) (lift i omega) (O i omega)
  uN : ∀ i, ℕ → BilateralField d → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → killedSobolevGraph (determiningCube d i)
  hRNmeas : ∀ i N lam f x, Measurable (fun omega => killedOccupationResolvent (determiningCube d i) KN N omega lam f x)
  hRNbound : ∀ i N omega lam, 0 < lam → ∀ f x, |killedOccupationResolvent (determiningCube d i) KN N omega lam f x| ≤ ‖f‖ / lam
  hfinite : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i N lam, 0 < lam → ∀ f,
    (killedOccupationResolvent (determiningCube d i) KN N omega lam f =ᵐ[
      volume.restrict (determiningCube d i : Set (SpatialCoordinates d))] (uN i N omega lam f).val.1) ∧
    (∀ w : killedSobolevGraph (determiningCube d i),
      sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N (rationalTriadicCenter d i)
        (rationalTriadicSide_pos d i)) (uN i N omega lam f).val w.val =
        ∫ x, (f x - lam * killedOccupationResolvent (determiningCube d i) KN N omega lam f x) * w.val.1 x
          ∂((cutoffSpeedMeasure M H omega N).restrict (closure (determiningCube d i : Set (SpatialCoordinates d))))) ∧
    sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))
      (uN i N omega lam f).val (uN i N omega lam f).val ≤ ‖f‖ ^ 2 *
        (((cutoffSpeedMeasure M H omega N).restrict (closure (determiningCube d i : Set (SpatialCoordinates d))))
          (determiningCube d i : Set (SpatialCoordinates d))).toReal / lam
  hpoint : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i N lam, 0 < lam → ∀ f,
    ∀ v : SpatialCoordinates d → ℝ, Continuous v →
      (v =ᵐ[volume.restrict (determiningCube d i : Set (SpatialCoordinates d))]
        killedOccupationResolvent (determiningCube d i) KN N omega lam f) →
      (∀ x ∉ (determiningCube d i : Set (SpatialCoordinates d)), v x = 0) →
      ∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), killedOccupationResolvent (determiningCube d i) KN N omega lam f x = v x

end Paper
