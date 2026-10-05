module

public import SubdiffusiveProcess.Paper.inputs_classical_mosco_liminf
public import SubdiffusiveProcess.Paper.car_variational
public import SubdiffusiveProcess.Section9.CountableLimitSubsequence
public import SubdiffusiveProcess.Section9.RepresentedComparisonDraft

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology SubdiffusiveProcess SubdiffusiveProcess.Section9
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Norm convergence of the actual killed inverse implies Mosco convergence on
an arbitrary centred cube. No full-sequence random almost-sure limit is assumed. -/
theorem aux_mfd_prop_uniform_resolvent_mosco_from_norm_limit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] [NeZero d]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hG : Tendsto (fun n => volumeResponseOperator
      (killedResponseSpace (centeredCube_killedPoincare z hr)) (a n)) atTop (𝓝 G)) :
    (∀ x y : DomainL2 (centeredCube z r hr), inner ℝ (G x) y = inner ℝ x (G y)) ∧
    (∀ x : DomainL2 (centeredCube z r hr), 0 ≤ inner ℝ x (G x)) ∧
    _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf
      (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube z r hr) //
        (v : SobolevData (centeredCube z r hr)).1 = u},
        ENNReal.ofReal (sobolevCoefficientForm (a N) v.val v.val))
      (fun u => (limitFormEnergy G u).toENNReal) ∧
    _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery
      (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube z r hr) //
        (v : SobolevData (centeredCube z r hr)).1 = u},
        ENNReal.ofReal (sobolevCoefficientForm (a N) v.val v.val))
      (fun u => (limitFormEnergy G u).toENNReal) := by
  have hstrong : ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto (fun n => (responseSolution
        (killedResponseSpace (centeredCube_killedPoincare z hr)) (a n)
        ((sobolevVolumeLoad f).comp
          (killedResponseSpace (centeredCube_killedPoincare z hr)).space.subtypeL)).val.1)
        atTop (𝓝 (G f)) := by
    intro f
    have hEval : Continuous (fun A : DomainL2 (centeredCube z r hr) →L[ℝ]
        DomainL2 (centeredCube z r hr) => A f) := continuous_id.clm_apply continuous_const
    simpa only [Function.comp_def, volumeResponseOperator_apply] using (hEval.tendsto G).comp hG
  obtain ⟨hsym, hpos, -, -⟩ := aux_car_variational_mosco z r hr
    (centeredCube_killedPoincare z hr) a G hstrong
  exact ⟨hsym, hpos, inputs_classical_mosco_liminf
    (centeredCube_killedPoincare z hr) a G hstrong⟩

/-- Every deterministic cutoff subsequence admits one further subsequence on
which all determining cubes have actual norm limits and Mosco limits together. -/
theorem aux_mfd_prop_uniform_resolvent_common_mosco_subsequence
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (G : KilledInverseFamily d (BilateralField d))
    (hconv : ∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N omega => volumeResponseOperator (determiningResponseSpace d i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
          (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))) atTop (G i))
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
        Tendsto (fun n => volumeResponseOperator (determiningResponseSpace d i)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (psi (phi n))
            (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))) atTop (𝓝 (G i omega)) ∧
        (∀ x y : DomainL2 (determiningCube d i),
          inner ℝ (G i omega x) y = inner ℝ x (G i omega y)) ∧
        (∀ x : DomainL2 (determiningCube d i), 0 ≤ inner ℝ x (G i omega x)) ∧
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf
          (fun n u => ⨅ v : {v : killedSobolevGraph (determiningCube d i) //
            (v : SobolevData (determiningCube d i)).1 = u},
            ENNReal.ofReal (sobolevCoefficientForm
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (psi (phi n))
                (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) v.val v.val))
          (fun u => (limitFormEnergy (G i omega) u).toENNReal) ∧
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery
          (fun n u => ⨅ v : {v : killedSobolevGraph (determiningCube d i) //
            (v : SobolevData (determiningCube d i)).1 = u},
            ENNReal.ofReal (sobolevCoefficientForm
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (psi (phi n))
                (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) v.val v.val))
          (fun u => (limitFormEnergy (G i omega) u).toENNReal) := by
  obtain ⟨phi, hphi, hae⟩ := exists_common_ae_subsequence (chaosSampleLaw M).toMeasure
    (fun i n omega => volumeResponseOperator (determiningResponseSpace d i)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (psi n)
        (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))) G
    (fun i => (hconv i).comp hpsi.tendsto_atTop)
  refine ⟨phi, hphi, ?_⟩
  filter_upwards [hae] with omega hω i
  exact ⟨hω i, aux_mfd_prop_uniform_resolvent_mosco_from_norm_limit
    (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (psi (phi n))
      (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) (G i omega) (hω i)⟩

end SubdiffusiveProcess.Paper
