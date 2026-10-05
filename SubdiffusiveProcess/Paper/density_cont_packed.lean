module

public import SubdiffusiveProcess.Paper.density_represented_source_continuity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization
open scoped Topology ENNReal NNReal ContDiff

/-- The conclusion of `density_represented_source_continuity` after its constant, folded into a definition (verbatim body). -/
def aux_density_cont_packed_body
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (_Pin : in_poincare d hd I) (_X : in_extension d hd I)
    (_W : SmallPerturbationInput d) (_Cp : CampanatoInput d)
    (_Sob : SobolevFoundationalInput d hd)
    (alpha : ℝ) (_ha : alpha ∈ Ioo (1 / 2 : ℝ) 1)
    (delta0 : ℝ) : Prop :=
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)) (_hS : S.space = killedSobolevGraph (centeredCube z r hr))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (env : ℕ → Ω → BilateralField d)
        (_hEnv : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure)
        (phi : ℕ → ℕ)
        (GN : ℕ → BilateralField d → DomainL2 (centeredCube z r hr) →L[ℝ]
          DomainL2 (centeredCube z r hr))
        (_hGN : ∀ n xi f, GN n xi f = (responseSolution S
          (cutoffPositiveCoefficient M H xi n z hr)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (G : Ω → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
        (_hConv : ∀ᵐ omega ∂P, Tendsto (fun n => GN (phi n) (env n omega)) atTop (𝓝 (G omega))),
      ∀ᵐ omega ∂P, ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
        ∀ fL2 : DomainL2 (centeredCube z r hr),
          (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] f →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          (G omega fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) ∧
          IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) U

/-- `density_represented_source_continuity`, with the conclusion after the constant folded into `aux_density_cont_packed_body`. -/
theorem density_cont_packed
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd)
    (alpha : ℝ) (ha : alpha ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ aux_density_cont_packed_body d hd I Pin X W Cp Sob alpha ha delta0 :=
  density_represented_source_continuity d hd I Pin X W Cp Sob alpha ha

end SubdiffusiveProcess.Paper
