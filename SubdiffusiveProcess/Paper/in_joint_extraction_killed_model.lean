module

public import SubdiffusiveProcess.Paper.response_l1_compact_model
public import SubdiffusiveProcess.Paper.in_joint_extraction_inprob

@[expose] public section

/-!
# Actual-model joint extraction: `hmem` / `hcompact` discharged

Application of `SubdiffusiveProcess.Paper.in_joint_extraction_inprob` (header, unchanged) to the actual killed
inverse family: the premises `hmem` and `hcompact` of the principal are *supplied* by
`SubdiffusiveProcess.Paper.response_l1_compact_model` (killed quadratic responses on every cube, zero test included)
instead of being assumed.  The remaining premises (`hcoer`/`htight` coercivity data, the test
sets, the law transfer, the standing inputs) are exactly those of the principal plus the
catalogue premise that every test in `D i` has a smooth compactly supported representative.

The disorder threshold `δ0` is fixed before the model, the countable family of cubes and the tests.
-/

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal Topology InnerProductSpace ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Actual-model joint extraction** (`hmem`/`hcompact` supplied by the model estimate). -/
theorem in_joint_extraction_killed_model
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (hInterp : CubeFractionalInterpolationInput d hd) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M) (Sreg : in_6_16 d M)
        (_It : in_iteration d M E Sreg) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (D : (i : ℕ) → Set (DomainL2 (centeredCube (z i) (r i) (hr i))))
        [_hDcount : ∀ i, Countable (D i)]
        (_hDdense : ∀ i, Dense (D i))
        (_hDadd : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, x + y ∈ D i)
        (_hDsmooth : ∀ i, ∀ x ∈ D i, ∃ F : SpatialCoordinates d → ℝ,
          ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
          tsupport F ⊆ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) ∧
          (x : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] F)
        (_hGN : ∀ i N om f, GN i N om f =
          (responseSolution (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (field om) N (z i) (hr i))
            ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1)
        (Kc : ℕ → ℕ → Ω → ℝ)
        (_hcoer : ∀ i N, ∀ᵐ om ∂P,
          ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
            cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
                (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
            cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
                (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
              Kc i N om *
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (field om) N (z i) (hr i))
                  (v : SobolevData (centeredCube (z i) (r i) (hr i)))
                  (v : SobolevData (centeredCube (z i) (r i) (hr i))))
        (_htight : ∀ i, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
          P {om | Mb < Kc i N om} ≤ ENNReal.ofReal rho)
        (_hprob : IsProbabilityMeasure P)
        (_hfield : Measurable field)
        (_hmap : Measure.map field P = (chaosSampleLaw M).toMeasure)
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
        (NE0 NF0 : ℕ → ℕ) (_hNE0 : StrictMono NE0) (_hNF0 : StrictMono NF0),
        ∃ NE NF : ℕ → ℕ,
          ∃ GE GF : (i : ℕ) → Ω →
            DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
              DomainL2 (centeredCube (z i) (r i) (hr i)),
          StrictMono NE ∧ StrictMono NF ∧
          in_joint_extracted_candidates d M H Ω P field z r hr Sspace
            (fun i N om => GN i N om) GE GF NE NF ∧
          (∃ δE δF : ℕ → ℕ, StrictMono δE ∧ StrictMono δF ∧
            NE = NE0 ∘ δE ∧ NF = NF0 ∘ δF) := by
  obtain ⟨δ0, hδ0, hsupply⟩ := response_l1_compact_model d hd E Pc Xc W Cp Sf
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm Sreg It H hH hδ Ω _ P field z r hr Sspace GN D _ hDdense hDadd hDsmooth hGN Kc
    hcoer htight hprob hfield hmap hS NE0 NF0 hNE0 hNF0
  obtain ⟨hmem, hcompact⟩ :=
    hsupply M Rm Sreg It H hH hδ Ω P field hfield hmap z r hr Sspace GN D hDsmooth hGN hS
  exact in_joint_extraction_inprob d hd hInterp M H Ω P field z r hr Sspace GN D hDdense hDadd
    hGN Kc hcoer htight hmem hcompact hprob hfield hmap hH hS NE0 NF0 hNE0 hNF0

end SubdiffusiveProcess.Paper
