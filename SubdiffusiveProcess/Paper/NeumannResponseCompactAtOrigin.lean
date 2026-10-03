module

public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw

@[expose] public section

open MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Lane4 Homogenization Set
open TopologicalSpace Homogenization.Book.Ch02
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]



def NeumannResponseCompactAtOrigin (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] : Prop :=
  ∀ (u : Fin d → ℝ), u ≠ 0 →
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ N, MemLp (fun omega => affineInverseNeumannResponse
            aux_lem_prefix_limit_atom_extraction_poincare.2
            (cutoffPositiveCoefficient M H omega N 0 one_pos) u) (ENNReal.ofReal 2)
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N => (hmem N).toLp (fun omega =>
          affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
            (cutoffPositiveCoefficient M H omega N 0 one_pos) u))))

end Paper
