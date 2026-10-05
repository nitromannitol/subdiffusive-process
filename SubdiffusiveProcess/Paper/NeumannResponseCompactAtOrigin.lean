module

public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw

@[expose] public section

open MeasureTheory SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization Set
open TopologicalSpace Homogenization.Book.Ch02
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]

/-- The typed Neumann-compactness property needed by the `sigmaStarInvCoarse` results:
compactness for `affineInverseNeumannResponse` at the origin-centred cube, with the
Poincaré witness from `aux_lem_prefix_limit_atom_extraction_poincare`.
Both `aux_g9_sigma_entries_compact_starinv_diag_compact` and
`aux_g9_sigma_entries_compact_starinv_offdiag_compact` take this property
as an explicit hypothesis. -/
def NeumannResponseCompactAtOrigin (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] : Prop :=
  ∀ (u : Fin d → ℝ), u ≠ 0 →
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (_Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ N, MemLp (fun omega => affineInverseNeumannResponse
            aux_lem_prefix_limit_atom_extraction_poincare.2
            (cutoffPositiveCoefficient M H omega N 0 one_pos) u) (ENNReal.ofReal 2)
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N => (hmem N).toLp (fun omega =>
          affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
            (cutoffPositiveCoefficient M H omega N 0 one_pos) u))))

end SubdiffusiveProcess.Paper
