module

public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Paper.classical_cube_fractional_interpolation
public import SubdiffusiveProcess.Paper.classical_cube_fractional_compact_embedding

@[expose] public section

/-! Classical fractional interpolation and Rellich compactness on each fixed cube.
This leaf records only the standard norm facts; it has no coefficient, form,
or stochastic hypotheses or conclusions. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- E4: fixed-cube fractional interpolation and compactness in the concrete normalized norms. -/
theorem inputs_classical_e4_cube_norms (d : ℕ) (hd : 2 ≤ d) :
    SubdiffusiveProcess.CubeFractionalInterpolationInput d hd :=
  ⟨fun z r hr t ht => classical_cube_fractional_interpolation d hd z r hr t ht,
    fun z r hr t ht w M hb => classical_cube_fractional_compact_embedding d hd z r hr t ht w M hb⟩

end SubdiffusiveProcess.Paper
