module

public import SubdiffusiveProcess.Paper.mfd_thm_c1
public import SubdiffusiveProcess.Section9.ExtendedComparisonEndpoints

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Section9
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem mfd_lem_endpoints
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, 0 < M.delta → M.delta ≤ delta0 →
      (∀ (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
        HasJointCutoffLimits d hd M NE NF) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
        (GE GF : KilledInverseFamily d Ω) (NE NF : ℕ → ℕ),
        JointCutoffLimits d hd M Ω P field env GE GF NE NF →
      ∃ cL cU : ℝ, C0⁻¹ ≤ cL ∧ cL ≤ cU ∧ cU ≤ C0 ∧
        ∀ᵐ ω ∂P,
          lowerEndpoint d Ω GE GF ω = cL ∧ upperEndpoint d Ω GE GF ω = cU := by
  obtain ⟨delta0, hdelta0, hactual⟩ := aux_mfd_thm_c1_joint_conclusions d hd
  refine ⟨delta0, 1, hdelta0, le_rfl, ?_⟩
  intro M hMpos hMle
  obtain ⟨hExists, hSelected⟩ := hactual M hMpos hMle
  refine ⟨hExists, ?_⟩
  intro Ω _ P field env GE GF NE NF hjoint
  refine ⟨1, 1, by norm_num, le_rfl, le_rfl, ?_⟩
  filter_upwards [hSelected Ω P field env GE GF NE NF hjoint] with ω hω
  obtain ⟨u, hu, hpos⟩ := hω.2
  exact endpoints_eq_of_proportional GE GF ω 1 zero_lt_one
    (proportional_one_of_inverse_eq GE GF ω hω.1) ⟨0, u, hu, hpos⟩

end SubdiffusiveProcess.Paper
