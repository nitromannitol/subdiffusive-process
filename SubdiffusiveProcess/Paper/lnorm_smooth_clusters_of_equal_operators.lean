module

public import SubdiffusiveProcess.Paper.lnorm_actual_boundary_identification
public import SubdiffusiveProcess.Paper.prop_conc_form_gamma

@[expose] public section

/-! Equality of actual padded operator limits identifies the corresponding
smooth boundary-response limits. Operator equality itself is not asserted. -/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper
noncomputable section

/-- Equal padded killed-operator limits have equal smooth boundary-response cluster values. -/
theorem lnorm_smooth_clusters_of_equal_operators
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (NE NF : ℕ → ℕ),
      let h3r : 0 < 3 * r := mul_pos zero_lt_three hr
      ∀ (G : BilateralField d → DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
        DomainL2 (centeredCube z (3 * r) h3r))
        (g : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ g →
      ∀ (LE LF : BilateralField d → ℝ),
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        Tendsto (fun n => volumeResponseOperator
          (killedResponseSpace (centeredCube_killedPoincare z h3r))
          (cutoffPositiveCoefficient M H om (NE n) z h3r)) atTop (𝓝 (G om)) ∧
        Tendsto (fun n => volumeResponseOperator
          (killedResponseSpace (centeredCube_killedPoincare z h3r))
          (cutoffPositiveCoefficient M H om (NF n) z h3r)) atTop (𝓝 (G om))) →
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        Tendsto (fun n => sInf (continuousBoundaryEnergies z r hr
          (cutoffPositiveCoefficient M H om (NE n) z hr) g)) atTop (𝓝 (LE om)) ∧
        Tendsto (fun n => sInf (continuousBoundaryEnergies z r hr
          (cutoffPositiveCoefficient M H om (NF n) z hr) g)) atTop (𝓝 (LF om))) →
      LE =ᵐ[(chaosSampleLaw M).toMeasure] LF := by
  obtain ⟨deltaB, hdeltaB, hboundary⟩ := lnorm_actual_boundary_identification
    d hd I Pin X W Cp Sob Interp
  obtain ⟨deltaF, hdeltaF, hforms⟩ := prop_conc_form_gamma d hd I Pin X W Cp Sob Interp
  refine ⟨min deltaB deltaF, lt_min hdeltaB hdeltaF, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hr1 NE NF h3r G g hg LE LF hG hL
  have hdeltaB' : M.delta ≤ deltaB := hdelta.trans (min_le_left _ _)
  have hdeltaF' : M.delta ≤ deltaF := hdelta.trans (min_le_right _ _)
  filter_upwards [hG, hL,
    hboundary M Rm Sreg It H hIR hdeltaB' z r hr hr1 NE,
    hboundary M Rm Sreg It H hIR hdeltaB' z r hr hr1 NF,
    hforms M Rm Sreg It H hIR hdeltaF' z (3 * r) h3r
      (centeredCube_killedPoincare z h3r) NE] with om hGo hLo hEid hFid hForm
  obtain ⟨E, hE, _hNC, hcore, _hreg, _hloc, ⟨Gamma⟩⟩ := hForm _ (G om)
    (fun n f => volumeResponseOperator_apply _ _ f) hGo.1
  exact (hEid (G om) hGo.1 E Gamma hE hcore g hg (LE om) hLo.1).trans
    (hFid (G om) hGo.2 E Gamma hE hcore g hg (LF om) hLo.2).symm

end
end Paper
