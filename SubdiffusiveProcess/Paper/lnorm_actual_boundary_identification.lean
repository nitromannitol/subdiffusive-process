module

public import SubdiffusiveProcess.Paper.goodext_represented_controls_with_bank
public import SubdiffusiveProcess.Paper.lnorm_controlled_boundary_identification
public import SubdiffusiveProcess.Sobolev.VolumeResponseOperator

@[expose] public section

/-! Identify existing smooth response limits using actual cutoff controls on a
sample-dependent refinement. This module does not assert existence or uniqueness of operator limits. -/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Every existing smooth scalar limit is the local boundary minimum of its actual padded operator limit. -/
theorem lnorm_actual_boundary_identification
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (_hr1 : r ≤ 1) (N : ℕ → ℕ),
      let h3r : 0 < 3 * r := mul_pos zero_lt_three hr
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
        DomainL2 (centeredCube z (3 * r) h3r),
      Tendsto (fun n => volumeResponseOperator
        (killedResponseSpace (centeredCube_killedPoincare z h3r))
        (cutoffPositiveCoefficient M H om (N n) z h3r)) atTop (𝓝 G) →
      ∀ (E : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
        (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm),
      (∀ v, E.energy v = limitFormEnergy G v) →
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C) →
      ∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g → ∀ L : ℝ,
      Tendsto (fun n => sInf (continuousBoundaryEnergies z r hr
        (cutoffPositiveCoefficient M H om (N n) z hr) g)) atTop (𝓝 L) →
      L = sInf (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
        E.toClosedForm Gamma (centeredCube z r hr : Set (SpatialCoordinates d)) g) := by
  obtain ⟨delta0, hdelta0, h⟩ := goodext_represented_controls_with_bank
    d hd I Pin X W Cp Sob Interp ((d : ℝ) - 1 / 2) (3 / 4)
    (by linarith only []) (by linarith only []) (by norm_num) (by norm_num)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hr1 N
  let h3r : 0 < 3 * r := mul_pos zero_lt_three hr
  let S := killedResponseSpace (centeredCube_killedPoincare z h3r)
  have hcontrols := h M Rm Sreg It H hIR hdelta z (3 * r) h3r S rfl N
    (BilateralField d) (chaosSampleLaw M).toMeasure (fun _ om => om)
    (fun _ => measurable_id) (fun _ => Measure.map_id)
    PUnit (fun _ _ _ => (0 : ℝ)) (fun _ => (0 : ℝ≥0))
    (fun _ _ => MemLp.zero') (fun _ _ => by simp only [eLpNorm_fun_zero, ENNReal.coe_zero, le_refl])
  filter_upwards [hcontrols] with om hom
  intro G hConv E Gamma hE hcore g hg L hScalar
  obtain ⟨seq, hseq, ⟨A⟩, hcell, _⟩ := hom
  exact lnorm_controlled_boundary_identification hd z r hr h3r S rfl
    (fun n => cutoffCoefficient M H om (N (seq n)))
    (fun n => cutoffCoefficient_continuous M H om (N (seq n)))
    (fun n x => cutoffCoefficient_pos M H om (N (seq n)) x)
    (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z h3r)
    (fun n => (cutoffPositiveCoefficient_representative M H om (N (seq n)) z h3r).2.2.2)
    A (fun n => volumeResponseOperator S (cutoffPositiveCoefficient M H om (N (seq n)) z h3r))
    G (fun n f => volumeResponseOperator_apply _ _ f) (hConv.comp hseq.tendsto_atTop)
    E hE hcore Gamma ((d : ℝ) - 1 / 2) (3 / 4)
    (by linarith only []) (by linarith only []) (by norm_num) (by norm_num)
    (fun theta htheta thetaH hth => hcell 1 (by
      have h : (3 * r) / (3 : ℝ) ^ 1 = r := by ring
      rw [h]; exact hr1) theta htheta thetaH hth) (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hr)
    (fun n => (cutoffPositiveCoefficient_representative M H om (N (seq n)) z hr).2.2.2)
    g hg L (hScalar.comp hseq.tendsto_atTop)

end
end SubdiffusiveProcess.Paper
