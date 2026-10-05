module

public import SubdiffusiveProcess.Paper.prop_conc_actual_coercivity_cutoffs
public import SubdiffusiveProcess.Paper.prop_conc_mesh_approximate_control
public import SubdiffusiveProcess.Paper.prop_conc_controlled_forms
public import SubdiffusiveProcess.Sobolev.CountableSmoothSources

@[expose] public section

/-! Actual analytic controls on a common subsequence of arbitrary cutoff indices.
These controls supply compactness, smooth approximations and local cutoffs;
they do not assert boundary identification or concentration. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Actual coercivity, mesh and cutoff estimates inhabit the complete analytic control structure. -/
theorem prop_conc_actual_controls
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr))
        (_hS : S.space = killedSobolevGraph (centeredCube z r hr)) (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
          (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hr)) ∧
        aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
          (fun n => cutoffCoefficient M H om (N (seq n))) t alpha := by
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_actual_coercivity_cutoffs
    d hd I Pin X W Cp Sob t alpha ht htd ha ha1
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS N
  filter_upwards [hs M Rm Sreg It H hIR hdelta z r hr S hS N] with om hom
  obtain ⟨seq, B, hseq, hB, hfrac, hcoer, hcell, hcuts⟩ := hom
  obtain ⟨D, hDc, hDd, hDs⟩ := SmoothSources.exists_countable_dense_smooth_submodule z r hr
  refine ⟨seq, hseq, ⟨{
    K := B + 1
    K_pos := by linarith only [hB]
    coercive := ?_
    interpolation := Interp
    sources := D
    sources_countable := hDc
    sources_dense := hDd
    sources_smooth := hDs
    mesh := ?_
    t := t
    t_lower := ht
    t_upper := htd
    cutoffs := hcuts }⟩, hcell⟩
  · intro n v
    refine ⟨hfrac v, (hcoer n v).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith only []) (responseForm_nonneg _ _ _)
  · exact prop_conc_mesh_approximate_control hd z r hr S hS
      (fun n => cutoffCoefficient M H om (N (seq n)))
      (fun n => cutoffCoefficient_continuous M H om (N (seq n)))
      (fun n x => cutoffCoefficient_pos M H om (N (seq n)) x)
      (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hr)
      (fun n => (cutoffPositiveCoefficient_representative M H om (N (seq n)) z hr).2.2.2)
      t alpha hcell

end
end SubdiffusiveProcess.Paper
