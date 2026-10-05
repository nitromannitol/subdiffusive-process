module

public import SubdiffusiveProcess.Paper.prop_conc_native_cell_bounds_with_bank
public import SubdiffusiveProcess.Paper.prop_conc_coercivity_bank
public import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family

@[expose] public section

/-! Actual fractional coercivity and local cutoffs on one common subsequence.
All bounds are constructed from moment banks before the samplewise extraction.
No independence or concentration conclusion is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- The actual cutoff coefficients admit all local cutoff families along one further subsequence. -/
theorem prop_conc_actual_coercivity_cutoffs
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t alpha : ℝ)
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
      ∃ (seq : ℕ → ℕ) (B : ℝ), StrictMono seq ∧ 0 ≤ B ∧
        (∀ v : S.space,
          cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
            (fun _ : Fin 1 => v.val.1) < ⊤) ∧
        (∀ n (v : S.space),
          ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
              (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
                (fun _ : Fin 1 => v.val.1)).toReal ^ 2 ≤
            B * responseForm S (cutoffPositiveCoefficient M H om (N (seq n)) z hr) v v) ∧
        aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
          (fun n => cutoffCoefficient M H om (N (seq n))) t alpha ∧
        aux_prop_conc_mesh_cutoff_family_Cutoffs z r hr S
          (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hr) t := by
  classical
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_native_cell_bounds_with_bank d hd I Pin X W Cp Sob
    t alpha ht htd ha ha1
  obtain ⟨deltaC, hdeltaC, hc⟩ := prop_conc_coercivity_bank d hd I Pin Sob
  refine ⟨min delta0 deltaC, lt_min hdelta0 hdeltaC, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS N
  obtain ⟨Kc, Cc, hKc, hKcm, hKcn, hcoer⟩ := hc M Rm H hIR
    (hdelta.trans (min_le_right _ _)) z r hr
  let Idx := (J : ℕ) × OddGridIndex d (triadicHalf J)
  let cz : Idx → SpatialCoordinates d := fun i => oddGridCenter z r (triadicHalf i.1) i.2
  let cr : Idx → ℝ := fun i => r / (2 * (triadicHalf i.1 : ℝ) + 1)
  have chr : ∀ i, 0 < cr i := fun _ => div_pos hr (by positivity)
  filter_upwards [hs M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) Idx cz cr chr Kc Cc hKcm hKcn N] with om hom
  obtain ⟨seq, hseq, ⟨B, hB, hBK⟩, hcells⟩ := hom
  have hcellAll : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
      (fun n => cutoffCoefficient M H om (N (seq n))) t alpha := by
    intro J hside theta htheta thetaH hthetaH k
    exact hcells ⟨J, k⟩ ((lane2_cell_side_eq r J).le.trans hside) theta
      (htheta.of_le (WithTop.coe_le_coe.mpr le_top))
      (thetaH.restrict (oddGridCell z r hr (triadicHalf J) k).isOpen
        (oddGridCell_subset z hr (triadicHalf J) k)) hthetaH
  refine ⟨seq, B, hseq, hB, ?_, ?_, hcellAll, ?_⟩
  · intro v
    exact Sob.h1_fractional_finite z r hr
      ⟨v.val, killedSobolevGraph_le_weakSobolevGraph (hS ▸ v.property)⟩
  · intro n v
    have hc0 := hcoer (N (seq n)) om ⟨v.val, hS ▸ v.property⟩
    have hle : Kc (N (seq n)) om ≤ B := (le_abs_self _).trans (hBK n)
    exact hc0.trans (mul_le_mul_of_nonneg_right hle (sobolevCoefficientForm_nonneg _ _))

  · have ht0 : 0 ≤ t := by
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith only [hdR, ht]
    apply prop_conc_mesh_cutoff_family d hd z r hr S hS
      (fun n => cutoffCoefficient M H om (N (seq n)))
      (fun n => cutoffCoefficient_continuous M H om (N (seq n)))
      (fun n x => cutoffCoefficient_pos M H om (N (seq n)) x)
      (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hr)
      (fun n => (cutoffPositiveCoefficient_representative M H om (N (seq n)) z hr).2.2.2)
      t alpha ht0 ha
    exact hcellAll

end
end SubdiffusiveProcess.Paper
