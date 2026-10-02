import SubdiffusiveProcess.Paper.prop_conc_native_cell_bounds_with_moment
import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family

/-! Actual mesh controls preserving a distinguished moment majorant.
The geometric cell catalogue is fixed before the samplewise common extraction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff
namespace Paper
noncomputable section

/-- The actual nested mesh catalogue has common cell controls and a uniform moment majorant. -/
theorem prop_conc_mesh_bounds_with_moment
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∀ (Bbank : ℕ → BilateralField d → ℝ) (Cbank : ℝ≥0),
        (∀ n, MemLp (Bbank n) 1 (chaosSampleLaw M).toMeasure) →
        (∀ n, eLpNorm (Bbank n) 1 (chaosSampleLaw M).toMeasure ≤ Cbank) →
      ∀ (Qbank : ℕ → BilateralField d → ℝ) (p : ℝ), 1 ≤ p →
      ∀ Qbound : ℝ≥0,
        (∀ n, MemLp (Qbank n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) →
        (∀ n, eLpNorm (Qbank n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ Qbound) →
      ∀ N : ℕ → ℕ,
      ∃ Kbank : BilateralField d → ℝ, Measurable Kbank ∧ (∀ om, 0 ≤ Kbank om) ∧
        eLpNorm Kbank (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (2 * ((Qbound : ℝ) + 1)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        (∀ n, |Qbank (N (seq n)) om| ≤ Kbank om) ∧
        (∃ B : ℝ, 0 ≤ B ∧ ∀ n, |Bbank (N (seq n)) om| ≤ B) ∧
      aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
        (fun n => cutoffCoefficient M H om (N (seq n))) t alpha := by
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_native_cell_bounds_with_moment d hd I Pin X W Cp Sob
    t alpha ht htd ha ha1
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr Bbank Cbank hBmem hBnorm
    Qbank p hp Qbound hQmem hQnorm N
  let Idx := (J : ℕ) × OddGridIndex d (triadicHalf J)
  let cz : Idx → SpatialCoordinates d := fun i => oddGridCenter z r (triadicHalf i.1) i.2
  let cr : Idx → ℝ := fun i => r / (2 * (triadicHalf i.1 : ℝ) + 1)
  have chr : ∀ i, 0 < cr i := fun _ => div_pos hr (by positivity)
  obtain ⟨Kbank, hKm, hK0, hKn, hsamples⟩ :=
    hs M Rm Sreg It H hIR hdelta Idx cz cr chr Bbank Cbank hBmem hBnorm
      Qbank p hp Qbound hQmem hQnorm N
  refine ⟨Kbank, hKm, hK0, hKn, hsamples.mono ?_⟩
  intro om hom
  obtain ⟨seq, hseq, hQbound, hBbound, hcells⟩ := hom
  refine ⟨seq, hseq, hQbound, hBbound, ?_⟩
  intro J hside theta htheta thetaH hthetaH k
  exact hcells ⟨J, k⟩ ((lane2_cell_side_eq r J).le.trans hside) theta
    (htheta.of_le (WithTop.coe_le_coe.mpr le_top))
    (thetaH.restrict (oddGridCell z r hr (triadicHalf J) k).isOpen
      (oddGridCell_subset z hr (triadicHalf J) k)) hthetaH

end
end Paper
