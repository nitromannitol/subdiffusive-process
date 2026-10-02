import SubdiffusiveProcess.Paper.prop_conc_mesh_bounds_with_moment
import SubdiffusiveProcess.Paper.prop_conc_coercivity_bank
import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family

/-! Actual fractional coercivity and local cutoffs on one common subsequence.
The extraction preserves a uniform moment majorant for a distinguished bank.
No independence or concentration conclusion is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- Actual smooth cell bounds produce the local cutoff families on the same fixed sequence. -/
theorem aux_prop_conc_actual_coercivity_cutoffs_with_moment_cutoffs
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ → ℕ) (t alpha : ℝ) (ht0 : 0 ≤ t) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
      (fun n => cutoffCoefficient M H om (N n)) t alpha) :
    aux_prop_conc_mesh_cutoff_family_Cutoffs z r hr S
      (fun n => cutoffPositiveCoefficient M H om (N n) z hr) t := by
  apply prop_conc_mesh_cutoff_family d hd z r hr S hS
    (fun n => cutoffCoefficient M H om (N n))
    (fun n => cutoffCoefficient_continuous M H om (N n))
    (fun n x => cutoffCoefficient_pos M H om (N n) x)
    (fun n => cutoffPositiveCoefficient M H om (N n) z hr)
    (fun n => (cutoffPositiveCoefficient_representative M H om (N n) z hr).2.2.2)
    t alpha ht0 ha
  exact hcell

/-- The actual mesh supplier at a fixed model and infrared field. -/
def aux_prop_conc_actual_coercivity_cutoffs_with_moment_Mesh
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (t alpha : ℝ) : Prop :=
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
        (fun n => cutoffCoefficient M H om (N (seq n))) t alpha

/-- The fractional coercivity bank at a fixed model and infrared field. -/
def aux_prop_conc_actual_coercivity_cutoffs_with_moment_Coercivity
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) : Prop :=
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∃ (K : ℕ → BilateralField d → ℝ) (C : ℝ≥0),
        (∀ n om, 0 ≤ K n om) ∧
        (∀ n, MemLp (K n) 1 (chaosSampleLaw M).toMeasure) ∧
        (∀ n, eLpNorm (K n) 1 (chaosSampleLaw M).toMeasure ≤ C) ∧
        ∀ n om (v : killedSobolevGraph (centeredCube z r hr)),
          ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
              (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
                (fun _ : Fin 1 => v.val.1)).toReal ^ 2 ≤
            K n om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om n z hr)
              v.val v.val

/-- Combine fixed-model mesh and coercivity suppliers without changing the selected subsequence. -/
theorem aux_prop_conc_actual_coercivity_cutoffs_with_moment_from_suppliers
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (ha : 0 < alpha)
    (hs : aux_prop_conc_actual_coercivity_cutoffs_with_moment_Mesh M H t alpha)
    (hc : aux_prop_conc_actual_coercivity_cutoffs_with_moment_Coercivity hd M H) :
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr))
        (_hS : S.space = killedSobolevGraph (centeredCube z r hr))
        (Qbank : ℕ → BilateralField d → ℝ) (p : ℝ), 1 ≤ p →
      ∀ Qbound : ℝ≥0,
        (∀ n, MemLp (Qbank n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) →
        (∀ n, eLpNorm (Qbank n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ Qbound) →
      ∀ N : ℕ → ℕ,
      ∃ Kbank : BilateralField d → ℝ, Measurable Kbank ∧ (∀ om, 0 ≤ Kbank om) ∧
        eLpNorm Kbank (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (2 * ((Qbound : ℝ) + 1)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∃ (seq : ℕ → ℕ) (B : ℝ), StrictMono seq ∧ (∀ n, |Qbank (N (seq n)) om| ≤ Kbank om) ∧ 0 ≤ B ∧
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
  intro z r hr S hS Qbank p hp Qbound hQmem hQnorm N
  obtain ⟨Kc, Cc, hKc, hKcm, hKcn, hcoer⟩ := hc z r hr
  obtain ⟨Kbank, hKm, hK0, hKn, hsamples⟩ :=
    hs z r hr Kc Cc hKcm hKcn
      Qbank p hp Qbound hQmem hQnorm N
  refine ⟨Kbank, hKm, hK0, hKn, hsamples.mono ?_⟩
  intro om hom
  obtain ⟨seq, hseq, hQbound, ⟨B, hB, hBK⟩, hcellAll⟩ := hom
  refine ⟨seq, B, hseq, hQbound, hB, ?_, ?_, hcellAll, ?_⟩
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
    exact aux_prop_conc_actual_coercivity_cutoffs_with_moment_cutoffs hd z hr S hS M H om
      (fun n => N (seq n)) t alpha ht0 ha hcellAll


/-- The actual cutoff coefficients admit all local cutoff families along one further subsequence. -/
theorem prop_conc_actual_coercivity_cutoffs_with_moment
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
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr))
        (_hS : S.space = killedSobolevGraph (centeredCube z r hr))
        (Qbank : ℕ → BilateralField d → ℝ) (p : ℝ), 1 ≤ p →
      ∀ Qbound : ℝ≥0,
        (∀ n, MemLp (Qbank n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) →
        (∀ n, eLpNorm (Qbank n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ Qbound) →
      ∀ N : ℕ → ℕ,
      ∃ Kbank : BilateralField d → ℝ, Measurable Kbank ∧ (∀ om, 0 ≤ Kbank om) ∧
        eLpNorm Kbank (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (2 * ((Qbound : ℝ) + 1)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∃ (seq : ℕ → ℕ) (B : ℝ), StrictMono seq ∧ (∀ n, |Qbank (N (seq n)) om| ≤ Kbank om) ∧ 0 ≤ B ∧
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
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_mesh_bounds_with_moment d hd I Pin X W Cp Sob
    t alpha ht htd ha ha1
  obtain ⟨deltaC, hdeltaC, hc⟩ := prop_conc_coercivity_bank d hd I Pin Sob
  refine ⟨min delta0 deltaC, lt_min hdelta0 hdeltaC, ?_⟩
  intro M Rm Sreg It H hIR hdelta
  exact aux_prop_conc_actual_coercivity_cutoffs_with_moment_from_suppliers hd Sob M H t alpha ht ha
    (hs M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)))
    (hc M Rm H hIR (hdelta.trans (min_le_right _ _)))

end
end Paper
