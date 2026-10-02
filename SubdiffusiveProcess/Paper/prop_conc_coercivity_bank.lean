import SubdiffusiveProcess.Probability.FiniteMomentBank
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.inputs_classical_fractional_coercivity_patching
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative

/-! Actual fractional coercivity on arbitrary bounded cubes, with a uniform L1 bank.
The deterministic finite-cover constant may depend on the cube. This supplies
compactness for R1, and does not supply scale-uniform concentration constants. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- Actual cutoff energies dominate the unnormalized fractional norm with an L1-bounded coefficient bank on every fixed cube. -/
theorem prop_conc_coercivity_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (Sob : SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
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
              v.val v.val := by
  classical
  obtain ⟨delta, hdelta, hc⟩ := aux_lem_coercivity_compat d hd I Pin Sob
  refine ⟨delta 1, hdelta 1 le_rfl, ?_⟩
  intro M Rm H hIR hdel z r hr
  obtain ⟨centers, A, hA, hpatch⟩ := inputs_classical_fractional_coercivity_patching d hd z r hr
  choose K hK hmom using fun i : centers => hc M Rm H hIR i.val 1 one_pos le_rfl
  choose C hmem hnorm using fun i : centers => hmom i 1 le_rfl hdel
  obtain ⟨B, CB, hB, hBm, hBn, hKB⟩ :=
    SubdiffusiveProcess.Probability.exists_finite_L1_majorant (chaosSampleLaw M).toMeasure
      K (fun i => (C i).toNNReal)
      (fun i n => by simpa only [ENNReal.ofReal_one] using hmem i n)
      (fun i n => by simpa only [ENNReal.ofReal_one, ENNReal.coe_toNNReal] using hnorm i n)
  refine ⟨fun n om => A * B n om, A.toNNReal * CB,
    (fun n om => mul_nonneg hA.le (hB n om)),
    (fun n => (hBm n).const_mul A), ?_, ?_⟩
  · intro n
    calc
      _ ≤ ‖A‖ₑ * eLpNorm (B n) 1 (chaosSampleLaw M).toMeasure := eLpNorm_const_smul_le
      _ ≤ ‖A‖ₑ * CB := mul_le_mul' le_rfl (hBn n)
      _ = _ := by rw [Real.enorm_eq_ofReal hA.le, ENNReal.coe_mul]; rfl
  · intro n om v
    apply hpatch (cutoffCoefficient M H om n) (cutoffCoefficient_continuous M H om n)
      (cutoffCoefficient_pos M H om n) (cutoffPositiveCoefficient M H om n z hr)
      (cutoffPositiveCoefficient_representative M H om n z hr).2.2.2
      (fun i => cutoffPositiveCoefficient M H om n i.val one_pos)
      (fun i => (cutoffPositiveCoefficient_representative M H om n i.val one_pos).2.2.2)
      (B n om) (hB n om) _ v
    intro i w
    apply ((hK i n om).2 w).2.trans
    apply mul_le_mul_of_nonneg_right _ (sobolevCoefficientForm_nonneg _ _)
    exact hKB i n om

end
end Paper
