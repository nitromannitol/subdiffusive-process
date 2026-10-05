module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.infrared_characterization_local_lipschitz_majorant

@[expose] public section

/-!
Reduction of the general-infrared cutoff coefficient to a constant multiple of the zero-infrared
one, up to a cell-oscillation `exp(±D_q)` error. `cutoffCoefficient`
factors EXACTLY as `exp(H omega x) * cutoffCoefficient M 0 omega N x` (an identity, no estimate
needed); the oscillation of `H omega` on a cell is controlled by
`SubdiffusiveProcess.Paper.infrared_characterization_local_lipschitz_majorant`'s local Lipschitz majorant `G`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Exact factorization: the cutoff coefficient with infrared field `H` is `exp(H omega x)` times
the zero-infrared cutoff coefficient (`H ≡ 0`). No estimate, just unfolding `cutoffCoefficient`. -/
theorem aux_infrared_cutoff_coefficient_reduction_factorization {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) :
    cutoffCoefficient M H omega N x =
      Real.exp (H omega x) * cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x := by
  unfold cutoffCoefficient cutoffPotential
  simp only [ContinuousMap.zero_apply, zero_add]
  rw [show H omega x + (∑ j ∈ Finset.range (N + 1), omega (-Int.ofNat j) x) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
      H omega x + ((∑ j ∈ Finset.range (N + 1), omega (-Int.ofNat j) x) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) by ring,
    Real.exp_add]
  ring

/-- Pointwise sandwich: on a cell of radius `r` centred at `z`, the cutoff coefficient with
infrared field `H` lies within `exp(±(G omega * r))` of `exp(H omega z)` times the zero-infrared
cutoff coefficient, where `G` is `H`'s local Lipschitz majorant on the cell
(`infrared_characterization_local_lipschitz_majorant`). -/
theorem infrared_cutoff_coefficient_reduction {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        ∃ G : BilateralField d → ℝ, (∀ om, 0 ≤ G om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            ∀ (N : ℕ) (x : SpatialCoordinates d),
              x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              (Real.exp (-(G om * r)) *
                  (Real.exp (H om z) * cutoffCoefficient M (fun _ => 0) om N x) ≤
                cutoffCoefficient M H om N x ∧
              cutoffCoefficient M H om N x ≤
                Real.exp (G om * r) *
                  (Real.exp (H om z) * cutoffCoefficient M (fun _ => 0) om N x))) ∧
          MemLp G (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure := by
  obtain ⟨C, hC, hmaj⟩ := infrared_characterization_local_lipschitz_majorant d hd z r hr 1 le_rfl
  refine ⟨C, hC, ?_⟩
  intro M H hInfrared
  obtain ⟨G, hGnn, hGlip, hGmem, _⟩ := hmaj M H hInfrared
  refine ⟨G, hGnn, ?_, hGmem⟩
  filter_upwards [hGlip] with om hom
  intro N x hx
  rw [aux_infrared_cutoff_coefficient_reduction_factorization M H om N x]
  have hzmem : z ∈ (closedCube z r hr : Set (SpatialCoordinates d)) :=
    Metric.mem_closedBall_self (by linarith)
  have hosc : |H om x - H om z| ≤ G om * r := by
    have hd := hom x z hx hzmem
    have hdxz : dist x z ≤ r := (Metric.mem_closedBall.mp hx).trans (by linarith)
    calc |H om x - H om z| ≤ G om * dist x z := hd
      _ ≤ G om * r := mul_le_mul_of_nonneg_left hdxz (hGnn om)
  have hpos : 0 < cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x :=
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  set c0 := cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x with hc0
  have hlow : -(G om * r) + H om z ≤ H om x := by linarith [(abs_le.mp hosc).1]
  have hhigh : H om x ≤ G om * r + H om z := by linarith [(abs_le.mp hosc).2]
  constructor
  · calc Real.exp (-(G om * r)) * (Real.exp (H om z) * c0)
        = Real.exp (-(G om * r) + H om z) * c0 := by rw [Real.exp_add]; ring
      _ ≤ Real.exp (H om x) * c0 := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hlow) hpos.le
  · calc Real.exp (H om x) * c0
        ≤ Real.exp (G om * r + H om z) * c0 :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hhigh) hpos.le
      _ = Real.exp (G om * r) * (Real.exp (H om z) * c0) := by rw [Real.exp_add]; ring

end SubdiffusiveProcess.Paper
