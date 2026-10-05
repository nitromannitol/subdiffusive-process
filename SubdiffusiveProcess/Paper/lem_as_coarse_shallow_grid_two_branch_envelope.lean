module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_uniform_factor_envelope
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_uniform_factor_envelope

@[expose] public section

open MeasureTheory Set Metric SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The exact physical factor of either infrared branch at one retained cell. -/
def aux_lem_as_coarse_shallow_grid_two_branch_factor {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (withIR : Bool) (N k : ℕ) (ω : BilateralField d)
    (y : SpatialCoordinates d) : ℝ :=
  let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
    if withIR then H else fun _ => 0
  let G : SpatialCoordinates d → ℝ :=
    fun x => Hc ω x + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
  let R : ℝ := (3 : ℝ)^(-(k : ℤ)) / 2
  let osc : ℝ := sSup {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R),
    ∃ x' ∈ Metric.closedBall y (3 * R), v = |G x - G x'|}
  let s : ℝ :=
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp (G y - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
  Real.exp osc * (s + s⁻¹)

/-- One almost-sure random constant works for both infrared choices, every
cutoff, every retained depth, and every finite response-bank coordinate. -/
theorem lem_as_coarse_shallow_grid_two_branch_envelope
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ι : Type*) [Fintype ι]
    (q eta rho : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) (hetarho : eta < rho)
    (hrate : (d : ℝ) < q * (rho - eta)) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (C : ℝ), 0 ≤ C →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
        _root_.SubdiffusiveProcess.Paper.in_responses d M →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ Z : ι → BilateralField d → ℝ,
          (∀ b, AEStronglyMeasurable (Z b) (chaosSampleLaw M).toMeasure) →
          (∀ b, eLpNorm (Z b) (ENNReal.ofReal (2 * q))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C) →
          ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 1 ≤ K ∧
            ∀ (withIR : Bool) (N k : ℕ), k ≤ N →
              ∀ Q : TriadicCube d,
                Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) →
              ∀ b : ι,
                |aux_lem_as_coarse_shallow_grid_two_branch_factor M H withIR
                    N k ω (cubeCenter Q) *
                  (1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k
                    (cubeCenter Q) ω))| ≤
                  K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  obtain ⟨δF, hδF, hδF1, hF⟩ :=
    lem_as_coarse_shallow_grid_uniform_factor_envelope d hd ι q eta rho hq heta hetarho hrate
  obtain ⟨δ0, hδ0, hδ01, h0⟩ :=
    lem_as_coarse_shallow_grid_zero_ir_uniform_factor_envelope d hd ι q eta rho hq heta hetarho hrate
  refine ⟨min δF δ0, lt_min hδF hδ0, (min_le_left _ _).trans hδF1, ?_⟩
  intro C hC M Rm H hH hMd Z hZ hZbound
  have hMdF : M.delta ≤ δF := hMd.trans (min_le_left _ _)
  have hMd0 : M.delta ≤ δ0 := hMd.trans (min_le_right _ _)
  have hFE := hF C hC M Rm H hH hMdF Z hZ hZbound
  have h0E := h0 C hC M Rm H hH hMd0 Z hZ hZbound
  filter_upwards [hFE, h0E] with ω hωF hω0
  obtain ⟨KF, hKF, hFbound⟩ := hωF
  obtain ⟨K0, hK0, h0bound⟩ := hω0
  refine ⟨max KF K0, le_trans hKF (le_max_left _ _), ?_⟩
  intro withIR N k hkN Q hQ b
  cases withIR with
  | false =>
      have hb := h0bound N k hkN Q hQ b
      simpa [aux_lem_as_coarse_shallow_grid_two_branch_factor] using
        hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (by norm_num) _))
  | true =>
      have hb := hFbound N k hkN Q hQ b
      simpa [aux_lem_as_coarse_shallow_grid_two_branch_factor] using
        hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (by norm_num) _))

end SubdiffusiveProcess.Paper

