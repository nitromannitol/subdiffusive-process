module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_uniform_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_uniform_factor_envelope
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_shifted_bank
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_factor_product
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_envelope_exponential
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set Metric SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The uniform factor times one plus a shifted unit-bank coordinate: the
measurable, `N`-independent test variable of one retained cell. -/
theorem aux_lem_as_coarse_shallow_grid_zero_ir_uniform_factor_bank_product
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q eta : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ B0 delta0 : ℝ, 0 < B0 ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (C : ℝ), 0 ≤ C →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        Paper.in_responses d M →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let G0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω x => ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
        let R0 : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let oscSet0 : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R0 k),
            ∃ x' ∈ Metric.closedBall y (3 * R0 k),
              v = |G0 k ω x - G0 k ω x'|}
        let osc0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => sSup (oscSet0 k ω y)
        let D0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => Real.exp (osc0 k ω y) *
            Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
              (Real.exp (G0 k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
                Real.exp (-(G0 k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)))
        ∀ (k : ℕ) (Q : TriadicCube d),
          Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) →
          ∀ Z : BilateralField d → ℝ,
            AEStronglyMeasurable Z (chaosSampleLaw M).toMeasure →
            eLpNorm Z (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal C →
            AEStronglyMeasurable (fun ω => D0 k ω (cubeCenter Q) *
              (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)))
              (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun ω => D0 k ω (cubeCenter Q) *
              (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  obtain ⟨B0, delta0, hB0, hd0, hd01, hD⟩ :=
    lem_as_coarse_shallow_grid_zero_ir_uniform_factor_moment_rate d hd (2 * q) eta
      (by linarith) heta
  refine ⟨B0, delta0, hB0, hd0, hd01, ?_⟩
  intro C hC M Rm H hH hMd G0 R0 oscSet0 osc0 D0 k Q hQ Z hZ hZbound
  have hDk := hD M Rm H hH hMd k Q hQ
  have hshiftmeas : AEStronglyMeasurable
      (fun ω => Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω))
      (chaosSampleLaw M).toMeasure := by
    change AEStronglyMeasurable
      (Z ∘ aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q)) _
    exact hZ.comp_measurePreserving
      (lem_as_coarse_shallow_grid_scale_shift M k (cubeCenter Q))
  have hshiftbound := lem_as_coarse_shallow_grid_shifted_bank M k (cubeCenter Q)
    Z (ENNReal.ofReal (2 * q)) (ENNReal.ofReal C) hZ hZbound
  have hprod := lem_as_coarse_shallow_grid_factor_product
    (chaosSampleLaw M).toMeasure q hq hDk.1 hshiftmeas
    (ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ)))) (ENNReal.ofReal C)
    hDk.2 hshiftbound
  refine ⟨hDk.1.mul (aestronglyMeasurable_const.add hshiftmeas), ?_⟩
  have hpow : 0 ≤ (3 : ℝ) ^ (eta * (k : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    eLpNorm (fun ω => D0 k ω (cubeCenter Q) *
        (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ))) * (1 + ENNReal.ofReal C) := hprod
    _ = ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hC,
        ← ENNReal.ofReal_mul (mul_nonneg hB0.le hpow)]
      congr 1
      ring

/-- **Almost-sure uniform-cutoff envelope.** For any finite bank of unit-scale
variables with a common `L^{2q}` bound, one random constant controls every
actual shallow-cell factor times one plus its shifted bank coordinate,
simultaneously for all cutoffs `N ≥ k`, all depths `k`, all descendants of
`originCube d 0` and all bank indices. The disorder threshold depends only on
`d, q, eta`. -/
theorem lem_as_coarse_shallow_grid_zero_ir_uniform_factor_envelope
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ι : Type*) [Fintype ι]
    (q eta rho : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) (hetarho : eta < rho)
    (hrate : (d : ℝ) < q * (rho - eta)) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (C : ℝ), 0 ≤ C →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        Paper.in_responses d M →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let G0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω x => ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
        let s0 : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k ω x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G0 k ω x - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        let R0 : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let oscSet0 : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R0 k),
            ∃ x' ∈ Metric.closedBall y (3 * R0 k),
              v = |G0 k ω x - G0 k ω x'|}
        let osc0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => sSup (oscSet0 k ω y)
        ∀ Z : ι → BilateralField d → ℝ,
          (∀ b, AEStronglyMeasurable (Z b) (chaosSampleLaw M).toMeasure) →
          (∀ b, eLpNorm (Z b) (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal C) →
          ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 1 ≤ K ∧
            ∀ (N k : ℕ), k ≤ N → ∀ Q : TriadicCube d,
              Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) → ∀ b : ι,
              |Real.exp (osc0 k ω (cubeCenter Q)) *
                  (s0 N k ω (cubeCenter Q) + (s0 N k ω (cubeCenter Q))⁻¹) *
                (1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω))| ≤
                K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  obtain ⟨B0, delta0, hB0, hd0, hd01, hprod⟩ :=
    aux_lem_as_coarse_shallow_grid_zero_ir_uniform_factor_bank_product d hd q eta hq heta
  refine ⟨delta0, hd0, hd01, ?_⟩
  intro C hC M Rm H hH hMd G0 s0 R0 oscSet0 osc0 Z hZ hZbound
  have hdom := aux_lem_as_coarse_shallow_grid_uniform_factor_dominates d M Rm (fun _ => 0)
  have hP := hprod C hC M Rm H hH hMd
  let D0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
    fun k ω y => Real.exp (osc0 k ω y) *
      Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
        (Real.exp (G0 k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
          Real.exp (-(G0 k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)))
  let Gset : ℕ → Finset (TriadicCube d × ι) := fun k =>
    descendantsAtScale (originCube d 0) (-(k : ℤ)) ×ˢ (Finset.univ : Finset ι)
  let X : ℕ → TriadicCube d × ι → BilateralField d → ℝ := fun k i ω =>
    D0 k ω (cubeCenter i.1) *
      (1 + Z i.2 (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter i.1) ω))
  have hcard : ∀ k : ℕ,
      ((Gset k).card : ℝ) ≤ (Fintype.card ι : ℝ) * (3 : ℝ) ^ ((d : ℝ) * (k : ℝ)) := by
    intro k
    have hdepth :
        (descendantsAtScale (originCube d 0) (-(k : ℤ))).card = (3 ^ d) ^ k := by
      rw [descendantsAtScale_eq_descendantsAtDepth (originCube d 0)
        (by simp [originCube])]
      convert descendantsAtDepth_card (originCube d 0) k using 1; simp [originCube]
    have hpow : (((3 ^ d) ^ k : ℕ) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * (k : ℝ)) := by
      calc
        (((3 ^ d) ^ k : ℕ) : ℝ) = ((3 : ℝ) ^ d) ^ k := by norm_cast
        _ = ((3 : ℝ) ^ (d : ℝ)) ^ (k : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast]
        _ = (3 : ℝ) ^ ((d : ℝ) * (k : ℝ)) := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hG : (Gset k).card = (3 ^ d) ^ k * Fintype.card ι := by
      simp only [Gset, Finset.card_product, hdepth, Finset.card_univ]
    rw [hG, Nat.cast_mul, hpow, mul_comm]
  have hX : ∀ k i, i ∈ Gset k →
      AEStronglyMeasurable (X k i) (chaosSampleLaw M).toMeasure := by
    intro k i hi
    exact (hP k i.1 (Finset.mem_product.mp hi).1 (Z i.2) (hZ i.2) (hZbound i.2)).1
  have hLp : ∀ k i, i ∈ Gset k →
      eLpNorm (X k i) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
    intro k i hi
    exact (hP k i.1 (Finset.mem_product.mp hi).1 (Z i.2) (hZ i.2) (hZbound i.2)).2
  have henv := lem_as_coarse_shallow_grid_envelope_exponential
    (chaosSampleLaw M).toMeasure Gset X (d : ℝ) q (B0 * (1 + C))
    (Fintype.card ι : ℝ) eta rho (by linarith) (mul_nonneg hB0.le (by linarith))
    (Nat.cast_nonneg _) hetarho hrate hcard hX hLp
  filter_upwards [henv] with ω hω
  obtain ⟨K, hK1, hK⟩ := hω
  refine ⟨K, hK1, ?_⟩
  intro N k hkN Q hQ b
  have hmem : (Q, b) ∈ Gset k := Finset.mem_product.mpr ⟨hQ, Finset.mem_univ b⟩
  have hXb : |X k (Q, b) ω| ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) := hK k (Q, b) hmem
  have hdom0 := hdom N k hkN ω (cubeCenter Q)
  have hX0 : 0 ≤ Real.exp (osc0 k ω (cubeCenter Q)) *
      (s0 N k ω (cubeCenter Q) + (s0 N k ω (cubeCenter Q))⁻¹) := by
    simpa only [ContinuousMap.zero_apply, zero_add, G0, s0, R0, oscSet0, osc0]
      using hdom0.1
  have hXD : Real.exp (osc0 k ω (cubeCenter Q)) *
      (s0 N k ω (cubeCenter Q) + (s0 N k ω (cubeCenter Q))⁻¹) ≤
      D0 k ω (cubeCenter Q) := by
    simpa only [ContinuousMap.zero_apply, zero_add, G0, s0, R0, oscSet0, osc0,
      D0, mul_assoc] using hdom0.2.1
  have hD0 : 0 ≤ D0 k ω (cubeCenter Q) := hX0.trans hXD
  calc
    |Real.exp (osc0 k ω (cubeCenter Q)) *
          (s0 N k ω (cubeCenter Q) + (s0 N k ω (cubeCenter Q))⁻¹) *
        (1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω))| =
      Real.exp (osc0 k ω (cubeCenter Q)) *
          (s0 N k ω (cubeCenter Q) + (s0 N k ω (cubeCenter Q))⁻¹) *
        |1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)| := by
      rw [abs_mul, abs_of_nonneg hX0]
    _ ≤ D0 k ω (cubeCenter Q) *
        |1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)| :=
      mul_le_mul_of_nonneg_right hXD (abs_nonneg _)
    _ = |X k (Q, b) ω| := by
      change _ = |D0 k ω (cubeCenter Q) *
        (1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω))|
      rw [abs_mul, abs_of_nonneg hD0]
    _ ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) := hXb


end Paper


