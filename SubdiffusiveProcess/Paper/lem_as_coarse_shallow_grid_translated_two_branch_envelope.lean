module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_translated_zero_ir_bank_product
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_two_branch_envelope
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_factor_pointwise
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_uniform_factor_envelope

@[expose] public section

open MeasureTheory Set Metric SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-! ## C. Removing the infrared field pointwise -/

/-- The infrared-free layers `G0_k ω` as a continuous map. -/
def aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0c {d : ℕ} (k : ℕ) (ω : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ⟨aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0 k ω, continuous_finset_sum _ (fun j _ => (ω (-(j : ℤ))).continuous)⟩

/-- Pure deterministic removal of a continuous infrared field `h` from the
cell factor, at the cost of `exp (3 ‖h‖_{ball})`. -/
theorem aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_remove_ir {d : ℕ} (f0 h : C(SpatialCoordinates d, ℝ))
    (y : SpatialCoordinates d) (r : ℝ) (hr : 0 ≤ r) (c t : ℝ) (hc : 0 < c) :
    Real.exp (sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r, ∃ x' ∈ Metric.closedBall y r,
        v = |(h x + f0 x) - (h x' + f0 x')|}) *
      (c * Real.exp ((h y + f0 y) - t) + (c * Real.exp ((h y + f0 y) - t))⁻¹) ≤
    Real.exp (sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r, ∃ x' ∈ Metric.closedBall y r,
        v = |f0 x - f0 x'|}) *
      (c * Real.exp (f0 y - t) + (c * Real.exp (f0 y - t))⁻¹) *
      Real.exp (3 * ‖h.restrict (Metric.closedBall y r : Set (SpatialCoordinates d))‖) := by
  have hs : 0 < c * Real.exp ((h y + f0 y) - t) := mul_pos hc (Real.exp_pos _)
  have hpt := lem_as_coarse_shallow_grid_zero_ir_factor_pointwise (h + f0) (-h) y r hr
    (Metric.mem_closedBall_self hr) _ hs
  dsimp only at hpt
  have hcancel : h + f0 + -h = f0 := by abel
  rw [hcancel] at hpt
  have hscal : Real.exp ((-h) y) * (c * Real.exp ((h y + f0 y) - t)) =
      c * Real.exp (f0 y - t) := by
    rw [ContinuousMap.neg_apply, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have hnorm : ‖(-h).restrict (Metric.closedBall y r : Set (SpatialCoordinates d))‖ =
      ‖h.restrict (Metric.closedBall y r : Set (SpatialCoordinates d))‖ := by
    have : (-h).restrict (Metric.closedBall y r : Set (SpatialCoordinates d)) =
        -(h.restrict (Metric.closedBall y r : Set (SpatialCoordinates d))) := by
      ext x
      rfl
    rw [this, norm_neg]
  rw [hscal, hnorm] at hpt
  exact hpt

/-! ## D. The two exact branch factors against `D0` -/

/-- The infrared-free branch factor is the `H = 0` factor on the same cell. -/
theorem aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_two_branch_false_eq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N k : ℕ)
    (ω : BilateralField d) (y : SpatialCoordinates d) :
    aux_lem_as_coarse_shallow_grid_two_branch_factor M H false N k ω y =
      Real.exp (aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_osc0 k ω y) *
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
            Real.exp (aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0 k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
            Real.exp (aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0 k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))⁻¹) := by
  simp only [aux_lem_as_coarse_shallow_grid_two_branch_factor, Bool.false_eq_true, if_false,
    ContinuousMap.zero_apply, zero_add]
  rfl

/-- The infrared branch factor, unfolded. -/
theorem aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_two_branch_true_eq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N k : ℕ)
    (ω : BilateralField d) (y : SpatialCoordinates d) :
    aux_lem_as_coarse_shallow_grid_two_branch_factor M H true N k ω y =
      Real.exp (sSup {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
          ∃ x' ∈ Metric.closedBall y (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
          v = |(H ω x + aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0c k ω x) - (H ω x' + aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0c k ω x')|}) *
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
            Real.exp ((H ω y + aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0c k ω y) -
              (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
            Real.exp ((H ω y + aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0c k ω y) -
              (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))⁻¹) := by
  simp only [aux_lem_as_coarse_shallow_grid_two_branch_factor, if_true]
  rfl

/-- The infrared-free branch factor is at most `D0` (uniformly in `N ≥ k`). -/
theorem aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_two_branch_false_le_D0 {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N k : ℕ) (hkN : k ≤ N)
    (ω : BilateralField d) (y : SpatialCoordinates d) :
    0 ≤ aux_lem_as_coarse_shallow_grid_two_branch_factor M H false N k ω y ∧
      aux_lem_as_coarse_shallow_grid_two_branch_factor M H false N k ω y ≤
        aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M k ω y := by
  have hdom := aux_lem_as_coarse_shallow_grid_uniform_factor_dominates d M Rm (fun _ => 0)
    N k hkN ω y
  rw [aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_two_branch_false_eq]
  simp only [ContinuousMap.zero_apply, zero_add] at hdom
  refine ⟨hdom.1, ?_⟩
  have h2 := hdom.2.1
  unfold aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0
  rw [mul_assoc]
  exact h2

/-- The infrared branch factor is at most the infrared-free factor times one
compact exponential of `H`. -/
theorem aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_two_branch_true_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N k : ℕ)
    (ω : BilateralField d) (y : SpatialCoordinates d) :
    aux_lem_as_coarse_shallow_grid_two_branch_factor M H true N k ω y ≤
      aux_lem_as_coarse_shallow_grid_two_branch_factor M H false N k ω y *
        Real.exp (3 * ‖(H ω).restrict (Metric.closedBall y (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)) :
          Set (SpatialCoordinates d))‖) := by
  rw [aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_two_branch_true_eq, aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_two_branch_false_eq]
  have hc : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
    div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)
  exact aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_remove_ir (aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0c k ω) (H ω) y _ (by positivity) _ _ hc

/-! ## E. The almost-sure two-branch envelope on a translated centre family -/

theorem aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_ball_subset {d : ℕ} (k : ℕ) (y z : SpatialCoordinates d) (L : ℝ)
    (hyz : dist y z ≤ L) :
    Metric.closedBall y (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)) ⊆
      Metric.closedBall z (L + 3 / 2) := by
  have hr_le : (3 : ℝ) ^ (-(k : ℤ)) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by omega))
  intro x hx
  rw [Metric.mem_closedBall] at hx ⊢
  have := dist_triangle x y z
  nlinarith

/-- **Translated two-branch envelope.** The disorder threshold depends only on
`d, q, η, ρ` (not on the model, the root or the centre family). For any finite
centre family `cen n` of size `≤ Cc 3^{dn}` inside a fixed ball `B(z, L)`, one
random constant bounds both exact branch factors times one plus any shifted
bank coordinate, simultaneously for all cutoffs `N ≥ n`, all depths `n` and all
centres of `cen n`. The random constant is the infrared-free envelope times
`exp (3 ‖H ω‖_{B(z, L + 3/2)})`. -/
theorem lem_as_coarse_shallow_grid_translated_two_branch_envelope
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
        ∀ Z : ι → BilateralField d → ℝ,
          (∀ b, AEStronglyMeasurable (Z b) (chaosSampleLaw M).toMeasure) →
          (∀ b, eLpNorm (Z b) (ENNReal.ofReal (2 * q))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C) →
        ∀ (cen : ℕ → Finset (SpatialCoordinates d)) (Cc : ℝ),
          (∀ n : ℕ, ((cen n).card : ℝ) ≤ Cc * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ))) →
        ∀ (z : SpatialCoordinates d) (L : ℝ),
          (∀ n : ℕ, ∀ y ∈ cen n, dist y z ≤ L) →
          ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 1 ≤ K ∧
            ∀ (withIR : Bool) (N n : ℕ), n ≤ N →
              ∀ y ∈ cen n, ∀ b : ι,
                |aux_lem_as_coarse_shallow_grid_two_branch_factor M H withIR N n ω y *
                  (1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift n y ω))| ≤
                  K * (3 : ℝ) ^ (rho * (n : ℝ)) := by
  obtain ⟨B0, delta0, hB0, hd0, hd01, hprod⟩ :=
    lem_as_coarse_shallow_grid_translated_zero_ir_bank_product d hd q eta hq heta
  refine ⟨delta0, hd0, hd01, ?_⟩
  intro C hC M Rm H hH hMd Z hZ hZbound cen Cc hcard z L hL
  have hP := hprod C hC M Rm H hH hMd
  have hCc : 0 ≤ Cc := by
    have h0 := hcard 0
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at h0
    exact (Nat.cast_nonneg _).trans h0
  let Gset : ℕ → Finset (SpatialCoordinates d × ι) := fun n =>
    cen n ×ˢ (Finset.univ : Finset ι)
  let X : ℕ → SpatialCoordinates d × ι → BilateralField d → ℝ := fun n i ω =>
    aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M n ω i.1 *
      (1 + Z i.2 (aux_lem_as_coarse_shallow_grid_scaleShift n i.1 ω))
  have hGcard : ∀ n : ℕ,
      ((Gset n).card : ℝ) ≤ (Cc * (Fintype.card ι : ℝ)) *
        (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) := by
    intro n
    have hG : (Gset n).card = (cen n).card * Fintype.card ι := by
      simp only [Gset, Finset.card_product, Finset.card_univ]
    rw [hG, Nat.cast_mul]
    have hι : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    calc ((cen n).card : ℝ) * (Fintype.card ι : ℝ) ≤
        (Cc * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ))) * (Fintype.card ι : ℝ) :=
          mul_le_mul_of_nonneg_right (hcard n) hι
      _ = (Cc * (Fintype.card ι : ℝ)) * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) := by ring
  have hX : ∀ n i, i ∈ Gset n →
      AEStronglyMeasurable (X n i) (chaosSampleLaw M).toMeasure := by
    intro n i _
    exact (hP n i.1 (Z i.2) (hZ i.2) (hZbound i.2)).1
  have hLp : ∀ n i, i ∈ Gset n →
      eLpNorm (X n i) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (n : ℝ))) := by
    intro n i _
    exact (hP n i.1 (Z i.2) (hZ i.2) (hZbound i.2)).2
  have henv := lem_as_coarse_shallow_grid_envelope_exponential
    (chaosSampleLaw M).toMeasure Gset X (d : ℝ) q (B0 * (1 + C))
    (Cc * (Fintype.card ι : ℝ)) eta rho (by linarith) (mul_nonneg hB0.le (by linarith))
    (mul_nonneg hCc (Nat.cast_nonneg _)) hetarho hrate hGcard hX hLp
  filter_upwards [henv] with ω hω
  obtain ⟨K0, hK01, hK0⟩ := hω
  let EK : ℝ := Real.exp (3 * ‖(H ω).restrict
    (Metric.closedBall z (L + 3 / 2) : Set (SpatialCoordinates d))‖)
  have hEK1 : 1 ≤ EK := Real.one_le_exp (by positivity)
  refine ⟨EK * K0, one_le_mul_of_one_le_of_one_le hEK1 hK01, ?_⟩
  intro withIR N n hnN y hy b
  have hmem : (y, b) ∈ Gset n := Finset.mem_product.mpr ⟨hy, Finset.mem_univ b⟩
  have hXb : |X n (y, b) ω| ≤ K0 * (3 : ℝ) ^ (rho * (n : ℝ)) := hK0 n (y, b) hmem
  obtain ⟨hF0, hFD⟩ := aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_two_branch_false_le_D0 M Rm H N n hnN ω y
  have hD0 : 0 ≤ aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M n ω y := hF0.trans hFD
  have hEball : Real.exp (3 * ‖(H ω).restrict
      (Metric.closedBall y (3 * ((3 : ℝ)^(-(n : ℤ)) / 2)) : Set (SpatialCoordinates d))‖) ≤
      EK := by
    apply Real.exp_le_exp.mpr
    have hsub := aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_ball_subset n y z L (hL n y hy)
    have hmono := ContinuousMap.norm_restrict_mono_set (H ω)
      (K := ⟨Metric.closedBall y (3 * ((3 : ℝ)^(-(n : ℤ)) / 2)),
        ProperSpace.isCompact_closedBall _ _⟩)
      (L := ⟨Metric.closedBall z (L + 3 / 2), ProperSpace.isCompact_closedBall _ _⟩) hsub
    exact mul_le_mul_of_nonneg_left hmono (by norm_num)
  -- both branch factors are nonnegative and below `EK * D0`
  have hbranch : 0 ≤ aux_lem_as_coarse_shallow_grid_two_branch_factor M H withIR N n ω y ∧
      aux_lem_as_coarse_shallow_grid_two_branch_factor M H withIR N n ω y ≤
        EK * aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M n ω y := by
    cases withIR with
    | false =>
        exact ⟨hF0, hFD.trans (le_mul_of_one_le_left hD0 hEK1)⟩
    | true =>
        have hT := aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_two_branch_true_le M H N n ω y
        have hT0 : 0 ≤ aux_lem_as_coarse_shallow_grid_two_branch_factor M H true N n ω y := by
          rw [aux_lem_as_coarse_shallow_grid_translated_two_branch_envelope_two_branch_true_eq]
          have hc : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
            div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)
          positivity
        refine ⟨hT0, hT.trans ?_⟩
        calc aux_lem_as_coarse_shallow_grid_two_branch_factor M H false N n ω y *
              Real.exp (3 * ‖(H ω).restrict
                (Metric.closedBall y (3 * ((3 : ℝ)^(-(n : ℤ)) / 2)) :
                  Set (SpatialCoordinates d))‖) ≤
            aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M n ω y * EK :=
              mul_le_mul hFD hEball (Real.exp_pos _).le hD0
          _ = EK * aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M n ω y := mul_comm _ _
  calc
    |aux_lem_as_coarse_shallow_grid_two_branch_factor M H withIR N n ω y *
        (1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift n y ω))| =
      aux_lem_as_coarse_shallow_grid_two_branch_factor M H withIR N n ω y *
        |1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift n y ω)| := by
      rw [abs_mul, abs_of_nonneg hbranch.1]
    _ ≤ (EK * aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M n ω y) *
        |1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift n y ω)| :=
      mul_le_mul_of_nonneg_right hbranch.2 (abs_nonneg _)
    _ = EK * |X n (y, b) ω| := by
      change _ = EK * |aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M n ω y *
        (1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift n y ω))|
      rw [abs_mul, abs_of_nonneg hD0]
      ring
    _ ≤ EK * (K0 * (3 : ℝ) ^ (rho * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hXb (by positivity)
    _ = EK * K0 * (3 : ℝ) ^ (rho * (n : ℝ)) := by ring

end Paper




