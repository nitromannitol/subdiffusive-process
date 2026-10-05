module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_uniform_factor_envelope
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift

@[expose] public section

open MeasureTheory Set Metric SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ## Translation identities for the infrared-free cell factor -/

/-- The infrared-free coarse field `G0_k = Σ_{j<k} g_{-j}`. -/
def aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0
    {d : ℕ} (k : ℕ) (ω : BilateralField d) (x : SpatialCoordinates d) : ℝ :=
  ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x

/-- Its oscillation on the enlarged cell ball of depth `k` around `y`. -/
def aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_osc0
    {d : ℕ} (k : ℕ) (ω : BilateralField d) (y : SpatialCoordinates d) : ℝ :=
  sSup {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
    ∃ x' ∈ Metric.closedBall y (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
      v = |aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0 k ω x -
        aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0 k ω x'|}

/-- The `N`-independent infrared-free factor `D0`. -/
def aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ)
    (ω : BilateralField d) (y : SpatialCoordinates d) : ℝ :=
  Real.exp (aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_osc0 k ω y) *
    Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) *
      (Real.exp (aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0 k ω y -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
        Real.exp (-(aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0 k ω y -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)))

theorem aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_shift_zero_apply
    {d : ℕ} (w : SpatialCoordinates d) (ω : BilateralField d) (j : ℤ)
    (x : SpatialCoordinates d) :
    (aux_lem_as_coarse_shallow_grid_scaleShift 0 w ω) j x = ω j (w + x) := by
  simp only [aux_lem_as_coarse_shallow_grid_scaleShift, aux_lem_as_coarse_shallow_grid_cellMap,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, Nat.cast_zero, sub_zero]
  congr 1
  funext i
  simp [_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation]

theorem aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0_shift
    {d : ℕ} (k : ℕ) (w : SpatialCoordinates d) (ω : BilateralField d)
    (x : SpatialCoordinates d) :
    aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0 k
        (aux_lem_as_coarse_shallow_grid_scaleShift 0 w ω) x =
      aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0 k ω (w + x) := by
  unfold aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0
  exact Finset.sum_congr rfl fun j _ =>
    aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_shift_zero_apply w ω _ x

theorem aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_osc0_shift
    {d : ℕ} (k : ℕ) (w : SpatialCoordinates d) (ω : BilateralField d)
    (y : SpatialCoordinates d) :
    aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_osc0 k
        (aux_lem_as_coarse_shallow_grid_scaleShift 0 w ω) y =
      aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_osc0 k ω (w + y) := by
  unfold aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_osc0
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq,
    aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0_shift]
  constructor
  · rintro ⟨x, hx, x', hx', rfl⟩
    refine ⟨w + x, ?_, w + x', ?_, rfl⟩
    · rw [Metric.mem_closedBall, dist_add_left]; exact hx
    · rw [Metric.mem_closedBall, dist_add_left]; exact hx'
  · rintro ⟨x, hx, x', hx', rfl⟩
    refine ⟨x - w, ?_, x' - w, ?_, ?_⟩
    · rw [Metric.mem_closedBall, ← dist_add_left w, add_sub_cancel]; exact hx
    · rw [Metric.mem_closedBall, ← dist_add_left w, add_sub_cancel]; exact hx'
    · rw [add_sub_cancel, add_sub_cancel]

theorem aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0_shift
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ)
    (w : SpatialCoordinates d) (ω : BilateralField d) (y : SpatialCoordinates d) :
    aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M k
        (aux_lem_as_coarse_shallow_grid_scaleShift 0 w ω) y =
      aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M k ω (w + y) := by
  unfold aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0
  rw [aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_osc0_shift,
    aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_G0_shift]

theorem aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_scaleShift_shift
    {d : ℕ} (k : ℕ) (w y : SpatialCoordinates d) (ω : BilateralField d) :
    aux_lem_as_coarse_shallow_grid_scaleShift k y
        (aux_lem_as_coarse_shallow_grid_scaleShift 0 w ω) =
      aux_lem_as_coarse_shallow_grid_scaleShift k (w + y) ω := by
  funext j
  ext x
  have h1 : aux_lem_as_coarse_shallow_grid_scaleShift k y
      (aux_lem_as_coarse_shallow_grid_scaleShift 0 w ω) j x =
      (aux_lem_as_coarse_shallow_grid_scaleShift 0 w ω) (j - k)
        (aux_lem_as_coarse_shallow_grid_cellMap k y x) := rfl
  rw [h1, aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_shift_zero_apply]
  change ω (j - k) (w + aux_lem_as_coarse_shallow_grid_cellMap k y x) =
    ω (j - k) (aux_lem_as_coarse_shallow_grid_cellMap k (w + y) x)
  congr 1
  funext i
  simp only [aux_lem_as_coarse_shallow_grid_cellMap, ContinuousMap.coe_mk,
    _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation, Pi.add_apply]
  ring

/-! ## Moments at an arbitrary center -/

/-- The infrared-free factor times a shifted unit-bank variable has its actual
`L^q` moment bound at every center. The model's small-disorder threshold is
chosen before the model and the center. -/
theorem lem_as_coarse_shallow_grid_translated_zero_ir_bank_product
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q eta : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ B0 delta0 : ℝ, 0 < B0 ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (C : ℝ), 0 ≤ C →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
        _root_.SubdiffusiveProcess.Paper.in_responses d M →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (k : ℕ) (y : SpatialCoordinates d),
          ∀ Z : BilateralField d → ℝ,
            AEStronglyMeasurable Z (chaosSampleLaw M).toMeasure →
            eLpNorm Z (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal C →
            AEStronglyMeasurable (fun ω =>
              aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M k ω y *
              (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k y ω)))
              (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun ω =>
              aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M k ω y *
              (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k y ω)))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  obtain ⟨B0, delta0, hB0, hd0, hd01, hprod⟩ :=
    aux_lem_as_coarse_shallow_grid_zero_ir_uniform_factor_bank_product d hd q eta hq heta
  refine ⟨B0, delta0, hB0, hd0, hd01, ?_⟩
  intro C hC M Rm H hH hMd k y Z hZ hZbound
  obtain ⟨Q, hQ⟩ := descendantsAtScale_nonempty (originCube d 0)
    (show -(k : ℤ) ≤ (originCube d 0).scale by
      change -(k : ℤ) ≤ 0
      omega)
  have hPQ := hprod C hC M Rm H hH hMd k Q hQ Z hZ hZbound
  dsimp only at hPQ
  let w : SpatialCoordinates d := y - cubeCenter Q
  have hy : w + cubeCenter Q = y := sub_add_cancel y (cubeCenter Q)
  let XQ : BilateralField d → ℝ := fun ω =>
    aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M k ω
        (cubeCenter Q) *
      (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω))
  have hXQ : AEStronglyMeasurable XQ (chaosSampleLaw M).toMeasure := hPQ.1
  have hXQb : eLpNorm XQ (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ))) := hPQ.2
  have hT := lem_as_coarse_shallow_grid_scale_shift M 0 w
  have hcomp : (fun ω =>
      aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0 M k ω y *
        (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k y ω))) =
      XQ ∘ aux_lem_as_coarse_shallow_grid_scaleShift 0 w := by
    funext ω
    simp only [Function.comp_apply, XQ,
      aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_D0_shift,
      aux_lem_as_coarse_shallow_grid_translated_zero_ir_bank_product_scaleShift_shift, hy]
  rw [hcomp]
  exact ⟨hXQ.comp_measurePreserving hT,
    (eLpNorm_comp_measurePreserving hXQ hT).trans_le hXQb⟩

end SubdiffusiveProcess.Paper
