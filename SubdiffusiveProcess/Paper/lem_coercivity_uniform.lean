module

public import SubdiffusiveProcess.Paper.lambda_inv_moments_uniform
public import SubdiffusiveProcess.Paper.besov_h34_coercivity
public import SubdiffusiveProcess.Paper.coercivity_dilation
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

open Classical in
/-- Top-level helper (not a `set`/`let` inside the theorem below, to avoid a `whnf` heartbeat
timeout: bundling `lambda_inv_moments_uniform`'s per-`p` choice behind a top-level `def`,
referenced only by NAME thereafter, elaborates once and stays opaque, unlike an in-proof `set`
whose RHS Lean tries to re-examine at each subsequent use). Packages, for each order `p ≥ 1`, the
pair (threshold, moment bound) that `lambda_inv_moments_uniform` supplies at that order (junk
value `(1,1)` when `p < 1`, never used by any caller respecting the hypothesis). -/
noncomputable def aux_lem_coercivity_uniform_F {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hrle : r ≤ 1)
    (hs : (1 / 8 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 4)) (C' : ℝ) (p : ℝ) : ℝ × ℝ :=
  if hp : 1 ≤ p then
    let w := lambda_inv_moments_uniform d hd E (1 / 8 : ℝ) hs z r hr hrle p hp
    (w.choose, C' * w.choose_spec.2.choose)
  else (1, 1)

theorem aux_lem_coercivity_uniform_F_pos {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hrle : r ≤ 1)
    (hs : (1 / 8 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 4)) (C' : ℝ) (hC' : 0 < C') (p : ℝ) (hp : 1 ≤ p) :
    0 < (aux_lem_coercivity_uniform_F hd E z r hr hrle hs C' p).1 ∧
      0 < (aux_lem_coercivity_uniform_F hd E z r hr hrle hs C' p).2 := by
  unfold aux_lem_coercivity_uniform_F
  rw [dite_eq_left hp]
  exact ⟨(lambda_inv_moments_uniform d hd E (1 / 8 : ℝ) hs z r hr hrle p hp).choose_spec.1,
    mul_pos hC'
      (lambda_inv_moments_uniform d hd E (1 / 8 : ℝ) hs z r hr hrle p hp).choose_spec.2.choose_spec.1⟩

theorem aux_lem_coercivity_uniform_F_main {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hrle : r ≤ 1)
    (hs : (1 / 8 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 4)) (C' : ℝ) (hC' : 0 < C') (p : ℝ) (hp : 1 ≤ p)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (hMdelta : M.delta ≤ (aux_lem_coercivity_uniform_F hd E z r hr hrle hs C' p).1) (N : ℕ) :
    MemLp (fun om : BilateralField d =>
        (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8 : ℝ) 1)⁻¹)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
    eLpNorm (fun om : BilateralField d =>
        (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8 : ℝ) 1)⁻¹)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((aux_lem_coercivity_uniform_F hd E z r hr hrle hs C' p).2 / C') := by
  unfold aux_lem_coercivity_uniform_F at hMdelta ⊢
  rw [dite_eq_left hp] at hMdelta ⊢
  obtain ⟨hmem, hbound⟩ :=
    (lambda_inv_moments_uniform d hd E (1 / 8 : ℝ) hs z r hr hrle p hp).choose_spec.2.choose_spec.2
      M Rm H hH hMdelta N
  refine ⟨hmem, ?_⟩
  rwa [mul_div_cancel_left₀ _ hC'.ne']



theorem lem_coercivity_uniform
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hrle : r ≤ 1) :
    ∃ delta0 : ℝ → ℝ, (∀ p, 1 ≤ p → 0 < delta0 p) ∧
      ∃ Cbound : ℝ → ℝ, (∀ p, 1 ≤ p → 0 < Cbound p) ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∃ K : ℕ → BilateralField d → ℝ,
        (∀ (N : ℕ) (om : BilateralField d),
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
                (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) < ⊤ ∧
            cubeFractionalSqNorm hd z r hr threeQuarterOrder
                (v : SobolevData (centeredCube z r hr)).1 ≤
              K N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr))) ∧
          (∀ v : meanZeroSobolevGraph (centeredCube z r hr),
            cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
                (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) < ⊤ ∧
            cubeFractionalSqNorm hd z r hr threeQuarterOrder
                (v : SobolevData (centeredCube z r hr)).1 ≤
              K N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr)))) ∧
        (∀ p, 1 ≤ p → M.delta ≤ delta0 p →
          ∀ N, MemLp (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
            eLpNorm (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (Cbound p)) := by
  have hs : (1 / 8 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 4) := by constructor <;> norm_num
  obtain ⟨C, hC, hunit⟩ := besov_h34_coercivity d hd E P S (1 / 8 : ℝ) hs
  have horigin :
      ∀ (hr1 : (0 : ℝ) < 1)
        (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 hr1)),
        (∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 hr1),
          cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 hr1 threeQuarterOrder
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr1)).1 ≤
            C * (E.lam (0 : SpatialCoordinates d) 1 hr1 a
              (0 : SpatialCoordinates d) 1 (1 / 8 : ℝ) 1)⁻¹ *
              sobolevCoefficientForm a
                (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr1))
                (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr1))) ∧
        (∀ v : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 hr1),
          cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 hr1 threeQuarterOrder
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr1)).1 ≤
            C * (E.lam (0 : SpatialCoordinates d) 1 hr1 a
              (0 : SpatialCoordinates d) 1 (1 / 8 : ℝ) 1)⁻¹ *
              sobolevCoefficientForm a
                (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr1))
                (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr1))) := by
    intro h1 a
    exact ⟨fun v => (hunit (0 : SpatialCoordinates d) h1 a).1 v |>.2,
      fun v => (hunit (0 : SpatialCoordinates d) h1 a).2 v |>.2⟩
  obtain ⟨C', hC', hcoercive⟩ :=
    coercivity_dilation d hd E (1 / 8 : ℝ) hs C hC horigin z r hr hrle
  refine ⟨fun p => (aux_lem_coercivity_uniform_F hd E z r hr hrle hs C' p).1,
    fun p hp => (aux_lem_coercivity_uniform_F_pos hd E z r hr hrle hs C' hC' p hp).1,
    fun p => (aux_lem_coercivity_uniform_F hd E z r hr hrle hs C' p).2,
    fun p hp => (aux_lem_coercivity_uniform_F_pos hd E z r hr hrle hs C' hC' p hp).2, ?_⟩
  intro M Rm H hH
  let K : ℕ → BilateralField d → ℝ := fun N om =>
    C' * (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8 : ℝ) 1)⁻¹
  refine ⟨K, ?_, ?_⟩
  · intro N om
    constructor
    · intro v
      have hu : (v : SobolevData (centeredCube z r hr)) ∈
          weakSobolevGraph (centeredCube z r hr) :=
        killedSobolevGraph_le_weakSobolevGraph v.property
      let u : weakSobolevGraph (centeredCube z r hr) :=
        ⟨(v : SobolevData (centeredCube z r hr)), hu⟩
      have hfinite := S.h1_fractional_finite z r hr u
      refine ⟨?_, ?_⟩
      · simpa [u] using hfinite
      · simpa [K] using (hcoercive (cutoffPositiveCoefficient M H om N z hr)).1 v
    · intro v
      have hu : (v : SobolevData (centeredCube z r hr)) ∈
          weakSobolevGraph (centeredCube z r hr) :=
        (inf_le_left : meanZeroSobolevGraph (centeredCube z r hr) ≤
          weakSobolevGraph (centeredCube z r hr)) v.property
      let u : weakSobolevGraph (centeredCube z r hr) :=
        ⟨(v : SobolevData (centeredCube z r hr)), hu⟩
      have hfinite := S.h1_fractional_finite z r hr u
      refine ⟨?_, ?_⟩
      · simpa [u] using hfinite
      · simpa [K] using (hcoercive (cutoffPositiveCoefficient M H om N z hr)).2 v
  · intro p hp hMdelta N
    obtain ⟨hmem, hbound⟩ :=
      aux_lem_coercivity_uniform_F_main hd E z r hr hrle hs C' hC' p hp M Rm H hH hMdelta N
    refine ⟨hmem.const_mul C', ?_⟩
    calc eLpNorm (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure
        = eLpNorm (C' • (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8 : ℝ) 1)⁻¹))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure := rfl
      _ ≤ ‖C'‖ₑ * eLpNorm (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8 : ℝ) 1)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure :=
          (eLpNorm_const_smul_le (c := C')
            (f := fun om : BilateralField d =>
              (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8 : ℝ) 1)⁻¹)
            (p := ENNReal.ofReal p) (μ := (chaosSampleLaw M).toMeasure))
      _ ≤ ‖C'‖ₑ * ENNReal.ofReal ((aux_lem_coercivity_uniform_F hd E z r hr hrle hs C' p).2 / C') := by
          gcongr
      _ = ENNReal.ofReal (aux_lem_coercivity_uniform_F hd E z r hr hrle hs C' p).2 := by
        rw [Real.enorm_eq_ofReal hC'.le, ← ENNReal.ofReal_mul hC'.le,
          mul_div_cancel₀ _ hC'.ne']

end SubdiffusiveProcess.Paper
