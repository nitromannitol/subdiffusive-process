module

public import SubdiffusiveProcess.Paper.lem_cell_ellipticity
public import SubdiffusiveProcess.Paper.lem_extension_cell_moment_uniform_root
public import SubdiffusiveProcess.Paper.inputs_J_witness

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.Paper
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The cell comparison and its two Hölder steps, with the unit-cell moment and
small-disorder cap selected before the model. The uniform infrared envelope is
bounded at that cap, retaining the dimension-only exponential rate. -/
theorem cell_ellipticity_moment_uniform {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (p : ℝ) (hp : 1 ≤ p)
    (s s0 : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hs0 : 0 < s0) (h2 : 2 * s0 ≤ s)
    (z1 : SpatialCoordinates d) (R1 : ℝ) (hR1 : 0 < R1)
    (w1 : SpatialCoordinates d) (r1 : ℝ) (hr1 : 0 < r1)
    (hsub1 : (centeredCube w1 r1 hr1 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z1 R1 hR1 : Set (SpatialCoordinates d)))
    (hid : ∀ x : SpatialCoordinates d, (fun i => w1 i + r1 * x i) = x)
    (Cq0 : ℝ) (hCq0 : 0 < Cq0)
    (deltaCap : ℝ) :
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H), M.delta ≤ deltaCap →
      ∀ (qn : ℝ≥0∞), (qn = 1 ∨ qn = 2) →
      ( ∀ N' : ℕ,
      AEStronglyMeasurable (fun om =>
        E.Lam z1 R1 hR1 (cutoffPositiveCoefficient M H om N' z1 hR1) w1 r1 s0 2 +
          (E.lam z1 R1 hR1 (cutoffPositiveCoefficient M H om N' z1 hR1) w1 r1 s0 2)⁻¹)
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om =>
        E.Lam z1 R1 hR1 (cutoffPositiveCoefficient M H om N' z1 hR1) w1 r1 s0 2 +
          (E.lam z1 R1 hR1 (cutoffPositiveCoefficient M H om N' z1 hR1) w1 r1 s0 2)⁻¹)
        (ENNReal.ofReal (2 * (2 * p))) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cq0) →
      ∀ (N k : ℕ), k ≤ N → ∀ (w : SpatialCoordinates d),
        (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
        eLpNorm
            (fun om =>
              E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn +
                (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn)⁻¹)
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cq * Real.exp ((2 * Real.log 2 +
            (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
              (p + p ^ 2) * M.delta ^ 2 * (k : ℝ))) := by
  obtain ⟨CK, hCKnn, hCKb⟩ := aux_lem_extension_cell_moment_aboveEnvelope_moment (d := d) hd
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let K : Compacts (SpatialCoordinates d) := ⟨Metric.closedBall z0 R, isCompact_closedBall _ _⟩
  let K0 : Compacts (SpatialCoordinates d) := ⟨Metric.closedBall 0 1, isCompact_closedBall _ _⟩
  set C1 : ℝ := (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ with hC1
  have hC1pos : 0 < C1 := by
    have := aux_lem_cell_ellipticity_base_lt_one (s := s0) (q := 2) (by linarith only [hs0])
    exact inv_pos.2 (by linarith only [this])
  set B : ℝ → ℝ := fun v => aux_lem_extension_cell_moment_aboveRate d v with hB
  set a1 : ℝ := Real.exp (Real.log 4 / (2 * p) + 4 * (2 * p) * CK K * deltaCap ^ 2 +
    B (2 * p) * deltaCap ^ 2) with ha1
  set a2 : ℝ := Real.exp (Real.log 4 / (2 * (2 * p)) + 4 * (2 * (2 * p)) * CK K0 * deltaCap ^ 2 +
    B (2 * (2 * p)) * deltaCap ^ 2 + B (2 * (2 * p)) * deltaCap ^ 2 * ((0 : ℕ) : ℝ)) with ha2
  refine ⟨C1 * a1 * a2 * Cq0, by positivity, ?_⟩
  intro M H hH hdelta qn hq hY N k hk w hcell
  have hsq : M.delta ^ 2 ≤ deltaCap ^ 2 :=
    pow_le_pow_left₀ M.shellPrefix.delta_pos.le hdelta 2
  have hKnn := hCKnn K
  have hK0nn := hCKnn K0
  have hB1 := (aux_lem_extension_cell_moment_aboveRate_pos d (2 * p) (by positivity)).le
  have hB2 := (aux_lem_extension_cell_moment_aboveRate_pos d (2 * (2 * p)) (by positivity)).le
  have hsub : (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
      Set (SpatialCoordinates d)) ⊆ (centeredCube z0 R hR : Set (SpatialCoordinates d)) := hcell
  have hK : ∀ x ∈ openCubeSet (originCube d 0),
      (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈ (K : Set (SpatialCoordinates d)) := by
    intro x hx
    have hyroot := hsub (aux_lem_extension_cell_moment_cellAffine_mem w _ (by positivity) hx)
    change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 ≤ R
    change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 < R / 2 at hyroot
    linarith only [hyroot, hR]
  have hK0 : ∀ x ∈ openCubeSet (originCube d 0), x ∈ (K0 : Set (SpatialCoordinates d)) :=
    fun x hx => aux_lem_cell_ellipticity_closedBall_zero_mem hx
  set μ := (chaosSampleLaw M).toMeasure with hμ
  set T := aux_lem_extension_cell_moment_zoom (k : ℤ) w with hT
  have hTmp : MeasurePreserving T μ μ :=
    aux_lem_extension_cell_moment_zoom_measurePreserving M (k : ℤ) w
  let G1 : BilateralField d → ℝ := fun om =>
    Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K k w om)
  let G2 : BilateralField d → ℝ := fun om =>
    Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K0 0 0 om)
  let Y : BilateralField d → ℝ := fun om =>
    E.Lam z1 R1 hR1 (cutoffPositiveCoefficient M H om (N - k) z1 hR1) w1 r1 s0 2 +
      (E.lam z1 R1 hR1 (cutoffPositiveCoefficient M H om (N - k) z1 hR1) w1 r1 s0 2)⁻¹
  let X : BilateralField d → ℝ := fun om =>
    E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ))) s qn +
      (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))
        s qn)⁻¹
  have hG1m : AEStronglyMeasurable G1 μ :=
    (aux_lem_extension_cell_moment_aboveEnvelope_measurable M H hH.1 K k w).exp.aestronglyMeasurable
  have hG2m : AEStronglyMeasurable G2 μ :=
    (aux_lem_extension_cell_moment_aboveEnvelope_measurable M H hH.1 K0 0 0).exp.aestronglyMeasurable
  obtain ⟨hYm, hYb⟩ := hY (N - k)
  have hGYm : AEStronglyMeasurable (fun om => G2 om * Y om) μ := hG2m.mul hYm
  have hGYTm : AEStronglyMeasurable (fun om => G2 (T om) * Y (T om)) μ :=
    hGYm.comp_measurePreserving hTmp
  have hYnn : ∀ om, 0 ≤ Y om := fun om => by
    have h1 := E.Lam_pos z1 R1 hR1 (cutoffPositiveCoefficient M H om (N - k) z1 hR1) w1 r1 s0 2
    have h2 := inv_pos.2 (E.lam_pos z1 R1 hR1 (cutoffPositiveCoefficient M H om (N - k) z1 hR1)
      w1 r1 s0 2)
    exact (add_pos h1 h2).le
  have hXnn : ∀ om, 0 ≤ X om := fun om => by
    have h1 := E.Lam_pos z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
      ((3 : ℝ) ^ (-(k : ℤ))) s qn
    have h2 := inv_pos.2 (E.lam_pos z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w
      ((3 : ℝ) ^ (-(k : ℤ))) s qn)
    exact (add_pos h1 h2).le
  have hpoint : ∀ om, X om ≤ C1 * (G1 om * (G2 (T om) * Y (T om))) := fun om => by
    have h := aux_lem_cell_ellipticity_pointwise E M H z0 R hR N k hk w hsub K K0 hK hK0 s s0 hs
      hs0 h2 qn hq z1 R1 hR1 w1 r1 hr1 hsub1 hid om
    calc X om ≤ _ := h
      _ = _ := by
        simp only [G1, G2, Y, T, Real.exp_add]
        ring
  have hnorm1 : eLpNorm X (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C1 *
      eLpNorm (fun om => G1 om * (G2 (T om) * Y (T om))) (ENNReal.ofReal p) μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (aux_lem_cell_ellipticity_aestronglyMeasurable hd E M H hH s hs z0 R hR N w _ (by positivity) hcell qn hq)
    filter_upwards with om
    rw [Real.norm_of_nonneg (hXnn om), Real.norm_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hYnn _)))]
    exact hpoint om
  have hnorm2 := aux_lem_extension_cell_moment_eLpNorm_mul μ p hp0 G1
    (fun om => G2 (T om) * Y (T om)) hG1m hGYTm
  have hnorm3 : eLpNorm (fun om => G2 (T om) * Y (T om)) (ENNReal.ofReal (2 * p)) μ =
      eLpNorm (fun om => G2 om * Y om) (ENNReal.ofReal (2 * p)) μ :=
    eLpNorm_comp_measurePreserving (g := fun om => G2 om * Y om) hGYm hTmp
  have hnorm4 := aux_lem_extension_cell_moment_eLpNorm_mul μ (2 * p) (by positivity) G2 Y
    hG2m hYm
  have hG1b : eLpNorm G1 (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal (Real.exp
      (Real.log 4 / (2 * p) + 4 * (2 * p) * CK K * M.delta ^ 2 + B (2 * p) * M.delta ^ 2 +
        B (2 * p) * M.delta ^ 2 * (k : ℝ))) :=
    hCKb M H hH K k w (2 * p) (by positivity)
  have hG2b : eLpNorm G2 (ENNReal.ofReal (2 * (2 * p))) μ ≤ ENNReal.ofReal a2 := by
    refine (hCKb M H hH K0 0 0 (2 * (2 * p)) (by positivity)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [ha2]
    apply Real.exp_le_exp.2
    simp only [Nat.cast_zero, mul_zero, add_zero]
    have hfirst := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ 4 * (2 * (2 * p)) * CK K0 by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hsq hB2
    linarith only [hfirst, hsecond]
  have hcd : B (2 * p) ≤ (2 * Real.log 2 +
      (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) * (p + p ^ 2) := by
    simp only [hB, aux_lem_extension_cell_moment_aboveRate]
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : 0 ≤ Real.log 2 * ((p - 1) * (p + 2)) :=
      mul_nonneg hl.le (mul_nonneg (sub_nonneg.2 hp) (by linarith only [hp0]))
    have h2 : 0 ≤ (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 * (p * (p - 1)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg hp0.le (sub_nonneg.2 hp))
    nlinarith only [h1, h2]
  have hexp : Real.exp (Real.log 4 / (2 * p) + 4 * (2 * p) * CK K * M.delta ^ 2 +
      B (2 * p) * M.delta ^ 2 + B (2 * p) * M.delta ^ 2 * (k : ℝ)) ≤
      a1 * Real.exp ((2 * Real.log 2 +
        (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
          (p + p ^ 2) * M.delta ^ 2 * (k : ℝ)) := by
    rw [ha1, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hk0 : (0 : ℝ) ≤ M.delta ^ 2 * (k : ℝ) := by positivity
    have hfirst := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ 4 * (2 * p) * CK K by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hsq hB1
    linarith only [hfirst, hsecond, mul_le_mul_of_nonneg_right hcd hk0]
  calc eLpNorm X (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal C1 * eLpNorm (fun om => G1 om * (G2 (T om) * Y (T om)))
          (ENNReal.ofReal p) μ := hnorm1
    _ ≤ ENNReal.ofReal C1 * (eLpNorm G1 (ENNReal.ofReal (2 * p)) μ *
          eLpNorm (fun om => G2 (T om) * Y (T om)) (ENNReal.ofReal (2 * p)) μ) :=
        mul_le_mul' le_rfl hnorm2
    _ = ENNReal.ofReal C1 * (eLpNorm G1 (ENNReal.ofReal (2 * p)) μ *
          eLpNorm (fun om => G2 om * Y om) (ENNReal.ofReal (2 * p)) μ) := by rw [hnorm3]
    _ ≤ ENNReal.ofReal C1 * (eLpNorm G1 (ENNReal.ofReal (2 * p)) μ *
          (eLpNorm G2 (ENNReal.ofReal (2 * (2 * p))) μ *
            eLpNorm Y (ENNReal.ofReal (2 * (2 * p))) μ)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hnorm4)
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal (a1 * Real.exp ((2 * Real.log 2 +
          (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
            (p + p ^ 2) * M.delta ^ 2 * (k : ℝ))) *
          (ENNReal.ofReal a2 * ENNReal.ofReal Cq0)) := by
        refine mul_le_mul' le_rfl (mul_le_mul' ?_ (mul_le_mul' hG2b hYb))
        exact hG1b.trans (ENNReal.ofReal_le_ofReal hexp)
    _ = ENNReal.ofReal (C1 * a1 * a2 * Cq0 * Real.exp ((2 * Real.log 2 +
          (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
            (p + p ^ 2) * M.delta ^ 2 * (k : ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring


/-- The paper's ellipticity moments for the characterized ellipticity data
constructed by `inputs_J_witness`. The prefactor is chosen before the model
and the two values of `q`; the rate depends only on the dimension. -/
theorem cell_ellipticity_uniform :
    ∀ (d : ℕ) (hd : 2 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
    let E : in_J d := Classical.choice (_root_.SubdiffusiveProcess.Paper.inputs_J_witness d hd)
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ p : ℝ, 1 ≤ p →
      ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        ∃ Cq : ℝ, 0 < Cq ∧
          ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
            (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            InfraredCharacterization M H → M.delta ≤ delta0 →
          ∀ (qn : ℝ≥0∞), (qn = 1 ∨ qn = 2) →
          ∀ N k : ℕ, k ≤ N → ∀ w : SpatialCoordinates d,
            centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR →
            AEStronglyMeasurable (fun ω =>
              E.Lam z0 R hR (cutoffPositiveCoefficient M H ω N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn +
                (E.lam z0 R hR (cutoffPositiveCoefficient M H ω N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn)⁻¹) (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun ω =>
              E.Lam z0 R hR (cutoffPositiveCoefficient M H ω N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn +
                (E.lam z0 R hR (cutoffPositiveCoefficient M H ω N z0 hR)
                  w ((3 : ℝ) ^ (-(k : ℤ))) s qn)⁻¹)
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (Cq * Real.exp (Cd * (p + p ^ 2) * M.delta ^ 2 * (k : ℝ))) := by
  intro d hd _ _ E
  refine ⟨2 * Real.log 2 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2,
    by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity, ?_⟩
  intro s hs p hp
  let s0 : ℝ := min (s / 2) (1 / 16)
  have hs0 : 0 < s0 := lt_min (by linarith only [hs.1]) (by norm_num)
  have h2 : 2 * s0 ≤ s := by have := min_le_left (s / 2) (1 / 16); linarith only [this]
  have hs0le : s0 ≤ 1 / 16 := min_le_right _ _
  let beta : ℝ := 1 / 2 + 4 * s0
  have hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1 :=
    ⟨by dsimp [beta]; linarith only [hs0], by dsimp [beta]; linarith only [hs0le]⟩
  have hs0eq : (beta - 1 / 2) / 4 = s0 := by dsimp [beta]; ring
  obtain ⟨delta0, Cd0, hdelta0, _hCd0, Cfn, hCfn, hmono, hcell⟩ :=
    lem_extension_cell_moment_uniform_root hd E beta (2 * (2 * p)) hbeta
      (by linarith only [hp]) (0 : SpatialCoordinates d) 2 (by norm_num)
  have hunit : centeredCube (0 : SpatialCoordinates d) 1 one_pos ≤
      centeredCube (0 : SpatialCoordinates d) 2 (by norm_num) :=
    aux_lem_cell_ellipticity_cell_le 0 1 one_pos rfl rfl
  refine ⟨delta0, hdelta0, ?_⟩
  intro z0 R hR
  obtain ⟨Cq, hCq, hbound⟩ := cell_ellipticity_moment_uniform hd E z0 R hR p hp s s0 hs hs0 h2
    (0 : SpatialCoordinates d) 2 (by norm_num) 0 1 one_pos
    (fun x hx => hunit hx)
    (fun x => by funext i; simp only [Pi.zero_apply, zero_add, one_mul])
    (Cfn delta0) (hCfn delta0) delta0
  refine ⟨Cq, hCq, ?_⟩
  intro M H hH hdelta qn hq N k hk w hsub
  have hY : ∀ N' : ℕ,
      AEStronglyMeasurable (fun ω =>
        E.Lam 0 2 (by norm_num) (cutoffPositiveCoefficient M H ω N' 0 (by norm_num))
            0 1 s0 2 +
          (E.lam 0 2 (by norm_num) (cutoffPositiveCoefficient M H ω N' 0 (by norm_num))
            0 1 s0 2)⁻¹) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun ω =>
        E.Lam 0 2 (by norm_num) (cutoffPositiveCoefficient M H ω N' 0 (by norm_num))
            0 1 s0 2 +
          (E.lam 0 2 (by norm_num) (cutoffPositiveCoefficient M H ω N' 0 (by norm_num))
            0 1 s0 2)⁻¹) (ENNReal.ofReal (2 * (2 * p))) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cfn delta0) := by
    intro N'
    have hunit' : centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-((0 : ℕ) : ℤ)))
        (by positivity) ≤ centeredCube (0 : SpatialCoordinates d) 2 (by norm_num) := by
      simpa only [Nat.cast_zero, neg_zero, zpow_zero] using hunit
    have h := hcell M H hH hdelta 0 N' 0 hunit'
    simp only [Nat.cast_zero, neg_zero, zpow_zero, hs0eq, mul_zero, Real.exp_zero, mul_one] at h
    exact ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal
      (hmono M.delta delta0 M.shellPrefix.delta_pos.le hdelta))⟩
  exact ⟨aux_lem_cell_ellipticity_aestronglyMeasurable hd E M H hH s hs z0 R hR N w _
    (by positivity) hsub qn hq, hbound M H hH hdelta qn hq hY N k hk w hsub⟩

end SubdiffusiveProcess.AuditExports
