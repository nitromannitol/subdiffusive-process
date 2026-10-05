module

public import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison
public import SubdiffusiveProcess.FiniteStopping.ObservationTree
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lane4_reference_point_moments

@[expose] public section

/-!
# `lfsc_reference_grid_bound` — crude lower bound of the reference scale on the stage-2 grid

Paper `\label{mfd:lem-finite-source-comparison}`, proof paragraph 1: "the crude grid bounds give
`s_M(q)^{-1} ≤ 3^{εN} r^{-η₀}`".  For a stage-2 cell of side `r = 3^{-k}` (centre `x` in the root cube) the
inverse reference scale is at most `exp(-H(x) - Σ_{j<k} ω_{-j}(x) + kτ²)`; its `a`-th moment is at most
`exp(C δ²)+exp(A(2a+4a²)δ²k)` (compact exponential moment of the infrared field, layer moments), so a Markov bound
and a union bound over the `≤ 3^{d(k+|j|)}` cells of depth `k`, with `a η₀ ≥ d+1` and `δ₀` depending only on `(d,σ)`,
give one event of probability `≤ C 3^{-γN}` outside which every stage-2 cell satisfies the bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

/-- The inverse reference scale is at most the exponential of the centred coarse potential
(`ahom_{N-k}/ahom_N ≥ 1`). -/
theorem aux_lfsc_reference_grid_bound_inv_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
    (Hp : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N k : ℕ) (hk : k ≤ N) (x : SpatialCoordinates d) :
    (SubdiffusiveProcess.FiniteStopping.reference model Hp omega N k x)⁻¹ ≤
      Real.exp (-(Hp omega x) - ((∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) := by
  have hahompos (m : ℕ) : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom model m :=
    lt_of_lt_of_le (Real.exp_pos _) (Rm.ahom_lower m)
  set r : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom model (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom model N with hr
  have hrpos : 0 < r := div_pos (hahompos _) (hahompos _)
  have hr1 : 1 ≤ r := by
    by_cases hk0 : k = 0
    · subst hk0
      simp [hr, div_self (ne_of_gt (hahompos N))]
    · apply (le_div_iff₀ (hahompos N)).2
      simpa using (Rm.ahom_ordering (N - k) N (by omega)).1
  have hkap : SubdiffusiveProcess.FiniteStopping.kappaSeq model (N - k) /
      SubdiffusiveProcess.FiniteStopping.kappaSeq model N =
      Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) * r := by
    unfold SubdiffusiveProcess.FiniteStopping.kappaSeq
    rw [hr, Nat.cast_sub hk]
    have h1 := hahompos (N - k)
    have h2 := hahompos N
    have e : Real.exp ((((N : ℝ) - k) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) =
        Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) *
          Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    field_simp
  have href : SubdiffusiveProcess.FiniteStopping.reference model Hp omega N k x =
      r * Real.exp (Hp omega x + ((∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) := by
    unfold SubdiffusiveProcess.FiniteStopping.reference
    rw [hkap]
    rw [show Hp omega x + ((∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) =
        (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) +
          (Hp omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) by ring]
    simp only [Real.exp_add]
    ring
  rw [href, mul_inv, ← Real.exp_neg]
  have hinv : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have hexp : Real.exp (-(Hp omega x + ((∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P))) =
      Real.exp (-(Hp omega x) - ((∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) := by
    congr 1; ring
  rw [hexp]
  calc r⁻¹ * Real.exp (-(Hp omega x) - ((∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P))
      ≤ 1 * Real.exp (-(Hp omega x) - ((∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) :=
        mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
    _ = _ := one_mul _

/-- Exponential moment of the infrared field at one point of a compact, from the uniform compact moment. -/
theorem aux_lfsc_reference_grid_bound_Hexp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (Kc : TopologicalSpace.Compacts (SpatialCoordinates d)) (CH : ℝ)
    (hHmom : ∀ lam : ℝ, 0 ≤ lam →
      Integrable (fun omega => Real.exp
        (lam * ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖)) (chaosSampleLaw M).toMeasure ∧
      (∫ omega, Real.exp (lam * ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖)
        ∂(chaosSampleLaw M).toMeasure) ≤ 2 * Real.exp (CH * lam ^ 2 * M.delta ^ 2))
    (y : SpatialCoordinates d) (hyK : y ∈ (Kc : Set (SpatialCoordinates d))) (t : ℝ) :
    Integrable (fun omega => Real.exp (t * H omega y)) (chaosSampleLaw M).toMeasure ∧
    (∫ omega, Real.exp (t * H omega y) ∂(chaosSampleLaw M).toMeasure) ≤
      2 * Real.exp (CH * t ^ 2 * M.delta ^ 2) := by
  have hnorm := hHmom |t| (abs_nonneg t)
  have htarget : Measurable (fun omega => Real.exp (t * H omega y)) :=
    (measurable_const.mul ((continuous_eval_const y).measurable.comp hH.1)).exp
  have hdom : ∀ omega, t * H omega y ≤
      |t| * ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖ := by
    intro omega
    have hb := ((H omega).restrict (Kc : Set (SpatialCoordinates d))).norm_coe_le_norm ⟨y, hyK⟩
    calc t * H omega y ≤ |t * H omega y| := le_abs_self _
      _ = |t| * |H omega y| := abs_mul _ _
      _ ≤ |t| * ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖ := by
        rw [← Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hb (abs_nonneg t)
  have hint : Integrable (fun omega => Real.exp (t * H omega y)) (chaosSampleLaw M).toMeasure := by
    refine hnorm.1.mono' htarget.aestronglyMeasurable ?_
    filter_upwards [] with omega
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (hdom omega)
  refine ⟨hint, ?_⟩
  calc (∫ omega, Real.exp (t * H omega y) ∂(chaosSampleLaw M).toMeasure) ≤
        ∫ omega, Real.exp (|t| * ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖)
          ∂(chaosSampleLaw M).toMeasure :=
      integral_mono hint hnorm.1 (fun omega => Real.exp_le_exp.mpr (hdom omega))
    _ ≤ 2 * Real.exp (CH * |t| ^ 2 * M.delta ^ 2) := hnorm.2
    _ = 2 * Real.exp (CH * t ^ 2 * M.delta ^ 2) := by rw [sq_abs]

/-- **Markov bound at one point**: the inverse reference scale exceeds `exp L` with probability at most
`((E₁ + e^{B₀δ²k})/2) e^{-aL}`. -/
theorem aux_lfsc_reference_grid_bound_point {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
    (Hp : BilateralField d → C(SpatialCoordinates d, ℝ))
    (S k : ℕ) (hk : k ≤ S) (x : SpatialCoordinates d)
    (hHmeas : Measurable (fun omega : BilateralField d => Hp omega x))
    {a : ℝ} (ha : 0 < a) (L E1 : ℝ)
    (hE1i : Integrable (fun omega : BilateralField d => Real.exp (-2 * a * Hp omega x))
      (chaosSampleLaw model).toMeasure)
    (hE1 : (∫ omega : BilateralField d, Real.exp (-2 * a * Hp omega x)
      ∂(chaosSampleLaw model).toMeasure) ≤ E1) :
    (chaosSampleLaw model).toMeasure
      {omega | Real.exp L < (SubdiffusiveProcess.FiniteStopping.reference model Hp omega S k x)⁻¹} ≤
      ENNReal.ofReal ((E1 + Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) *
        (|-2 * a| + (-2 * a) ^ 2) * model.delta ^ 2 * (k : ℝ))) / 2 * Real.exp (-(a * L))) := by
  set P := (chaosSampleLaw model).toMeasure with hP
  set cen : BilateralField d → ℝ := fun omega =>
    (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P with hcen
  have hsum := aux_lane4_reference_point_moments_sum model k x (-2 * a)
  set E2 : ℝ := Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) *
        (|-2 * a| + (-2 * a) ^ 2) * model.delta ^ 2 * (k : ℝ)) with hE2
  have hcenMeas : Measurable cen := by
    apply Measurable.sub _ measurable_const
    apply Finset.measurable_sum
    intro j _
    exact (continuous_eval_const x).measurable.comp (measurable_pi_apply (-(j : ℤ)))
  set f : BilateralField d → ℝ := fun omega => Real.exp (a * (-(Hp omega x) - cen omega)) with hf
  set g : BilateralField d → ℝ := fun omega =>
    (Real.exp (-2 * a * Hp omega x) + Real.exp (-2 * a * cen omega)) / 2 with hg
  have hfg : ∀ omega, f omega ≤ g omega := by
    intro omega
    have e1 : f omega = Real.exp (-(a * Hp omega x)) * Real.exp (-(a * cen omega)) := by
      rw [hf]; dsimp only; rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-2 * a * Hp omega x) =
        Real.exp (-(a * Hp omega x)) * Real.exp (-(a * Hp omega x)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e3 : Real.exp (-2 * a * cen omega) =
        Real.exp (-(a * cen omega)) * Real.exp (-(a * cen omega)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1, hg]; dsimp only; rw [e2, e3]
    nlinarith [sq_nonneg (Real.exp (-(a * Hp omega x)) - Real.exp (-(a * cen omega)))]
  have hgint : Integrable g P := by
    have := hE1i.add hsum.1
    exact this.div_const 2
  have hfmeas : Measurable f := by
    rw [hf]
    exact (measurable_const.mul ((hHmeas.neg).sub hcenMeas)).exp
  have hfint : Integrable f P := by
    refine hgint.mono' hfmeas.aestronglyMeasurable ?_
    filter_upwards [] with omega
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hfg omega
  have hgI : (∫ omega, g omega ∂P) ≤ (E1 + E2) / 2 := by
    have h1 : (∫ omega, g omega ∂P) =
        ((∫ omega, Real.exp (-2 * a * Hp omega x) ∂P) + ∫ omega, Real.exp (-2 * a * cen omega) ∂P) / 2 := by
      rw [hg]; dsimp only
      rw [integral_div, integral_add hE1i hsum.1]
    rw [h1]
    have := hsum.2
    linarith
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := f)
    (ae_of_all _ (fun omega => (Real.exp_pos _).le)) hfint (Real.exp (a * L))
  have hsub : {omega | Real.exp L < (SubdiffusiveProcess.FiniteStopping.reference model Hp omega S k x)⁻¹}
      ⊆ {omega | Real.exp (a * L) ≤ f omega} := by
    intro omega hom
    have hinv := aux_lfsc_reference_grid_bound_inv_le model Rm Hp omega S k hk x
    have h1 : Real.exp L < Real.exp (-(Hp omega x) - cen omega) := lt_of_lt_of_le hom hinv
    have h2 : L < -(Hp omega x) - cen omega := Real.exp_lt_exp.mp h1
    show Real.exp (a * L) ≤ f omega
    rw [hf]; dsimp only
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hmono := measure_mono (μ := P) hsub
  have hE2pos : 0 ≤ E2 := (Real.exp_pos _).le
  have hE1nn : 0 ≤ E1 := le_trans (integral_nonneg (fun omega => (Real.exp_pos _).le)) hE1
  have hfin : P {omega | Real.exp (a * L) ≤ f omega} ≠ ⊤ := measure_ne_top _ _
  have hreal : (P {omega | Real.exp (a * L) ≤ f omega}).toReal ≤
      (E1 + E2) / 2 * Real.exp (-(a * L)) := by
    have hpos : 0 < Real.exp (a * L) := Real.exp_pos _
    have hm : Real.exp (a * L) * (P {omega | Real.exp (a * L) ≤ f omega}).toReal ≤ (E1 + E2) / 2 :=
      le_trans (by simpa [measureReal_def] using hmark) (le_trans (integral_mono hfint hgint hfg) hgI)
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith
  calc P {omega | Real.exp L < (SubdiffusiveProcess.FiniteStopping.reference model Hp omega S k x)⁻¹}
      ≤ P {omega | Real.exp (a * L) ≤ f omega} := hmono
    _ ≤ _ := by
      rw [ENNReal.le_ofReal_iff_toReal_le hfin (by positivity)]
      exact hreal

/-- Per-level arithmetic: `cnt · ((c₁+E₂)/2 · e^{-aL}) ≤ ((c₁+1)/2) 3^{d|j|} e^{-aεN log 3}`. -/
theorem aux_lfsc_reference_grid_bound_level_arith
    {d k : ℕ} (jn : ℕ) {a η0 ε Nr c1 E2 cnt : ℝ} (haη : a * η0 = (d : ℝ) + 1) (hc1 : 0 ≤ c1)
    (hE2 : E2 ≤ (3 : ℝ) ^ k) (hE2nn : 0 ≤ E2)
    (hcnt : cnt ≤ (3 : ℝ) ^ (d * jn) * (3 : ℝ) ^ (d * k)) :
    cnt * ((c1 + E2) / 2 * Real.exp (-(a * ((ε * Nr + (k : ℝ) * η0) * Real.log 3)))) ≤
      (c1 + 1) / 2 * (3 : ℝ) ^ (d * jn) * Real.exp (-(a * ε * Nr * Real.log 3)) := by
  set T : ℝ := (3 : ℝ) ^ k with hT
  have hT1 : 1 ≤ T := one_le_pow₀ (by norm_num)
  have hTpos : 0 < T := by linarith
  have hTk : Real.exp ((k : ℝ) * Real.log 3) = T := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hsplit : Real.exp (-(a * ((ε * Nr + (k : ℝ) * η0) * Real.log 3))) =
      Real.exp (-(a * ε * Nr * Real.log 3)) * (T⁻¹) ^ (d + 1) := by
    have h1 : -(a * ((ε * Nr + (k : ℝ) * η0) * Real.log 3)) =
        -(a * ε * Nr * Real.log 3) + ((d + 1 : ℕ) : ℝ) * (-((k : ℝ) * Real.log 3)) := by
      have : ((d + 1 : ℕ) : ℝ) = a * η0 := by rw [haη]; push_cast; ring
      rw [this]; ring
    rw [h1, Real.exp_add, Real.exp_nat_mul, Real.exp_neg ((k : ℝ) * Real.log 3), hTk]
  have hcnt' : cnt ≤ (3 : ℝ) ^ (d * jn) * T ^ d := by
    rw [hT, ← pow_mul, mul_comm k d]; exact hcnt
  have hW : 0 < Real.exp (-(a * ε * Nr * Real.log 3)) := Real.exp_pos _
  have hkey : (c1 + E2) / 2 * T⁻¹ ≤ (c1 + 1) / 2 := by
    have h1 : c1 * T⁻¹ ≤ c1 := by
      calc c1 * T⁻¹ ≤ c1 * 1 := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hT1) hc1
        _ = c1 := mul_one _
    have h2 : E2 * T⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hTpos]; exact hE2
    calc (c1 + E2) / 2 * T⁻¹ = (c1 * T⁻¹ + E2 * T⁻¹) / 2 := by ring
      _ ≤ (c1 + 1) / 2 := by linarith
  have hpow : T ^ d * (T⁻¹) ^ (d + 1) = T⁻¹ := by
    rw [pow_succ, inv_pow, mul_comm ((T ^ d)⁻¹) T⁻¹]
    field_simp
  rw [hsplit]
  calc cnt * ((c1 + E2) / 2 * (Real.exp (-(a * ε * Nr * Real.log 3)) * (T⁻¹) ^ (d + 1)))
      ≤ ((3 : ℝ) ^ (d * jn) * T ^ d) *
        ((c1 + E2) / 2 * (Real.exp (-(a * ε * Nr * Real.log 3)) * (T⁻¹) ^ (d + 1))) := by
        apply mul_le_mul_of_nonneg_right hcnt'
        positivity
    _ = (3 : ℝ) ^ (d * jn) * Real.exp (-(a * ε * Nr * Real.log 3)) *
        ((c1 + E2) / 2 * (T ^ d * (T⁻¹) ^ (d + 1))) := by ring
    _ = (3 : ℝ) ^ (d * jn) * Real.exp (-(a * ε * Nr * Real.log 3)) *
        ((c1 + E2) / 2 * T⁻¹) := by rw [hpow]
    _ ≤ (3 : ℝ) ^ (d * jn) * Real.exp (-(a * ε * Nr * Real.log 3)) * ((c1 + 1) / 2) := by
        apply mul_le_mul_of_nonneg_left hkey
        positivity
    _ = _ := by ring

/-- A stage-2 centre lies within `3^j/2` of the root centre. -/
theorem aux_lfsc_reference_grid_bound_centre_dist {d : ℕ} (z : SpatialCoordinates d) (j : ℤ)
    (hr : (0 : ℝ) < (3 : ℝ) ^ j) (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ)
    (w : Fin s → OddGridIndex d mg) :
    dist (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
      (descendantSide 1 t0 ((3 : ℝ) ^ j)) s w) z < (3 : ℝ) ^ j / 2 := by
  set x := descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
      (descendantSide 1 t0 ((3 : ℝ) ^ j)) s w with hx
  have hxc : x ∈ (SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s w :
      Set (SpatialCoordinates d)) := by
    rw [SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube]
    change x ∈ Metric.ball x _
    exact Metric.mem_ball_self (half_pos (descendantSide_pos mg s (descendantSide_pos 1 t0 hr)))
  have hxr := SubdiffusiveProcess.FiniteStopping.cell2_subset_root z hr t0 mg w0 s w hxc
  change x ∈ Metric.ball z ((3 : ℝ) ^ j / 2) at hxr
  exact Metric.mem_ball.mp hxr

/-- The side of a stage-2 cell. -/
theorem aux_lfsc_reference_grid_bound_side (H1 t0 s : ℕ) (j : ℤ) :
    descendantSide (subdivisionHalfWidth H1) s (descendantSide 1 t0 ((3 : ℝ) ^ j)) =
      (3 : ℝ) ^ (j - ((1 * t0 : ℕ) : ℤ) - ((H1 * s : ℕ) : ℤ)) := by
  rw [SubdiffusiveProcess.FiniteStopping.descendantSide_zpow 1 1 (by norm_num) j t0]
  rw [SubdiffusiveProcess.FiniteStopping.descendantSide_zpow H1 (subdivisionHalfWidth H1)
    (two_mul_subdivisionHalfWidth_add_one H1) _ s]

/-- Cardinality of the stage-1 × stage-2 index set. -/
theorem aux_lfsc_reference_grid_bound_card (d H1 t0 s : ℕ) :
    (Fintype.card ((Fin t0 → OddGridIndex d 1) × (Fin s → OddGridIndex d (subdivisionHalfWidth H1))) : ℝ) =
      (3 : ℝ) ^ (d * (t0 + H1 * s)) := by
  simp only [Fintype.card_prod, Fintype.card_fun, OddGridIndex, Fintype.card_fin,
    two_mul_subdivisionHalfWidth_add_one]
  push_cast
  simp only [← pow_mul, ← pow_add]
  congr 1
  ring

/-- Index arithmetic of the observation window. -/
theorem aux_lfsc_reference_grid_bound_obs_arith (H1 N : ℕ) (hH1 : 0 < H1) (hN : 2 * H1 ≤ N) (j : ℤ)
    (s : ℕ) (hs : s ≤ SubdiffusiveProcess.FiniteStopping.obsB H1 N) :
    H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) ≤ N ∧
    SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j + H1 * s ≤
      H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) + j.natAbs := by
  have hlo : 4 * (H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N) ≤ N + (4 * H1 - 1) := by
    have h := Nat.div_mul_le_self (N + (4 * H1 - 1)) (4 * H1)
    unfold SubdiffusiveProcess.FiniteStopping.obsLo
    calc 4 * (H1 * ((N + (4 * H1 - 1)) / (4 * H1))) = (N + (4 * H1 - 1)) / (4 * H1) * (4 * H1) := by ring
      _ ≤ _ := h
  have hhi : 4 * (H1 * SubdiffusiveProcess.FiniteStopping.obsHi H1 N) ≤ 3 * N := by
    have h := Nat.div_mul_le_self (3 * N) (4 * H1)
    unfold SubdiffusiveProcess.FiniteStopping.obsHi
    calc 4 * (H1 * (3 * N / (4 * H1))) = 3 * N / (4 * H1) * (4 * H1) := by ring
      _ ≤ _ := h
  have hexp : H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) =
      H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N + H1 * s := Nat.mul_add _ _ _
  constructor
  · rw [hexp]
    unfold SubdiffusiveProcess.FiniteStopping.obsB at hs
    by_cases hle : SubdiffusiveProcess.FiniteStopping.obsLo H1 N ≤ SubdiffusiveProcess.FiniteStopping.obsHi H1 N
    · have hs' : SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s ≤ SubdiffusiveProcess.FiniteStopping.obsHi H1 N := by omega
      have := Nat.mul_le_mul_left H1 hs'
      rw [Nat.mul_add] at this
      omega
    · have hs0 : s = 0 := by omega
      subst hs0
      omega
  · unfold SubdiffusiveProcess.FiniteStopping.obsT0
    rw [hexp]
    generalize H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N = X
    generalize H1 * s = Y
    omega

theorem aux_lfsc_reference_grid_bound_reference_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (Hp : BilateralField d → C(SpatialCoordinates d, ℝ))
    (S k : ℕ) (x : SpatialCoordinates d) (hHm : Measurable (fun omega : BilateralField d => Hp omega x)) :
    Measurable (fun omega : BilateralField d =>
      SubdiffusiveProcess.FiniteStopping.reference model Hp omega S k x) := by
  unfold SubdiffusiveProcess.FiniteStopping.reference
  refine measurable_const.mul ?_
  refine (hHm.add ?_).exp
  apply Finset.measurable_sum
  intro i _
  exact (continuous_eval_const x).measurable.comp (measurable_pi_apply (-(i : ℤ)))

/-- **Union bound over the stage-2 cells** of one infrared parameter `Hp`: outside one event, the inverse
reference scale of every stage-2 cell is at most `3^{εN} r^{-η₀}`. -/
theorem aux_lfsc_reference_grid_bound_event {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
    (Hp : BilateralField d → C(SpatialCoordinates d, ℝ))
    {a η0 R c1 ε : ℝ} (ha : 0 < a) (hη0 : 0 < η0) (haη : a * η0 = (d : ℝ) + 1) (hc1 : 0 ≤ c1)
    (hδ : (4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) * (|-2 * a| + (-2 * a) ^ 2) * model.delta ^ 2 ≤ 1 / 4)
    (hH : ∀ x : SpatialCoordinates d, ‖x‖ ≤ R →
      Measurable (fun omega : BilateralField d => Hp omega x) ∧
      Integrable (fun omega : BilateralField d => Real.exp (-2 * a * Hp omega x))
        (chaosSampleLaw model).toMeasure ∧
      (∫ omega : BilateralField d, Real.exp (-2 * a * Hp omega x) ∂(chaosSampleLaw model).toMeasure) ≤ c1)
    (z : SpatialCoordinates d) (j : ℤ) (hR : ‖z‖ + (3 : ℝ) ^ j ≤ R) (H1 : ℕ) (hH1 : 0 < H1)
    (N S : ℕ) (hN : 2 * H1 ≤ N) (hNS : N ≤ S) :
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal
        (((N : ℝ) + 1) * ((c1 + 1) / 2 * (3 : ℝ) ^ (d * j.natAbs)) *
          Real.exp (-(a * ε * (N : ℝ) * Real.log 3))) ∧
      ∀ omega ∉ Bad,
        ∀ (w0 : Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
          (w : Fin s → OddGridIndex d (subdivisionHalfWidth H1)),
          s ≤ SubdiffusiveProcess.FiniteStopping.obsB H1 N →
        (SubdiffusiveProcess.FiniteStopping.reference model Hp omega S
          (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s))
          (descendantCenter (subdivisionHalfWidth H1)
            (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
            (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) s w))⁻¹ ≤
          (3 : ℝ) ^ (ε * (N : ℝ)) *
            (descendantSide (subdivisionHalfWidth H1) s
              (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ (-η0) := by
  classical
  have hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (lt_trans Real.exp_one_lt_d9 (by norm_num))
  -- the per-cell event
  let E : (s : ℕ) → (Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) →
      (Fin s → OddGridIndex d (subdivisionHalfWidth H1)) → Set (BilateralField d) :=
    fun s w0 w => {omega | Real.exp ((ε * (N : ℝ) +
        ((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) : ℕ) : ℝ) * η0) * Real.log 3) <
      (SubdiffusiveProcess.FiniteStopping.reference model Hp omega S
        (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s))
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
          (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) s w))⁻¹}
  -- every stage-2 centre lies in the ball of radius `R`
  have hcenR : ∀ (s : ℕ) w0 w, ‖descendantCenter (subdivisionHalfWidth H1)
      (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
      (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) s w‖ ≤ R := by
    intro s w0 w
    have hd := aux_lfsc_reference_grid_bound_centre_dist z j hr
      (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) (subdivisionHalfWidth H1) w0 s w
    rw [dist_eq_norm] at hd
    have := norm_le_norm_add_norm_sub' (descendantCenter (subdivisionHalfWidth H1)
      (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
      (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) s w) z
    linarith
  have hEmeas : ∀ s w0 w, MeasurableSet (E s w0 w) := by
    intro s w0 w
    have hm := aux_lfsc_reference_grid_bound_reference_measurable model Hp S
      (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s))
      (descendantCenter (subdivisionHalfWidth H1)
        (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
        (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) s w)
      (hH _ (hcenR s w0 w)).1
    exact measurableSet_lt measurable_const hm.inv
  -- the probability of one cell event
  have hEprob : ∀ s w0 w, s ≤ SubdiffusiveProcess.FiniteStopping.obsB H1 N →
      (chaosSampleLaw model).toMeasure (E s w0 w) ≤ ENNReal.ofReal
        ((c1 + Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) * (|-2 * a| + (-2 * a) ^ 2) *
          model.delta ^ 2 * ((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) : ℕ) : ℝ))) / 2 *
          Real.exp (-(a * ((ε * (N : ℝ) +
            ((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) : ℕ) : ℝ) * η0) * Real.log 3)))) := by
    intro s w0 w hs
    have hk := (aux_lfsc_reference_grid_bound_obs_arith H1 N hH1 hN j s hs).1
    obtain ⟨hm, hint, hle⟩ := hH _ (hcenR s w0 w)
    exact aux_lfsc_reference_grid_bound_point model Rm Hp S _ (hk.trans hNS) _ hm ha _ c1 hint hle
  refine ⟨⋃ s ∈ Finset.range (SubdiffusiveProcess.FiniteStopping.obsB H1 N + 1),
    ⋃ p : (Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) ×
      (Fin s → OddGridIndex d (subdivisionHalfWidth H1)), E s p.1 p.2, ?_, ?_, ?_⟩
  · exact Finset.measurableSet_biUnion _
      (fun s _ => MeasurableSet.iUnion (fun p => hEmeas s p.1 p.2))
  · set P := (chaosSampleLaw model).toMeasure with hP
    set W := Real.exp (-(a * ε * (N : ℝ) * Real.log 3)) with hW
    have hBN : SubdiffusiveProcess.FiniteStopping.obsB H1 N ≤ N := by
      unfold SubdiffusiveProcess.FiniteStopping.obsB SubdiffusiveProcess.FiniteStopping.obsHi
      refine le_trans (Nat.sub_le _ _) ?_
      apply Nat.div_le_of_le_mul
      nlinarith
    have hlev : ∀ s ∈ Finset.range (SubdiffusiveProcess.FiniteStopping.obsB H1 N + 1),
        P (⋃ p : (Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) ×
          (Fin s → OddGridIndex d (subdivisionHalfWidth H1)), E s p.1 p.2) ≤
        ENNReal.ofReal ((c1 + 1) / 2 * (3 : ℝ) ^ (d * j.natAbs) * W) := by
      intro s hs'
      have hs : s ≤ SubdiffusiveProcess.FiniteStopping.obsB H1 N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs')
      obtain ⟨hk, hk2⟩ := aux_lfsc_reference_grid_bound_obs_arith H1 N hH1 hN j s hs
      set kk : ℕ := H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) with hkk
      set E2 : ℝ := Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) * (|-2 * a| + (-2 * a) ^ 2) *
          model.delta ^ 2 * (kk : ℝ)) with hE2
      have hE2le : E2 ≤ (3 : ℝ) ^ kk := by
        have h1 : (4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) * (|-2 * a| + (-2 * a) ^ 2) *
            model.delta ^ 2 * (kk : ℝ) ≤ (kk : ℝ) * Real.log 3 := by
          have h2 := mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg kk : (0 : ℝ) ≤ kk)
          nlinarith [Nat.cast_nonneg (α := ℝ) kk]
        calc E2 ≤ Real.exp ((kk : ℝ) * Real.log 3) := Real.exp_le_exp.mpr h1
          _ = (3 : ℝ) ^ kk := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      have hcard := aux_lfsc_reference_grid_bound_card d H1
        (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) s
      have hcnt : (Fintype.card ((Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) ×
          (Fin s → OddGridIndex d (subdivisionHalfWidth H1))) : ℝ) ≤
          (3 : ℝ) ^ (d * j.natAbs) * (3 : ℝ) ^ (d * kk) := by
        rw [hcard, ← pow_add]
        apply pow_le_pow_right₀ (by norm_num)
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left d (by omega)
      have harith := aux_lfsc_reference_grid_bound_level_arith (d := d) (k := kk) j.natAbs (a := a) (η0 := η0)
        (ε := ε) (Nr := (N : ℝ)) (c1 := c1) (E2 := E2) (cnt := _) haη hc1 hE2le (Real.exp_pos _).le hcnt
      calc P (⋃ p : (Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) ×
            (Fin s → OddGridIndex d (subdivisionHalfWidth H1)), E s p.1 p.2)
          ≤ ∑ p : (Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) ×
            (Fin s → OddGridIndex d (subdivisionHalfWidth H1)), P (E s p.1 p.2) :=
            measure_iUnion_fintype_le _ _
        _ ≤ ∑ p : (Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) ×
            (Fin s → OddGridIndex d (subdivisionHalfWidth H1)),
            ENNReal.ofReal ((c1 + E2) / 2 * Real.exp (-(a * ((ε * (N : ℝ) + (kk : ℝ) * η0) * Real.log 3)))) :=
            Finset.sum_le_sum (fun p _ => hEprob s p.1 p.2 hs)
        _ = ENNReal.ofReal ((Fintype.card ((Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) →
              OddGridIndex d 1) × (Fin s → OddGridIndex d (subdivisionHalfWidth H1))) : ℝ) *
              ((c1 + E2) / 2 * Real.exp (-(a * ((ε * (N : ℝ) + (kk : ℝ) * η0) * Real.log 3))))) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        _ ≤ _ := ENNReal.ofReal_le_ofReal harith
    calc P (⋃ s ∈ Finset.range (SubdiffusiveProcess.FiniteStopping.obsB H1 N + 1),
          ⋃ p : (Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) ×
            (Fin s → OddGridIndex d (subdivisionHalfWidth H1)), E s p.1 p.2)
        ≤ ∑ s ∈ Finset.range (SubdiffusiveProcess.FiniteStopping.obsB H1 N + 1),
          P (⋃ p : (Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) ×
            (Fin s → OddGridIndex d (subdivisionHalfWidth H1)), E s p.1 p.2) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ s ∈ Finset.range (SubdiffusiveProcess.FiniteStopping.obsB H1 N + 1),
          ENNReal.ofReal ((c1 + 1) / 2 * (3 : ℝ) ^ (d * j.natAbs) * W) := Finset.sum_le_sum hlev
      _ = ENNReal.ofReal (((SubdiffusiveProcess.FiniteStopping.obsB H1 N + 1 : ℕ) : ℝ) *
            ((c1 + 1) / 2 * (3 : ℝ) ^ (d * j.natAbs) * W)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hBN' : ((SubdiffusiveProcess.FiniteStopping.obsB H1 N + 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
            exact_mod_cast Nat.succ_le_succ hBN
          have hpos : 0 ≤ (c1 + 1) / 2 * (3 : ℝ) ^ (d * j.natAbs) * W := by positivity
          calc ((SubdiffusiveProcess.FiniteStopping.obsB H1 N + 1 : ℕ) : ℝ) *
                ((c1 + 1) / 2 * (3 : ℝ) ^ (d * j.natAbs) * W)
              ≤ ((N : ℝ) + 1) * ((c1 + 1) / 2 * (3 : ℝ) ^ (d * j.natAbs) * W) :=
                mul_le_mul_of_nonneg_right hBN' hpos
            _ = _ := by ring
  · intro omega hom w0 s w hs
    have hnot : omega ∉ E s w0 w := by
      intro hmem
      exact hom (Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hs))
        (Set.mem_iUnion.mpr ⟨(w0, w), hmem⟩))
    change ¬ (Real.exp _ < _) at hnot
    have hle := not_lt.mp hnot
    refine hle.trans ?_
    rw [aux_lfsc_reference_grid_bound_side]
    have hint : (((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) : ℕ)) : ℤ) ≤
        -(j - ((1 * SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j : ℕ) : ℤ) - ((H1 * s : ℕ) : ℤ)) := by
      unfold SubdiffusiveProcess.FiniteStopping.obsT0
      rw [Nat.mul_add]
      generalize H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N = X
      generalize H1 * s = Y
      omega
    have hreal : (((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) : ℕ)) : ℝ) ≤
        -(((j - ((1 * SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j : ℕ) : ℤ) -
          ((H1 * s : ℕ) : ℤ) : ℤ) : ℝ)) := by exact_mod_cast hint
    set e : ℤ := j - ((1 * SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j : ℕ) : ℤ) - ((H1 * s : ℕ) : ℤ) with he
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ e := zpow_pos (by norm_num) e
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos h3pos, ← Real.exp_add,
      Real.log_zpow]
    apply Real.exp_le_exp.mpr
    have hη : 0 ≤ η0 * Real.log 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hreal hη]

/-- **Crude grid bound on the reference scale** (paper `\label{mfd:lem-finite-source-comparison}`, proof
paragraph 1): one event `Bad` of probability `≤ C 3^{-γN}`, independent of the infrared flag, outside which the
inverse reference scale of every stage-2 cell of side `r` is at most `3^{εN} r^{-η₀}`, `η₀ = min σ 1 / 2`. -/
theorem lfsc_reference_grid_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
    ∀ (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ), 0 < H1 →
    ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
      ∀ omega ∉ Bad, ∀ infrared : Bool,
      let Hused : BilateralField d → C(SpatialCoordinates d, ℝ) :=
        if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
      let source := if reverse then N else M
      let mg := subdivisionHalfWidth H1
      let t0 := SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j
      let B := SubdiffusiveProcess.FiniteStopping.obsB H1 N
      ∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg), s ≤ B →
        (SubdiffusiveProcess.FiniteStopping.reference model Hused omega source
          (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s))
          (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
            (descendantSide 1 t0 ((3 : ℝ) ^ j)) s w))⁻¹ ≤ (3 : ℝ) ^ (ε * (N : ℝ)) *
          (descendantSide mg s (descendantSide 1 t0 ((3 : ℝ) ^ j))) ^ (-(min σ 1 / 2)) := by
  classical
  obtain ⟨CH, hCH0, hHmom⟩ :=
    SubdiffusiveProcess.exists_uniform_compactExponentialMoment_of_infraredCharacterization
      (d := d) hd
  set η0 : ℝ := min σ 1 / 2 with hη0def
  have hη0 : 0 < η0 := by
    rw [hη0def]; have := lt_min hσ one_pos; linarith
  set a : ℝ := ((d : ℝ) + 1) / η0 with hadef
  have ha : 0 < a := by positivity
  have haη : a * η0 = (d : ℝ) + 1 := by rw [hadef]; field_simp
  set A : ℝ := 4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2 with hAdef
  set B0 : ℝ := A * (|-2 * a| + (-2 * a) ^ 2) with hB0def
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB00 : 0 ≤ B0 := by rw [hB0def]; positivity
  refine ⟨min 1 (1 / (B0 + 1)), lt_min one_pos (by positivity), ?_⟩
  intro model Rm H hH hδ z j H1 hH1 ε hε
  have hdpos : 0 < model.delta := model.shellPrefix.delta_pos
  have hδ1 : model.delta ≤ 1 := hδ.trans (min_le_left _ _)
  have hδ2 : model.delta ≤ 1 / (B0 + 1) := hδ.trans (min_le_right _ _)
  have hδsq : A * (|-2 * a| + (-2 * a) ^ 2) * model.delta ^ 2 ≤ 1 / 4 := by
    have h1 : B0 * model.delta ^ 2 ≤ B0 * (1 / (B0 + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdpos.le hδ2 2) hB00
    have h2 : B0 * (1 / (B0 + 1)) ^ 2 ≤ 1 / 4 := by
      rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (B0 - 1)]
    rw [hB0def] at h1 h2
    exact h1.trans h2
  -- the compact and the moment constants
  set R : ℝ := ‖z‖ + (3 : ℝ) ^ j with hRdef
  let Kc : TopologicalSpace.Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall (0 : SpatialCoordinates d) R, ProperSpace.isCompact_closedBall _ _⟩
  set c1 : ℝ := 2 * Real.exp (CH Kc * (-2 * a) ^ 2) with hc1def
  have hc1 : 2 ≤ c1 := by
    rw [hc1def]
    have := Real.one_le_exp (mul_nonneg (hCH0 Kc) (sq_nonneg (-2 * a)))
    linarith
  have hc10 : 0 ≤ c1 := by linarith
  have hHflag : ∀ x : SpatialCoordinates d, ‖x‖ ≤ R →
      Measurable (fun omega : BilateralField d => H omega x) ∧
      Integrable (fun omega : BilateralField d => Real.exp (-2 * a * H omega x))
        (chaosSampleLaw model).toMeasure ∧
      (∫ omega : BilateralField d, Real.exp (-2 * a * H omega x) ∂(chaosSampleLaw model).toMeasure) ≤ c1 := by
    intro x hx
    have hxK : x ∈ (Kc : Set (SpatialCoordinates d)) := by
      change x ∈ Metric.closedBall (0 : SpatialCoordinates d) R
      rwa [mem_closedBall_zero_iff]
    obtain ⟨hi, hle⟩ := aux_lfsc_reference_grid_bound_Hexp model H hH Kc (CH Kc)
      (fun lam hlam => hHmom model H hH Kc lam hlam) x hxK (-2 * a)
    refine ⟨(continuous_eval_const x).measurable.comp hH.1, hi, hle.trans ?_⟩
    rw [hc1def]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left (pow_le_one₀ hdpos.le hδ1 (n := 2)) (mul_nonneg (hCH0 Kc) (sq_nonneg (-2 * a)))
    nlinarith
  have hzflag : ∀ x : SpatialCoordinates d, ‖x‖ ≤ R →
      Measurable (fun omega : BilateralField d =>
        (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega x) ∧
      Integrable (fun omega : BilateralField d => Real.exp (-2 * a *
        (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega x)) (chaosSampleLaw model).toMeasure ∧
      (∫ omega : BilateralField d, Real.exp (-2 * a *
        (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega x) ∂(chaosSampleLaw model).toMeasure) ≤ c1 := by
    intro x _
    simp only [Pi.zero_apply, ContinuousMap.zero_apply, mul_zero, Real.exp_zero]
    refine ⟨measurable_const, integrable_const _, ?_⟩
    simp only [integral_const, smul_eq_mul, mul_one]
    have : (chaosSampleLaw model).toMeasure.real Set.univ = 1 := by simp
    rw [this]; linarith
  -- the constants of the statement
  set c2 : ℝ := (c1 + 1) / 2 * (3 : ℝ) ^ (d * j.natAbs) with hc2def
  have hc2 : 0 < c2 := by rw [hc2def]; positivity
  set γ : ℝ := a * ε / 2 with hγdef
  have hγ : 0 < γ := by positivity
  set μ : ℝ := γ * Real.log 3 with hμdef
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have hμ : 0 < μ := by rw [hμdef]; positivity
  refine ⟨2 * c2 * (1 / μ + 1), γ, 2 * H1, by positivity, hγ, ?_⟩
  intro N M hN hNM reverse
  have hNS : N ≤ (if reverse then N else M) := by
    by_cases hrev : reverse <;> simp [hrev, hNM]
  obtain ⟨Bad1, hm1, hp1, hprop1⟩ := aux_lfsc_reference_grid_bound_event model Rm H ha hη0 haη hc10 hδsq
    hHflag z j le_rfl H1 hH1 N (if reverse then N else M) hN hNS (ε := ε)
  obtain ⟨Bad2, hm2, hp2, hprop2⟩ := aux_lfsc_reference_grid_bound_event model Rm
    (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) ha hη0 haη hc10 hδsq
    hzflag z j le_rfl H1 hH1 N (if reverse then N else M) hN hNS (ε := ε)
  refine ⟨Bad1 ∪ Bad2, hm1.union hm2, ?_, ?_⟩
  · set W : ℝ := Real.exp (-(a * ε * (N : ℝ) * Real.log 3)) with hW
    have hWpos : 0 < W := Real.exp_pos _
    have hbnn : 0 ≤ ((N : ℝ) + 1) * c2 * W := by positivity
    have hN1 : (N : ℝ) + 1 ≤ (1 / μ + 1) * Real.exp (μ * (N : ℝ)) := by
      have hexp := Real.add_one_le_exp (μ * (N : ℝ))
      have h1μ : 0 < 1 / μ + 1 := by positivity
      have hexpand : (1 / μ + 1) * (μ * (N : ℝ) + 1) = (N : ℝ) + 1 / μ + μ * (N : ℝ) + 1 := by
        field_simp
        ring
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have h2 : (0 : ℝ) < 1 / μ := by positivity
      have hμN : 0 ≤ μ * (N : ℝ) := by positivity
      calc (N : ℝ) + 1 ≤ (N : ℝ) + 1 / μ + μ * (N : ℝ) + 1 := by linarith
        _ = (1 / μ + 1) * (μ * (N : ℝ) + 1) := hexpand.symm
        _ ≤ (1 / μ + 1) * Real.exp (μ * (N : ℝ)) := mul_le_mul_of_nonneg_left hexp h1μ.le
    have hprod : Real.exp (μ * (N : ℝ)) * W = (3 : ℝ) ^ (-γ * (N : ℝ)) := by
      rw [hW, ← Real.exp_add, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      congr 1
      rw [hμdef, hγdef]
      ring
    calc (chaosSampleLaw model).toMeasure (Bad1 ∪ Bad2)
        ≤ (chaosSampleLaw model).toMeasure Bad1 + (chaosSampleLaw model).toMeasure Bad2 :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (((N : ℝ) + 1) * c2 * W) + ENNReal.ofReal (((N : ℝ) + 1) * c2 * W) :=
          add_le_add hp1 hp2
      _ = ENNReal.ofReal (2 * (((N : ℝ) + 1) * c2 * W)) := by
          rw [← ENNReal.ofReal_add hbnn hbnn]; congr 1; ring
      _ ≤ ENNReal.ofReal (2 * c2 * (1 / μ + 1) * (3 : ℝ) ^ (-γ * (N : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← hprod]
          calc 2 * (((N : ℝ) + 1) * c2 * W) = 2 * c2 * (((N : ℝ) + 1) * W) := by ring
            _ ≤ 2 * c2 * ((1 / μ + 1) * Real.exp (μ * (N : ℝ)) * W) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_right hN1 hWpos.le
            _ = _ := by ring
  · intro omega hom infrared
    have h1 : omega ∉ Bad1 := fun h => hom (Or.inl h)
    have h2 : omega ∉ Bad2 := fun h => hom (Or.inr h)
    cases infrared
    · simpa using hprop2 omega h2
    · simpa using hprop1 omega h1

end SubdiffusiveProcess.Paper
