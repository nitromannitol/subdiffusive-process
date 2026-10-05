module

public import SubdiffusiveProcess.Paper.rem_resolved

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem aux_rem_resolved_uniform_sqrt_power_bound
    (C t : ℝ) (hC : 0 ≤ C) (ht : 0 ≤ t) (N : ℕ) :
    (1 + C * Real.sqrt (1 + (N : ℝ))) ^ t ≤
      (1 + C) ^ t * (1 + (N : ℝ)) ^ (t / 2) := by
  have hsqrt : 1 ≤ Real.sqrt (1 + (N : ℝ)) := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + (N : ℝ)),
      Real.sqrt_nonneg (1 + (N : ℝ))]
  have harg : 0 ≤ 1 + C * Real.sqrt (1 + (N : ℝ)) := by positivity
  have hcmp : 1 + C * Real.sqrt (1 + (N : ℝ)) ≤
      (1 + C) * Real.sqrt (1 + (N : ℝ)) := by nlinarith
  calc
    _ ≤ ((1 + C) * Real.sqrt (1 + (N : ℝ))) ^ t :=
      Real.rpow_le_rpow harg hcmp ht
    _ = (1 + C) ^ t * (Real.sqrt (1 + (N : ℝ))) ^ t := by
      rw [Real.mul_rpow (by linarith) (Real.sqrt_nonneg _)]
    _ = (1 + C) ^ t * (1 + (N : ℝ)) ^ (t / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : 0 ≤ 1 + (N : ℝ))]
      ring



theorem aux_rem_resolved_uniform_rate_bound
    (A C t a s : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (ha : a < s * Real.log 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      A * (1 + C * Real.sqrt (1 + (N : ℝ))) ^ t *
        Real.exp (a * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ s ≤ B := by
  obtain ⟨Brate, hBrate, hrate⟩ :=
    aux_rem_resolved_microscopic_poly_exp_bounded (t / 2)
      (s * Real.log 3 - a) (sub_pos.mpr ha)
  refine ⟨A * (1 + C) ^ t * Brate, by positivity, ?_⟩
  intro N
  have hid := aux_rem_resolved_microscopic_scale_exp_identity a s N
  have hfac : 0 ≤ A * Real.exp (a * (N : ℝ)) *
      ((3 : ℝ) ^ (-(N : ℝ))) ^ s := by positivity
  have hstep := mul_le_mul_of_nonneg_left
    (aux_rem_resolved_uniform_sqrt_power_bound C t hC ht N) hfac
  have hright := mul_le_mul_of_nonneg_left (hrate N)
    (mul_nonneg hA (Real.rpow_nonneg (by linarith : 0 ≤ 1 + C) t))
  calc
    A * (1 + C * Real.sqrt (1 + (N : ℝ))) ^ t *
        Real.exp (a * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ s =
      (A * Real.exp (a * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ s) *
        (1 + C * Real.sqrt (1 + (N : ℝ))) ^ t := by ring
    _ ≤ (A * Real.exp (a * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ s) *
          ((1 + C) ^ t * (1 + (N : ℝ)) ^ (t / 2)) := hstep
    _ = (A * (1 + C) ^ t) *
          ((1 + (N : ℝ)) ^ (t / 2) * Real.exp (a * (N : ℝ)) *
            ((3 : ℝ) ^ (-(N : ℝ))) ^ s) := by ring
    _ = (A * (1 + C) ^ t) *
          ((1 + (N : ℝ)) ^ (t / 2) *
            Real.exp (-(s * Real.log 3 - a) * (N : ℝ))) := by
              simp only [mul_assoc, hid]
    _ ≤ A * (1 + C) ^ t * Brate := by simpa [mul_assoc] using hright



theorem aux_rem_resolved_uniform_scaled_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p z : ℝ) (f : Ω → ℝ) (F B : ℝ)
    (hz : 0 ≤ z) (hF : 0 ≤ F)
    (hf : eLpNorm f (ENNReal.ofReal p) P ≤ ENNReal.ofReal F)
    (hnum : F * z ≤ B) :
    eLpNorm (fun w => f w * z)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal B := by
  calc
    _ = ENNReal.ofReal z * eLpNorm f (ENNReal.ofReal p) P := by
      have hfun : (fun w => f w * z) = (fun w => z * f w) := by funext w; ring
      rw [hfun]
      exact aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm P p _ hz f
    _ ≤ ENNReal.ofReal z * ENNReal.ofReal F :=
      mul_le_mul_of_nonneg_left hf zero_le
    _ = ENNReal.ofReal (F * z) := by
      rw [ENNReal.ofReal_mul hF]
      ac_rfl
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hnum

/-- Small isolated-context companion used inside `rem_resolved_uniform`'s own proof: weakens the
per-model growth-rate moment bound (from `lem_extremes`'s own `hmb`) from the true, model-dependent
rate to a FIXED worst-case rate, via `exp` monotonicity. Extracted to a top-level lemma (avoiding
`gcongr` inline) because `gcongr`'s automation timed out when run directly inside the large ambient
context of `rem_resolved_uniform`'s proof -- same family of heartbeat-budget issue documented in
`rem_bank_neumann_coercive_uniform`'s RECEIPT.md. -/
theorem aux_rem_resolved_uniform_hSb2_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (q : ℝ)
    (g : Ω → ℝ) (Cpe rate rmaxHalf : ℝ) (N : ℕ)
    (hCpe : 0 ≤ Cpe) (hrate_le : rate ≤ rmaxHalf)
    (hg : eLpNorm g (ENNReal.ofReal q) P ≤ ENNReal.ofReal (Cpe * Real.exp (rate * (N : ℝ)))) :
    eLpNorm (fun om => ‖g om‖ + ‖g om‖) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (2 * Cpe * Real.exp (rmaxHalf * (N : ℝ))) := by
  have h2 : (fun om => ‖g om‖ + ‖g om‖) = fun om => (2 : ℝ) * ‖g om‖ := by funext om; ring
  have hexp_mono : Real.exp (rate * (N : ℝ)) ≤ Real.exp (rmaxHalf * (N : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate_le (Nat.cast_nonneg N))
  have hstep : Cpe * Real.exp (rate * (N : ℝ)) ≤ Cpe * Real.exp (rmaxHalf * (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hexp_mono hCpe
  have hgm : AEStronglyMeasurable g P :=
    (show MemLp g (ENNReal.ofReal q) P from lt_of_le_of_lt hg ENNReal.ofReal_lt_top).aestronglyMeasurable
  rw [h2, aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm P q 2 (by norm_num), eLpNorm_norm g hgm]
  calc ENNReal.ofReal 2 * eLpNorm g (ENNReal.ofReal q) P
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal (Cpe * Real.exp (rate * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hg zero_le
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (Cpe * Real.exp (rmaxHalf * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hstep) zero_le
    _ = ENNReal.ofReal (2 * (Cpe * Real.exp (rmaxHalf * (N : ℝ)))) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
    _ = ENNReal.ofReal (2 * Cpe * Real.exp (rmaxHalf * (N : ℝ))) := by congr 1; ring



theorem aux_rem_resolved_uniform_hstat
    (d : ℕ) (hd : 2 ≤ d) (t t1 : ℝ) (ht : (d : ℝ) - 1 < t)
    (p CD CE CK aRate : ℝ) (hp : 1 ≤ p)
    (hCD : 0 ≤ CD) (hCE : 0 ≤ CE) (hCK : 0 ≤ CK) (ha0 : 0 ≤ aRate)
    (ha : aRate < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ D M mInv Kmac : ℕ → Ω → ℝ,
      (∀ N w, 0 ≤ D N w ∧ 0 ≤ M N w ∧ 0 ≤ mInv N w ∧ 0 ≤ Kmac N w) →
      (∀ N, MemLp (D N) (ENNReal.ofReal (2 * p * max 1 t)) P ∧
        MemLp (M N) (ENNReal.ofReal (2 * p * max 1 t)) P ∧
        MemLp (mInv N) (ENNReal.ofReal (2 * p * max 1 t)) P ∧
        MemLp (Kmac N) (ENNReal.ofReal (2 * p * max 1 t)) P) →
      (∀ N, eLpNorm (D N) (ENNReal.ofReal (2 * p * max 1 t)) P ≤
        ENNReal.ofReal (CD * Real.sqrt (1 + (N : ℝ)))) →
      (∀ N, eLpNorm (fun w => M N w + mInv N w) (ENNReal.ofReal (2 * p * max 1 t)) P ≤
        ENNReal.ofReal (CE * Real.exp (aRate * (N : ℝ)))) →
      (∀ N, eLpNorm (Kmac N) (ENNReal.ofReal (2 * p * max 1 t)) P ≤ ENNReal.ofReal CK) →
      ∀ N : ℕ,
        eLpNorm (fun w => (1 + D N w) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N w)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B ∧
        eLpNorm (fun w => mInv N w * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B ∧
        eLpNorm (fun w => M N w * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + D N w) ^ t)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B := by
  have ht0 : 0 ≤ t := by
    have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hlog : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  have hrate1 : 0 < (t1 - t) * Real.log 3 := by
    have hle : min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 ≤
        (t1 - t) * Real.log 3 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hlog
    exact lt_of_le_of_lt ha0 (lt_of_lt_of_le ha hle)
  have hrate2 : aRate < ((d : ℝ) + 2 - t) * Real.log 3 := by
    have hle : min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 ≤
        ((d : ℝ) + 2 - t) * Real.log 3 :=
      mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hlog
    exact lt_of_lt_of_le ha hle
  have hrate3 : aRate < ((d : ℝ) - t) * Real.log 3 := by
    have hle : min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 ≤
        ((d : ℝ) - t) * Real.log 3 :=
      mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hlog
    exact lt_of_lt_of_le ha hle
  obtain ⟨B1, hB1, hrateB1⟩ :=
    aux_rem_resolved_uniform_rate_bound CK CD t 0 (t1 - t) hCK hCD ht0 hrate1
  obtain ⟨B2, hB2, hrateB2⟩ :=
    aux_rem_resolved_uniform_rate_bound CE 0 0 aRate ((d : ℝ) + 2 - t) hCE (le_refl _)
      (le_refl _) hrate2
  obtain ⟨B3, hB3, hrateB3⟩ :=
    aux_rem_resolved_uniform_rate_bound CE CD t aRate ((d : ℝ) - t) hCE hCD ht0 hrate3
  refine ⟨max B1 (max B2 B3), le_trans hB1 (le_max_left _ _), ?_⟩
  intro Ω _ P _ D M mInv Kmac hnonneg hLp hDnorm hSumnorm hKnorm N
  have hDN := (hLp N).1
  have hMN := (hLp N).2.1
  have hmN := (hLp N).2.2.1
  have hKN := (hLp N).2.2.2
  have hKprod := aux_rem_resolved_microscopic_K_product_bound P p t
    (CD * Real.sqrt (1 + (N : ℝ))) CK hp ht0
    (mul_nonneg hCD (Real.sqrt_nonneg _)) hCK
    (D N) (Kmac N) (fun w => (hnonneg N w).1)
    hDN hKN (hDnorm N) (hKnorm N)
  have hMprod := aux_rem_resolved_microscopic_M_product_bound P p t
    (CD * Real.sqrt (1 + (N : ℝ)))
    (CE * Real.exp (aRate * (N : ℝ))) hp ht0
    (mul_nonneg hCD (Real.sqrt_nonneg _)) (mul_nonneg hCE (Real.exp_pos _).le)
    (D N) (M N) (mInv N)
    (fun w => (hnonneg N w).1) (fun w => (hnonneg N w).2.1)
    (fun w => (hnonneg N w).2.2.1)
    hDN hMN (hDnorm N) (hSumnorm N)
  have hmBound := aux_rem_resolved_microscopic_mInv_bound P p t
    (CE * Real.exp (aRate * (N : ℝ))) hp
    (M N) (mInv N) (fun w => (hnonneg N w).2.1)
    (fun w => (hnonneg N w).2.2.1) hmN (hSumnorm N)
  have hKnum : CK * (1 + CD * Real.sqrt (1 + (N : ℝ))) ^ t *
      ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) ≤ B1 := by
    simpa using hrateB1 N
  have hmNum : CE * Real.exp (aRate * (N : ℝ)) *
      ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) ≤ B2 := by
    simpa using hrateB2 N
  have hMnum : (CE * Real.exp (aRate * (N : ℝ))) *
      (1 + CD * Real.sqrt (1 + (N : ℝ))) ^ t *
      ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) ≤ B3 := by
    convert hrateB3 N using 1 ; ring
  refine ⟨?_, ?_, ?_⟩
  · have hscale := aux_rem_resolved_uniform_scaled_bound P p
        (((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t))
        (fun w => (1 + D N w) ^ t * Kmac N w)
        (CK * (1 + CD * Real.sqrt (1 + (N : ℝ))) ^ t) B1
        (by positivity) (by positivity) hKprod hKnum
    have hle : ENNReal.ofReal B1 ≤ ENNReal.ofReal (max B1 (max B2 B3)) :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have := hscale.trans hle
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this
  · have hscale := aux_rem_resolved_uniform_scaled_bound P p
        (((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (mInv N) (CE * Real.exp (aRate * (N : ℝ))) B2
        (by positivity) (by positivity) hmBound hmNum
    exact hscale.trans (ENNReal.ofReal_le_ofReal
      (le_trans (le_max_left _ _) (le_max_right _ _)))
  · have hscale := aux_rem_resolved_uniform_scaled_bound P p
        (((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t))
        (fun w => M N w * (1 + D N w) ^ t)
        ((CE * Real.exp (aRate * (N : ℝ))) *
          (1 + CD * Real.sqrt (1 + (N : ℝ))) ^ t) B3
        (by positivity) (by positivity) hMprod hMnum
    have hle : ENNReal.ofReal B3 ≤ ENNReal.ofReal (max B1 (max B2 B3)) :=
      ENNReal.ofReal_le_ofReal (le_trans (le_max_right _ _) (le_max_right _ _))
    have := hscale.trans hle
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this

/-- Small isolated-context companion used inside `rem_resolved_uniform`'s own proof: instantiates
the hoisted `aux_rem_resolved_uniform_hstat`'s universally-quantified tail at one model's own random
fields, producing the three per-N moment bounds needed by `hmom`. Extracted to a top-level lemma
(rather than inlining the instantiation, which applies an opaque multi-∀ fact to four distinct
function arguments) because inlining it pushed `rem_resolved_uniform`'s overall elaboration past the
200000-heartbeat budget -- same family of decl-head whnf timeout documented in
`rem_bank_neumann_coercive_uniform`'s RECEIPT.md. -/
theorem aux_rem_resolved_uniform_Cbound_M
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t t1 p CD CE CK aRate Cbound_val : ℝ)
    (hall : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ D M mInv Kmac : ℕ → Ω → ℝ,
      (∀ N w, 0 ≤ D N w ∧ 0 ≤ M N w ∧ 0 ≤ mInv N w ∧ 0 ≤ Kmac N w) →
      (∀ N, MemLp (D N) (ENNReal.ofReal (2 * p * max 1 t)) P ∧
        MemLp (M N) (ENNReal.ofReal (2 * p * max 1 t)) P ∧
        MemLp (mInv N) (ENNReal.ofReal (2 * p * max 1 t)) P ∧
        MemLp (Kmac N) (ENNReal.ofReal (2 * p * max 1 t)) P) →
      (∀ N, eLpNorm (D N) (ENNReal.ofReal (2 * p * max 1 t)) P ≤
        ENNReal.ofReal (CD * Real.sqrt (1 + (N : ℝ)))) →
      (∀ N, eLpNorm (fun w => M N w + mInv N w) (ENNReal.ofReal (2 * p * max 1 t)) P ≤
        ENNReal.ofReal (CE * Real.exp (aRate * (N : ℝ)))) →
      (∀ N, eLpNorm (Kmac N) (ENNReal.ofReal (2 * p * max 1 t)) P ≤ ENNReal.ofReal CK) →
      ∀ N : ℕ,
        eLpNorm (fun w => (1 + D N w) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N w)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cbound_val ∧
        eLpNorm (fun w => mInv N w * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cbound_val ∧
        eLpNorm (fun w => M N w * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + D N w) ^ t)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cbound_val)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (De mlow mhigh U V : ℕ → BilateralField d → ℝ)
    (hDe0 : ∀ N om, 0 ≤ De N om) (hU0 : ∀ N om, 0 ≤ U N om)
    (hV1 : ∀ N om, 0 ≤ 1 + V N om)
    (hDeLp : ∀ N, MemLp (De N) (ENNReal.ofReal (2 * p * max 1 t)) (chaosSampleLaw M).toMeasure)
    (hmLp : ∀ N, MemLp (fun om => mhigh N om + (mlow N om)⁻¹) (ENNReal.ofReal (2 * p * max 1 t))
      (chaosSampleLaw M).toMeasure)
    (hDeb : ∀ N, eLpNorm (De N) (ENNReal.ofReal (2 * p * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CD * Real.sqrt (1 + (N : ℝ))))
    (hSb2 : ∀ N, eLpNorm (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ + ‖mhigh N om + (mlow N om)⁻¹‖)
      (ENNReal.ofReal (2 * p * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CE * Real.exp (aRate * (N : ℝ))))
    (hWfst : ∀ N, MemLp (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * p * max 1 t))
      (chaosSampleLaw M).toMeasure)
    (hWsnd : ∀ N, eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * p * max 1 t))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CK) :
    ∀ N,
      eLpNorm (fun om => (1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) *
          (U N om * (1 + V N om))) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cbound_val ∧
      eLpNorm (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cbound_val ∧
      eLpNorm (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) *
          (1 + De N om) ^ t) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cbound_val := fun N =>
  hall (BilateralField d) (chaosSampleLaw M).toMeasure De
    (fun N om => ‖mhigh N om + (mlow N om)⁻¹‖) (fun N om => ‖mhigh N om + (mlow N om)⁻¹‖)
    (fun N om => U N om * (1 + V N om))
    (fun N om => ⟨hDe0 N om, norm_nonneg _, norm_nonneg _, mul_nonneg (hU0 N om) (hV1 N om)⟩)
    (fun N => ⟨hDeLp N, (hmLp N).norm, (hmLp N).norm, hWfst N⟩)
    hDeb hSb2 hWsnd N

/-- Small isolated-context companion used inside `rem_resolved_uniform`'s own proof: the
three-term moment bound for `K`, taking the measurability/eLpNorm facts about the model's random
fields as PRE-COMPUTED parameters (rather than re-deriving them inline) so the caller never needs
to state their types itself. Extracted to a top-level lemma because inlining this derivation
(`AEStronglyMeasurable` products plus a Hölder downgrade plus one call to
`aux_rem_resolved_three_term_moment`) was part of what pushed `rem_resolved_uniform`'s overall
elaboration past the 200000-heartbeat budget. -/
theorem aux_rem_resolved_uniform_hmom
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t t1 pmax Cm Cmic Cp Cbound_val : ℝ)
    (hA1 : 0 ≤ Cm * 2 ^ t1) (hA2 : 0 ≤ Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1))
    (hA3 : 0 ≤ Cmic * 2 ^ t) (hCp : 0 ≤ Cp) (hCbound_val0 : 0 ≤ Cbound_val) (hpmax : 1 ≤ pmax)
    (hpq : pmax ≤ 2 * pmax * max 1 t) (ht_nn : 0 ≤ t)
    (k : ℕ) (ps : Fin k → ℝ) (hps_le : ∀ i, ps i ≤ pmax)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (U V De mlow mhigh : ℕ → BilateralField d → ℝ)
    (N : ℕ)
    (hDe0 : ∀ om, 0 ≤ De N om)
    (hDeLp : MemLp (De N) (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure)
    (hW1 : MemLp (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
      (chaosSampleLaw M).toMeasure)
    (hW2 : eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)))
    (hmNorm : AEStronglyMeasurable (fun om => ‖mhigh N om + (mlow N om)⁻¹‖)
      (chaosSampleLaw M).toMeasure)
    (hCbound_M :
      eLpNorm (fun om => (1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) *
          (U N om * (1 + V N om))) (ENNReal.ofReal pmax) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cbound_val ∧
      eLpNorm (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (ENNReal.ofReal pmax) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cbound_val ∧
      eLpNorm (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) *
          (1 + De N om) ^ t) (ENNReal.ofReal pmax) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cbound_val) :
    ∀ i : Fin k,
      MemLp (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * Cbound_val + (Cmic * 2 ^ t) * Cbound_val) := by
  intro i
  have hDt := (aux_rem_resolved_microscopic_one_add_power_memLp (chaosSampleLaw M).toMeasure
    pmax t hpmax ht_nn (De N) hDe0 hDeLp).aestronglyMeasurable
  have hWm := hW1.aestronglyMeasurable
  have hWb : eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal pmax)
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)).trans hW2
  have hT1m : AEStronglyMeasurable (fun om =>
      (1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om)))
      (chaosSampleLaw M).toMeasure :=
    (hDt.mul aestronglyMeasurable_const).mul hWm
  have hT2m : AEStronglyMeasurable (fun om =>
      ‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
      (chaosSampleLaw M).toMeasure :=
    hmNorm.mul aestronglyMeasurable_const
  exact aux_rem_resolved_three_term_moment (chaosSampleLaw M).toMeasure pmax _ _ _
    (Cp * (1 + Cp)) Cbound_val hpmax hA1 hA2 hA3 (by positivity) hCbound_val0 _ _ _ hWm hT1m hT2m
    hWb hCbound_M.1 hCbound_M.2.1 (ps i) (hps_le i)

/-- Model-uniform twin of `rem_resolved` (`rem_resolved`): same
conclusion, with the moment bound `Cbound : Fin k → ℝ` chosen once, before `∀ M`, instead of inside
it. Every ingredient of the frozen proof up to the point where it consults
`aux_rem_resolved_microscopic_statistical_conjunct` on the model's own random fields is reused
completely unchanged (`rem_resolved_meshes`, `aux_rem_resolved_micro_local`, `rem_resolved_microscopic`,
`lem_extremes`, `aux_rem_resolved_rate`, `aux_rem_resolved_UV_moment`,
`aux_rem_resolved_three_term_moment`, `aux_rem_resolved_sample`, `aux_rem_resolved_second`); the one
change is: the growth-rate threshold is tightened by a factor 2 (`rmax / 2` in place of `rmax`) so
that the true per-model rate `Cde·δ+Cpe·δ²` is bounded by the FIXED `rmax / 2`, and
`aux_rem_resolved_uniform_hstat` above (in place of `aux_rem_resolved_microscopic_statistical_conjunct`)
is invoked ONCE, before `∀ M`, at this fixed rate, producing one moment bound `Cbound_val` reused by
every model. Does not edit `rem_resolved` or `rem_resolved_microscopic`. -/
theorem rem_resolved_uniform :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < (d : ℝ) →
    (∀ i : Fin k, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧ ∃ Cbound : Fin k → ℝ,
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d M) (Sreg : in_6_16 d M)
      (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
    let a : ℕ → BilateralField d → PositiveCoefficient Q :=
      fun N omega => cutoffPositiveCoefficient M H omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
    ∃ (K : ℕ → BilateralField d → ℝ),
      (∀ N omega, 0 ≤ K N omega) ∧
      (∀ i N,
        MemLp (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
      (∀ i N,
        eLpNorm (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (∀ N : ℕ,
          ∀ f : SpatialCoordinates d → ℝ,
            AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
          ∀ Kf : ℝ, 0 ≤ Kf →
            (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
              |f y| ≤ Kf) →
            (∫ y in (Q : Set (SpatialCoordinates d)), f y) = 0 →
          ∀ u : meanZeroSobolevGraph Q,
            SolvesNeumann (a N omega) f u →
          ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (a N omega)
              (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
              (sobolevGradient (u : SobolevData Q)) ≤
                K N omega *
                  (sobolevCoefficientForm (a N omega)
                    (u : SobolevData Q) (u : SobolevData Q) + Kf ^ 2) * r ^ t) ∧
        (∀ N : ℕ,
          ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho →
            (∀ tau : ℝ, 0 ≤ rho tau) →
            (∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
            (∫ tau, rho tau) = 1 →
          ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
          ∀ Cρ : ℝ, 0 ≤ Cρ →
            (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
              ∀ y : SpatialCoordinates d, y ∈ (Q : Set (SpatialCoordinates d)) →
                |faceBump rho pvec eps y| ≤ Cρ * eps⁻¹) →
          ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
          ∀ v : meanZeroSobolevGraph Q,
            SolvesNeumann (a N omega) (faceBump rho pvec eps) v →
          ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (a N omega)
              (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
              (sobolevGradient (v : SobolevData Q)) ≤
                K N omega *
                  (sobolevCoefficientForm (a N omega)
                    (v : SobolevData Q) (v : SobolevData Q) +
                    Cρ ^ 2 * eps ^ (-2 : ℝ)) * r ^ t) := by
  intro d hd _ _ E _P _X _W D t k ps ht_low ht_high hps
  have hdt : 0 < (d : ℝ) - t := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht_nn : 0 ≤ t := by linarith
  have hex1 : ∃ t1 : ℝ, t1 = t + ((d : ℝ) - t) / 3 := ⟨_, rfl⟩
  obtain ⟨t1, ht1⟩ := hex1
  have hex0 : ∃ t0 : ℝ, t0 = t + 2 * ((d : ℝ) - t) / 3 := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ := hex0
  have htt1 : t < t1 := by rw [ht1]; linarith
  have ht1d : t1 < (d : ℝ) := by rw [ht1]; linarith
  have ht0_low : (d : ℝ) - 1 < t0 := by rw [ht0]; linarith
  have ht0_high : t0 < (d : ℝ) := by rw [ht0]; linarith
  have heta_pos : 0 < t0 - t1 := by rw [ht0, ht1]; linarith
  have heta_lt : t0 - t1 < t0 - ((d : ℝ) - 1) := by rw [ht0, ht1]; linarith
  have hetas_pos : 0 < ((d : ℝ) + 2 - t0) / 2 := by linarith
  have hetas_lt : ((d : ℝ) + 2 - t0) / 2 < (d : ℝ) + 2 - t0 := by linarith
  have hexp : ∃ pmax : ℝ, pmax = 1 + ∑ i : Fin k, |ps i| := ⟨_, rfl⟩
  obtain ⟨pmax, hpmax_def⟩ := hexp
  have hsum_nn : 0 ≤ ∑ i : Fin k, |ps i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hpmax : 1 ≤ pmax := by rw [hpmax_def]; linarith
  have hps_le : ∀ i : Fin k, ps i ≤ pmax := by
    intro i
    have h1 : ps i ≤ |ps i| := le_abs_self _
    have h2 : |ps i| ≤ ∑ j : Fin k, |ps j| :=
      Finset.single_le_sum (f := fun j => |ps j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hpmax_def]; linarith
  have hmax1 : (1 : ℝ) ≤ max 1 t := le_max_left _ _
  have hq1 : 1 ≤ 2 * pmax * max 1 t := by nlinarith
  have hpq : pmax ≤ 2 * pmax * max 1 t := by nlinarith
  have hqmesh_p : 1 ≤ 2 * (2 * pmax * max 1 t) := by linarith
  have hqmesh_q : 2 * (2 * pmax * max 1 t) ≤
      max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) := le_max_left _ _
  have hqmesh_eta : (d : ℝ) <
      max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) := by
    have h1 : ((d : ℝ) + 1) / (t0 - t1) * (t0 - t1) = (d : ℝ) + 1 := by
      field_simp
    have h2 : ((d : ℝ) + 1) / (t0 - t1) * (t0 - t1) ≤
        max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) heta_pos.le
    linarith
  have hRpos : (0 : ℝ) < (3 : ℝ) ^ (-7 : ℤ) / 2 := by positivity
  have hRlt : (3 : ℝ) ^ (-7 : ℤ) / 2 < 1 / (100 * 10) := by norm_num
  have hRmem : (3 : ℝ) ^ (-7 : ℤ) / 2 ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) := ⟨-7, rfl⟩
  have hM := rem_resolved_meshes d hd 10 ((3 : ℝ) ^ (-7 : ℤ) / 2) t0 (t0 - t1)
    (((d : ℝ) + 2 - t0) / 2) (2 * (2 * pmax * max 1 t))
    (max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1))) (by norm_num) hRpos hRlt hRmem
    ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt hqmesh_p hqmesh_q hqmesh_eta
  rcases hM with ⟨_, -, _, _, Cm, delta0m, Cp, _, -, -, hCm, hdelta0m, hCp, -, _,
    _, -, -, -, _, _, -, -, hmesh⟩
  have hp1 : (2 : ℝ) ≤ 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by
    have : 0 ≤ 4 * (d : ℝ) / ((d : ℝ) - t) := by positivity
    linarith
  have htp : t < (d : ℝ) - 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) := by
    have hp1pos : 0 < 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by linarith
    have hkey : 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) < ((d : ℝ) - t) / 2 := by
      rw [div_lt_iff₀ hp1pos]
      have h4 : ((d : ℝ) - t) * (4 * (d : ℝ) / ((d : ℝ) - t)) = 4 * (d : ℝ) := by
        field_simp
      nlinarith
    linarith
  have hml := aux_rem_resolved_micro_local d hd _W (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) t t1 hp1
    ht_low htt1 ht1d htp
  rcases hml with ⟨Cmic, hCmic, hmicL⟩
  have hX := aux_lem_extremes_compat d hd (fun _ => (1 / 2 : ℝ)) 1 one_pos (2 * pmax * max 1 t) hq1
  rcases hX with ⟨Cpe, Cde, cde, hCpe, hCde, hcde, hextM⟩
  have hexr : ∃ rmax : ℝ,
      rmax = min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := ⟨_, rfl⟩
  obtain ⟨rmax, hrmax_def⟩ := hexr
  have hrmax : 0 < rmax := by
    rw [hrmax_def]
    refine mul_pos (lt_min (by linarith) (lt_min (by linarith) hdt)) ?_
    exact Real.log_pos (by norm_num)
  have hrmax2 : 0 < rmax / 2 := by linarith
  have hrmax2' : rmax / 2 < rmax := by linarith
  have ha2 : rmax / 2 < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 :=
    hrmax_def ▸ hrmax2'
  have hqpos : 0 < 2 * pmax * max 1 t := by linarith
  have hCE0 : (0 : ℝ) ≤ 2 * Cpe := by positivity
  have hCK0 : (0 : ℝ) ≤ Cp * (1 + Cp) := by positivity
  -- HOISTED: the moment bound is produced once, before ∀ M, at the fixed rate `rmax / 2`.
  obtain ⟨Cbound_val, hCbound_val0, hCbound_val_all⟩ :=
    aux_rem_resolved_uniform_hstat d hd t t1 ht_low pmax Cpe (2 * Cpe) (Cp * (1 + Cp)) (rmax / 2)
      hpmax hCpe.le hCE0 hCK0 hrmax2.le ha2
  have hA1 : 0 ≤ Cm * 2 ^ t1 := mul_nonneg hCm.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA3 : 0 ≤ Cmic * 2 ^ t := mul_nonneg hCmic.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA2 : 0 ≤ Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1) :=
    mul_nonneg hA3 (mul_nonneg hCm.le
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _).le)
  refine ⟨min (min delta0m (cde / (2 * pmax * max 1 t)))
      (min 1 ((rmax / 2) / (2 * (Cde + Cpe)))),
    lt_min (lt_min hdelta0m (div_pos hcde hqpos)) (lt_min one_pos (div_pos hrmax2 (by positivity))),
    fun _ : Fin k => (Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
      (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * Cbound_val + (Cmic * 2 ^ t) * Cbound_val,
    ?_⟩
  intro M _Rm Sreg _It H hIR hδ Q a
  clear hd2 ht1 ht0 ht1d ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt hRpos hRlt hRmem
    hqmesh_p hqmesh_q hqmesh_eta hp1 htp hsum_nn hpmax_def hmax1 hqpos hCE0 hCK0 ha2 hrmax2' hdt
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδm : M.delta ≤ delta0m := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδe : M.delta ≤ cde / (2 * pmax * max 1 t) :=
    hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr2 : M.delta ≤ (rmax / 2) / (2 * (Cde + Cpe)) :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrate2 := aux_rem_resolved_rate Cde Cpe (rmax / 2) M.delta hCde hCpe hrmax2 hδpos hδ1 hδr2
  have hmM := hmesh M E _P _X _Rm Sreg _It D H hIR hδm
  rcases hmM with ⟨_, U, V, -, -, hU0, hV0, hULp, hVLp, hUb, hVb, hae⟩
  have heM := hextM M H hIR hδe
  rcases heM with ⟨De, mlow, mhigh, hDe0, heae, hDeLp, hmLp, hDeb, hmb⟩
  -- Weakened statistical hypothesis: the TRUE per-model rate is ≤ the FIXED `rmax / 2`.
  have hSb2 : ∀ N : ℕ,
      eLpNorm (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ + ‖mhigh N om + (mlow N om)⁻¹‖)
        (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * Cpe * Real.exp ((rmax / 2) * (N : ℝ))) := fun N =>
    aux_rem_resolved_uniform_hSb2_bound (chaosSampleLaw M).toMeasure (2 * pmax * max 1 t)
      (fun om => mhigh N om + (mlow N om)⁻¹) Cpe (Cde * M.delta + Cpe * M.delta ^ 2) (rmax / 2) N
      hCpe.le hrate2.2.le (hmb N)
  have hV1 : ∀ N om, 0 ≤ 1 + V N om := fun N om => by linarith [hV0 N om]
  have hW : ∀ N, MemLp (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
      (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) := fun N =>
    aux_rem_resolved_UV_moment (chaosSampleLaw M).toMeasure (2 * pmax * max 1 t) Cp hq1 hCp.le
      (U N) (V N) (hULp N) (hVLp N) (hUb N) (hVb N)
  have hW1 : ∀ N, MemLp (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
      (chaosSampleLaw M).toMeasure := fun N => (hW N).1
  have hW2 : ∀ N, eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) := fun N => (hW N).2
  have hCbound_M := aux_rem_resolved_uniform_Cbound_M d t t1 pmax Cpe (2 * Cpe) (Cp * (1 + Cp))
    (rmax / 2) Cbound_val hCbound_val_all M De mlow mhigh U V hDe0 hU0 hV1 hDeLp hmLp hDeb hSb2
    hW1 hW2
  have hmom : ∀ (i : Fin k) (N : ℕ),
      MemLp (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * Cbound_val + (Cmic * 2 ^ t) * Cbound_val) := by
    intro i N
    exact aux_rem_resolved_uniform_hmom d t t1 pmax Cm Cmic Cp Cbound_val hA1 hA2 hA3 hCp.le
      hCbound_val0 hpmax hpq ht_nn k ps hps_le M U V De mlow mhigh N (hDe0 N) (hDeLp N) (hW1 N)
      (hW2 N) (hmLp N).norm.aestronglyMeasurable (hCbound_M N) i
  refine ⟨fun N om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)),
    ?_, fun i N => (hmom i N).1, fun i N => (hmom i N).2, ?_⟩
  · intro N om
    have h1 : 0 ≤ U N om * (1 + V N om) := mul_nonneg (hU0 N om) (hV1 N om)
    have h2 : 0 ≤ (1 + De N om) ^ t := (Real.rpow_pos_of_pos (by linarith [hDe0 N om]) _).le
    have h3 : 0 ≤ ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h4 : 0 ≤ ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h5 := norm_nonneg (mhigh N om + (mlow N om)⁻¹)
    exact add_nonneg (add_nonneg (mul_nonneg hA1 h1) (mul_nonneg hA2 (mul_nonneg (mul_nonneg h2 h3) h1)))
      (mul_nonneg hA3 (mul_nonneg h5 h4))
  · filter_upwards [hae, heae] with om hω1 hω2
    have hfirst := fun N : ℕ => aux_rem_resolved_sample d M H om N t t1 t0 Cm Cmic
      (U N om) (V N om) (De N om) (mlow N om) (mhigh N om) (le_of_lt htt1) hCm.le hCmic
      (hU0 N om) (hV0 N om) (hDe0 N om) (hω2 N).2.1 (hω2 N).2.2 (hω2 N).1
      (hmicL ((3 : ℝ) ^ (-(N : ℝ))) (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)))
      ((hω1 N).2.2.2.2)
    exact ⟨hfirst, fun N => aux_rem_resolved_second (a N om) _ t (hfirst N)⟩

end SubdiffusiveProcess.Paper
