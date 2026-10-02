import SubdiffusiveProcess.Static.CutoffUnitCoercivity

/-! # Near-pair covers and fractional readout on arbitrary real cubes

This deterministic geometry is independent of any random coefficient.
It is adapted from the proved static coercivity geometry.
-/

open MeasureTheory Set TopologicalSpace Metric SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The Gagliardo double integral of `tight_static`'s coercivity clause. -/
def fractionalCoverIntegral {d : ℕ} (f : SpatialCoordinates d → ℝ) (U : Set (SpatialCoordinates d)) : ℝ≥0∞ :=
  ∫⁻ x in U, ∫⁻ z in U, ENNReal.ofReal ((f x - f z) ^ 2) /
    ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))

theorem cubeCover_oneDimensional (s t : ℝ) (ht : 0 < t) (hts : t < s) :
    ∃ A : Finset ℝ, (A.card : ℝ) ≤ 2 * s / t + 2 ∧
      (∀ a ∈ A, ∀ u : ℝ, |u - a| < t / 2 → |u| < s / 2) ∧
      ∀ u v : ℝ, |u| < s / 2 → |v| < s / 2 → |u - v| < t / 4 →
        ∃ a ∈ A, |u - a| < t / 2 ∧ |v - a| < t / 2 := by
  classical
  have hst : 0 < s - t := sub_pos.mpr hts
  have hq_pos : 0 < 2 * (s - t) / t := by positivity
  have hq_nn : 0 ≤ 2 * (s - t) / t := le_of_lt hq_pos
  set m : ℕ := ⌈2 * (s - t) / t⌉₊ with hm
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact Nat.one_le_ceil_iff.mpr hq_pos
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hm_ge : 2 * (s - t) / t ≤ (m : ℝ) := by
    rw [hm]
    exact Nat.le_ceil _
  have hm_lt : (m : ℝ) < 2 * (s - t) / t + 1 := by
    rw [hm]
    exact Nat.ceil_lt_add_one hq_nn
  set h : ℝ := (s - t) / m with hh
  have hh_nn : 0 ≤ h := by
    rw [hh]
    positivity
  have h_le : h ≤ t / 2 := by
    have h1 : 2 * (s - t) ≤ (m : ℝ) * t := by
      have h2 := hm_ge
      rw [div_le_iff₀ ht] at h2
      exact h2
    rw [hh, div_le_iff₀ hmpos]
    nlinarith
  have hmh : (m : ℝ) * h = s - t := by
    rw [hh]
    exact mul_div_cancel₀ (s - t) hmne
  set b : ℕ → ℝ := fun j => -(s / 2) + j * h with hb
  have hb_mono : ∀ {i j : ℕ}, i ≤ j → b i ≤ b j := by
    intro i j hij
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hhij : (i : ℝ) * h ≤ (j : ℝ) * h := mul_le_mul_of_nonneg_right hij' hh_nn
    rw [hb]
    linarith
  have hbm : b m = s / 2 - t := by
    rw [hb]
    dsimp only
    rw [hmh]
    ring
  have hbsucc : ∀ j : ℕ, b (j + 1) = b j + h := by
    intro j
    rw [hb]
    push_cast
    ring
  set A : Finset ℝ := (Finset.range (m + 1)).image (fun j => b j + t / 2) with hA
  refine ⟨A, ?_, ?_, ?_⟩
  · have hcard_le : A.card ≤ m + 1 := by
      rw [hA]
      calc ((Finset.range (m + 1)).image (fun j => b j + t / 2)).card
          ≤ (Finset.range (m + 1)).card := Finset.card_image_le
        _ = m + 1 := Finset.card_range _
    have hcard1 : (A.card : ℝ) ≤ (m : ℝ) + 1 := by
      have h' : (A.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hcard_le
      simpa using h'
    have htne : t ≠ 0 := ne_of_gt ht
    have hsimp : 2 * (s - t) / t + 2 = 2 * s / t := by
      field_simp
      ring
    have hcard2 : (m : ℝ) + 1 < 2 * s / t + 2 := by
      linarith [hm_lt, hsimp]
    linarith
  · intro a ha u hu
    rw [hA] at ha
    obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp ha
    have hjle : j ≤ m := by
      have hj' := Finset.mem_range.mp hj
      omega
    have hbj_ge : -(s / 2) ≤ b j := by
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hj0h : 0 ≤ (j : ℝ) * h := mul_nonneg hj0 hh_nn
      rw [hb]
      linarith
    have hbj_le : b j ≤ s / 2 - t := by
      have h1 := hb_mono hjle
      rwa [hbm] at h1
    have hulp := (abs_lt.mp hu).1
    have hup := (abs_lt.mp hu).2
    rw [abs_lt]
    constructor
    · linarith
    · linarith
  · intro u v hu hv huv
    set lo : ℝ := min u v with hlo
    set hi : ℝ := max u v with hhi
    have hlo_gt : -(s / 2) < lo := by
      rw [hlo]
      exact lt_min_iff.mpr ⟨(abs_lt.mp hu).1, (abs_lt.mp hv).1⟩
    have hhi_lt : hi < s / 2 := by
      rw [hhi]
      exact max_lt_iff.mpr ⟨(abs_lt.mp hu).2, (abs_lt.mp hv).2⟩
    have hsub : hi - lo = |u - v| := by
      rw [hlo, hhi]
      exact (max_sub_min_eq_abs u v).trans (abs_sub_comm v u)
    have hlo_le_u : lo ≤ u := by rw [hlo]; exact min_le_left u v
    have hlo_le_v : lo ≤ v := by rw [hlo]; exact min_le_right u v
    have hu_le_hi : u ≤ hi := by rw [hhi]; exact le_max_left u v
    have hv_le_hi : v ≤ hi := by rw [hhi]; exact le_max_right u v
    have hP0 : b 0 < lo := by
      have hb0 : b 0 = -(s / 2) := by
        rw [hb]
        push_cast
        ring
      linarith
    set j : ℕ := Nat.findGreatest (fun k => b k < lo) m with hj
    have hjm : j ≤ m := by
      rw [hj]
      exact Nat.findGreatest_le m
    have hjP : b j < lo := by
      rw [hj]
      exact Nat.findGreatest_spec (P := fun k => b k < lo) (Nat.zero_le m) hP0
    have hkey : hi < b j + t := by
      by_cases hjm' : j = m
      · rw [hjm', hbm]
        linarith
      · have hnotP : ¬ (b (j + 1) < lo) := by
          have h1 : Nat.findGreatest (fun k => b k < lo) m < j + 1 := by
            rw [← hj]
            exact Nat.lt_succ_self j
          have h2 : j + 1 ≤ m := by omega
          exact Nat.findGreatest_is_greatest h1 h2
        have hlo_le_succ : lo ≤ b (j + 1) := le_of_not_gt hnotP
        have hsucc_le : b (j + 1) ≤ b j + t / 2 := by
          rw [hbsucc j]
          linarith
        have hlt : hi - lo < t / 4 := by
          rw [hsub]
          exact huv
        linarith
    refine ⟨b j + t / 2, ?_, ?_, ?_⟩
    · rw [hA]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjm), rfl⟩
    · rw [abs_lt]
      constructor <;> linarith
    · rw [abs_lt]
      constructor <;> linarith

theorem cubeCover_product {d : ℕ} (s t : ℝ) (ht : 0 < t) (hts : t < s) (A : Finset ℝ)
    (hcard : (A.card : ℝ) ≤ 2 * s / t + 2)
    (hsub : ∀ a ∈ A, ∀ u : ℝ, |u - a| < t / 2 → |u| < s / 2)
    (hcov : ∀ u v : ℝ, |u| < s / 2 → |v| < s / 2 → |u - v| < t / 4 →
        ∃ a ∈ A, |u - a| < t / 2 ∧ |v - a| < t / 2) :
    ∃ Y : Finset (Fin d → ℝ),
      (Y.card : ℝ) ≤ (2 * s / t + 2) ^ d ∧
      (∀ y ∈ Y, Metric.ball y (t / 2) ⊆ Metric.ball (0 : Fin d → ℝ) (s / 2)) ∧
      ∀ x ∈ Metric.ball (0 : Fin d → ℝ) (s / 2),
        ∀ z ∈ Metric.ball (0 : Fin d → ℝ) (s / 2), ‖x - z‖ < t / 4 →
          ∃ y ∈ Y, x ∈ Metric.ball y (t / 2) ∧ z ∈ Metric.ball y (t / 2) := by
  refine ⟨Fintype.piFinset (fun _ : Fin d => A), ?_, ?_, ?_⟩
  · have hcard' : ((Fintype.piFinset (fun _ : Fin d => A)).card : ℝ) = (A.card : ℝ) ^ d := by
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_pow]
    rw [hcard']
    exact pow_le_pow_left₀ (by positivity) hcard d
  · intro y hy x hx
    have hspos : 0 < s / 2 := by linarith
    have htpos : 0 < t / 2 := by linarith
    rw [Metric.mem_ball] at hx ⊢
    rw [dist_pi_lt_iff hspos]
    intro i
    have hyi : y i ∈ A := (Fintype.mem_piFinset.mp hy) i
    have hxdist : dist (x i) (y i) < t / 2 := (dist_pi_lt_iff htpos).mp hx i
    have hxi : |x i - y i| < t / 2 := by rw [Real.dist_eq] at hxdist; exact hxdist
    have := hsub (y i) hyi (x i) hxi
    rw [Real.dist_eq]
    simpa using this
  · intro x hx z hz hxz
    have hspos : 0 < s / 2 := by linarith
    have htpos : 0 < t / 2 := by linarith
    have h4pos : 0 < t / 4 := by linarith
    rw [Metric.mem_ball] at hx hz
    have hxi : ∀ i, |x i| < s / 2 := by
      intro i
      have := (dist_pi_lt_iff hspos).mp hx i
      rw [Real.dist_eq] at this
      simpa using this
    have hzi : ∀ i, |z i| < s / 2 := by
      intro i
      have := (dist_pi_lt_iff hspos).mp hz i
      rw [Real.dist_eq] at this
      simpa using this
    have hxzi : ∀ i, |x i - z i| < t / 4 := by
      intro i
      have := (pi_norm_lt_iff h4pos).mp hxz i
      rw [Real.norm_eq_abs, Pi.sub_apply] at this
      exact this
    refine ⟨fun i => Classical.choose (hcov (x i) (z i) (hxi i) (hzi i) (hxzi i)), ?_, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      exact (Classical.choose_spec (hcov (x i) (z i) (hxi i) (hzi i) (hxzi i))).1
    · rw [Metric.mem_ball, dist_pi_lt_iff htpos]
      intro i
      rw [Real.dist_eq]
      exact (Classical.choose_spec (hcov (x i) (z i) (hxi i) (hzi i) (hxzi i))).2.1
    · rw [Metric.mem_ball, dist_pi_lt_iff htpos]
      intro i
      rw [Real.dist_eq]
      exact (Classical.choose_spec (hcov (x i) (z i) (hxi i) (hzi i) (hxzi i))).2.2

/-- **(COVER)** Near pairs of a sup-norm ball of radius `s/2` are covered by boundedly many
sup-norm balls of radius `t/2` inside it.  Route: per coordinate `m := ⌈2(s-t)/t⌉₊ ≥ 1`,
`h := (s-t)/m ≤ t/2`, starts `a_j := -s/2 + j h` (`j ≤ m`, `a_m = s/2 - t`), centres
`a_j + t/2`; for `x_i ≤ z_i < x_i + t/4` take the largest `j` with `a_j < x_i`. -/
theorem exists_cube_nearPair_cover {d : ℕ} (s t : ℝ) (ht : 0 < t) (hts : t < s) :
    ∃ Y : Finset (SpatialCoordinates d),
      (Y.card : ℝ) ≤ (2 * s / t + 2) ^ d ∧
      (∀ y ∈ Y, Metric.ball y (t / 2) ⊆ Metric.ball (0 : SpatialCoordinates d) (s / 2)) ∧
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2),
        ∀ z ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2), ‖x - z‖ < t / 4 →
          ∃ y ∈ Y, x ∈ Metric.ball y (t / 2) ∧ z ∈ Metric.ball y (t / 2) := by
  obtain ⟨A, hcard, hsub, hcov⟩ := cubeCover_oneDimensional s t ht hts
  exact cubeCover_product s t ht hts A hcard hsub hcov



/-- The Gagliardo kernel `k(x,z) = (f x - f z)^2 / ‖x - z‖^{d+3/2}` (as in `fractionalCoverIntegral`). -/
def cubeFractionalKernel {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x z : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((f x - f z) ^ 2) / ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))

/-- (GS1) Near part: restricting both variables to a measurable `B` by indicators is bounded by
the Gagliardo integral over `B`. Route: `lintegral_indicator` twice / `setLIntegral_mono_set`-type
comparison `∫⁻ x in V, B.indicator g x ≤ ∫⁻ x in B, g x` (`lintegral_indicator hB`,
`Measure.restrict_mono`/`Measure.restrict_restrict`), inner and outer. -/
theorem fractionalCover_near {d : ℕ} (f : (Fin d → ℝ) → ℝ) (V B : Set (Fin d → ℝ))
    (hB : MeasurableSet B) :
    ∫⁻ x in V, ∫⁻ z in V, B.indicator 1 x * B.indicator 1 z * cubeFractionalKernel f x z ≤
      fractionalCoverIntegral f B := by
  have h_inner_eq (x : Fin d → ℝ) :
      ∫⁻ z in V, B.indicator 1 z * cubeFractionalKernel f x z =
        ∫⁻ z in V ∩ B, cubeFractionalKernel f x z := by
    have h_pointwise : ∀ z : Fin d → ℝ,
        B.indicator 1 z * cubeFractionalKernel f x z =
          B.indicator (cubeFractionalKernel f x) z := by
      intro z; simp [Set.indicator]
    calc
      ∫⁻ z in V, B.indicator 1 z * cubeFractionalKernel f x z
          = ∫⁻ z, B.indicator 1 z * cubeFractionalKernel f x z ∂(Measure.restrict volume V) := rfl
      _ = ∫⁻ z, B.indicator (cubeFractionalKernel f x) z ∂(Measure.restrict volume V) := by
        rw [lintegral_congr h_pointwise]
      _ = ∫⁻ z in V, B.indicator (cubeFractionalKernel f x) z := rfl
      _ = ∫⁻ z in B ∩ V, cubeFractionalKernel f x z := by rw [setLIntegral_indicator hB]
      _ = ∫⁻ z in V ∩ B, cubeFractionalKernel f x z := by rw [Set.inter_comm]
  have h_outer_eq : ∀ x : Fin d → ℝ,
      B.indicator 1 x * (∫⁻ z in V ∩ B, cubeFractionalKernel f x z) =
        B.indicator (fun x => ∫⁻ z in V ∩ B, cubeFractionalKernel f x z) x := by
    intro x; simp [Set.indicator]
  have h_inter_subset : V ∩ B ⊆ B := fun _ h => h.2
  have h_indicator_ne_top (x : Fin d → ℝ) : B.indicator 1 x ≠ ∞ := by
    rw [Set.indicator]
    split <;> simp
  calc
    ∫⁻ x in V, ∫⁻ z in V, B.indicator 1 x * B.indicator 1 z * cubeFractionalKernel f x z
        = ∫⁻ x in V, B.indicator 1 x * (∫⁻ z in V, B.indicator 1 z * cubeFractionalKernel f x z) := by
      refine lintegral_congr fun x => ?_
      calc
        ∫⁻ z in V, B.indicator 1 x * B.indicator 1 z * cubeFractionalKernel f x z
            = ∫⁻ z in V, B.indicator 1 x * (B.indicator 1 z * cubeFractionalKernel f x z) := by
          refine lintegral_congr fun z => ?_
          ring
        _ = B.indicator 1 x * ∫⁻ z in V, B.indicator 1 z * cubeFractionalKernel f x z := by
          rw [lintegral_const_mul' (B.indicator 1 x) _ (h_indicator_ne_top x)]
    _ = ∫⁻ x in V, B.indicator 1 x * (∫⁻ z in V ∩ B, cubeFractionalKernel f x z) := by
      refine lintegral_congr fun x => ?_
      simp [h_inner_eq x]
    _ = ∫⁻ x, B.indicator 1 x * (∫⁻ z in V ∩ B, cubeFractionalKernel f x z)
        ∂(Measure.restrict volume V) := rfl
    _ = ∫⁻ x, B.indicator (fun x => ∫⁻ z in V ∩ B, cubeFractionalKernel f x z) x
        ∂(Measure.restrict volume V) := by
      rw [lintegral_congr (μ := Measure.restrict volume V) h_outer_eq]
    _ = ∫⁻ x in V, B.indicator (fun x => ∫⁻ z in V ∩ B, cubeFractionalKernel f x z) x := rfl
    _ = ∫⁻ x in B ∩ V, (∫⁻ z in V ∩ B, cubeFractionalKernel f x z) := by
      rw [setLIntegral_indicator hB]
    _ = ∫⁻ x in V ∩ B, (∫⁻ z in V ∩ B, cubeFractionalKernel f x z) := by rw [Set.inter_comm]
    _ ≤ ∫⁻ x in B, (∫⁻ z in V ∩ B, cubeFractionalKernel f x z) :=
      lintegral_mono_set h_inter_subset
    _ ≤ ∫⁻ x in B, (∫⁻ z in B, cubeFractionalKernel f x z) :=
      lintegral_mono fun x => lintegral_mono_set h_inter_subset
    _ = fractionalCoverIntegral f B := rfl

/-- (GS2) Far part: pairs at distance `≥ t/4` cost at most `4 (4/t)^{d+3/2} s^d ∫_V f²`. Route:
pointwise `k ≤ ofReal((f x - f z)^2) * ofReal((4/t)^e)` when `‖x-z‖ ≥ t/4` (then
`‖x-z‖^e ≥ (t/4)^e`, `Real.rpow_le_rpow`), `(f x - f z)^2 ≤ 2 f x^2 + 2 f z^2`; Tonelli-free: each
of the two terms integrates to `vol(V) * ∫_V f²` with `vol(ball 0 (s/2)) = ofReal s ^ d`
(`Real.volume_pi_ball`, sup norm), `lintegral_const_mul`, `lintegral_add_left`. -/
theorem fractionalCover_far {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ∫⁻ x in Metric.ball (0 : Fin d → ℝ) (s / 2), ∫⁻ z in Metric.ball (0 : Fin d → ℝ) (s / 2),
        (if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0) ≤
      ENNReal.ofReal (4 * (4 / t) ^ ((d : ℝ) + 3 / 2) * s ^ d) *
        ∫⁻ x in Metric.ball (0 : Fin d → ℝ) (s / 2), ENNReal.ofReal (f x ^ 2) := by
  set V := Metric.ball (0 : Fin d → ℝ) (s / 2)
  set e := (d : ℝ) + 3 / 2
  have hV : MeasurableSet V := measurableSet_ball
  have hvol : ∫⁻ x in V, (1 : ℝ≥0∞) = ENNReal.ofReal (s ^ d) := by
    rw [setLIntegral_const V (c := 1)]
    dsimp [V]
    rw [Real.volume_pi_ball (0 : Fin d → ℝ) (half_pos hs)]
    have h_eq : (2 * (s / 2)) = s := by ring
    simp [Fintype.card_fin, h_eq]
  have ht4_pos : 0 < t / 4 := div_pos ht (by norm_num)
  have h_pointwise (x z : Fin d → ℝ) :
      (if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0) ≤
        2 * ENNReal.ofReal ((4 / t) ^ e) * (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f z ^ 2)) := by
    by_cases hfar : t / 4 ≤ ‖x - z‖
    · rw [if_pos hfar]
      dsimp [cubeFractionalKernel]
      have h_norm_pos : 0 < ‖x - z‖ := by linarith
      have he_pos : 0 ≤ e := by
        have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
        positivity
      have h_rpow : (t / 4) ^ e ≤ ‖x - z‖ ^ e :=
        Real.rpow_le_rpow (div_nonneg ht.le (by norm_num)) hfar he_pos
      have h_denom_pos : 0 < ENNReal.ofReal (‖x - z‖ ^ e) :=
        ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos h_norm_pos _)
      have h_denom_bound : ENNReal.ofReal ((t / 4) ^ e) ≤ ENNReal.ofReal (‖x - z‖ ^ e) :=
        ENNReal.ofReal_le_ofReal h_rpow
      have h_inv_bound : (ENNReal.ofReal (‖x - z‖ ^ e))⁻¹ ≤ (ENNReal.ofReal ((t / 4) ^ e))⁻¹ :=
        (ENNReal.inv_le_inv).mpr h_denom_bound
      have h_sq_bound : ENNReal.ofReal ((f x - f z) ^ 2) ≤
          2 * ENNReal.ofReal (f x ^ 2) + 2 * ENNReal.ofReal (f z ^ 2) := by
        have h_sq_real : (f x - f z) ^ 2 ≤ 2 * (f x ^ 2) + 2 * (f z ^ 2) := by
          have h_nonneg_sq : 0 ≤ (f x + f z) ^ 2 := pow_two_nonneg _
          nlinarith
        calc
          ENNReal.ofReal ((f x - f z) ^ 2) ≤ ENNReal.ofReal (2 * (f x ^ 2) + 2 * (f z ^ 2)) :=
            ENNReal.ofReal_le_ofReal h_sq_real
          _ = ENNReal.ofReal (2 * (f x ^ 2)) + ENNReal.ofReal (2 * (f z ^ 2)) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity)]
          _ = ENNReal.ofReal 2 * ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal 2 * ENNReal.ofReal (f z ^ 2) := by
            simp [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
          _ = 2 * ENNReal.ofReal (f x ^ 2) + 2 * ENNReal.ofReal (f z ^ 2) := by norm_num
      have h_inv_eq : (ENNReal.ofReal ((t / 4) ^ e))⁻¹ = ENNReal.ofReal ((4 / t) ^ e) := by
        calc
          (ENNReal.ofReal ((t / 4) ^ e))⁻¹ = ENNReal.ofReal (((t / 4) ^ e)⁻¹) := by
            rw [ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (div_pos ht (by norm_num)) _)]
          _ = ENNReal.ofReal ((4 / t) ^ e) := by
            congr 1
            calc
              ((t / 4) ^ e)⁻¹ = ((t / 4)⁻¹) ^ e := by
                rw [Real.inv_rpow (by positivity : 0 ≤ t / 4) _]
              _ = (4 / t) ^ e := by ring
      calc
        ENNReal.ofReal ((f x - f z) ^ 2) / ENNReal.ofReal (‖x - z‖ ^ e)
            = ENNReal.ofReal ((f x - f z) ^ 2) * (ENNReal.ofReal (‖x - z‖ ^ e))⁻¹ := rfl
        _ ≤ ENNReal.ofReal ((f x - f z) ^ 2) * (ENNReal.ofReal ((t / 4) ^ e))⁻¹ := by
          gcongr
        _ = ENNReal.ofReal ((f x - f z) ^ 2) * ENNReal.ofReal ((4 / t) ^ e) := by rw [h_inv_eq]
        _ ≤ (2 * ENNReal.ofReal (f x ^ 2) + 2 * ENNReal.ofReal (f z ^ 2)) * ENNReal.ofReal ((4 / t) ^ e) :=
          mul_le_mul' h_sq_bound (le_refl _)
        _ = 2 * ENNReal.ofReal ((4 / t) ^ e) * (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f z ^ 2)) := by
          ring
    · rw [if_neg hfar]
      positivity
  have h_meas_fx2 : Measurable fun x : Fin d → ℝ => ENNReal.ofReal (f x ^ 2) :=
    Measurable.ennreal_ofReal (Measurable.pow_const hf 2)
  have h_meas_fz2 : Measurable fun z : Fin d → ℝ => ENNReal.ofReal (f z ^ 2) :=
    Measurable.ennreal_ofReal (Measurable.pow_const hf 2)
  have h_meas_fx2_V : AEMeasurable (fun x : Fin d → ℝ => ENNReal.ofReal (f x ^ 2)) (volume.restrict V) :=
    (h_meas_fx2.aemeasurable.restrict (s := V))
  have h_meas_fz2_V : AEMeasurable (fun z : Fin d → ℝ => ENNReal.ofReal (f z ^ 2)) (volume.restrict V) :=
    (h_meas_fz2.aemeasurable.restrict (s := V))
  have h_meas_const_V (c : ℝ≥0∞) : AEMeasurable (fun _ : Fin d → ℝ => c) (volume.restrict V) :=
    ((measurable_const.aemeasurable (μ := volume)).restrict (s := V))
  have h_sum_double : ∫⁻ x in V, ∫⁻ z in V, (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f z ^ 2)) =
      2 * ENNReal.ofReal (s ^ d) * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2)) := by
    set C := ∫⁻ z in V, ENNReal.ofReal (f z ^ 2)
    have hC : C = ∫⁻ x in V, ENNReal.ofReal (f x ^ 2) := rfl
    have h_vol_eq : volume V = ENNReal.ofReal (s ^ d) := by
      calc
        volume V = 1 * volume V := by simp
        _ = ∫⁻ x in V, (1 : ℝ≥0∞) := by rw [setLIntegral_const V (c := 1)]
        _ = ENNReal.ofReal (s ^ d) := hvol
    have h_inner (x : Fin d → ℝ) : ∫⁻ z in V, (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f z ^ 2)) =
        ENNReal.ofReal (f x ^ 2) * volume V + C := by
      rw [lintegral_add_left' (h_meas_const_V (ENNReal.ofReal (f x ^ 2))) (fun z => ENNReal.ofReal (f z ^ 2))]
      rw [setLIntegral_const V (c := ENNReal.ofReal (f x ^ 2)), hC]
    calc
      ∫⁻ x in V, ∫⁻ z in V, (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f z ^ 2))
          = ∫⁻ x in V, (ENNReal.ofReal (f x ^ 2) * volume V + C) := by
        refine setLIntegral_congr_fun hV fun x hx => h_inner x
      _ = (∫⁻ x in V, ENNReal.ofReal (f x ^ 2) * volume V) + (∫⁻ x in V, C) := by
        rw [lintegral_add_left' (h_meas_fx2_V.mul_const (volume V)) (fun _ => C)]
      _ = (∫⁻ x in V, ENNReal.ofReal (f x ^ 2)) * volume V + C * volume V := by
        rw [lintegral_mul_const (volume V) h_meas_fx2, setLIntegral_const V (c := C)]
      _ = (∫⁻ x in V, ENNReal.ofReal (f x ^ 2)) * volume V + volume V * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2)) := by
        rw [hC]
        ring
      _ = 2 * volume V * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2)) := by ring
      _ = 2 * ENNReal.ofReal (s ^ d) * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2)) := by rw [h_vol_eq]
  calc
    ∫⁻ x in V, ∫⁻ z in V, (if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0)
        ≤ ∫⁻ x in V, ∫⁻ z in V,
          2 * ENNReal.ofReal ((4 / t) ^ e) * (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f z ^ 2)) := by
      refine setLIntegral_mono' hV fun x hx => ?_
      refine setLIntegral_mono' hV fun z hz => h_pointwise x z
    _ = 2 * ENNReal.ofReal ((4 / t) ^ e) *
        ∫⁻ x in V, ∫⁻ z in V, (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f z ^ 2)) := by
      have hC_ne_top : 2 * ENNReal.ofReal ((4 / t) ^ e) ≠ ∞ :=
        ENNReal.mul_ne_top (by norm_num) (by exact ENNReal.ofReal_ne_top)
      have h_inner (x : Fin d → ℝ) : ∫⁻ z in V,
          2 * ENNReal.ofReal ((4 / t) ^ e) * (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f z ^ 2)) =
          2 * ENNReal.ofReal ((4 / t) ^ e) * ∫⁻ z in V, (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f z ^ 2)) := by
        rw [lintegral_const_mul' _ _ hC_ne_top]
      rw [lintegral_congr h_inner]
      rw [lintegral_const_mul' _ _ hC_ne_top]
    _ = 2 * ENNReal.ofReal ((4 / t) ^ e) *
        (2 * ENNReal.ofReal (s ^ d) * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2))) := by rw [h_sum_double]
    _ = 4 * ENNReal.ofReal ((4 / t) ^ e) * ENNReal.ofReal (s ^ d) * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2)) := by ring
    _ = ENNReal.ofReal 4 * ENNReal.ofReal ((4 / t) ^ e) * ENNReal.ofReal (s ^ d) * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2)) := by norm_num
    _ = ENNReal.ofReal (4 * (4 / t) ^ e) * ENNReal.ofReal (s ^ d) * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2)) := by
      rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (4 : ℝ))]
    _ = ENNReal.ofReal (4 * (4 / t) ^ e * s ^ d) * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2)) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * (4 / t) ^ e)]
    _ = ENNReal.ofReal (4 * (4 / t) ^ ((d : ℝ) + 3 / 2) * s ^ d) *
        ∫⁻ x in Metric.ball (0 : Fin d → ℝ) (s / 2), ENNReal.ofReal (f x ^ 2) := by
      simp [e, V]

/-- (GS3) Pointwise split on `V × V` from the covering property. -/
theorem fractionalCover_pointwise {d : ℕ} (f : (Fin d → ℝ) → ℝ) (s t : ℝ)
    (Y : Finset (Fin d → ℝ))
    (hcov : ∀ x ∈ Metric.ball (0 : Fin d → ℝ) (s / 2),
      ∀ z ∈ Metric.ball (0 : Fin d → ℝ) (s / 2), ‖x - z‖ < t / 4 →
        ∃ y ∈ Y, x ∈ Metric.ball y (t / 2) ∧ z ∈ Metric.ball y (t / 2))
    (x z : Fin d → ℝ) (hx : x ∈ Metric.ball (0 : Fin d → ℝ) (s / 2))
    (hz : z ∈ Metric.ball (0 : Fin d → ℝ) (s / 2)) :
    cubeFractionalKernel f x z ≤
      (∑ y ∈ Y, (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
          cubeFractionalKernel f x z) +
        (if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0) := by
  by_cases hfar : t / 4 ≤ ‖x - z‖
  · rw [if_pos hfar]
    have hsum_nonneg : 0 ≤ ∑ y ∈ Y, (Metric.ball y (t / 2)).indicator 1 x *
        (Metric.ball y (t / 2)).indicator 1 z * cubeFractionalKernel f x z :=
      Finset.sum_nonneg fun y _ => by positivity
    exact le_add_of_nonneg_left hsum_nonneg
  · rw [if_neg hfar]
    have hnear : ‖x - z‖ < t / 4 := by linarith
    rcases hcov x hx z hz hnear with ⟨y, hy, hxy, hzy⟩
    have h_term_nonneg (y' : Fin d → ℝ) : 0 ≤ (Metric.ball y' (t / 2)).indicator 1 x *
        (Metric.ball y' (t / 2)).indicator 1 z * cubeFractionalKernel f x z := by
      positivity
    calc
      cubeFractionalKernel f x z
          = ((Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z) *
              cubeFractionalKernel f x z := by
        simp [hxy, hzy]
      _ ≤ ∑ y' ∈ Y, (Metric.ball y' (t / 2)).indicator 1 x *
          (Metric.ball y' (t / 2)).indicator 1 z * cubeFractionalKernel f x z :=
        Finset.single_le_sum (fun y' _ => h_term_nonneg y') hy
      _ = (∑ y' ∈ Y, (Metric.ball y' (t / 2)).indicator 1 x *
          (Metric.ball y' (t / 2)).indicator 1 z * cubeFractionalKernel f x z) + 0 := by simp

/-- (GS4) Integrating the pointwise split: the double integral over `V` of `k` is at most the sum
of the Finset-sum part and the far part. Route: `setLIntegral_mono`-style monotonicity on `V`
(inner, then outer; use `ae_restrict_mem`/`setLIntegral_congr_fun`-type pointwise-on-`V` bounds
from `hpt`), then `lintegral_add_left`/`lintegral_add_right` and `lintegral_finset_sum`
(measurability from `hf`: `Measurable.ennreal_ofReal`, `measurable_norm`, `ENNReal.measurable_div`
/`Measurable.div`, `measurable_const.indicator`, `Measurable.ite`), inner then outer. -/
theorem fractionalCover_integrate {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (s t : ℝ) (Y : Finset (Fin d → ℝ))
    (hpt : ∀ x ∈ Metric.ball (0 : Fin d → ℝ) (s / 2), ∀ z ∈ Metric.ball (0 : Fin d → ℝ) (s / 2),
      cubeFractionalKernel f x z ≤
        (∑ y ∈ Y, (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
            cubeFractionalKernel f x z) +
          (if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0)) :
    fractionalCoverIntegral f (Metric.ball (0 : Fin d → ℝ) (s / 2)) ≤
      (∑ y ∈ Y, ∫⁻ x in Metric.ball (0 : Fin d → ℝ) (s / 2), ∫⁻ z in Metric.ball (0 : Fin d → ℝ) (s / 2),
          (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
            cubeFractionalKernel f x z) +
        ∫⁻ x in Metric.ball (0 : Fin d → ℝ) (s / 2), ∫⁻ z in Metric.ball (0 : Fin d → ℝ) (s / 2),
          (if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0) := by
  set V := Metric.ball (0 : Fin d → ℝ) (s / 2) with hVdef
  have hV : MeasurableSet V := measurableSet_ball
  have hk : Measurable (Function.uncurry (cubeFractionalKernel f)) := by
    change Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      ENNReal.ofReal ((f p.1 - f p.2) ^ 2) / ENNReal.ofReal (‖p.1 - p.2‖ ^ ((d : ℝ) + 3 / 2))
    refine Measurable.div ?_ ?_
    · exact ENNReal.measurable_ofReal.comp
        (((hf.comp measurable_fst).sub (hf.comp measurable_snd)).pow_const 2)
    · refine ENNReal.measurable_ofReal.comp ?_
      exact ((continuous_norm.comp (continuous_fst.sub continuous_snd)).rpow_const
        (fun _ => Or.inr (by positivity : 0 ≤ (d : ℝ) + 3 / 2))).measurable
  have hind : ∀ y : Fin d → ℝ, Measurable
      ((Metric.ball y (t / 2)).indicator (1 : (Fin d → ℝ) → ℝ≥0∞)) :=
    fun y => measurable_one.indicator measurableSet_ball
  have hC : ∀ y : Fin d → ℝ, Measurable (Function.uncurry fun x z : Fin d → ℝ =>
      (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
        cubeFractionalKernel f x z) := by
    intro y
    exact (((hind y).comp measurable_fst).mul ((hind y).comp measurable_snd)).mul hk
  have hF : Measurable (Function.uncurry fun x z : Fin d → ℝ =>
      if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0) := by
    refine Measurable.ite ?_ hk measurable_const
    exact measurableSet_le measurable_const
      (measurable_norm.comp (measurable_fst.sub measurable_snd))
  calc fractionalCoverIntegral f V = ∫⁻ x in V, ∫⁻ z in V, cubeFractionalKernel f x z := rfl
    _ ≤ ∫⁻ x in V, ∫⁻ z in V,
          ((∑ y ∈ Y, (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
            cubeFractionalKernel f x z) +
          (if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0)) :=
        setLIntegral_mono' hV fun x hx => setLIntegral_mono' hV fun z hz => hpt x hx z hz
    _ = ∫⁻ x in V, ((∑ y ∈ Y, ∫⁻ z in V,
          (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
            cubeFractionalKernel f x z) +
          ∫⁻ z in V, (if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0)) := by
        refine lintegral_congr fun x => ?_
        have hFx : Measurable fun z : Fin d → ℝ =>
            if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0 :=
          hF.of_uncurry_left
        have hCx : ∀ y ∈ Y, Measurable fun z : Fin d → ℝ =>
            (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
              cubeFractionalKernel f x z :=
          fun y _ => (hC y).of_uncurry_left
        rw [lintegral_add_right _ hFx, lintegral_finset_sum _ hCx]
    _ = _ := by
        have hFo : Measurable fun x : Fin d → ℝ => ∫⁻ z in V,
            (if t / 4 ≤ ‖x - z‖ then cubeFractionalKernel f x z else 0) :=
          hF.lintegral_prod_right (ν := volume.restrict V)
        have hCo : ∀ y ∈ Y, Measurable fun x : Fin d → ℝ => ∫⁻ z in V,
            (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
              cubeFractionalKernel f x z :=
          fun y _ => (hC y).lintegral_prod_right (ν := volume.restrict V)
        rw [lintegral_add_right _ hFo, lintegral_finset_sum _ hCo]


/-- **(GAGSPLIT)** Near pairs go to the covering balls, far pairs (`‖x - z‖ ≥ t/4`) are bounded by
`(f x - f z)² ≤ 2 f(x)² + 2 f(z)²`, kernel `≤ (4/t)^{d+3/2}`, `vol (ball 0 (s/2)) = s^d`. -/
theorem fractionalCover_bound {d : ℕ} (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (Y : Finset (SpatialCoordinates d))
    (hcov : ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2),
      ∀ z ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2), ‖x - z‖ < t / 4 →
        ∃ y ∈ Y, x ∈ Metric.ball y (t / 2) ∧ z ∈ Metric.ball y (t / 2)) :
    fractionalCoverIntegral f (Metric.ball (0 : SpatialCoordinates d) (s / 2)) ≤
      (∑ y ∈ Y, fractionalCoverIntegral f (Metric.ball y (t / 2))) +
        ENNReal.ofReal (4 * (4 / t) ^ ((d : ℝ) + 3 / 2) * s ^ d) *
          ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2), ENNReal.ofReal (f x ^ 2) := by
  have hint := fractionalCover_integrate f hf s t Y
    (fun x hx z hz => fractionalCover_pointwise f s t Y hcov x z hx hz)
  refine hint.trans (add_le_add (Finset.sum_le_sum fun y _ => ?_) (fractionalCover_far f hf s t hs ht))
  exact fractionalCover_near f _ _ measurableSet_ball


end SubdiffusiveProcess.Static
