import SubdiffusiveProcess.Paper.tight_static_cut
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.lane4_besov_h34_coercivity
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Lane1.TriadicGrid
import SubdiffusiveProcess.Sobolev.DirichletComparison
import SubdiffusiveProcess.Sobolev.PotentialCoefficient
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Geometry.CoordinateFold
import SubdiffusiveProcess.Sobolev.PartitionEnergy
import SubdiffusiveProcess.Paper.lem_extremes
import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence

-- ===== module HCoer.Stmts =====
section
/-!
# hCoer (tight_static clause 2): the deterministic transfer lemmas

Ports the unit-cube coercivity of a reference coefficient `b` to a physical cube `Q = ball y (t/2)`
whose coefficient `A` dominates `c • b` after the affine chart `x ↦ y + t x`.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The Gagliardo double integral of `tight_static`'s coercivity clause. -/
def aux_hcoer_gag {d : ℕ} (f : SpatialCoordinates d → ℝ) (U : Set (SpatialCoordinates d)) : ℝ≥0∞ :=
  ∫⁻ x in U, ∫⁻ z in U, ENNReal.ofReal ((f x - f z) ^ 2) /
    ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))

theorem aux_hcoer_cover_1d (s t : ℝ) (ht : 0 < t) (hts : t < s) :
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

theorem aux_hcoer_cover_of_1d {d : ℕ} (s t : ℝ) (ht : 0 < t) (hts : t < s) (A : Finset ℝ)
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
theorem aux_hcoer_cover {d : ℕ} (s t : ℝ) (ht : 0 < t) (hts : t < s) :
    ∃ Y : Finset (SpatialCoordinates d),
      (Y.card : ℝ) ≤ (2 * s / t + 2) ^ d ∧
      (∀ y ∈ Y, Metric.ball y (t / 2) ⊆ Metric.ball (0 : SpatialCoordinates d) (s / 2)) ∧
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2),
        ∀ z ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2), ‖x - z‖ < t / 4 →
          ∃ y ∈ Y, x ∈ Metric.ball y (t / 2) ∧ z ∈ Metric.ball y (t / 2) := by
  obtain ⟨A, hcard, hsub, hcov⟩ := aux_hcoer_cover_1d s t ht hts
  exact aux_hcoer_cover_of_1d s t ht hts A hcard hsub hcov



/-- The Gagliardo kernel `k(x,z) = (f x - f z)^2 / ‖x - z‖^{d+3/2}` (as in `aux_hcoer_gag`). -/
def aux_hcoer_gag_kernel {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x z : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((f x - f z) ^ 2) / ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))

/-- (GS1) Near part: restricting both variables to a measurable `B` by indicators is bounded by
the Gagliardo integral over `B`. Route: `lintegral_indicator` twice / `setLIntegral_mono_set`-type
comparison `∫⁻ x in V, B.indicator g x ≤ ∫⁻ x in B, g x` (`lintegral_indicator hB`,
`Measure.restrict_mono`/`Measure.restrict_restrict`), inner and outer. -/
theorem aux_hcoer_gag_split_near {d : ℕ} (f : (Fin d → ℝ) → ℝ) (V B : Set (Fin d → ℝ))
    (hB : MeasurableSet B) :
    ∫⁻ x in V, ∫⁻ z in V, B.indicator 1 x * B.indicator 1 z * aux_hcoer_gag_kernel f x z ≤
      aux_hcoer_gag f B := by
  have h_inner_eq (x : Fin d → ℝ) :
      ∫⁻ z in V, B.indicator 1 z * aux_hcoer_gag_kernel f x z =
        ∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z := by
    have h_pointwise : ∀ z : Fin d → ℝ,
        B.indicator 1 z * aux_hcoer_gag_kernel f x z =
          B.indicator (aux_hcoer_gag_kernel f x) z := by
      intro z; simp [Set.indicator]
    calc
      ∫⁻ z in V, B.indicator 1 z * aux_hcoer_gag_kernel f x z
          = ∫⁻ z, B.indicator 1 z * aux_hcoer_gag_kernel f x z ∂(Measure.restrict volume V) := rfl
      _ = ∫⁻ z, B.indicator (aux_hcoer_gag_kernel f x) z ∂(Measure.restrict volume V) := by
        rw [lintegral_congr h_pointwise]
      _ = ∫⁻ z in V, B.indicator (aux_hcoer_gag_kernel f x) z := rfl
      _ = ∫⁻ z in B ∩ V, aux_hcoer_gag_kernel f x z := by rw [setLIntegral_indicator hB]
      _ = ∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z := by rw [Set.inter_comm]
  have h_outer_eq : ∀ x : Fin d → ℝ,
      B.indicator 1 x * (∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z) =
        B.indicator (fun x => ∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z) x := by
    intro x; simp [Set.indicator]
  have h_inter_subset : V ∩ B ⊆ B := fun _ h => h.2
  have h_indicator_ne_top (x : Fin d → ℝ) : B.indicator 1 x ≠ ∞ := by
    rw [Set.indicator]
    split <;> simp
  calc
    ∫⁻ x in V, ∫⁻ z in V, B.indicator 1 x * B.indicator 1 z * aux_hcoer_gag_kernel f x z
        = ∫⁻ x in V, B.indicator 1 x * (∫⁻ z in V, B.indicator 1 z * aux_hcoer_gag_kernel f x z) := by
      refine lintegral_congr fun x => ?_
      calc
        ∫⁻ z in V, B.indicator 1 x * B.indicator 1 z * aux_hcoer_gag_kernel f x z
            = ∫⁻ z in V, B.indicator 1 x * (B.indicator 1 z * aux_hcoer_gag_kernel f x z) := by
          refine lintegral_congr fun z => ?_
          ring
        _ = B.indicator 1 x * ∫⁻ z in V, B.indicator 1 z * aux_hcoer_gag_kernel f x z := by
          rw [lintegral_const_mul' (B.indicator 1 x) _ (h_indicator_ne_top x)]
    _ = ∫⁻ x in V, B.indicator 1 x * (∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z) := by
      refine lintegral_congr fun x => ?_
      simp [h_inner_eq x]
    _ = ∫⁻ x, B.indicator 1 x * (∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z)
        ∂(Measure.restrict volume V) := rfl
    _ = ∫⁻ x, B.indicator (fun x => ∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z) x
        ∂(Measure.restrict volume V) := by
      rw [lintegral_congr (μ := Measure.restrict volume V) h_outer_eq]
    _ = ∫⁻ x in V, B.indicator (fun x => ∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z) x := rfl
    _ = ∫⁻ x in B ∩ V, (∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z) := by
      rw [setLIntegral_indicator hB]
    _ = ∫⁻ x in V ∩ B, (∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z) := by rw [Set.inter_comm]
    _ ≤ ∫⁻ x in B, (∫⁻ z in V ∩ B, aux_hcoer_gag_kernel f x z) :=
      lintegral_mono_set h_inter_subset
    _ ≤ ∫⁻ x in B, (∫⁻ z in B, aux_hcoer_gag_kernel f x z) :=
      lintegral_mono fun x => lintegral_mono_set h_inter_subset
    _ = aux_hcoer_gag f B := rfl

/-- (GS2) Far part: pairs at distance `≥ t/4` cost at most `4 (4/t)^{d+3/2} s^d ∫_V f²`. Route:
pointwise `k ≤ ofReal((f x - f z)^2) * ofReal((4/t)^e)` when `‖x-z‖ ≥ t/4` (then
`‖x-z‖^e ≥ (t/4)^e`, `Real.rpow_le_rpow`), `(f x - f z)^2 ≤ 2 f x^2 + 2 f z^2`; Tonelli-free: each
of the two terms integrates to `vol(V) * ∫_V f²` with `vol(ball 0 (s/2)) = ofReal s ^ d`
(`Real.volume_pi_ball`, sup norm), `lintegral_const_mul`, `lintegral_add_left`. -/
theorem aux_hcoer_gag_split_far {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ∫⁻ x in Metric.ball (0 : Fin d → ℝ) (s / 2), ∫⁻ z in Metric.ball (0 : Fin d → ℝ) (s / 2),
        (if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0) ≤
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
      (if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0) ≤
        2 * ENNReal.ofReal ((4 / t) ^ e) * (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f z ^ 2)) := by
    by_cases hfar : t / 4 ≤ ‖x - z‖
    · rw [if_pos hfar]
      dsimp [aux_hcoer_gag_kernel]
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
    ∫⁻ x in V, ∫⁻ z in V, (if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0)
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
theorem aux_hcoer_gag_split_pointwise {d : ℕ} (f : (Fin d → ℝ) → ℝ) (s t : ℝ)
    (Y : Finset (Fin d → ℝ))
    (hcov : ∀ x ∈ Metric.ball (0 : Fin d → ℝ) (s / 2),
      ∀ z ∈ Metric.ball (0 : Fin d → ℝ) (s / 2), ‖x - z‖ < t / 4 →
        ∃ y ∈ Y, x ∈ Metric.ball y (t / 2) ∧ z ∈ Metric.ball y (t / 2))
    (x z : Fin d → ℝ) (hx : x ∈ Metric.ball (0 : Fin d → ℝ) (s / 2))
    (hz : z ∈ Metric.ball (0 : Fin d → ℝ) (s / 2)) :
    aux_hcoer_gag_kernel f x z ≤
      (∑ y ∈ Y, (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
          aux_hcoer_gag_kernel f x z) +
        (if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0) := by
  by_cases hfar : t / 4 ≤ ‖x - z‖
  · rw [if_pos hfar]
    have hsum_nonneg : 0 ≤ ∑ y ∈ Y, (Metric.ball y (t / 2)).indicator 1 x *
        (Metric.ball y (t / 2)).indicator 1 z * aux_hcoer_gag_kernel f x z :=
      Finset.sum_nonneg fun y _ => by positivity
    exact le_add_of_nonneg_left hsum_nonneg
  · rw [if_neg hfar]
    have hnear : ‖x - z‖ < t / 4 := by linarith
    rcases hcov x hx z hz hnear with ⟨y, hy, hxy, hzy⟩
    have h_term_nonneg (y' : Fin d → ℝ) : 0 ≤ (Metric.ball y' (t / 2)).indicator 1 x *
        (Metric.ball y' (t / 2)).indicator 1 z * aux_hcoer_gag_kernel f x z := by
      positivity
    calc
      aux_hcoer_gag_kernel f x z
          = ((Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z) *
              aux_hcoer_gag_kernel f x z := by
        simp [hxy, hzy]
      _ ≤ ∑ y' ∈ Y, (Metric.ball y' (t / 2)).indicator 1 x *
          (Metric.ball y' (t / 2)).indicator 1 z * aux_hcoer_gag_kernel f x z :=
        Finset.single_le_sum (fun y' _ => h_term_nonneg y') hy
      _ = (∑ y' ∈ Y, (Metric.ball y' (t / 2)).indicator 1 x *
          (Metric.ball y' (t / 2)).indicator 1 z * aux_hcoer_gag_kernel f x z) + 0 := by simp

/-- (GS4) Integrating the pointwise split: the double integral over `V` of `k` is at most the sum
of the Finset-sum part and the far part. Route: `setLIntegral_mono`-style monotonicity on `V`
(inner, then outer; use `ae_restrict_mem`/`setLIntegral_congr_fun`-type pointwise-on-`V` bounds
from `hpt`), then `lintegral_add_left`/`lintegral_add_right` and `lintegral_finset_sum`
(measurability from `hf`: `Measurable.ennreal_ofReal`, `measurable_norm`, `ENNReal.measurable_div`
/`Measurable.div`, `measurable_const.indicator`, `Measurable.ite`), inner then outer. -/
theorem aux_hcoer_gag_split_integrate {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (s t : ℝ) (Y : Finset (Fin d → ℝ))
    (hpt : ∀ x ∈ Metric.ball (0 : Fin d → ℝ) (s / 2), ∀ z ∈ Metric.ball (0 : Fin d → ℝ) (s / 2),
      aux_hcoer_gag_kernel f x z ≤
        (∑ y ∈ Y, (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
            aux_hcoer_gag_kernel f x z) +
          (if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0)) :
    aux_hcoer_gag f (Metric.ball (0 : Fin d → ℝ) (s / 2)) ≤
      (∑ y ∈ Y, ∫⁻ x in Metric.ball (0 : Fin d → ℝ) (s / 2), ∫⁻ z in Metric.ball (0 : Fin d → ℝ) (s / 2),
          (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
            aux_hcoer_gag_kernel f x z) +
        ∫⁻ x in Metric.ball (0 : Fin d → ℝ) (s / 2), ∫⁻ z in Metric.ball (0 : Fin d → ℝ) (s / 2),
          (if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0) := by
  set V := Metric.ball (0 : Fin d → ℝ) (s / 2) with hVdef
  have hV : MeasurableSet V := measurableSet_ball
  have hk : Measurable (Function.uncurry (aux_hcoer_gag_kernel f)) := by
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
        aux_hcoer_gag_kernel f x z) := by
    intro y
    exact (((hind y).comp measurable_fst).mul ((hind y).comp measurable_snd)).mul hk
  have hF : Measurable (Function.uncurry fun x z : Fin d → ℝ =>
      if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0) := by
    refine Measurable.ite ?_ hk measurable_const
    exact measurableSet_le measurable_const
      (measurable_norm.comp (measurable_fst.sub measurable_snd))
  calc aux_hcoer_gag f V = ∫⁻ x in V, ∫⁻ z in V, aux_hcoer_gag_kernel f x z := rfl
    _ ≤ ∫⁻ x in V, ∫⁻ z in V,
          ((∑ y ∈ Y, (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
            aux_hcoer_gag_kernel f x z) +
          (if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0)) :=
        setLIntegral_mono' hV fun x hx => setLIntegral_mono' hV fun z hz => hpt x hx z hz
    _ = ∫⁻ x in V, ((∑ y ∈ Y, ∫⁻ z in V,
          (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
            aux_hcoer_gag_kernel f x z) +
          ∫⁻ z in V, (if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0)) := by
        refine lintegral_congr fun x => ?_
        have hFx : Measurable fun z : Fin d → ℝ =>
            if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0 :=
          hF.of_uncurry_left
        have hCx : ∀ y ∈ Y, Measurable fun z : Fin d → ℝ =>
            (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
              aux_hcoer_gag_kernel f x z :=
          fun y _ => (hC y).of_uncurry_left
        rw [lintegral_add_right _ hFx, lintegral_finset_sum _ hCx]
    _ = _ := by
        have hFo : Measurable fun x : Fin d → ℝ => ∫⁻ z in V,
            (if t / 4 ≤ ‖x - z‖ then aux_hcoer_gag_kernel f x z else 0) :=
          hF.lintegral_prod_right (ν := volume.restrict V)
        have hCo : ∀ y ∈ Y, Measurable fun x : Fin d → ℝ => ∫⁻ z in V,
            (Metric.ball y (t / 2)).indicator 1 x * (Metric.ball y (t / 2)).indicator 1 z *
              aux_hcoer_gag_kernel f x z :=
          fun y _ => (hC y).lintegral_prod_right (ν := volume.restrict V)
        rw [lintegral_add_right _ hFo, lintegral_finset_sum _ hCo]


/-- **(GAGSPLIT)** Near pairs go to the covering balls, far pairs (`‖x - z‖ ≥ t/4`) are bounded by
`(f x - f z)² ≤ 2 f(x)² + 2 f(z)²`, kernel `≤ (4/t)^{d+3/2}`, `vol (ball 0 (s/2)) = s^d`. -/
theorem aux_hcoer_gag_split {d : ℕ} (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (Y : Finset (SpatialCoordinates d))
    (hcov : ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2),
      ∀ z ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2), ‖x - z‖ < t / 4 →
        ∃ y ∈ Y, x ∈ Metric.ball y (t / 2) ∧ z ∈ Metric.ball y (t / 2)) :
    aux_hcoer_gag f (Metric.ball (0 : SpatialCoordinates d) (s / 2)) ≤
      (∑ y ∈ Y, aux_hcoer_gag f (Metric.ball y (t / 2))) +
        ENNReal.ofReal (4 * (4 / t) ^ ((d : ℝ) + 3 / 2) * s ^ d) *
          ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2), ENNReal.ofReal (f x ^ 2) := by
  have hint := aux_hcoer_gag_split_integrate f hf s t Y
    (fun x hx z hz => aux_hcoer_gag_split_pointwise f s t Y hcov x z hx hz)
  refine hint.trans (add_le_add (Finset.sum_le_sum fun y _ => ?_) (aux_hcoer_gag_split_far f hf s t hs ht))
  exact aux_hcoer_gag_split_near f _ _ measurableSet_ball

/-! ### Shared geometric/analytic infrastructure for the transfer lemmas -/

/-- The Euclidean norm of a coordinate difference is at most `√d` times the sup norm. -/
theorem aux_hcoer_transfer_euclidean_le_sup {d : ℕ} (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * ‖x - y‖ := by
  have h1 : ∀ j : Fin d, (x j - y j) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    intro j
    have hb : ‖x - y‖ ≥ |x j - y j| := by
      have := (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).mp le_rfl j
      simpa [Pi.sub_apply, Real.norm_eq_abs] using this
    calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
      _ ≤ ‖x - y‖ ^ 2 := by
          apply sq_le_sq'
          · linarith [abs_nonneg (x j - y j), hb]
          · exact hb
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)
      ≤ Real.sqrt (∑ _j : Fin d, ‖x - y‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum (fun j _ => h1 j)
    _ = Real.sqrt (d * ‖x - y‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = Real.sqrt d * ‖x - y‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg _)]

/-- Pointwise kernel domination: the sup-norm Gagliardo kernel is dominated by the Euclidean
one, up to the dimensional constant `(√d)^{d+3/2}`. -/
theorem aux_hcoer_transfer_kernel_pointwise {d : ℕ} (F : SpatialCoordinates d → ℝ)
    (x y : SpatialCoordinates d) :
    ENNReal.ofReal ((F x - F y) ^ 2) / ENNReal.ofReal (‖x - y‖ ^ ((d : ℝ) + 3 / 2)) ≤
      ENNReal.ofReal ((Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) *
        (ENNReal.ofReal ((F x - F y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 3 / 2)) := by
  set e : ℝ := (d : ℝ) + 3 / 2 with he_def
  have he : 0 < e := by positivity
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (x - y)) he.le]
  by_cases hxy : x = y
  · subst hxy
    simp
  · have hd0 : 0 < d := by
      by_contra hcon
      push_neg at hcon
      have hd00 : d = 0 := by omega
      subst hd00
      exact hxy (Subsingleton.elim x y)
    have hp0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hq0 : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      apply Real.sqrt_pos.mpr
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra h; push_neg at h; exact hxy (funext h)
      have hne : x j - y j ≠ 0 := sub_ne_zero.mpr hj
      have hjpos : 0 < (x j - y j) ^ 2 := by positivity
      calc (0 : ℝ) < (x j - y j) ^ 2 := hjpos
        _ ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin d => (x i - y i) ^ 2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have hK0 : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd0)
    have hle : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * ‖x - y‖ :=
      aux_hcoer_transfer_euclidean_le_sup x y
    have hA : (0 : ℝ) ≤ (F x - F y) ^ 2 := sq_nonneg _
    have h1 : (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ e ≤
        (Real.sqrt d) ^ e * ‖x - y‖ ^ e := by
      rw [← Real.mul_rpow hK0.le (norm_nonneg _)]
      exact Real.rpow_le_rpow hq0.le hle he.le
    have hreal : (F x - F y) ^ 2 / ‖x - y‖ ^ e ≤
        (Real.sqrt d) ^ e * ((F x - F y) ^ 2 /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ e) := by
      rw [show (Real.sqrt d) ^ e * ((F x - F y) ^ 2 /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ e) =
          ((Real.sqrt d) ^ e * (F x - F y) ^ 2) /
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ e from
        (mul_div_assoc _ _ _).symm]
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hp0 e) (Real.rpow_pos_of_pos hq0 e)]
      nlinarith [mul_le_mul_of_nonneg_left h1 hA]
    have h2 : ENNReal.ofReal ((F x - F y) ^ 2 / ‖x - y‖ ^ e) ≤
        ENNReal.ofReal ((Real.sqrt d) ^ e * ((F x - F y) ^ 2 /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ e)) :=
      ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hp0 e),
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (x - y)) he.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (Real.sqrt_nonneg (d : ℝ)) e),
      ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hq0 e),
      ← ENNReal.ofReal_rpow_of_nonneg
        (Real.sqrt_nonneg (∑ j : Fin d, (x j - y j) ^ 2)) he.le] at h2
    exact h2

/-- The a.e. class of `aux_hcoer_gag`'s function argument does not matter: the Gagliardo
double integral only sees function differences. -/
theorem aux_hcoer_transfer_gag_congr_ae {d : ℕ} (f g : SpatialCoordinates d → ℝ)
    (U : Set (SpatialCoordinates d)) (hU : MeasurableSet U)
    (hfg : ∀ᵐ x ∂volume.restrict U, f x = g x) :
    aux_hcoer_gag f U = aux_hcoer_gag g U := by
  unfold aux_hcoer_gag
  apply lintegral_congr_ae
  filter_upwards [hfg] with x hx
  apply lintegral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hx, hy]

/-- `aux_hcoer_gag` on a cube is bounded by the reference Gagliardo seminorm on that same
cube, up to the dimensional constant and the cube's volume. -/
theorem aux_hcoer_transfer_gag_le_seminorm {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (F : DomainL2 (centeredCube z r hr)) :
    aux_hcoer_gag (F : SpatialCoordinates d → ℝ)
        (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) *
        volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
        (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => F)) ^ 2 := by
  have hmono : aux_hcoer_gag (F : SpatialCoordinates d → ℝ)
      (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal ((Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) *
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal (((F : SpatialCoordinates d → ℝ) x - F y) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 3 / 2) := by
    unfold aux_hcoer_gag
    rw [← lintegral_const_mul' _ _ (by finiteness)]
    refine lintegral_mono fun x => ?_
    rw [← lintegral_const_mul' _ _ (by finiteness)]
    refine lintegral_mono fun y => ?_
    exact aux_hcoer_transfer_kernel_pointwise F x y
  have hunfold : cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => F) =
      ((ENNReal.ofReal (threeQuarterOrder : ℝ) /
          volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal (∑ _i : Fin 1, ((F : SpatialCoordinates d → ℝ) x - F y) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * (threeQuarterOrder : ℝ))) ^ (1 / 2 : ℝ) := rfl
  have hsimp : ∀ x y : SpatialCoordinates d,
      (∑ _i : Fin 1, ((F : SpatialCoordinates d → ℝ) x - F y) ^ 2) = (F x - F y) ^ 2 := by
    intro x y; simp
  have hexp : (d : ℝ) + 2 * (threeQuarterOrder : ℝ) = (d : ℝ) + 3 / 2 := by
    show (d : ℝ) + 2 * (3 / 4 : ℝ) = (d : ℝ) + 3 / 2
    ring
  set D : ℝ≥0∞ := ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (((F : SpatialCoordinates d → ℝ) x - F y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 3 / 2) with hD_def
  have hseminorm_sq : (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
      (fun _ : Fin 1 => F)) ^ 2 =
      (ENNReal.ofReal (threeQuarterOrder : ℝ) /
        volume (centeredCube z r hr : Set (SpatialCoordinates d))) * D := by
    rw [hunfold]
    simp only [hsimp, hexp]
    rw [← hD_def]
    generalize (ENNReal.ofReal (threeQuarterOrder : ℝ) /
      volume (centeredCube z r hr : Set (SpatialCoordinates d)) * D) = X
    by_cases hX0 : X = 0
    · subst hX0; simp
    · by_cases hXtop : X = ⊤
      · subst hXtop; simp
      · calc (X ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = (X ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
              simpa using (ENNReal.rpow_natCast (X ^ (1 / 2 : ℝ)) 2).symm
          _ = X ^ ((1 / 2 : ℝ) * 2) := (ENNReal.rpow_mul X (1 / 2) 2).symm
          _ = X ^ (1 : ℝ) := by norm_num
          _ = X := by simp
  have hthreeq : (threeQuarterOrder : ℝ) = 3 / 4 := rfl
  have hvolQ_ne_top : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ⊤ := by
    rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top
  have hvolQ_ne_zero : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ 0 := by
    rw [centeredCube_volume]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hcancel : volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
      (ENNReal.ofReal (threeQuarterOrder : ℝ) /
        volume (centeredCube z r hr : Set (SpatialCoordinates d))) =
      ENNReal.ofReal (threeQuarterOrder : ℝ) :=
    ENNReal.mul_div_cancel' (fun h => absurd h hvolQ_ne_zero) (fun h => absurd h hvolQ_ne_top)
  have hfinal_eq : ENNReal.ofReal ((Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) * D =
      ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) *
        volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
        (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => F)) ^ 2 := by
    rw [hseminorm_sq]
    rw [show ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) *
          volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
          (ENNReal.ofReal (threeQuarterOrder : ℝ) /
            volume (centeredCube z r hr : Set (SpatialCoordinates d)) * D) =
        ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) *
            (volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
              (ENNReal.ofReal (threeQuarterOrder : ℝ) /
                volume (centeredCube z r hr : Set (SpatialCoordinates d)))) * D from by ring]
    rw [hcancel, hthreeq, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  exact hmono.trans hfinal_eq.le

/-- The Gagliardo seminorm squared is invariant under shifting the function by an a.e.
constant: the double integral only sees differences. -/
theorem aux_hcoer_transfer_seminorm_shift_ae {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (cst : ℝ) (v w : DomainL2 (centeredCube z r hr))
    (hvw : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (w : SpatialCoordinates d → ℝ) x = (v : SpatialCoordinates d → ℝ) x - cst) :
    cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => w) =
      cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v) := by
  unfold cubeFractionalL2Seminorm
  have hD : (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ _i : Fin 1, ((w : SpatialCoordinates d → ℝ) x -
            (w : SpatialCoordinates d → ℝ) y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (threeQuarterOrder : ℝ))) =
      (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ _i : Fin 1, ((v : SpatialCoordinates d → ℝ) x -
            (v : SpatialCoordinates d → ℝ) y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (threeQuarterOrder : ℝ))) := by
    apply lintegral_congr_ae
    filter_upwards [hvw] with x hx
    apply lintegral_congr_ae
    filter_upwards [hvw] with y hy
    congr 1
    congr 1
    simp only [Fin.sum_univ_one]
    rw [hx, hy]
    ring
  rw [hD]

/-- Build a `PositiveCoefficient` on a cube from a globally continuous, everywhere-positive
function, tied to it a.e. on the cube. -/
theorem aux_hcoer_transfer_coeff_of_continuous {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (A : SpatialCoordinates d → ℝ) (hAcont : Continuous A)
    (hApos : ∀ x, 0 < A x) :
    ∃ a : PositiveCoefficient (centeredCube z r hr),
      ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (a.val : SpatialCoordinates d → ℝ) x = A x := by
  haveI : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  set AC : C(closedCube z r hr, ℝ) :=
    ⟨fun x => A (x : SpatialCoordinates d), hAcont.comp continuous_subtype_val⟩ with hAC_def
  have hACpos : ∀ x, 0 < AC x := fun x => hApos _
  refine ⟨normalizedContinuousPositiveCoefficient (Ω := centeredCube z r hr) (closedCube z r hr)
    AC hACpos 1 one_pos, ?_⟩
  have hcoeFn := normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube z r hr)
    (closedCube z r hr) AC hACpos 1 one_pos
  filter_upwards [hcoeFn, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with x hx hxmem
  rw [hx hxmem, hAC_def]
  simp

/-- Every weak Sobolev datum has a mean-zero representative with the same gradient, whose
value differs from the original by an explicit a.e. constant shift. -/
theorem aux_hcoer_transfer_mean_zero_shift {d : ℕ} {Om : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d))) (u : weakSobolevGraph Om) :
    ∃ (v : meanZeroSobolevGraph Om) (cst : ℝ),
      (∀ i : Fin d, (v : SobolevData Om).2 i = (u : SobolevData Om).2 i) ∧
      ∀ᵐ x ∂volume.restrict (Om : Set (SpatialCoordinates d)),
        (v : SobolevData Om).1 x = (u : SobolevData Om).1 x - cst := by
  classical
  set c : ℝ := (volume.real (Om : Set (SpatialCoordinates d)))⁻¹ *
    ∫ x in (Om : Set (SpatialCoordinates d)), (u : SobolevData Om).1 x with hc
  refine ⟨⟨(u : SobolevData Om) -
      (domainConstantL2 (Ω := Om) c, fun _ => (0 : DomainL2 Om)), ?_⟩, c, ?_, ?_⟩
  · rw [mem_meanZeroSobolevGraph_iff]
    refine ⟨Submodule.sub_mem _ u.property (constantSobolevData_mem_weak c), ?_⟩
    have hco : ((((u : SobolevData Om) -
        (domainConstantL2 (Ω := Om) c, fun _ => (0 : DomainL2 Om))).1 :
          DomainL2 Om) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))]
      fun x => (u : SobolevData Om).1 x - c := by
      filter_upwards [Lp.coeFn_sub ((u : SobolevData Om).1)
        (domainConstantL2 (Ω := Om) c), domainConstantL2_coeFn (Ω := Om) c] with x h1 h2
      change (((((u : SobolevData Om).1 - domainConstantL2 (Ω := Om) c) :
        DomainL2 Om) : SpatialCoordinates d → ℝ)) x = _
      rw [h1, Pi.sub_apply, h2]
    rw [integral_congr_ae hco]
    have hInt : Integrable (fun x => ((u : SobolevData Om).1 : SpatialCoordinates d → ℝ) x)
        (volume.restrict (Om : Set (SpatialCoordinates d))) := by
      have h := (Lp.memLp ((u : SobolevData Om).1)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      simpa using h
    rw [integral_sub hInt (integrable_const c)]
    rw [MeasureTheory.setIntegral_const, hc, smul_eq_mul]
    have hne : volume.real (Om : Set (SpatialCoordinates d)) ≠ 0 := ne_of_gt hvol
    field_simp
    ring
  · intro i
    show (u : SobolevData Om).2 i - (0 : DomainL2 Om) = _
    exact sub_zero _
  · filter_upwards [Lp.coeFn_sub ((u : SobolevData Om).1)
      (domainConstantL2 (Ω := Om) c), domainConstantL2_coeFn (Ω := Om) c] with x h1 h2
    change (((((u : SobolevData Om).1 - domainConstantL2 (Ω := Om) c) :
      DomainL2 Om) : SpatialCoordinates d → ℝ)) x = _
    rw [h1, Pi.sub_apply, h2]

/-- The cube volume-normalized square norm splits into its Gagliardo seminorm and its
normalized `L²` summand. -/
theorem aux_hcoer_transfer_sqnorm_eq {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (v : DomainL2 (centeredCube z r hr)) :
    cubeFractionalSqNorm hd z r hr threeQuarterOrder v =
      cubeFractionalVecSeminormSq hd z r hr threeQuarterOrder (fun _ : Fin 1 => v) +
        ‖v‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm
  simp

/-- Energy domination: the physical coefficient's energy on the pulled-back unit-cube datum
`w1`, discounted by `c`, is dominated by `t^{2-d}` times the physical energy integral of `v`
on `Q`. -/
theorem aux_hcoer_transfer_energy_bound {d : ℕ} (y : SpatialCoordinates d) (t : ℝ) (ht : 0 < t)
    (A : SpatialCoordinates d → ℝ) (hAcont : Continuous A) (hApos : ∀ x, 0 < A x)
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (c : ℝ) (hc : 0 < c)
    (hcoefdom : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), c * (b.val : SpatialCoordinates d → ℝ) x ≤ A (y + t • x))
    (v : Homogenization.H1Function (centeredCube y t ht : Set (SpatialCoordinates d)))
    (u1 : SobolevData (centeredCube y t ht))
    (hu1grad : ∀ i : Fin d, (u1.2 i : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube y t ht : Set (SpatialCoordinates d))] fun z => v.grad z i)
    (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hw1 : w1 ∈ weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hvalue : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), w1.1 x = u1.1 (cubeDilation y 0 t x))
    (hgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), w1.2 i x = t * u1.2 i (cubeDilation y 0 t x)) :
    (c * sobolevCoefficientForm b w1 w1 ≤
      t ^ ((2 : ℝ) - d) * ∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
        A z * Homogenization.vecDot (v.grad z) (v.grad z)) ∧
    (ENNReal.ofReal (∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
        A z * Homogenization.vecDot (v.grad z) (v.grad z)) =
      ∫⁻ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
        ENNReal.ofReal (A z * Homogenization.vecDot (v.grad z) (v.grad z))) := by
  obtain ⟨aA, haA_ae⟩ := aux_hcoer_transfer_coeff_of_continuous y t ht A hAcont hApos
  obtain ⟨bA, hbA⟩ := lane4_dilation_coefficient_transport d y 0 t ht one_pos aA
  have hqmp := lane4_dilation_quasi_measure_preserving d y 0 t ht one_pos
  have hcomp : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      (aA.val : SpatialCoordinates d → ℝ) (cubeDilation y 0 t x) = A (cubeDilation y 0 t x) :=
    hqmp.ae haA_ae
  have hbAeqA : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), (bA.val : SpatialCoordinates d → ℝ) x =
        A (cubeDilation y 0 t x) := by
    filter_upwards [hbA, hcomp] with x hx1 hx2
    rw [hx1, hx2]
  have hcubedil : ∀ x : SpatialCoordinates d, cubeDilation y 0 t x = y + t • x := by
    intro x; funext i; simp [cubeDilation, smul_eq_mul]
  have hcoefdom' : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), c * (b.val : SpatialCoordinates d → ℝ) x ≤
        (bA.val : SpatialCoordinates d → ℝ) x := by
    filter_upwards [hcoefdom, hbAeqA] with x hx1 hx2
    rw [hx2, hcubedil x]
    exact hx1
  have hscale_eq : c * sobolevCoefficientForm b w1 w1 =
      sobolevCoefficientForm (scalePositiveCoefficient c hc b) w1 w1 :=
    (sobolevCoefficientForm_scale c hc b w1 w1).symm
  have hscale_val : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      ((scalePositiveCoefficient c hc b).val : SpatialCoordinates d → ℝ) x =
        c * (b.val : SpatialCoordinates d → ℝ) x :=
    scalePositiveCoefficient_coeFn c hc b
  have hmono : sobolevCoefficientForm (scalePositiveCoefficient c hc b) w1 w1 ≤
      sobolevCoefficientForm bA w1 w1 := by
    apply sobolevCoefficientForm_mono
    filter_upwards [hscale_val, hcoefdom'] with x hx1 hx2
    rw [hx1]; exact hx2
  have henergy : sobolevCoefficientForm aA u1 u1 =
      t ^ ((d : ℝ) - 2) * sobolevCoefficientForm bA w1 w1 :=
    aux_lane4_coercivity_dilation_energy_scaling d y t ht one_pos aA bA u1 w1 hbA hvalue hgrad
  have hexp0 : ((2 : ℝ) - (d : ℝ)) + ((d : ℝ) - 2) = 0 := by ring
  have hbA_eq : t ^ ((2 : ℝ) - (d : ℝ)) * sobolevCoefficientForm aA u1 u1 =
      sobolevCoefficientForm bA w1 w1 := by
    rw [henergy, ← mul_assoc, ← Real.rpow_add ht, hexp0, Real.rpow_zero, one_mul]
  have hstep : c * sobolevCoefficientForm b w1 w1 ≤
      t ^ ((2 : ℝ) - (d : ℝ)) * sobolevCoefficientForm aA u1 u1 := by
    rw [hscale_eq, hbA_eq]; exact hmono
  have haA_sum : sobolevCoefficientForm aA u1 u1 =
      ∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
        A z * ∑ i : Fin d, (u1.2 i z) ^ 2 := by
    rw [sobolevCoefficientForm_eq_sum_integral]
    have hintchange : ∀ i : Fin d,
        (∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
          (aA.val : SpatialCoordinates d → ℝ) z * (u1.2 i z * u1.2 i z)) =
        ∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
          A z * (u1.2 i z * u1.2 i z) := by
      intro i
      apply integral_congr_ae
      filter_upwards [haA_ae] with z hz
      rw [hz]
    simp only [hintchange]
    have heq : (fun z => A z * ∑ i : Fin d, (u1.2 i z) ^ 2) =
        fun z => ∑ i : Fin d, A z * (u1.2 i z * u1.2 i z) := by
      funext z
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [heq]
    symm
    apply integral_finset_sum
    intro i _
    have haA_int := integrable_weighted_coordinates aA.val
      (sobolevGradient u1) (sobolevGradient u1) i
    have hsg : (sobolevGradient u1 i : SpatialCoordinates d → ℝ) =
        (u1.2 i : SpatialCoordinates d → ℝ) := rfl
    rw [hsg] at haA_int
    have hae : (fun z => A z * (u1.2 i z * u1.2 i z)) =ᵐ[volume.restrict
        (centeredCube y t ht : Set (SpatialCoordinates d))]
        (fun z => (aA.val : SpatialCoordinates d → ℝ) z * (u1.2 i z * u1.2 i z)) := by
      filter_upwards [haA_ae] with z hz
      rw [hz]
    exact haA_int.congr hae.symm
  have hgrad_congr : (fun z => ∑ i : Fin d, (u1.2 i z) ^ 2) =ᵐ[volume.restrict
      (centeredCube y t ht : Set (SpatialCoordinates d))]
      fun z => Homogenization.vecDot (v.grad z) (v.grad z) := by
    have hae : ∀ᵐ z ∂volume.restrict (centeredCube y t ht : Set (SpatialCoordinates d)),
        ∀ i : Fin d, (u1.2 i : SpatialCoordinates d → ℝ) z = v.grad z i := by
      rw [ae_all_iff]; exact hu1grad
    filter_upwards [hae] with z hz
    simp only [Homogenization.vecDot, sq]
    exact Finset.sum_congr rfl (fun i _ => by rw [hz i])
  have hR_eq : (∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
      A z * ∑ i : Fin d, (u1.2 i z) ^ 2) =
      ∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
        A z * Homogenization.vecDot (v.grad z) (v.grad z) := by
    apply integral_congr_ae
    filter_upwards [hgrad_congr] with z hz
    rw [hz]
  have hR_int : Integrable (fun z => A z * Homogenization.vecDot (v.grad z) (v.grad z))
      (volume.restrict (centeredCube y t ht : Set (SpatialCoordinates d))) := by
    have hintsum : Integrable (fun z => A z * ∑ i : Fin d, (u1.2 i z) ^ 2)
        (volume.restrict (centeredCube y t ht : Set (SpatialCoordinates d))) := by
      have heq : (fun z => A z * ∑ i : Fin d, (u1.2 i z) ^ 2) =
          fun z => ∑ i : Fin d, A z * (u1.2 i z * u1.2 i z) := by
        funext z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [heq]
      apply integrable_finset_sum
      intro i _
      have haA_int := integrable_weighted_coordinates aA.val
        (sobolevGradient u1) (sobolevGradient u1) i
      have hsg : (sobolevGradient u1 i : SpatialCoordinates d → ℝ) =
          (u1.2 i : SpatialCoordinates d → ℝ) := rfl
      rw [hsg] at haA_int
      have hae : (fun z => A z * (u1.2 i z * u1.2 i z)) =ᵐ[volume.restrict
          (centeredCube y t ht : Set (SpatialCoordinates d))]
          (fun z => (aA.val : SpatialCoordinates d → ℝ) z * (u1.2 i z * u1.2 i z)) := by
        filter_upwards [haA_ae] with z hz
        rw [hz]
      exact haA_int.congr hae.symm
    have hgrad_congr_A : (fun z => A z * ∑ i : Fin d, (u1.2 i z) ^ 2) =ᵐ[volume.restrict
        (centeredCube y t ht : Set (SpatialCoordinates d))]
        (fun z => A z * Homogenization.vecDot (v.grad z) (v.grad z)) := by
      filter_upwards [hgrad_congr] with z hz
      rw [hz]
    exact hintsum.congr hgrad_congr_A
  have hR_nonneg : 0 ≤ᵐ[volume.restrict (centeredCube y t ht : Set (SpatialCoordinates d))]
      (fun z => A z * Homogenization.vecDot (v.grad z) (v.grad z)) := by
    filter_upwards with z
    apply mul_nonneg (hApos z).le
    simp only [Homogenization.vecDot]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hlint_eq : ENNReal.ofReal (∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
      A z * Homogenization.vecDot (v.grad z) (v.grad z)) =
      ∫⁻ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
        ENNReal.ofReal (A z * Homogenization.vecDot (v.grad z) (v.grad z)) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hR_int hR_nonneg
  refine ⟨?_, hlint_eq⟩
  rw [← hR_eq, ← haA_sum]
  exact hstep

/-- **(TRANSFER, mean-zero)** Coercivity of a reference coefficient `b` on the unit cube, transported
to the cube `ball y (t/2)` whose (physical) coefficient `A` dominates `c · b` after the affine chart
`x ↦ y + t x`.  Route (Lane4 vocabulary): `exists_weakSobolevGraph_of_nativeH1` on
`centeredCube y t` (= `ball y (t/2)`, `ball_eq_centeredCube`), `aux_lane4_coercivity_dilation_weak_pullback`,
subtract the mean (`constantSobolevData_mem_weak`), `S.h1_fractional_finite` (the seminorm is finite,
so `cubeFractionalSqNorm`'s `toReal` is faithful), `lane4_gagliardo_dilation_scaling` (`s = 3/4`),
the chart change of variables for the energy, and `‖·‖₂ ≤ √d ‖·‖` for the kernel. -/
theorem aux_hcoer_transfer_meanzero {d : ℕ} (hd : 2 ≤ d) (S : SobolevFoundationalInput d hd) :
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (y : SpatialCoordinates d) (t : ℝ), 0 < t →
      ∀ (A : SpatialCoordinates d → ℝ), Continuous A → (∀ x, 0 < A x) →
      ∀ (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) (c Kb : ℝ),
        0 < c → 0 ≤ Kb →
        (∀ᵐ x ∂(volume.restrict
            (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
          c * (b.val : SpatialCoordinates d → ℝ) x ≤ A (y + t • x)) →
        (∀ w : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
          cubeFractionalSqNorm hd 0 1 one_pos threeQuarterOrder
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 ≤
            Kb * sobolevCoefficientForm b
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))) →
        ∀ v : Homogenization.H1Function (Metric.ball y (t / 2)),
          aux_hcoer_gag v.toFun (Metric.ball y (t / 2)) ≤
            ENNReal.ofReal (Cd * Kb * c⁻¹ * t ^ (1 / 2 : ℝ)) *
              ∫⁻ x in Metric.ball y (t / 2),
                ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)) := by
  refine ⟨(4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2), by positivity, ?_⟩
  intro y t ht A hAcont hApos b c Kb hc hKb hcoefdom hcoer v
  obtain ⟨u1, hu1val, hu1grad⟩ := exists_weakSobolevGraph_of_nativeH1
    (Om := centeredCube y t ht)
    (v : Homogenization.H1Function (centeredCube y t ht : Set (SpatialCoordinates d)))
  obtain ⟨w1, hw1val, hw1grad⟩ := aux_lane4_coercivity_dilation_weak_pullback d y t ht one_pos u1
  obtain ⟨w0, cst, hw0grad, hw0shift⟩ := aux_hcoer_transfer_mean_zero_shift
    (Om := centeredCube (0 : SpatialCoordinates d) 1 one_pos)
    (by rw [centeredCube_one_volume_real]; norm_num) w1
  have hEB := aux_hcoer_transfer_energy_bound y t ht A hAcont hApos b c hc hcoefdom
    (v : Homogenization.H1Function (centeredCube y t ht : Set (SpatialCoordinates d)))
    (u1 : SobolevData (centeredCube y t ht)) hu1grad
    (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) w1.property
    hw1val hw1grad
  obtain ⟨hEB1, hEB2⟩ := hEB
  set R : ℝ := ∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
    A z * Homogenization.vecDot (v.grad z) (v.grad z) with hR_def
  have hform_eq : sobolevCoefficientForm b
      (w0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
      (w0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) =
      sobolevCoefficientForm b
        (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
        (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) := by
    rw [sobolevCoefficientForm_eq_sum_integral, sobolevCoefficientForm_eq_sum_integral]
    exact Finset.sum_congr rfl (fun i _ => by rw [hw0grad i])
  have hRnonneg : 0 ≤ R := by
    rw [hR_def]
    apply integral_nonneg
    intro z
    apply mul_nonneg (hApos z).le
    simp only [Homogenization.vecDot]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  have hform_bound : sobolevCoefficientForm b
      (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
      (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) ≤
      c⁻¹ * (t ^ ((2 : ℝ) - d) * R) := by
    have := mul_le_mul_of_nonneg_left hEB1 hcinv.le
    rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at this
  have hcoer_w0 := hcoer w0
  have hsqnorm_eq := aux_hcoer_transfer_sqnorm_eq hd 0 1 one_pos
    (w0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1
  have hdrop : cubeFractionalVecSeminormSq hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) ≤
      Kb * sobolevCoefficientForm b
        (w0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
        (w0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) := by
    have hL2nonneg : (0 : ℝ) ≤ ‖(w0 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ^ 2 /
        volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)) := by positivity
    linarith [hsqnorm_eq, hcoer_w0]
  have hseminormSq_bound : cubeFractionalVecSeminormSq hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) ≤
      Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R)) := by
    have hstep1 : cubeFractionalVecSeminormSq hd 0 1 one_pos threeQuarterOrder
        (fun _ : Fin 1 => (w0 : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) ≤
        Kb * sobolevCoefficientForm b
          (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
          (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) := by
      rw [← hform_eq]; exact hdrop
    exact hstep1.trans (mul_le_mul_of_nonneg_left hform_bound hKb)
  -- cross to ENNReal via finiteness of the mean-zero seminorm
  have hY0_fin : cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w0 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) < ⊤ :=
    S.h1_fractional_finite 0 1 one_pos
      ⟨(w0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)),
        (inf_le_left : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) ≤
          weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) w0.property⟩
  have hY0sq_eq : (cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w0 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) ^ 2 =
      ENNReal.ofReal (cubeFractionalVecSeminormSq hd 0 1 one_pos threeQuarterOrder
        (fun _ : Fin 1 => (w0 : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) := by
    unfold cubeFractionalVecSeminormSq
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hY0_fin.ne]
  have hY0sq_le : (cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w0 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) ^ 2 ≤
      ENNReal.ofReal (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R))) := by
    rw [hY0sq_eq]; exact ENNReal.ofReal_le_ofReal hseminormSq_bound
  have hshift : cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w0 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) =
      cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
        (fun _ : Fin 1 => (w1 : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) :=
    aux_hcoer_transfer_seminorm_shift_ae hd (0 : SpatialCoordinates d) 1 one_pos cst
      (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1
      (w0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 hw0shift
  have hY1sq_le : (cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w1 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) ^ 2 ≤
      ENNReal.ofReal (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R))) := by
    rw [← hshift]; exact hY0sq_le
  have hfg : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      (fun _ : Fin 1 => (w1 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) (0 : Fin 1) x =
      (fun _ : Fin 1 => (u1 : SobolevData (centeredCube y t ht)).1) (0 : Fin 1)
        (cubeDilation y 0 t x) := hw1val
  have hgagl := lane4_gagliardo_dilation_scaling d 1 hd y 0 t ht one_pos threeQuarterOrder
    (fun _ : Fin 1 => (u1 : SobolevData (centeredCube y t ht)).1)
    (fun _ : Fin 1 => (w1 : SobolevData
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)
    (fun _ : Fin 1 => hfg)
  have hXQ_eq : (cubeFractionalL2Seminorm hd y t ht threeQuarterOrder
      (fun _ : Fin 1 => (u1 : SobolevData (centeredCube y t ht)).1)) ^ 2 =
      ENNReal.ofReal (t ^ (-(2 * (threeQuarterOrder : ℝ)))) *
        (cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
          (fun _ : Fin 1 => (w1 : SobolevData
            (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) ^ 2 :=
    hgagl.1
  have hXQ_le : (cubeFractionalL2Seminorm hd y t ht threeQuarterOrder
      (fun _ : Fin 1 => (u1 : SobolevData (centeredCube y t ht)).1)) ^ 2 ≤
      ENNReal.ofReal (t ^ (-(2 * (threeQuarterOrder : ℝ)))) *
        ENNReal.ofReal (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R))) := by
    rw [hXQ_eq]
    exact mul_le_mul_of_nonneg_left hY1sq_le (zero_le _)
  have hXQ_fin : cubeFractionalL2Seminorm hd y t ht threeQuarterOrder
      (fun _ : Fin 1 => (u1 : SobolevData (centeredCube y t ht)).1) < ⊤ :=
    S.h1_fractional_finite y t ht u1
  have hgag_le := aux_hcoer_transfer_gag_le_seminorm hd y t ht
    (u1 : SobolevData (centeredCube y t ht)).1
  have hgag_congr : aux_hcoer_gag v.toFun (Metric.ball y (t / 2)) =
      aux_hcoer_gag ((u1 : SobolevData (centeredCube y t ht)).1 : SpatialCoordinates d → ℝ)
        (centeredCube y t ht : Set (SpatialCoordinates d)) :=
    aux_hcoer_transfer_gag_congr_ae v.toFun
      ((u1 : SobolevData (centeredCube y t ht)).1 : SpatialCoordinates d → ℝ)
      (centeredCube y t ht : Set (SpatialCoordinates d)) (centeredCube y t ht).isOpen.measurableSet
      hu1val.symm
  rw [hgag_congr]
  refine hgag_le.trans ?_
  refine (mul_le_mul_of_nonneg_left hXQ_le (zero_le _)).trans ?_
  rw [centeredCube_volume]
  have hexp34 : (-(2 * (threeQuarterOrder : ℝ))) = -(3 / 2 : ℝ) := by
    show (-(2 * (3 / 4 : ℝ))) = -(3 / 2 : ℝ); ring
  rw [hexp34]
  have ht_pow : t ^ d = t ^ ((d : ℝ)) := (Real.rpow_natCast t d).symm
  rw [ht_pow]
  have hcombine : t ^ ((d : ℝ)) * (t ^ (-(3 / 2) : ℝ) * t ^ ((2 : ℝ) - (d : ℝ))) =
      t ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    ring
  have hnum_eq : (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * t ^ ((d : ℝ)) *
      (t ^ (-(3 / 2) : ℝ) * (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - (d : ℝ)) * R)))) =
      (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ * t ^ ((1 : ℝ) / 2) * R := by
    calc (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * t ^ ((d : ℝ)) *
        (t ^ (-(3 / 2) : ℝ) * (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - (d : ℝ)) * R))))
        = ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) * (Kb * c⁻¹) *
          (t ^ ((d : ℝ)) * (t ^ (-(3 / 2) : ℝ) * t ^ ((2 : ℝ) - (d : ℝ)))) * R := by ring
      _ = ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) * (Kb * c⁻¹) * t ^ ((1 : ℝ) / 2) * R := by
          rw [hcombine]
      _ = (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ * t ^ ((1 : ℝ) / 2) * R := by
          ring
  have hK1nonneg : (0:ℝ) ≤ (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) := by positivity
  have htdnonneg : (0:ℝ) ≤ t ^ ((d : ℝ)) := Real.rpow_nonneg ht.le _
  have hinnernonneg : (0:ℝ) ≤ Kb * (c⁻¹ * (t ^ ((2 : ℝ) - (d : ℝ)) * R)) := by positivity
  have ht32nonneg : (0:ℝ) ≤ t ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg ht.le _
  apply le_of_eq
  calc ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) *
      ENNReal.ofReal (t ^ ((d : ℝ))) *
      (ENNReal.ofReal (t ^ (-(3 / 2) : ℝ)) *
        ENNReal.ofReal (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - (d : ℝ)) * R))))
      = ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * t ^ ((d : ℝ)) *
          (t ^ (-(3 / 2) : ℝ) * (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - (d : ℝ)) * R))))) := by
        rw [← ENNReal.ofReal_mul ht32nonneg, ← ENNReal.ofReal_mul hK1nonneg,
          ← ENNReal.ofReal_mul (mul_nonneg hK1nonneg htdnonneg)]
    _ = ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ *
          t ^ ((1 : ℝ) / 2) * R) := by rw [hnum_eq]
    _ = ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ *
          t ^ ((1 : ℝ) / 2)) * ENNReal.ofReal R := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ *
          t ^ ((1 : ℝ) / 2)) * ∫⁻ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
            ENNReal.ofReal (A z * Homogenization.vecDot (v.grad z) (v.grad z)) := by
        rw [hEB2]

/-- Pure numeric combination for the Gagliardo term (kept as its own declaration to stay
inside the per-declaration heartbeat budget). -/
theorem aux_hcoer_transfer_gag_ennreal_combine (d : ℕ) (t Kb c R : ℝ) (ht : 0 < t)
    (hKb : 0 ≤ Kb) (hc : 0 < c) (hR : 0 ≤ R) :
    ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) *
        ENNReal.ofReal (t ^ ((d : ℝ))) *
        (ENNReal.ofReal (t ^ (-(3 / 2) : ℝ)) *
          ENNReal.ofReal (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - (d : ℝ)) * R)))) =
      ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ * t ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal R := by
  have hcombine : t ^ ((d : ℝ)) * (t ^ (-(3 / 2) : ℝ) * t ^ ((2 : ℝ) - (d : ℝ))) =
      t ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    ring
  have hnum_eq : (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * t ^ ((d : ℝ)) *
      (t ^ (-(3 / 2) : ℝ) * (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - (d : ℝ)) * R)))) =
      (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ * t ^ ((1 : ℝ) / 2) * R := by
    calc (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * t ^ ((d : ℝ)) *
        (t ^ (-(3 / 2) : ℝ) * (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - (d : ℝ)) * R))))
        = ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) * (Kb * c⁻¹) *
          (t ^ ((d : ℝ)) * (t ^ (-(3 / 2) : ℝ) * t ^ ((2 : ℝ) - (d : ℝ)))) * R := by ring
      _ = ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2)) * (Kb * c⁻¹) * t ^ ((1 : ℝ) / 2) * R := by
          rw [hcombine]
      _ = (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ * t ^ ((1 : ℝ) / 2) * R := by
          ring
  have hK1nonneg : (0 : ℝ) ≤ (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) := by positivity
  have htdnonneg : (0 : ℝ) ≤ t ^ ((d : ℝ)) := Real.rpow_nonneg ht.le _
  have ht32nonneg : (0 : ℝ) ≤ t ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg ht.le _
  rw [← ENNReal.ofReal_mul ht32nonneg, ← ENNReal.ofReal_mul hK1nonneg,
    ← ENNReal.ofReal_mul (mul_nonneg hK1nonneg htdnonneg), hnum_eq,
    ENNReal.ofReal_mul (by positivity)]

/-- Pure numeric combination for the `L²` term. -/
theorem aux_hcoer_transfer_l2_ennreal_combine (d : ℕ) (t Kb c R : ℝ) (ht : 0 < t)
    (hKb : 0 ≤ Kb) (hc : 0 < c) (hR : 0 ≤ R) :
    ENNReal.ofReal (t ^ d) * ENNReal.ofReal (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R))) =
      ENNReal.ofReal (Kb * c⁻¹ * t ^ (2 : ℝ)) * ENNReal.ofReal R := by
  have ht_pow2 : t ^ d = t ^ ((d : ℝ)) := (Real.rpow_natCast t d).symm
  have ht2_eq : t ^ ((d : ℝ)) * t ^ ((2 : ℝ) - (d : ℝ)) = t ^ (2 : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hnum : t ^ d * (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - (d : ℝ)) * R))) = Kb * c⁻¹ * t ^ (2 : ℝ) * R := by
    rw [ht_pow2]
    calc t ^ ((d : ℝ)) * (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - (d : ℝ)) * R)))
        = (Kb * c⁻¹) * (t ^ ((d : ℝ)) * t ^ ((2 : ℝ) - (d : ℝ))) * R := by ring
      _ = (Kb * c⁻¹) * t ^ (2 : ℝ) * R := by rw [ht2_eq]
      _ = Kb * c⁻¹ * t ^ (2 : ℝ) * R := by ring
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ t ^ d), hnum,
    ENNReal.ofReal_mul (by positivity)]

/-- **(TRANSFER, killed)** As `aux_hcoer_transfer_meanzero` for `H¹₀` functions and the killed
coercivity of `b`; the `L²` term comes from the normalized `L²` part of `cubeFractionalSqNorm`
(scale `t²`), the Gagliardo term with scale `t^{1/2}`. -/
theorem aux_hcoer_transfer_killed {d : ℕ} (hd : 2 ≤ d) (S : SobolevFoundationalInput d hd) :
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (y : SpatialCoordinates d) (t : ℝ), 0 < t →
      ∀ (A : SpatialCoordinates d → ℝ), Continuous A → (∀ x, 0 < A x) →
      ∀ (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) (c Kb : ℝ),
        0 < c → 0 ≤ Kb →
        (∀ᵐ x ∂(volume.restrict
            (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
          c * (b.val : SpatialCoordinates d → ℝ) x ≤ A (y + t • x)) →
        (∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
          cubeFractionalSqNorm hd 0 1 one_pos threeQuarterOrder
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 ≤
            Kb * sobolevCoefficientForm b
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))) →
        ∀ v : Homogenization.H10Function (Metric.ball y (t / 2)),
          aux_hcoer_gag v.toFun (Metric.ball y (t / 2)) +
              ∫⁻ x in Metric.ball y (t / 2), ENNReal.ofReal (v.toFun x ^ 2) ≤
            ENNReal.ofReal (Cd * Kb * c⁻¹ * (t ^ (1 / 2 : ℝ) + t ^ 2)) *
              ∫⁻ x in Metric.ball y (t / 2),
                ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)) := by
  refine ⟨(4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) + 1, by positivity, ?_⟩
  intro y t ht A hAcont hApos b c Kb hc hKb hcoefdom hcoer v
  obtain ⟨u1, hu1val, hu1grad⟩ := exists_killedSobolevGraph_of_nativeH10
    (Ω := centeredCube y t ht)
    (v : Homogenization.H10Function (centeredCube y t ht : Set (SpatialCoordinates d)))
  obtain ⟨w1, hw1val, hw1grad⟩ := aux_lane4_coercivity_dilation_killed_pullback d y t ht one_pos u1
  have hw1weak : (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) ∈
      weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) :=
    killedSobolevGraph_le_weakSobolevGraph w1.property
  have hEB := aux_hcoer_transfer_energy_bound y t ht A hAcont hApos b c hc hcoefdom
    (v : Homogenization.H10Function (centeredCube y t ht : Set (SpatialCoordinates d))).toH1Function
    (u1 : SobolevData (centeredCube y t ht)) hu1grad
    (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) hw1weak
    hw1val hw1grad
  obtain ⟨hEB1, hEB2⟩ := hEB
  set R : ℝ := ∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
    A z * Homogenization.vecDot (v.grad z) (v.grad z) with hR_def
  have hRnonneg : 0 ≤ R := by
    rw [hR_def]
    apply integral_nonneg
    intro z
    apply mul_nonneg (hApos z).le
    simp only [Homogenization.vecDot]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  have hform_bound : sobolevCoefficientForm b
      (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
      (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) ≤
      c⁻¹ * (t ^ ((2 : ℝ) - d) * R) := by
    have h := mul_le_mul_of_nonneg_left hEB1 hcinv.le
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h
    exact h
  have hcoer_w1 := hcoer w1
  have hsqnorm_eq := aux_hcoer_transfer_sqnorm_eq hd 0 1 one_pos
    (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1
  -- seminorm side
  have hdrop_semi : cubeFractionalVecSeminormSq hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) ≤
      Kb * sobolevCoefficientForm b
        (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
        (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) := by
    have hL2nonneg : (0 : ℝ) ≤ ‖(w1 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ^ 2 /
        volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)) := by positivity
    linarith [hsqnorm_eq, hcoer_w1]
  have hseminormSq_bound : cubeFractionalVecSeminormSq hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) ≤
      Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R)) :=
    hdrop_semi.trans (mul_le_mul_of_nonneg_left hform_bound hKb)
  -- L2 side
  have hdrop_norm : ‖(w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ^ 2 ≤
      Kb * sobolevCoefficientForm b
        (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
        (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) := by
    have hseminonneg : (0 : ℝ) ≤ cubeFractionalVecSeminormSq hd 0 1 one_pos threeQuarterOrder
        (fun _ : Fin 1 => (w1 : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) := by
      unfold cubeFractionalVecSeminormSq; positivity
    have hvol1 : volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) = 1 := centeredCube_one_volume_real 0 one_pos
    have hsum1 : (∑ i : Fin 1, ‖(fun _ : Fin 1 => (w1 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) i‖ ^ 2) =
        ‖(w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ^ 2 := by
      simp
    rw [hvol1] at hsqnorm_eq
    simp only [hsum1, div_one] at hsqnorm_eq
    linarith [hsqnorm_eq, hcoer_w1]
  have hnormSq_bound : ‖(w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ^ 2 ≤
      Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R)) :=
    hdrop_norm.trans (mul_le_mul_of_nonneg_left hform_bound hKb)
  -- L2 term
  have hnormscale := aux_lane4_gagliardo_dilation_scaling_norm d y 0 ht one_pos
    (u1 : SobolevData (centeredCube y t ht)).1
    (w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 hw1val
  have hu1normSq_bound : ‖(u1 : SobolevData (centeredCube y t ht)).1‖ ^ 2 ≤
      t ^ d * (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R))) := by
    rw [hnormscale]
    exact mul_le_mul_of_nonneg_left hnormSq_bound (by positivity)
  have hnormsq_int : ‖(u1 : SobolevData (centeredCube y t ht)).1‖ ^ 2 =
      ∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
        ((u1 : SobolevData (centeredCube y t ht)).1 z) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with z
    simp [sq, RCLike.inner_apply]
  have hu1_int : Integrable (fun z => ((u1 : SobolevData (centeredCube y t ht)).1 z) ^ 2)
      (volume.restrict (centeredCube y t ht : Set (SpatialCoordinates d))) := by
    have hint := L2.integrable_inner (𝕜 := ℝ) (u1 : SobolevData (centeredCube y t ht)).1
      (u1 : SobolevData (centeredCube y t ht)).1
    simpa [sq, RCLike.inner_apply] using hint
  have hu1_nonneg : 0 ≤ᵐ[volume.restrict (centeredCube y t ht : Set (SpatialCoordinates d))]
      (fun z => ((u1 : SobolevData (centeredCube y t ht)).1 z) ^ 2) := by
    filter_upwards with z; positivity
  have hlint_normsq : ENNReal.ofReal (∫ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
      ((u1 : SobolevData (centeredCube y t ht)).1 z) ^ 2) =
      ∫⁻ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
        ENNReal.ofReal (((u1 : SobolevData (centeredCube y t ht)).1 z) ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hu1_int hu1_nonneg
  have hvtoFun_congr : ∫⁻ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((v.toFun z) ^ 2) =
      ∫⁻ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
        ENNReal.ofReal (((u1 : SobolevData (centeredCube y t ht)).1 z) ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [hu1val] with z hz
    rw [hz]
  have hL2term_le : (∫⁻ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((v.toFun z) ^ 2)) ≤
      ENNReal.ofReal (t ^ d * (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R)))) := by
    rw [hvtoFun_congr, ← hlint_normsq, ← hnormsq_int]
    exact ENNReal.ofReal_le_ofReal hu1normSq_bound
  have hL2term_le' : (∫⁻ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((v.toFun z) ^ 2)) ≤
      ENNReal.ofReal (Kb * c⁻¹ * t ^ (2 : ℝ)) *
        ∫⁻ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
          ENNReal.ofReal (A z * Homogenization.vecDot (v.grad z) (v.grad z)) := by
    refine hL2term_le.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ t ^ d),
      aux_hcoer_transfer_l2_ennreal_combine d t Kb c R ht hKb hc hRnonneg, hEB2]
  -- Gagliardo term (same route as the mean-zero case, using w1 directly)
  have hY1_fin : cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w1 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) < ⊤ :=
    S.h1_fractional_finite 0 1 one_pos
      ⟨(w1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)), hw1weak⟩
  have hY1sq_eq : (cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w1 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) ^ 2 =
      ENNReal.ofReal (cubeFractionalVecSeminormSq hd 0 1 one_pos threeQuarterOrder
        (fun _ : Fin 1 => (w1 : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) := by
    unfold cubeFractionalVecSeminormSq
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hY1_fin.ne]
  have hY1sq_le : (cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
      (fun _ : Fin 1 => (w1 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) ^ 2 ≤
      ENNReal.ofReal (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R))) := by
    rw [hY1sq_eq]; exact ENNReal.ofReal_le_ofReal hseminormSq_bound
  have hfg : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      (fun _ : Fin 1 => (w1 : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) (0 : Fin 1) x =
      (fun _ : Fin 1 => (u1 : SobolevData (centeredCube y t ht)).1) (0 : Fin 1)
        (cubeDilation y 0 t x) := hw1val
  have hgagl := lane4_gagliardo_dilation_scaling d 1 hd y 0 t ht one_pos threeQuarterOrder
    (fun _ : Fin 1 => (u1 : SobolevData (centeredCube y t ht)).1)
    (fun _ : Fin 1 => (w1 : SobolevData
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)
    (fun _ : Fin 1 => hfg)
  have hXQ_eq : (cubeFractionalL2Seminorm hd y t ht threeQuarterOrder
      (fun _ : Fin 1 => (u1 : SobolevData (centeredCube y t ht)).1)) ^ 2 =
      ENNReal.ofReal (t ^ (-(2 * (threeQuarterOrder : ℝ)))) *
        (cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
          (fun _ : Fin 1 => (w1 : SobolevData
            (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) ^ 2 :=
    hgagl.1
  have hXQ_le : (cubeFractionalL2Seminorm hd y t ht threeQuarterOrder
      (fun _ : Fin 1 => (u1 : SobolevData (centeredCube y t ht)).1)) ^ 2 ≤
      ENNReal.ofReal (t ^ (-(2 * (threeQuarterOrder : ℝ)))) *
        ENNReal.ofReal (Kb * (c⁻¹ * (t ^ ((2 : ℝ) - d) * R))) := by
    rw [hXQ_eq]
    exact mul_le_mul_of_nonneg_left hY1sq_le (zero_le _)
  have hgag_le := aux_hcoer_transfer_gag_le_seminorm hd y t ht
    (u1 : SobolevData (centeredCube y t ht)).1
  have hgag_congr : aux_hcoer_gag v.toFun (Metric.ball y (t / 2)) =
      aux_hcoer_gag ((u1 : SobolevData (centeredCube y t ht)).1 : SpatialCoordinates d → ℝ)
        (centeredCube y t ht : Set (SpatialCoordinates d)) :=
    aux_hcoer_transfer_gag_congr_ae v.toFun
      ((u1 : SobolevData (centeredCube y t ht)).1 : SpatialCoordinates d → ℝ)
      (centeredCube y t ht : Set (SpatialCoordinates d)) (centeredCube y t ht).isOpen.measurableSet
      hu1val.symm
  have hexp34 : (-(2 * (threeQuarterOrder : ℝ))) = -(3 / 2 : ℝ) := by
    show (-(2 * (3 / 4 : ℝ))) = -(3 / 2 : ℝ); ring
  have ht_pow2 : t ^ d = t ^ ((d : ℝ)) := (Real.rpow_natCast t d).symm
  have hgagTerm_le : aux_hcoer_gag v.toFun (Metric.ball y (t / 2)) ≤
      ENNReal.ofReal ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ *
          t ^ ((1 : ℝ) / 2)) *
        ∫⁻ z in (centeredCube y t ht : Set (SpatialCoordinates d)),
          ENNReal.ofReal (A z * Homogenization.vecDot (v.grad z) (v.grad z)) := by
    rw [hgag_congr]
    refine hgag_le.trans ?_
    refine (mul_le_mul_of_nonneg_left hXQ_le (zero_le _)).trans ?_
    rw [centeredCube_volume, hexp34, ht_pow2]
    exact le_of_eq
      ((aux_hcoer_transfer_gag_ennreal_combine d t Kb c R ht hKb hc hRnonneg).trans
        (by rw [hEB2]))
  -- combine
  have hsum_le := add_le_add hgagTerm_le hL2term_le'
  refine hsum_le.trans ?_
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply mul_le_mul_of_nonneg_right _ (zero_le _)
  apply ENNReal.ofReal_le_ofReal
  have hslack : (0 : ℝ) ≤ (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * (Kb * c⁻¹) * t ^ (2 : ℝ) +
      Kb * c⁻¹ * t ^ ((1 : ℝ) / 2) := by positivity
  have hexpand : (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ * t ^ (1 / 2 : ℝ) +
      Kb * c⁻¹ * t ^ (2 : ℝ) +
      ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * (Kb * c⁻¹) * t ^ (2 : ℝ) +
        Kb * c⁻¹ * t ^ ((1 : ℝ) / 2)) =
      ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) + 1) * Kb * c⁻¹ *
        (t ^ (1 / 2 : ℝ) + t ^ 2) := by
    rw [show (t:ℝ)^(2:ℕ) = t^(2:ℝ) from (Real.rpow_natCast t 2).symm]
    ring
  calc (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ * t ^ (1 / 2 : ℝ) +
      Kb * c⁻¹ * t ^ (2 : ℝ)
      ≤ (4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * Kb * c⁻¹ * t ^ (1 / 2 : ℝ) +
        Kb * c⁻¹ * t ^ (2 : ℝ) +
        ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) * (Kb * c⁻¹) * t ^ (2 : ℝ) +
          Kb * c⁻¹ * t ^ ((1 : ℝ) / 2)) := le_add_of_nonneg_right hslack
    _ = ((4 / 3) * (Real.sqrt d) ^ ((d : ℝ) + 3 / 2) + 1) * Kb * c⁻¹ *
        (t ^ (1 / 2 : ℝ) + t ^ 2) := hexpand

/-- **(ONE)** The constant coefficient `1` on the unit cube. -/
theorem aux_hcoer_one_coefficient (d : ℕ) :
    ∃ b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ∀ᵐ x ∂(volume.restrict
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
        (b.val : SpatialCoordinates d → ℝ) x = 1 := by
  refine ⟨expPotentialCoefficient (0 : Lp ℝ ∞ (volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))), ?_⟩
  filter_upwards [expPotentialCoefficient_coeFn (0 : Lp ℝ ∞ (volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))),
    Lp.coeFn_zero ℝ ∞ (volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))]
    with x hx hzero
  rw [hx]
  simpa using congrArg Real.exp hzero

end Paper
end
end

-- ===== module HCoer.SubMom =====
section
/-!
# hCoer: per-subcube random constants and their moments

A subcube of side `3^{-k}` centred at `y`:
* `k ≤ N`: zoom by `3^k` (`aux_hcut_cellEnv y k`), constant `cellConst⁻¹ · Kr (N-k) (cellEnv)`;
* `k > N`: translate by `y` only, constant `Kone · (e^{H y} · ml (T_y ω))⁻¹` (`ml` = lower bound of the
  cutoff-`N` coefficient on the closed unit cube).
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- Level `k ≤ N` subcube constant. -/
def aux_hcoer_Kin (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Kr : ℕ → BilateralField d → ℝ) (N : ℕ) (y : SpatialCoordinates d) (k : ℕ) (om : BilateralField d) : ℝ :=
  (aux_hcut_cellConst M H y k N om)⁻¹ * Kr (N - k) (aux_hcut_cellEnv y k om)

/-- Level `k > N` subcube constant. -/
def aux_hcoer_Kout (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (ml : BilateralField d → ℝ)
    (Kone : ℝ) (y : SpatialCoordinates d) (om : BilateralField d) : ℝ :=
  Kone * (Real.exp (H om y) * ml (aux_tight_scale_covariance_translate y om))⁻¹

/-- The subcube constant. -/
def aux_hcoer_Ksub (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Kr : ℕ → BilateralField d → ℝ) (ml : ℕ → BilateralField d → ℝ) (Kone : ℝ) (N : ℕ)
    (y : SpatialCoordinates d) (k : ℕ) (om : BilateralField d) : ℝ :=
  if k ≤ N then aux_hcoer_Kin M H Kr N y k om else aux_hcoer_Kout H (ml N) Kone y om

section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hcoer_measurable_translate (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (y : SpatialCoordinates d) :
    Measurable (aux_tight_scale_covariance_translate (d := d) y) :=
  (aux_tight_scale_covariance_measurePreserving_translate M y).measurable

lemma aux_hcoer_Kin_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (Kr : ℕ → BilateralField d → ℝ)
    (hKr0 : ∀ n om, 0 ≤ Kr n om) (N : ℕ) (y : SpatialCoordinates d) (k : ℕ) (om : BilateralField d) :
    0 ≤ aux_hcoer_Kin M H Kr N y k om :=
  mul_nonneg (inv_nonneg.2 (aux_hcut_cellConst_pos M Rm H y k N om).le) (hKr0 _ _)

lemma aux_hcoer_Kout_nonneg (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (ml : BilateralField d → ℝ)
    (hml0 : ∀ om, 0 < ml om) {Kone : ℝ} (hKone : 0 ≤ Kone) (y : SpatialCoordinates d)
    (om : BilateralField d) : 0 ≤ aux_hcoer_Kout H ml Kone y om :=
  mul_nonneg hKone (inv_nonneg.2 (mul_pos (Real.exp_pos _) (hml0 _)).le)

lemma aux_hcoer_Ksub_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (Kr : ℕ → BilateralField d → ℝ)
    (hKr0 : ∀ n om, 0 ≤ Kr n om) (ml : ℕ → BilateralField d → ℝ) (hml0 : ∀ n om, 0 < ml n om)
    {Kone : ℝ} (hKone : 0 ≤ Kone) (N : ℕ) (y : SpatialCoordinates d) (k : ℕ) (om : BilateralField d) :
    0 ≤ aux_hcoer_Ksub M H Kr ml Kone N y k om := by
  unfold aux_hcoer_Ksub
  split_ifs
  · exact aux_hcoer_Kin_nonneg M Rm H Kr hKr0 N y k om
  · exact aux_hcoer_Kout_nonneg H (ml N) (hml0 N) hKone y om

lemma aux_hcoer_measurable_Ksub (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (Kr : ℕ → BilateralField d → ℝ) (hKrm : ∀ n, Measurable (Kr n))
    (ml : ℕ → BilateralField d → ℝ) (hmlm : ∀ n, Measurable (ml n)) (Kone : ℝ) (N : ℕ)
    (y : SpatialCoordinates d) (k : ℕ) :
    Measurable (aux_hcoer_Ksub M H Kr ml Kone N y k) := by
  unfold aux_hcoer_Ksub
  split_ifs
  · exact (aux_hcut_measurable_cellConst M hH y k N).inv.mul
      ((hKrm _).comp (aux_hcut_measurable_cellEnv M y k))
  · have hHy : Measurable fun om => H om y := (continuous_eval_const y).measurable.comp hH.1
    exact measurable_const.mul ((hHy.exp.mul ((hmlm N).comp (aux_hcoer_measurable_translate M y))).inv)

/-- `cellConst⁻¹` has the same envelope as `cellConst`. -/
lemma aux_hcoer_cellConst_inv_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (y : SpatialCoordinates d) {n N : ℕ}
    (hn : 1 ≤ n) (om : BilateralField d) :
    (aux_hcut_cellConst M H y n N om)⁻¹ ≤
      Real.exp (|H om y|) * aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om) := by
  unfold aux_hcut_cellConst
  rw [mul_inv, inv_inv, ← Real.exp_neg]
  exact mul_le_mul (Real.exp_le_exp.2 (neg_le_abs _))
    (aux_prop_growth_large_root_shiftConst_le M Rm n (N - n) (by omega) _)
    (aux_prop_growth_large_root_shiftConst_pos M Rm _ _ _).le (Real.exp_pos _).le

/-- Generic cell moment: any `Z ≤ e^{|H y|} · shiftEnv (cellEnv)` times `K ∘ cellEnv`. -/
lemma aux_hcoer_Z_moment (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (y : SpatialCoordinates d) (n : ℕ)
    (Z : BilateralField d → ℝ) (hZm : Measurable Z) (hZ0 : ∀ om, 0 ≤ Z om)
    (hZ : ∀ om, Z om ≤ Real.exp (|H om y|) * aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om))
    (K : BilateralField d → ℝ) (hK : Measurable K) (hK0 : ∀ om, 0 ≤ K om) (p : ℝ) (hp : 1 ≤ p)
    (EH : ℝ≥0∞)
    (hEH : ∫⁻ om, ENNReal.ofReal (Real.exp (4 * p * |H om y|)) ∂(chaosSampleLaw M).toMeasure ≤ EH) :
    ∫⁻ om, ENNReal.ofReal ((Z om * K (aux_hcut_cellEnv y n om)) ^ p)
        ∂(chaosSampleLaw M).toMeasure ≤
      (EH ^ (1 / 2 : ℝ) * ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
          (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ om, ENNReal.ofReal (K om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^ (1 / 2 : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hmp := aux_hcut_measurePreserving_cellEnv M y n
  have h1 := aux_hcut_cs_ofReal (chaosSampleLaw M).toMeasure Z
    (fun om => K (aux_hcut_cellEnv y n om)) hZm (hK.comp hmp.measurable) hZ0 (fun om => hK0 _) p hp0
  have h2 : ∫⁻ om, ENNReal.ofReal (K (aux_hcut_cellEnv y n om) ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure =
      ∫⁻ om, ENNReal.ofReal (K om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure :=
    hmp.lintegral_comp (f := fun om => ENNReal.ofReal (K om ^ (2 * p)))
      (ENNReal.measurable_ofReal.comp (hK.pow_const _))
  have hHy : Measurable fun om => H om y := (continuous_eval_const y).measurable.comp hH.1
  have hS : Measurable fun om => aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om) := by
    unfold aux_prop_growth_large_root_shiftEnv
    exact (measurable_const.add ((aux_prop_growth_large_root_measurable_irAnchor n).comp
      hmp.measurable).abs).exp
  have h3 : ∫⁻ om, ENNReal.ofReal (Z om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure ≤
      ∫⁻ om, ENNReal.ofReal ((Real.exp (|H om y|) *
        aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om)) ^ (2 * p))
        ∂(chaosSampleLaw M).toMeasure :=
    lintegral_mono fun om => ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (hZ0 om) (hZ om) (by positivity))
  have h4 := aux_hcut_cs_ofReal (chaosSampleLaw M).toMeasure (fun om => Real.exp (|H om y|))
    (fun om => aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om)) hHy.abs.exp hS
    (fun om => (Real.exp_pos _).le)
    (fun om => le_trans zero_le_one (aux_prop_growth_large_root_one_le_shiftEnv M n _)) (2 * p) (by positivity)
  have h5 : ∫⁻ om, ENNReal.ofReal (Real.exp (|H om y|) ^ (2 * (2 * p))) ∂(chaosSampleLaw M).toMeasure ≤ EH := by
    refine le_trans (le_of_eq (lintegral_congr fun om => ?_)) hEH
    rw [← Real.exp_mul]; ring_nf
  have h6 : ∫⁻ om, ENNReal.ofReal (aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om) ^ (2 * (2 * p)))
      ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
          (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n) := by
    rw [hmp.lintegral_comp (f := fun om => ENNReal.ofReal
      (aux_prop_growth_large_root_shiftEnv M n om ^ (2 * (2 * p))))
      (ENNReal.measurable_ofReal.comp (by
        unfold aux_prop_growth_large_root_shiftEnv
        exact ((measurable_const.add (aux_prop_growth_large_root_measurable_irAnchor n).abs).exp).pow_const _))]
    have e : 2 * (2 * p) = 4 * p := by ring
    rw [e]
    exact aux_hcut_shiftEnv_lintegral M n (4 * p) (by linarith)
  calc ∫⁻ om, ENNReal.ofReal ((Z om * K (aux_hcut_cellEnv y n om)) ^ p) ∂(chaosSampleLaw M).toMeasure
      ≤ (∫⁻ om, ENNReal.ofReal (Z om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^ (1 / 2 : ℝ) *
          (∫⁻ om, ENNReal.ofReal (K (aux_hcut_cellEnv y n om) ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^
            (1 / 2 : ℝ) := h1
    _ ≤ (EH ^ (1 / 2 : ℝ) * ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
          (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ om, ENNReal.ofReal (K om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^ (1 / 2 : ℝ) := by
        rw [h2]
        gcongr
        exact h3.trans (h4.trans (by gcongr))

end Laws

end Paper
end
end

-- ===== module HCoer.SubMom2 =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Moment of the level-`k ≤ N` constant. -/
lemma aux_hcoer_Kin_moment (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (R CH : ℝ) (hCH : ∀ (lam : ℝ), 0 ≤ lam → ∀ y : SpatialCoordinates d, ‖y‖ ≤ R →
        Integrable (fun om => Real.exp (lam * |H om y|)) (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * |H om y|) ∂(chaosSampleLaw M).toMeasure ≤
          2 * Real.exp (CH * lam ^ 2 * M.delta ^ 2))
    (y : SpatialCoordinates d) (hy : ‖y‖ ≤ R) {k N : ℕ} (hk : 1 ≤ k)
    (Kr : ℕ → BilateralField d → ℝ) (hKrm : ∀ n, Measurable (Kr n)) (hKr0 : ∀ n om, 0 ≤ Kr n om)
    (p : ℝ) (hp : 1 ≤ p) (Cb2 : ℝ) (hCb2 : 0 ≤ Cb2)
    (hKb : ∀ n, ∫⁻ om, ENNReal.ofReal (Kr n om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb2)
    (hsmall : Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 + (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 2) :
    ∫⁻ om, ENNReal.ofReal (aux_hcoer_Kin M H Kr N y k om ^ p) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) *
        (2 * 4 ^ k) ^ (1 / 4 : ℝ) * Cb2 ^ (1 / 2 : ℝ)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hint, hbd⟩ := hCH (4 * p) (by positivity) y hy
  have hEH : ∫⁻ om, ENNReal.ofReal (Real.exp (4 * p * |H om y|)) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun om => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hbd
  have hX := aux_hcoer_Z_moment M hH y k (fun om => (aux_hcut_cellConst M H y k N om)⁻¹)
    (aux_hcut_measurable_cellConst M hH y k N).inv
    (fun om => inv_nonneg.2 (aux_hcut_cellConst_pos M Rm H y k N om).le)
    (fun om => aux_hcoer_cellConst_inv_le M Rm H y hk om) (Kr (N - k)) (hKrm _) (hKr0 _) p hp _ hEH
  unfold aux_hcoer_Kin
  refine hX.trans ?_
  have hS : ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
      (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ k) ≤ ENNReal.ofReal (2 * 4 ^ k) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have : 2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 + (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 4 := by
      linarith
    have h0 : 0 ≤ 2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 + (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) := by
      positivity
    gcongr
  have hA0 : 0 ≤ 2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2) := by positivity
  calc (ENNReal.ofReal (2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
            (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ k) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ om, ENNReal.ofReal (Kr (N - k) om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (2 * 4 ^ k) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) * ENNReal.ofReal Cb2 ^ (1 / 2 : ℝ) := by
        gcongr
        exact hKb _
    _ = ENNReal.ofReal ((2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) *
          (2 * 4 ^ k) ^ (1 / 4 : ℝ) * Cb2 ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hCb2 (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hA0,
          ← Real.rpow_mul (by positivity)]
        norm_num

/-- Moment of the level-`k > N` constant. -/
lemma aux_hcoer_Kout_moment (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (y : SpatialCoordinates d) (ml : BilateralField d → ℝ) (hmlm : Measurable ml) (hml0 : ∀ om, 0 < ml om)
    (Kone : ℝ) (hKone : 0 ≤ Kone) (p : ℝ) (hp : 1 ≤ p) (EH Eml : ℝ≥0∞)
    (hEH : ∫⁻ om, ENNReal.ofReal (Real.exp (2 * p * |H om y|)) ∂(chaosSampleLaw M).toMeasure ≤ EH)
    (hEml : ∫⁻ om, ENNReal.ofReal ((ml om)⁻¹ ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure ≤ Eml) :
    ∫⁻ om, ENNReal.ofReal (aux_hcoer_Kout H ml Kone y om ^ p) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Kone ^ p) * (EH ^ (1 / 2 : ℝ) * Eml ^ (1 / 2 : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hmp := aux_tight_scale_covariance_measurePreserving_translate M y
  have hHy : Measurable fun om => H om y := (continuous_eval_const y).measurable.comp hH.1
  have e : ∀ om, aux_hcoer_Kout H ml Kone y om ^ p =
      Kone ^ p * (Real.exp (-H om y) * (ml (aux_tight_scale_covariance_translate y om))⁻¹) ^ p := by
    intro om
    unfold aux_hcoer_Kout
    rw [mul_inv, ← Real.exp_neg, Real.mul_rpow hKone (by
      exact mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 (hml0 _).le))]
  simp_rw [e]
  have hK0 : 0 ≤ Kone ^ p := Real.rpow_nonneg hKone _
  simp_rw [ENNReal.ofReal_mul hK0]
  have hmeas : Measurable fun om => ENNReal.ofReal
      ((Real.exp (-H om y) * (ml (aux_tight_scale_covariance_translate y om))⁻¹) ^ p) :=
    ENNReal.measurable_ofReal.comp ((hHy.neg.exp.mul ((hmlm.comp hmp.measurable).inv)).pow_const p)
  rw [lintegral_const_mul _ hmeas]
  gcongr
  have h1 := aux_hcut_cs_ofReal (chaosSampleLaw M).toMeasure (fun om => Real.exp (-H om y))
    (fun om => (ml (aux_tight_scale_covariance_translate y om))⁻¹) hHy.neg.exp
    (hmlm.comp hmp.measurable).inv (fun om => (Real.exp_pos _).le)
    (fun om => inv_nonneg.2 (hml0 _).le) p hp0
  refine h1.trans ?_
  gcongr
  · refine le_trans (lintegral_mono fun om => ?_) hEH
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_mul, mul_comm]
    exact Real.exp_le_exp.2 (by nlinarith [neg_le_abs (H om y)])
  · rw [hmp.lintegral_comp (f := fun om => ENNReal.ofReal ((ml om)⁻¹ ^ (2 * p)))
      (ENNReal.measurable_ofReal.comp (hmlm.inv.pow_const _))]
    exact hEml

end Paper
end
end

-- ===== module HCoer.SubAe =====
section
/-!
# hCoer: almost-sure coercivity on one subcube
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The body of `aux_hcoer_transfer_meanzero` for a fixed constant `Cd`. -/
def aux_hcoer_TransferMZ (hd : 2 ≤ d) (Cd : ℝ) : Prop :=
  ∀ (y : SpatialCoordinates d) (t : ℝ), 0 < t →
  ∀ (A : SpatialCoordinates d → ℝ), Continuous A → (∀ x, 0 < A x) →
  ∀ (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) (c Kb : ℝ),
    0 < c → 0 ≤ Kb →
    (∀ᵐ x ∂(volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      c * (b.val : SpatialCoordinates d → ℝ) x ≤ A (y + t • x)) →
    (∀ w : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalSqNorm hd 0 1 one_pos threeQuarterOrder
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 ≤
        Kb * sobolevCoefficientForm b
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))) →
    ∀ v : Homogenization.H1Function (Metric.ball y (t / 2)),
      aux_hcoer_gag v.toFun (Metric.ball y (t / 2)) ≤
        ENNReal.ofReal (Cd * Kb * c⁻¹ * t ^ (1 / 2 : ℝ)) *
          ∫⁻ x in Metric.ball y (t / 2),
            ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x))

/-- Mean-zero coercivity of the reference coefficient `b` with constant `K`. -/
def aux_hcoer_CoerMZ (hd : 2 ≤ d) (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (K : ℝ) : Prop :=
  ∀ w : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
    cubeFractionalSqNorm hd 0 1 one_pos threeQuarterOrder
        (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 ≤
      K * sobolevCoefficientForm b
        (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
        (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))

lemma aux_hcoer_cutoffCoefficient_congr (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H H' : BilateralField d → C(SpatialCoordinates d, ℝ)} {om : BilateralField d} (h : H om = H' om)
    (N : ℕ) (x : SpatialCoordinates d) : cutoffCoefficient M H om N x = cutoffCoefficient M H' om N x := by
  simp only [cutoffCoefficient, cutoffPotential, h]

lemma aux_hcoer_three_inv_pos (k : ℕ) : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹ := by positivity

lemma aux_hcoer_three_inv_le_one (k : ℕ) : ((3 : ℝ) ^ k)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

lemma aux_hcoer_rpow_half_le_one (k : ℕ) : (((3 : ℝ) ^ k)⁻¹) ^ (1 / 2 : ℝ) ≤ 1 :=
  Real.rpow_le_one (aux_hcoer_three_inv_pos k).le (aux_hcoer_three_inv_le_one k) (by norm_num)

/-- Drop the harmless factor `t^{1/2} ≤ 1`. -/
lemma aux_hcoer_drop_t (Cd Kb c : ℝ) (hCd : 0 ≤ Cd) (hKb : 0 ≤ Kb) (hc : 0 < c) (k : ℕ) (E : ℝ≥0∞) :
    ENNReal.ofReal (Cd * Kb * c⁻¹ * (((3 : ℝ) ^ k)⁻¹) ^ (1 / 2 : ℝ)) * E ≤
      ENNReal.ofReal (Cd * (c⁻¹ * Kb)) * E := by
  refine mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) E
  have h0 : 0 ≤ Cd * Kb * c⁻¹ := by positivity
  calc Cd * Kb * c⁻¹ * (((3 : ℝ) ^ k)⁻¹) ^ (1 / 2 : ℝ) ≤ Cd * Kb * c⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (aux_hcoer_rpow_half_le_one k) h0
    _ = Cd * (c⁻¹ * Kb) := by ring

section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- **(SUBCUBE, `k ≤ N`)** -/
lemma aux_hcoer_sub_ae_in (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H H0 : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (hH0 : InfraredCharacterization M H0) (Cd : ℝ) (hCd : 0 < Cd) (htr : aux_hcoer_TransferMZ hd Cd)
    (Kr : ℕ → BilateralField d → ℝ) (hKr0 : ∀ n om, 0 ≤ Kr n om)
    (hKrc : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      aux_hcoer_CoerMZ hd (cutoffPositiveCoefficient M H0 om n 0 one_pos) (Kr n om))
    (N : ℕ) (y : SpatialCoordinates d) (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ v : Homogenization.H1Function (Metric.ball y (((3 : ℝ) ^ k)⁻¹ / 2)),
        aux_hcoer_gag v.toFun (Metric.ball y (((3 : ℝ) ^ k)⁻¹ / 2)) ≤
          ENNReal.ofReal (Cd * aux_hcoer_Kin M H Kr N y k om) *
            ∫⁻ x in Metric.ball y (((3 : ℝ) ^ k)⁻¹ / 2),
              ENNReal.ofReal (cutoffCoefficient M H om N x *
                Homogenization.vecDot (v.grad x) (v.grad x)) := by
  have hmp := aux_hcut_measurePreserving_cellEnv M y k
  have hE2 : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      H (aux_hcut_cellEnv y k om) = H0 (aux_hcut_cellEnv y k om) :=
    hmp.quasiMeasurePreserving.ae (aux_hcut_H_ae_eq M hH hH0)
  have hE3 : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      aux_hcoer_CoerMZ hd (cutoffPositiveCoefficient M H0 (aux_hcut_cellEnv y k om) (N - k) 0 one_pos)
        (Kr (N - k) (aux_hcut_cellEnv y k om)) :=
    hmp.quasiMeasurePreserving.ae (hKrc (N - k))
  filter_upwards [aux_hcut_ae_coeff_cell M Rm hH y hkN, hE2, hE3] with om h1 h2 h3
  intro v
  set om' := aux_hcut_cellEnv y k om with hom'
  have hc := aux_hcut_cellConst_pos M Rm H y k N om
  have hcb : ∀ᵐ x ∂(volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      aux_hcut_cellConst M H y k N om *
          ((cutoffPositiveCoefficient M H0 om' (N - k) 0 one_pos).val : SpatialCoordinates d → ℝ) x ≤
        cutoffCoefficient M H om N (y + ((3 : ℝ) ^ k)⁻¹ • x) := by
    filter_upwards [aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae M H0 om' (N - k) 0 one_pos]
      with x hx
    rw [hx, h1 x, ← aux_hcoer_cutoffCoefficient_congr M h2]
    rfl
  have hmain := htr y (((3 : ℝ) ^ k)⁻¹) (aux_hcoer_three_inv_pos k) (cutoffCoefficient M H om N)
    (cutoffCoefficient_continuous M H om N) (cutoffCoefficient_pos M H om N)
    (cutoffPositiveCoefficient M H0 om' (N - k) 0 one_pos) (aux_hcut_cellConst M H y k N om)
    (Kr (N - k) om') hc (hKr0 _ _) hcb h3 v
  refine hmain.trans ?_
  exact aux_hcoer_drop_t Cd (Kr (N - k) om') _ hCd.le (hKr0 _ _) hc k _

/-- **(SUBCUBE, `k > N`)** -/
lemma aux_hcoer_sub_ae_out (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (Cd : ℝ) (hCd : 0 < Cd) (htr : aux_hcoer_TransferMZ hd Cd)
    (ml : BilateralField d → ℝ) (hml0 : ∀ om, 0 < ml om) (N : ℕ)
    (hml : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ml om ≤ cutoffCoefficient M H om N x)
    (b1 : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hb1 : ∀ᵐ x ∂(volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      (b1.val : SpatialCoordinates d → ℝ) x = 1)
    (Kone : ℝ) (hKone0 : 0 ≤ Kone) (hKone : aux_hcoer_CoerMZ hd b1 Kone)
    (y : SpatialCoordinates d) (k : ℕ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ v : Homogenization.H1Function (Metric.ball y (((3 : ℝ) ^ k)⁻¹ / 2)),
        aux_hcoer_gag v.toFun (Metric.ball y (((3 : ℝ) ^ k)⁻¹ / 2)) ≤
          ENNReal.ofReal (Cd * aux_hcoer_Kout H ml Kone y om) *
            ∫⁻ x in Metric.ball y (((3 : ℝ) ^ k)⁻¹ / 2),
              ENNReal.ofReal (cutoffCoefficient M H om N x *
                Homogenization.vecDot (v.grad x) (v.grad x)) := by
  have hmp := aux_tight_scale_covariance_measurePreserving_translate M y
  have hF2 := hmp.quasiMeasurePreserving.ae hml
  filter_upwards [aux_hcut_ae_coeff_translate M hH y N, hF2] with om h1 h2
  intro v
  set c : ℝ := Real.exp (H om y) * ml (aux_tight_scale_covariance_translate y om) with hcdef
  have hc : 0 < c := mul_pos (Real.exp_pos _) (hml0 _)
  have hcb : ∀ᵐ x ∂(volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      c * (b1.val : SpatialCoordinates d → ℝ) x ≤ cutoffCoefficient M H om N (y + ((3 : ℝ) ^ k)⁻¹ • x) := by
    filter_upwards [hb1, ae_restrict_mem (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet]
      with x hx hxU
    rw [hx, mul_one, h1, hcdef]
    refine mul_le_mul_of_nonneg_left (h2 _ ?_) (Real.exp_pos _).le
    rw [centeredCube_coe_eq_ball] at hxU
    change dist (((3 : ℝ) ^ k)⁻¹ • x) 0 ≤ 1 / 2
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (aux_hcoer_three_inv_pos k).le]
    rw [Metric.mem_ball, dist_zero_right] at hxU
    calc ((3 : ℝ) ^ k)⁻¹ * ‖x‖ ≤ 1 * ‖x‖ :=
          mul_le_mul_of_nonneg_right (aux_hcoer_three_inv_le_one k) (norm_nonneg _)
      _ ≤ 1 / 2 := by linarith
  have hmain := htr y (((3 : ℝ) ^ k)⁻¹) (aux_hcoer_three_inv_pos k) (cutoffCoefficient M H om N)
    (cutoffCoefficient_continuous M H om N) (cutoffCoefficient_pos M H om N) b1 c Kone hc hKone0 hcb hKone v
  refine hmain.trans ?_
  have e : aux_hcoer_Kout H ml Kone y om = c⁻¹ * Kone := by
    unfold aux_hcoer_Kout; rw [hcdef]; ring
  rw [e]
  exact aux_hcoer_drop_t Cd Kone c hCd.le hKone0 hc k _

/-- **(SUBCUBE)** Both regimes. -/
lemma aux_hcoer_sub_ae (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H H0 : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (hH0 : InfraredCharacterization M H0) (Cd : ℝ) (hCd : 0 < Cd) (htr : aux_hcoer_TransferMZ hd Cd)
    (Kr : ℕ → BilateralField d → ℝ) (hKr0 : ∀ n om, 0 ≤ Kr n om)
    (hKrc : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      aux_hcoer_CoerMZ hd (cutoffPositiveCoefficient M H0 om n 0 one_pos) (Kr n om))
    (ml : ℕ → BilateralField d → ℝ) (hml0 : ∀ n om, 0 < ml n om)
    (hml : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ml n om ≤ cutoffCoefficient M H om n x)
    (b1 : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hb1 : ∀ᵐ x ∂(volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      (b1.val : SpatialCoordinates d → ℝ) x = 1)
    (Kone : ℝ) (hKone0 : 0 ≤ Kone) (hKone : aux_hcoer_CoerMZ hd b1 Kone)
    (N : ℕ) (y : SpatialCoordinates d) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ v : Homogenization.H1Function (Metric.ball y (((3 : ℝ) ^ k)⁻¹ / 2)),
        aux_hcoer_gag v.toFun (Metric.ball y (((3 : ℝ) ^ k)⁻¹ / 2)) ≤
          ENNReal.ofReal (Cd * aux_hcoer_Ksub M H Kr ml Kone N y k om) *
            ∫⁻ x in Metric.ball y (((3 : ℝ) ^ k)⁻¹ / 2),
              ENNReal.ofReal (cutoffCoefficient M H om N x *
                Homogenization.vecDot (v.grad x) (v.grad x)) := by
  unfold aux_hcoer_Ksub
  by_cases hkN : k ≤ N
  · simp only [hkN, if_true]
    exact aux_hcoer_sub_ae_in hd M Rm hH hH0 Cd hCd htr Kr hKr0 hKrc N y k hk hkN
  · simp only [hkN, if_false]
    exact aux_hcoer_sub_ae_out hd M hH Cd hCd htr (ml N) (hml0 N) N (hml N) b1 hb1 Kone hKone0 hKone y k

end Laws

end Paper
end
end

-- ===== module HCoer.Zoom =====
section
/-!
# hCoer: the `H¹₀` part through one zoomed-out cube `ball 0 (3^j/2)`
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The body of `aux_hcoer_transfer_killed` for a fixed constant `Cd`. -/
def aux_hcoer_TransferK (hd : 2 ≤ d) (Cd : ℝ) : Prop :=
  ∀ (y : SpatialCoordinates d) (t : ℝ), 0 < t →
  ∀ (A : SpatialCoordinates d → ℝ), Continuous A → (∀ x, 0 < A x) →
  ∀ (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) (c Kb : ℝ),
    0 < c → 0 ≤ Kb →
    (∀ᵐ x ∂(volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      c * (b.val : SpatialCoordinates d → ℝ) x ≤ A (y + t • x)) →
    (∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalSqNorm hd 0 1 one_pos threeQuarterOrder
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 ≤
        Kb * sobolevCoefficientForm b
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))) →
    ∀ v : Homogenization.H10Function (Metric.ball y (t / 2)),
      aux_hcoer_gag v.toFun (Metric.ball y (t / 2)) +
          ∫⁻ x in Metric.ball y (t / 2), ENNReal.ofReal (v.toFun x ^ 2) ≤
        ENNReal.ofReal (Cd * Kb * c⁻¹ * (t ^ (1 / 2 : ℝ) + t ^ 2)) *
          ∫⁻ x in Metric.ball y (t / 2),
            ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x))

/-- Killed coercivity of the reference coefficient `b` with constant `K`. -/
def aux_hcoer_CoerK (hd : 2 ≤ d) (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (K : ℝ) : Prop :=
  ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
    cubeFractionalSqNorm hd 0 1 one_pos threeQuarterOrder
        (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 ≤
      K * sobolevCoefficientForm b
        (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
        (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))

/-- The zoom-out constant. -/
def aux_hcoer_K0 (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Kr : ℕ → BilateralField d → ℝ) (N j : ℕ)
    (om : BilateralField d) : ℝ :=
  (aux_prop_growth_large_root_shiftConst M j N om)⁻¹ * Kr (N + j) (aux_prop_growth_large_root_scaleShift j om)

section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hcoer_K0_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (Kr : ℕ → BilateralField d → ℝ) (hKr0 : ∀ n om, 0 ≤ Kr n om) (N j : ℕ) (om : BilateralField d) :
    0 ≤ aux_hcoer_K0 M Kr N j om :=
  mul_nonneg (inv_nonneg.2 (aux_prop_growth_large_root_shiftConst_pos M Rm j N om).le) (hKr0 _ _)

lemma aux_hcoer_measurable_K0 (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Kr : ℕ → BilateralField d → ℝ) (hKrm : ∀ n, Measurable (Kr n)) (N j : ℕ) :
    Measurable (aux_hcoer_K0 M Kr N j) := by
  unfold aux_hcoer_K0
  refine Measurable.mul ?_ ((hKrm _).comp (aux_prop_growth_large_root_measurePreserving_scaleShift M j).measurable)
  exact (aux_hcut_measurable_shiftConst M j N).inv

/-- **(ZOOM-OUT)** a.s. killed coercivity on `ball 0 (3^j/2)`. -/
lemma aux_hcoer_zoom_ae (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H H0 : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (hH0 : InfraredCharacterization M H0) (Cd : ℝ) (hCd : 0 < Cd) (htr : aux_hcoer_TransferK hd Cd)
    (Kr : ℕ → BilateralField d → ℝ) (hKr0 : ∀ n om, 0 ≤ Kr n om)
    (hKrc : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      aux_hcoer_CoerK hd (cutoffPositiveCoefficient M H0 om n 0 one_pos) (Kr n om))
    (N j : ℕ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ v : Homogenization.H10Function (Metric.ball (0 : SpatialCoordinates d) ((3 : ℝ) ^ j / 2)),
        aux_hcoer_gag v.toFun (Metric.ball (0 : SpatialCoordinates d) ((3 : ℝ) ^ j / 2)) +
            ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) ((3 : ℝ) ^ j / 2), ENNReal.ofReal (v.toFun x ^ 2) ≤
          ENNReal.ofReal (Cd * (((3 : ℝ) ^ j) ^ (1 / 2 : ℝ) + ((3 : ℝ) ^ j) ^ 2) * aux_hcoer_K0 M Kr N j om) *
            ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) ((3 : ℝ) ^ j / 2),
              ENNReal.ofReal (cutoffCoefficient M H om N x *
                Homogenization.vecDot (v.grad x) (v.grad x)) := by
  have hmp := aux_prop_growth_large_root_measurePreserving_scaleShift M j
  have hE2 : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      H (aux_prop_growth_large_root_scaleShift j om) = H0 (aux_prop_growth_large_root_scaleShift j om) :=
    hmp.quasiMeasurePreserving.ae (aux_hcut_H_ae_eq M hH hH0)
  have hE3 : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      aux_hcoer_CoerK hd (cutoffPositiveCoefficient M H0 (aux_prop_growth_large_root_scaleShift j om) (N + j) 0
        one_pos) (Kr (N + j) (aux_prop_growth_large_root_scaleShift j om)) :=
    hmp.quasiMeasurePreserving.ae (hKrc (N + j))
  filter_upwards [aux_prop_growth_large_root_ae_infrared_scaleShift hH j, hE2, hE3] with om h1 h2 h3
  intro v
  set om' := aux_prop_growth_large_root_scaleShift j om with hom'
  have hc := aux_prop_growth_large_root_shiftConst_pos M Rm j N om
  have hcb : ∀ᵐ x ∂(volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      aux_prop_growth_large_root_shiftConst M j N om *
          ((cutoffPositiveCoefficient M H0 om' (N + j) 0 one_pos).val : SpatialCoordinates d → ℝ) x ≤
        cutoffCoefficient M H om N (0 + ((3 : ℝ) ^ j) • x) := by
    filter_upwards [aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae M H0 om' (N + j) 0 one_pos]
      with x hx
    rw [hx, zero_add, aux_prop_growth_large_root_cutoffCoefficient_scaleShift M H om j N h1
      (aux_prop_growth_large_root_ahom_pos_of M Rm _) x, ← aux_hcoer_cutoffCoefficient_congr M h2]
  have hmain := htr 0 ((3 : ℝ) ^ j) (by positivity) (cutoffCoefficient M H om N)
    (cutoffCoefficient_continuous M H om N) (cutoffCoefficient_pos M H om N)
    (cutoffPositiveCoefficient M H0 om' (N + j) 0 one_pos) (aux_prop_growth_large_root_shiftConst M j N om)
    (Kr (N + j) om') hc (hKr0 _ _) hcb h3 v
  refine hmain.trans (le_of_eq ?_)
  congr 2
  unfold aux_hcoer_K0
  rw [← hom']
  ring

/-- Moment of the zoom-out constant. -/
lemma aux_hcoer_K0_moment (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (Kr : ℕ → BilateralField d → ℝ) (hKrm : ∀ n, Measurable (Kr n)) (hKr0 : ∀ n om, 0 ≤ Kr n om)
    (N j : ℕ) (hj : 1 ≤ j) (p : ℝ) (hp : 1 ≤ p) (Cb2 : ℝ)
    (hKb : ∀ n, ∫⁻ om, ENNReal.ofReal (Kr n om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb2) :
    ∫⁻ om, ENNReal.ofReal (aux_hcoer_K0 M Kr N j om ^ p) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (2 * Real.exp ((2 * p) ^ 2 * M.delta ^ 2 / 4 +
          (2 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ j) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal Cb2 ^ (1 / 2 : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hmp := aux_prop_growth_large_root_measurePreserving_scaleShift M j
  have hsc := (aux_hcut_measurable_shiftConst M j N).inv
  have h1 := aux_hcut_cs_ofReal (chaosSampleLaw M).toMeasure
    (fun om => (aux_prop_growth_large_root_shiftConst M j N om)⁻¹)
    (fun om => Kr (N + j) (aux_prop_growth_large_root_scaleShift j om)) hsc
    ((hKrm _).comp hmp.measurable)
    (fun om => inv_nonneg.2 (aux_prop_growth_large_root_shiftConst_pos M Rm j N om).le)
    (fun om => hKr0 _ _) p hp0
  unfold aux_hcoer_K0
  refine h1.trans ?_
  gcongr
  · have hS : Measurable (aux_prop_growth_large_root_shiftEnv M j (d := d)) := by
      unfold aux_prop_growth_large_root_shiftEnv
      exact (measurable_const.add (aux_prop_growth_large_root_measurable_irAnchor j).abs).exp
    refine le_trans (lintegral_mono fun om => ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (inv_nonneg.2 (aux_prop_growth_large_root_shiftConst_pos M Rm j N om).le)
        (aux_prop_growth_large_root_shiftConst_inv_le M Rm j N (by omega) om) (by positivity))) ?_
    exact aux_hcut_shiftEnv_lintegral M j (2 * p) (by linarith)
  · rw [hmp.lintegral_comp (f := fun om => ENNReal.ofReal (Kr (N + j) om ^ (2 * p)))
      (ENNReal.measurable_ofReal.comp ((hKrm _).pow_const _))]
    exact hKb _

end Laws

end Paper
end
end

-- ===== module HCoer.Generic =====
section
/-!
# hCoer: small generic lemmas
-/

open Filter MeasureTheory Topology Metric
open scoped ENNReal NNReal
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- (G1) Power-mean: `(Σ z)^q ≤ #S^(q-1) Σ z^q` for `z ≥ 0`, `q ≥ 1`.
Route: `Real.rpow_arith_mean_le_arith_mean_rpow` with weights `1/#S`; empty `S` trivial. -/
lemma aux_hcoer_rpow_sum_le {ι : Type*} (S : Finset ι) (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) {q : ℝ}
    (hq : 1 ≤ q) : (∑ i ∈ S, z i) ^ q ≤ (S.card : ℝ) ^ (q - 1) * ∑ i ∈ S, z i ^ q := by
  exact Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S hq (fun i _ => hz i)



/-- (G2) Minkowski for three nonnegative terms, in the `∫⁻ ofReal(·^q)` form.
Route: `lintegral_ofReal_rpow_eq`-style identity `∫⁻ ofReal (f^q) = eLpNorm f q ^ q` for `f ≥ 0`,
`eLpNorm_add_le` twice, `eLpNorm_const`/`eLpNorm_const_smul_le`, probability measure. -/
lemma aux_hcoer_lintegral_three {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) {q : ℝ} (hq : 1 ≤ q) (CX CY : ℝ)
    (hCX : 0 ≤ CX) (hCY : 0 ≤ CY)
    (hXq : ∫⁻ ω, ENNReal.ofReal (X ω ^ q) ∂μ ≤ ENNReal.ofReal CX)
    (hYq : ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ ≤ ENNReal.ofReal CY) :
    ∫⁻ ω, ENNReal.ofReal ((a + b * X ω + c * Y ω) ^ q) ∂μ ≤
      ENNReal.ofReal ((a + b * CX ^ (1 / q) + c * CY ^ (1 / q)) ^ q) := by
    have hq_nonneg : 0 ≤ q := by linarith
    have hqne : q ≠ 0 := by linarith
    have hqinv : (0:ℝ) ≤ 1 / q := by rw [one_div]; exact inv_nonneg.mpr hq_nonneg
    set p : ℝ≥0∞ := ENNReal.ofReal q with hp_def
    have hp_toReal : p.toReal = q := by rw [hp_def]; exact ENNReal.toReal_ofReal hq_nonneg
    have hp_ne_zero : p ≠ 0 := by rw [hp_def]; exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    have hp_ne_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
    have hp1 : 1 ≤ p := by
      rw [hp_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
    have hμ_univ : μ Set.univ = 1 := IsProbabilityMeasure.measure_univ
    have hμ_ne_zero : μ ≠ 0 := by
      intro h; rw [h] at hμ_univ; simp at hμ_univ
    have hF_nonneg : ∀ ω : Ω, 0 ≤ a + b * X ω + c * Y ω := by
      intro ω
      have h1 : 0 ≤ b * X ω := mul_nonneg hb (hX0 ω)
      have h2 : 0 ≤ c * Y ω := mul_nonneg hc (hY0 ω)
      linarith
    have hm1 : AEStronglyMeasurable (fun _ : Ω => a) μ := measurable_const.aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun ω : Ω => b * X ω) μ := (measurable_const.mul hX).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (fun ω : Ω => c * Y ω) μ := (measurable_const.mul hY).aestronglyMeasurable
    have hm12 : AEStronglyMeasurable (fun ω : Ω => a + b * X ω) μ :=
      (measurable_const.add (measurable_const.mul hX)).aestronglyMeasurable
    have e1 : eLpNorm (fun _ : Ω => a) p μ = ENNReal.ofReal a := by
      rw [eLpNorm_const a hp_ne_zero hμ_ne_zero, hμ_univ, Real.enorm_eq_ofReal ha]
      simp
    have e2 : eLpNorm (fun ω : Ω => b * X ω) p μ ≤ ENNReal.ofReal b * eLpNorm X p μ := by
      have h := eLpNorm_const_smul_le (c := b) (f := X) (p := p) (μ := μ)
      rw [Real.enorm_eq_ofReal hb] at h
      exact h
    have e3 : eLpNorm (fun ω : Ω => c * Y ω) p μ ≤ ENNReal.ofReal c * eLpNorm Y p μ := by
      have h := eLpNorm_const_smul_le (c := c) (f := Y) (p := p) (μ := μ)
      rw [Real.enorm_eq_ofReal hc] at h
      exact h
    have eX : eLpNorm X p μ ≤ ENNReal.ofReal (CX ^ (1/q)) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top, hp_toReal]
      have hI : ∫⁻ ω, ‖X ω‖ₑ ^ q ∂μ = ∫⁻ ω, ENNReal.ofReal (X ω ^ q) ∂μ := by
        apply lintegral_congr; intro ω
        rw [Real.enorm_eq_ofReal (hX0 ω), ENNReal.ofReal_rpow_of_nonneg (hX0 ω) hq_nonneg]
      rw [hI]
      calc (∫⁻ ω, ENNReal.ofReal (X ω ^ q) ∂μ) ^ (1/q)
          ≤ (ENNReal.ofReal CX) ^ (1/q) := ENNReal.rpow_le_rpow hXq hqinv
        _ = ENNReal.ofReal (CX ^ (1/q)) := by rw [ENNReal.ofReal_rpow_of_nonneg hCX hqinv]
    have eY : eLpNorm Y p μ ≤ ENNReal.ofReal (CY ^ (1/q)) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top, hp_toReal]
      have hI : ∫⁻ ω, ‖Y ω‖ₑ ^ q ∂μ = ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ := by
        apply lintegral_congr; intro ω
        rw [Real.enorm_eq_ofReal (hY0 ω), ENNReal.ofReal_rpow_of_nonneg (hY0 ω) hq_nonneg]
      rw [hI]
      calc (∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ) ^ (1/q)
          ≤ (ENNReal.ofReal CY) ^ (1/q) := ENNReal.rpow_le_rpow hYq hqinv
        _ = ENNReal.ofReal (CY ^ (1/q)) := by rw [ENNReal.ofReal_rpow_of_nonneg hCY hqinv]
    have hb1 : 0 ≤ b * CX ^ (1/q) := mul_nonneg hb (Real.rpow_nonneg hCX _)
    have hc1 : 0 ≤ c * CY ^ (1/q) := mul_nonneg hc (Real.rpow_nonneg hCY _)
    have hbd : eLpNorm (fun ω : Ω => a + b * X ω + c * Y ω) p μ
        ≤ ENNReal.ofReal (a + b * CX ^ (1/q) + c * CY ^ (1/q)) := by
      have hF : eLpNorm (fun ω : Ω => a + b * X ω + c * Y ω) p μ
          ≤ eLpNorm (fun _ : Ω => a) p μ + eLpNorm (fun ω : Ω => b * X ω) p μ
            + eLpNorm (fun ω : Ω => c * Y ω) p μ := by
        calc eLpNorm (fun ω : Ω => a + b * X ω + c * Y ω) p μ
            ≤ eLpNorm (fun ω : Ω => a + b * X ω) p μ + eLpNorm (fun ω : Ω => c * Y ω) p μ :=
              eLpNorm_add_le hm12 hm3 hp1
          _ ≤ (eLpNorm (fun _ : Ω => a) p μ + eLpNorm (fun ω : Ω => b * X ω) p μ)
                + eLpNorm (fun ω : Ω => c * Y ω) p μ :=
              add_le_add (eLpNorm_add_le hm1 hm2 hp1) le_rfl
      rw [e1] at hF
      refine le_trans hF ?_
      have hsum : ENNReal.ofReal a + eLpNorm (fun ω : Ω => b * X ω) p μ
            + eLpNorm (fun ω : Ω => c * Y ω) p μ
          ≤ ENNReal.ofReal a + ENNReal.ofReal b * ENNReal.ofReal (CX ^ (1/q))
            + ENNReal.ofReal c * ENNReal.ofReal (CY ^ (1/q)) := by
        apply add_le_add
        · apply add_le_add
          · exact le_rfl
          · calc eLpNorm (fun ω : Ω => b * X ω) p μ ≤ ENNReal.ofReal b * eLpNorm X p μ := e2
              _ ≤ ENNReal.ofReal b * ENNReal.ofReal (CX ^ (1/q)) :=
                  mul_le_mul_of_nonneg_left eX (zero_le _)
        · calc eLpNorm (fun ω : Ω => c * Y ω) p μ ≤ ENNReal.ofReal c * eLpNorm Y p μ := e3
            _ ≤ ENNReal.ofReal c * ENNReal.ofReal (CY ^ (1/q)) :=
                mul_le_mul_of_nonneg_left eY (zero_le _)
      refine le_trans hsum ?_
      have heq : ENNReal.ofReal a + ENNReal.ofReal b * ENNReal.ofReal (CX ^ (1/q))
            + ENNReal.ofReal c * ENNReal.ofReal (CY ^ (1/q))
          = ENNReal.ofReal (a + b * CX ^ (1/q) + c * CY ^ (1/q)) := by
        rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul hc]
        rw [← ENNReal.ofReal_add ha hb1]
        rw [← ENNReal.ofReal_add (add_nonneg ha hb1) hc1]
      exact le_of_eq heq
    have hpow : eLpNorm (fun ω : Ω => a + b * X ω + c * Y ω) p μ ^ q
        = ∫⁻ ω, ENNReal.ofReal ((a + b * X ω + c * Y ω) ^ q) ∂μ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
      have hJ : ∫⁻ ω, ‖(fun ω : Ω => a + b * X ω + c * Y ω) ω‖ₑ ^ p.toReal ∂μ
          = ∫⁻ ω, ENNReal.ofReal ((a + b * X ω + c * Y ω) ^ q) ∂μ := by
        rw [hp_toReal]
        apply lintegral_congr; intro ω
        rw [Real.enorm_eq_ofReal (hF_nonneg ω), ENNReal.ofReal_rpow_of_nonneg (hF_nonneg ω) hq_nonneg]
      rw [hJ]
      rw [one_div, hp_toReal]
      exact ENNReal.rpow_inv_rpow hqne _
    have hR_nonneg : 0 ≤ a + b * CX ^ (1/q) + c * CY ^ (1/q) := by linarith [hb1, hc1, ha]
    have hfin := ENNReal.rpow_le_rpow hbd hq_nonneg
    rw [hpow, ENNReal.ofReal_rpow_of_nonneg hR_nonneg hq_nonneg] at hfin
    exact hfin



/-- (G3) `Σ_{n ≥ 1} n^{3 - 5q} ≤ 2` for `q ≥ 1` (compare with `Σ 1/n²`).
Route: termwise `n^(3-5q) ≤ n^(-2)` (`Real.rpow_le_rpow_of_exponent_le`, `n ≥ 1`), then
`hasSum_zeta_two`/`Real.tsum_one_div_nat_add_one_pow_two`-type bound `≤ π²/6 ≤ 2`, or telescoping
`1/n² ≤ 1/(n-1) - 1/n`. -/
lemma aux_hcoer_tsum_le {q : ℝ} (hq : 1 ≤ q) :
    ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) ^ (3 - 5 * q)) ≤ 2 := by
    have hrpow : ∀ n : ℕ, ((n:ℝ)+1)^(-2:ℝ) = 1/((n:ℝ)+1)^2 := by
      intro n
      have h2 : (-2:ℝ) = -(((2:ℕ):ℝ)) := by norm_num
      rw [h2, Real.rpow_neg (by positivity : (0:ℝ) ≤ (n:ℝ)+1) (((2:ℕ):ℝ)), Real.rpow_natCast]
      rw [one_div]
    have hbound : ∀ n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) ^ (3 - 5 * q)) ≤
        ENNReal.ofReal (((n : ℝ) + 1) ^ (-2 : ℝ)) := by
      intro n
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow_of_exponent_le
      · have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      · linarith
    have hsumm : Summable (fun n : ℕ => ((n:ℝ)+1)^(-2:ℝ)) := by
      have h0 : Summable (fun n : ℕ => ((n:ℝ))^(-2:ℝ)) :=
        Real.summable_nat_rpow.mpr (by norm_num : (-2:ℝ) < -1)
      have h1 := (summable_nat_add_iff (f := fun n : ℕ => ((n:ℝ))^(-2:ℝ)) 1).mpr h0
      simpa only [Nat.cast_add, Nat.cast_one] using h1
    have htsum : ∑' n : ℕ, ((n:ℝ)+1)^(-2:ℝ) = Real.pi^2/6 := by
      have hg : Summable (fun n : ℕ => 1/((n:ℝ))^2) := hasSum_zeta_two.summable
      have hshift := hg.tsum_eq_zero_add
      have hz : ∑' b : ℕ, 1/((b:ℝ))^2 = Real.pi^2/6 := hasSum_zeta_two.tsum_eq
      have e1 : ∑' b : ℕ, (1/((b:ℝ)+1)^2) = Real.pi^2/6 := by
        rw [hz] at hshift
        rw [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), div_zero, zero_add] at hshift
        rw [hshift]
        apply tsum_congr
        intro b
        push_cast
        ring
      rw [show (∑' n:ℕ, ((n:ℝ)+1)^(-2:ℝ)) = ∑' n:ℕ, 1/((n:ℝ)+1)^2 from
            tsum_congr (fun n => hrpow n)]
      exact e1
    calc
      ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) ^ (3 - 5 * q))
          ≤ ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) ^ (-2 : ℝ)) :=
            ENNReal.tsum_le_tsum hbound
      _ = ENNReal.ofReal (∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 : ℝ)) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun n => Real.rpow_nonneg (by positivity) _) hsumm).symm
      _ = ENNReal.ofReal (Real.pi^2/6) := by rw [htsum]
      _ ≤ 2 := by
            have h2 : Real.pi^2/6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
            calc ENNReal.ofReal (Real.pi^2/6) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal h2
              _ = 2 := by norm_num



/-- (G4) Existence of the level. -/
lemma aux_hcoer_exists_k {s : ℝ} (hs : 0 < s) : ∃ k : ℕ, 1 ≤ k ∧ 2 ≤ (3 : ℝ) ^ k * s := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / s) (by norm_num : (1 : ℝ) < 3)
  have hn' : (2 : ℝ) < 3 ^ n * s := (div_lt_iff₀ hs).mp hn
  refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
  have hpow : (3 : ℝ) ^ (n + 1) * s = (3 ^ n * s) * 3 := by rw [pow_succ]; ring
  rw [hpow]
  nlinarith



/-- (G5) Gagliardo congruence under a.e. equality on the domain. -/
lemma aux_hcoer_gag_congr_ae {d : ℕ} {f₁ f₂ : SpatialCoordinates d → ℝ} {U : Set (SpatialCoordinates d)}
    (h : f₁ =ᵐ[volume.restrict U] f₂) : aux_hcoer_gag f₁ U = aux_hcoer_gag f₂ U := by
  unfold aux_hcoer_gag
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  apply lintegral_congr_ae
  filter_upwards [h] with z hz
  rw [hx, hz]



/-- (G6) Gagliardo monotonicity in the domain. -/
lemma aux_hcoer_gag_mono {d : ℕ} (f : SpatialCoordinates d → ℝ) {U V : Set (SpatialCoordinates d)}
    (h : U ⊆ V) : aux_hcoer_gag f U ≤ aux_hcoer_gag f V := by
  unfold aux_hcoer_gag
  calc
    ∫⁻ x in U, ∫⁻ z in U, ENNReal.ofReal ((f x - f z) ^ 2) /
        ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))
        ≤ ∫⁻ x in U, ∫⁻ z in V, ENNReal.ofReal ((f x - f z) ^ 2) /
            ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2)) := by
          apply lintegral_mono
          intro x
          exact lintegral_mono_set h
    _ ≤ ∫⁻ x in V, ∫⁻ z in V, ENNReal.ofReal ((f x - f z) ^ 2) /
            ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2)) := by
          apply lintegral_mono_set h



end Paper
end
end

-- ===== module HCoer.Level =====
section
/-!
# hCoer: level choice, cover choice, and the deterministic per-`ω` clauses
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The subcube level of a ball of radius `s/2`: the least `k ≥ 1` with `3^{-k} ≤ s/2`. -/
def aux_hcoer_kOf (s : ℝ) : ℕ := by
  classical
  exact if hs : 0 < s then Nat.find (aux_hcoer_exists_k hs) else 1

lemma aux_hcoer_kOf_spec {s : ℝ} (hs : 0 < s) :
    1 ≤ aux_hcoer_kOf s ∧ 2 ≤ (3 : ℝ) ^ aux_hcoer_kOf s * s ∧
      (3 : ℝ) ^ aux_hcoer_kOf s * s ≤ max (3 * s) 6 := by
  classical
  unfold aux_hcoer_kOf
  simp only [dif_pos hs]
  have hspec := Nat.find_spec (aux_hcoer_exists_k hs)
  refine ⟨hspec.1, hspec.2, ?_⟩
  set k := Nat.find (aux_hcoer_exists_k hs) with hk
  by_cases hk1 : k = 1
  · rw [hk1, pow_one]; exact le_max_left _ _
  · have hk2 : 2 ≤ k := by have := hspec.1; omega
    have hmin := Nat.find_min (aux_hcoer_exists_k hs) (m := k - 1) (by omega)
    have hlt : (3 : ℝ) ^ (k - 1) * s < 2 := by
      by_contra hcon
      exact hmin ⟨by omega, not_lt.1 hcon⟩
    have e : (3 : ℝ) ^ k = 3 * 3 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]
    refine le_trans ?_ (le_max_right _ _)
    nlinarith

/-- The subcube side. -/
def aux_hcoer_tOf (s : ℝ) : ℝ := ((3 : ℝ) ^ aux_hcoer_kOf s)⁻¹

lemma aux_hcoer_tOf_pos (s : ℝ) : 0 < aux_hcoer_tOf s := by
  unfold aux_hcoer_tOf; positivity

lemma aux_hcoer_tOf_le {s : ℝ} (hs : 0 < s) : aux_hcoer_tOf s ≤ s / 2 := by
  obtain ⟨-, h2, -⟩ := aux_hcoer_kOf_spec hs
  unfold aux_hcoer_tOf
  have h3 : (0 : ℝ) < (3 : ℝ) ^ aux_hcoer_kOf s := by positivity
  rw [inv_le_iff_one_le_mul₀ h3]
  linarith

lemma aux_hcoer_tOf_lt {s : ℝ} (hs : 0 < s) : aux_hcoer_tOf s < s :=
  lt_of_le_of_lt (aux_hcoer_tOf_le hs) (by linarith)

/-- The chosen cover. -/
def aux_hcoer_Y (d : ℕ) (s : ℝ) : Finset (SpatialCoordinates d) := by
  classical
  exact if hs : 0 < s then
    Classical.choose (aux_hcoer_cover (d := d) s (aux_hcoer_tOf s) (aux_hcoer_tOf_pos s) (aux_hcoer_tOf_lt hs))
  else ∅

lemma aux_hcoer_Y_spec {s : ℝ} (hs : 0 < s) :
    ((aux_hcoer_Y d s).card : ℝ) ≤ (2 * s / aux_hcoer_tOf s + 2) ^ d ∧
      (∀ y ∈ aux_hcoer_Y d s, Metric.ball y (aux_hcoer_tOf s / 2) ⊆
        Metric.ball (0 : SpatialCoordinates d) (s / 2)) ∧
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2),
        ∀ z ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2), ‖x - z‖ < aux_hcoer_tOf s / 4 →
          ∃ y ∈ aux_hcoer_Y d s, x ∈ Metric.ball y (aux_hcoer_tOf s / 2) ∧
            z ∈ Metric.ball y (aux_hcoer_tOf s / 2) := by
  classical
  unfold aux_hcoer_Y
  simp only [dif_pos hs]
  exact Classical.choose_spec
    (aux_hcoer_cover (d := d) s (aux_hcoer_tOf s) (aux_hcoer_tOf_pos s) (aux_hcoer_tOf_lt hs))

/-- Level arithmetic for `s = ρ0 m / n`: `3^k ≤ 6 n` and `s/t ≤ 3 ρ0 + 6`. -/
lemma aux_hcoer_level_bounds {rho0 : ℝ} (hrho : 1 ≤ rho0) {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    0 < rho0 * m / n ∧ rho0 * m / n ≤ rho0 ∧
      (3 : ℝ) ^ aux_hcoer_kOf (rho0 * m / n) ≤ 6 * n ∧
      (3 : ℝ) ^ aux_hcoer_kOf (rho0 * m / n) * (rho0 * m / n) ≤ 3 * rho0 + 6 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hm1 hmn
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hn0 : (0 : ℝ) < n := by linarith
  set s := rho0 * m / n with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hsle : s ≤ rho0 := by
    rw [hsdef, div_le_iff₀ hn0]; nlinarith
  have hsge : 1 / (n : ℝ) ≤ s := by
    rw [hsdef]; apply div_le_div_of_nonneg_right _ hn0.le; nlinarith
  obtain ⟨-, -, h3⟩ := aux_hcoer_kOf_spec hs0
  refine ⟨hs0, hsle, ?_, ?_⟩
  · have h3pos : (0 : ℝ) < (3 : ℝ) ^ aux_hcoer_kOf s := by positivity
    rcases le_total (3 * s) 6 with h | h
    · rw [max_eq_right h] at h3
      have : (3 : ℝ) ^ aux_hcoer_kOf s ≤ 6 / s := by rw [le_div_iff₀ hs0]; exact h3
      refine this.trans ?_
      rw [div_le_iff₀ hs0]
      have : 1 ≤ (n : ℝ) * s := by rw [div_le_iff₀ hn0] at hsge; linarith
      nlinarith
    · rw [max_eq_left h] at h3
      have : (3 : ℝ) ^ aux_hcoer_kOf s ≤ 3 := by nlinarith
      linarith
  · refine h3.trans ?_
    rcases le_total (3 * s) 6 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith

end Paper
end
end

-- ===== module HCoer.Omega =====
section
/-!
# hCoer: the deterministic per-`ω` clauses
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The far-pair constant. -/
def aux_hcoer_C2 (d : ℕ) (rho0 : ℝ) : ℝ := 144 * 4 ^ (d + 2) * (3 * rho0 + 6) ^ d

lemma aux_hcoer_C2_nonneg (d : ℕ) {rho0 : ℝ} (hrho : 1 ≤ rho0) : 0 ≤ aux_hcoer_C2 d rho0 := by
  unfold aux_hcoer_C2; have : (0 : ℝ) ≤ 3 * rho0 + 6 := by linarith
  positivity

/-- The far-pair coefficient is at most `C2 n^5`. -/
lemma aux_hcoer_far_le {rho0 : ℝ} (hrho : 1 ≤ rho0) {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    4 * (4 / aux_hcoer_tOf (rho0 * m / n)) ^ ((d : ℝ) + 3 / 2) * (rho0 * m / n) ^ d ≤
      aux_hcoer_C2 d rho0 * (n : ℝ) ^ 5 := by
  obtain ⟨hs0, -, hT6, hTs⟩ := aux_hcoer_level_bounds hrho hm1 hmn
  set s := rho0 * m / n with hsdef
  set T : ℝ := (3 : ℝ) ^ aux_hcoer_kOf s with hTdef
  have hT1 : 1 ≤ T := one_le_pow₀ (by norm_num)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hm1 hmn
  have ht : 4 / aux_hcoer_tOf s = 4 * T := by
    unfold aux_hcoer_tOf; rw [← hTdef, div_inv_eq_mul]
  rw [ht]
  have h4T : 1 ≤ 4 * T := by linarith
  have hpow : (4 * T) ^ ((d : ℝ) + 3 / 2) ≤ (4 * T) ^ (d + 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h4T (by push_cast; linarith)
  have hsd : 0 ≤ s ^ d := pow_nonneg hs0.le d
  calc 4 * (4 * T) ^ ((d : ℝ) + 3 / 2) * s ^ d ≤ 4 * (4 * T) ^ (d + 2) * s ^ d := by gcongr
    _ = 4 * 4 ^ (d + 2) * ((T * s) ^ d * T ^ 2) := by rw [mul_pow, mul_pow, pow_add]; ring
    _ ≤ 4 * 4 ^ (d + 2) * ((3 * rho0 + 6) ^ d * (6 * n) ^ 2) := by
        gcongr
    _ = aux_hcoer_C2 d rho0 * (n : ℝ) ^ 2 := by unfold aux_hcoer_C2; ring
    _ ≤ aux_hcoer_C2 d rho0 * (n : ℝ) ^ 5 := by
        gcongr
        · exact aux_hcoer_C2_nonneg d hrho
        · exact hn1
        · norm_num

/-- ENNReal bookkeeping for the final combination. -/
lemma aux_hcoer_combine (a b X : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ X) (hb1 : b + 1 ≤ X)
    (E L : ℝ≥0∞) :
    ENNReal.ofReal a * E + (ENNReal.ofReal b * L + L) ≤ ENNReal.ofReal X * (E + L) := by
  have h1 : ENNReal.ofReal b * L + L = ENNReal.ofReal (b + 1) * L := by
    rw [ENNReal.ofReal_add hb zero_le_one, ENNReal.ofReal_one, add_mul, one_mul]
  rw [h1, mul_add]
  exact add_le_add (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hab) E)
    (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hb1) L)

/-- **(H¹ clause at one `ω`.)** -/
lemma aux_hcoer_H1_omega (Cd : ℝ) (hCd : 0 < Cd) {rho0 : ℝ} (hrho : 1 ≤ rho0)
    (A : SpatialCoordinates d → ℝ) (Kfun : SpatialCoordinates d → ℕ → ℝ) (hK0 : ∀ y k, 0 ≤ Kfun y k)
    {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (s : ℝ) (hs : s = rho0 * m / n)
    (hsub : ∀ y ∈ aux_hcoer_Y d s, ∀ v : Homogenization.H1Function (Metric.ball y (aux_hcoer_tOf s / 2)),
      aux_hcoer_gag v.toFun (Metric.ball y (aux_hcoer_tOf s / 2)) ≤
        ENNReal.ofReal (Cd * Kfun y (aux_hcoer_kOf s)) *
          ∫⁻ x in Metric.ball y (aux_hcoer_tOf s / 2),
            ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)))
    (K1 : ℝ) (hK1 : ((n : ℝ) ^ 5)⁻¹ * ∑ y ∈ aux_hcoer_Y d s, Kfun y (aux_hcoer_kOf s) ≤ K1)
    (v : Homogenization.H1Function (Metric.ball (0 : SpatialCoordinates d) (s / 2))) :
    aux_hcoer_gag v.toFun (Metric.ball (0 : SpatialCoordinates d) (s / 2)) +
        ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2), ENNReal.ofReal (v.toFun x ^ 2) ≤
      ENNReal.ofReal ((1 + aux_hcoer_C2 d rho0 + Cd * K1) * (n : ℝ) ^ (5 : ℝ)) *
        ((∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2),
            ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x))) +
          ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2), ENNReal.ofReal (v.toFun x ^ 2)) := by
  obtain ⟨hs0, -, -, -⟩ := aux_hcoer_level_bounds hrho hm1 hmn
  rw [← hs] at hs0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hm1 hmn
  have hn5 : (n : ℝ) ^ (5 : ℝ) = (n : ℝ) ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hn5]
  have hn5pos : 0 < (n : ℝ) ^ 5 := by positivity
  have hn5ge : 1 ≤ (n : ℝ) ^ 5 := one_le_pow₀ hn1
  obtain ⟨-, hYsub, hcov⟩ := aux_hcoer_Y_spec (d := d) hs0
  set t := aux_hcoer_tOf s with htdef
  set k := aux_hcoer_kOf s with hkdef
  set Y := aux_hcoer_Y d s with hYdef
  -- measurable modification
  have hae := v.memL2.1
  set f := hae.mk v.toFun with hfdef
  have hfm : Measurable f := hae.stronglyMeasurable_mk.measurable
  have hfe : v.toFun =ᵐ[volume.restrict (Metric.ball (0 : SpatialCoordinates d) (s / 2))] f := hae.ae_eq_mk
  have hgag : aux_hcoer_gag v.toFun (Metric.ball (0 : SpatialCoordinates d) (s / 2)) =
      aux_hcoer_gag f (Metric.ball (0 : SpatialCoordinates d) (s / 2)) := aux_hcoer_gag_congr_ae hfe
  have hL : ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2), ENNReal.ofReal (f x ^ 2) =
      ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2), ENNReal.ofReal (v.toFun x ^ 2) :=
    lintegral_congr_ae (hfe.mono fun x hx => by simp only [hx])
  have hsplit := aux_hcoer_gag_split f hfm s t hs0 (aux_hcoer_tOf_pos s) Y hcov
  rw [hL] at hsplit
  -- near part
  have hnear : ∀ y ∈ Y, aux_hcoer_gag f (Metric.ball y (t / 2)) ≤
      ENNReal.ofReal (Cd * Kfun y k) * ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2),
        ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)) := by
    intro y hy
    have hQ := hYsub y hy
    have hfeQ : v.toFun =ᵐ[volume.restrict (Metric.ball y (t / 2))] f :=
      ae_restrict_of_ae_restrict_of_subset hQ hfe
    rw [← aux_hcoer_gag_congr_ae hfeQ]
    have h := hsub y hy (v.restrict Metric.isOpen_ball hQ)
    refine h.trans (mul_le_mul_left' (lintegral_mono_set hQ) _)
  have hsum : (∑ y ∈ Y, aux_hcoer_gag f (Metric.ball y (t / 2))) ≤
      ENNReal.ofReal (Cd * ((n : ℝ) ^ 5 * K1)) * ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2),
        ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)) := by
    refine (Finset.sum_le_sum hnear).trans ?_
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun y _ => mul_nonneg hCd.le (hK0 _ _))]
    refine mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hCd.le
    have := mul_le_mul_of_nonneg_left hK1 hn5pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hn5pos.ne', one_mul] at this
  -- far part
  have hfar := aux_hcoer_far_le (d := d) hrho hm1 hmn
  rw [← hs] at hfar
  have hK1nn : 0 ≤ K1 := by
    refine le_trans ?_ hK1
    exact mul_nonneg (inv_nonneg.2 hn5pos.le) (Finset.sum_nonneg fun y _ => hK0 _ _)
  have hC2 := aux_hcoer_C2_nonneg d hrho
  rw [hgag]
  refine le_trans (add_le_add (hsplit.trans (add_le_add hsum
    (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hfar) _))) le_rfl) ?_
  rw [add_assoc]
  apply aux_hcoer_combine _ _ _ (by positivity) (by positivity)
  · nlinarith [mul_nonneg hC2 hn5pos.le]
  · nlinarith [mul_nonneg (mul_nonneg hCd.le hK1nn) hn5pos.le, hn5ge]

/-- **(H¹₀ clause at one `ω`.)**  From the killed estimate on a larger ball `W ⊇ V`, via zero extension. -/
lemma aux_hcoer_H10_omega (A : SpatialCoordinates d → ℝ) {s R : ℝ} (hsR : s ≤ R) (c : ℝ≥0∞)
    (hW : ∀ w : Homogenization.H10Function (Metric.ball (0 : SpatialCoordinates d) (R / 2)),
      aux_hcoer_gag w.toFun (Metric.ball (0 : SpatialCoordinates d) (R / 2)) +
          ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (R / 2), ENNReal.ofReal (w.toFun x ^ 2) ≤
        c * ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (R / 2),
          ENNReal.ofReal (A x * Homogenization.vecDot (w.grad x) (w.grad x)))
    (v : Homogenization.H10Function (Metric.ball (0 : SpatialCoordinates d) (s / 2))) :
    aux_hcoer_gag v.toFun (Metric.ball (0 : SpatialCoordinates d) (s / 2)) +
        ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2), ENNReal.ofReal (v.toFun x ^ 2) ≤
      c * ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2),
        ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)) := by
  classical
  have hVW : Metric.ball (0 : SpatialCoordinates d) (s / 2) ⊆ Metric.ball (0 : SpatialCoordinates d) (R / 2) :=
    Metric.ball_subset_ball (by linarith)
  let w := v.extendByZeroToOpenSuperset Metric.isOpen_ball.measurableSet Metric.isOpen_ball hVW
  have hwf : ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2), w.toFun x = v.toFun x := by
    intro x hx
    change (v.extendByZeroToOpenSuperset _ _ hVW).toH1Function.toFun x = _
    rw [Homogenization.H10Function.extendByZeroToOpenSuperset_toFun,
      Homogenization.H10Function.zeroExtension_apply_of_mem v hx]
  have hwg : ∀ x, w.grad x =
      if x ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2) then v.grad x else 0 := by
    intro x
    change (v.extendByZeroToOpenSuperset _ _ hVW).toH1Function.grad x = _
    rw [Homogenization.H10Function.extendByZeroToOpenSuperset_grad]
    split_ifs with hx
    · exact Homogenization.H10Function.zeroExtensionGrad_apply_of_mem v hx
    · exact Homogenization.H10Function.zeroExtensionGrad_apply_of_not_mem v hx
  have hgagVW : aux_hcoer_gag v.toFun (Metric.ball (0 : SpatialCoordinates d) (s / 2)) ≤
      aux_hcoer_gag w.toFun (Metric.ball (0 : SpatialCoordinates d) (R / 2)) := by
    have heq : aux_hcoer_gag v.toFun (Metric.ball (0 : SpatialCoordinates d) (s / 2)) =
        aux_hcoer_gag w.toFun (Metric.ball (0 : SpatialCoordinates d) (s / 2)) := by
      apply aux_hcoer_gag_congr_ae
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      exact (hwf x hx).symm
    rw [heq]; exact aux_hcoer_gag_mono _ hVW
  have hL : ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2), ENNReal.ofReal (v.toFun x ^ 2) ≤
      ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (R / 2), ENNReal.ofReal (w.toFun x ^ 2) := by
    refine le_trans (le_of_eq ?_) (lintegral_mono_set hVW)
    refine setLIntegral_congr_fun Metric.isOpen_ball.measurableSet ?_
    intro x hx
    simp only [hwf x hx]
  have hE : ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (R / 2),
        ENNReal.ofReal (A x * Homogenization.vecDot (w.grad x) (w.grad x)) =
      ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (s / 2),
        ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)) := by
    have hF : ∀ x, ENNReal.ofReal (A x * Homogenization.vecDot (w.grad x) (w.grad x)) =
        (Metric.ball (0 : SpatialCoordinates d) (s / 2)).indicator
          (fun x => ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x))) x := by
      intro x
      by_cases hx : x ∈ Metric.ball (0 : SpatialCoordinates d) (s / 2)
      · rw [Set.indicator_of_mem hx, hwg x, if_pos hx]
      · rw [Set.indicator_of_notMem hx, hwg x, if_neg hx]
        simp [Homogenization.vecDot]
    simp_rw [hF]
    rw [setLIntegral_indicator Metric.isOpen_ball.measurableSet, Set.inter_eq_left.2 hVW]
  calc _ ≤ aux_hcoer_gag w.toFun (Metric.ball (0 : SpatialCoordinates d) (R / 2)) +
          ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (R / 2), ENNReal.ofReal (w.toFun x ^ 2) :=
        add_le_add hgagVW hL
    _ ≤ c * ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (R / 2),
          ENNReal.ofReal (A x * Homogenization.vecDot (w.grad x) (w.grad x)) := hW w
    _ = _ := by rw [hE]

end Paper
end
end

-- ===== module HCoer.Sum =====
section
/-!
# hCoer: the weighted countable supremum `K1` and its moment
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The level term for `q' = m / n`. -/
def aux_hcoer_T (d : ℕ) (rho0 : ℝ) (Kfun : SpatialCoordinates d → ℕ → Ω → ℝ) (n m : ℕ) (om : Ω) : ℝ := by
  classical
  exact if 1 ≤ m ∧ m ≤ n then
    ((n : ℝ) ^ 5)⁻¹ * ∑ y ∈ aux_hcoer_Y d (rho0 * m / n), Kfun y (aux_hcoer_kOf (rho0 * m / n)) om
  else 0

/-- The weighted supremum. -/
def aux_hcoer_K1E (d : ℕ) (rho0 : ℝ) (Kfun : SpatialCoordinates d → ℕ → Ω → ℝ) (om : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ m : ℕ, ENNReal.ofReal (aux_hcoer_T d rho0 Kfun n m om)

lemma aux_hcoer_T_nonneg (rho0 : ℝ) (Kfun : SpatialCoordinates d → ℕ → Ω → ℝ)
    (hK0 : ∀ y k om, 0 ≤ Kfun y k om) (n m : ℕ) (om : Ω) : 0 ≤ aux_hcoer_T d rho0 Kfun n m om := by
  unfold aux_hcoer_T
  split_ifs
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hK0 _ _ _)
  · exact le_rfl

lemma aux_hcoer_measurable_T (rho0 : ℝ) (Kfun : SpatialCoordinates d → ℕ → Ω → ℝ)
    (hKm : ∀ y k, Measurable (Kfun y k)) (n m : ℕ) : Measurable (aux_hcoer_T d rho0 Kfun n m) := by
  unfold aux_hcoer_T
  split_ifs
  · exact measurable_const.mul (Finset.measurable_sum _ fun y _ => hKm _ _)
  · exact measurable_const

lemma aux_hcoer_measurable_K1E (rho0 : ℝ) (Kfun : SpatialCoordinates d → ℕ → Ω → ℝ)
    (hKm : ∀ y k, Measurable (Kfun y k)) : Measurable (aux_hcoer_K1E d rho0 Kfun) := by
  unfold aux_hcoer_K1E
  exact Measurable.iSup fun n => Measurable.iSup fun m =>
    ENNReal.measurable_ofReal.comp (aux_hcoer_measurable_T rho0 Kfun hKm n m)

lemma aux_hcoer_T_le_K1E (rho0 : ℝ) (Kfun : SpatialCoordinates d → ℕ → Ω → ℝ)
    (hK0 : ∀ y k om, 0 ≤ Kfun y k om) (n m : ℕ) (om : Ω) (hfin : aux_hcoer_K1E d rho0 Kfun om ≠ ⊤) :
    aux_hcoer_T d rho0 Kfun n m om ≤ (aux_hcoer_K1E d rho0 Kfun om).toReal := by
  have h : ENNReal.ofReal (aux_hcoer_T d rho0 Kfun n m om) ≤ aux_hcoer_K1E d rho0 Kfun om := by
    unfold aux_hcoer_K1E
    exact le_iSup_of_le n (le_iSup_of_le m le_rfl)
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h

/-- One level term's moment. -/
lemma aux_hcoer_T_moment (μ : Measure Ω) {rho0 : ℝ} (hrho : 1 ≤ rho0) {q : ℝ} (hq : 1 ≤ q)
    (Kfun : SpatialCoordinates d → ℕ → Ω → ℝ) (hKm : ∀ y k, Measurable (Kfun y k))
    (hK0 : ∀ y k om, 0 ≤ Kfun y k om) (Csub : ℝ) (hCsub : 0 ≤ Csub)
    (hmom : ∀ y k, ‖y‖ ≤ rho0 → 1 ≤ k →
      ∫⁻ om, ENNReal.ofReal (Kfun y k om ^ q) ∂μ ≤ ENNReal.ofReal (Csub * 9 ^ k))
    {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    ∫⁻ om, ENNReal.ofReal (aux_hcoer_T d rho0 Kfun n m om ^ q) ∂μ ≤
      ENNReal.ofReal (36 * (6 * rho0 + 14) ^ ((d : ℝ) * q) * Csub * ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ))⁻¹) := by
  classical
  have hq0 : 0 < q := by linarith
  obtain ⟨hs0, hsle, hT6, hTs⟩ := aux_hcoer_level_bounds hrho hm1 hmn
  set s := rho0 * m / n with hsdef
  set k := aux_hcoer_kOf s with hkdef
  set Y := aux_hcoer_Y d s with hYdef
  obtain ⟨hk1, -, -⟩ := aux_hcoer_kOf_spec hs0
  obtain ⟨hcard, hYsub, -⟩ := aux_hcoer_Y_spec (d := d) hs0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hm1 hmn
  have hn0 : (0 : ℝ) < n := by linarith
  have hy : ∀ y ∈ Y, ‖y‖ ≤ rho0 := by
    intro y hyY
    have h := hYsub y hyY (Metric.mem_ball_self (by have := aux_hcoer_tOf_pos s; linarith))
    rw [Metric.mem_ball, dist_zero_right] at h
    linarith
  -- the card bound
  have hcard' : (Y.card : ℝ) ≤ (6 * rho0 + 14) ^ d := by
    refine hcard.trans (pow_le_pow_left₀
      (add_nonneg (div_nonneg (by linarith) (aux_hcoer_tOf_pos s).le) (by norm_num)) ?_ d)
    have : 2 * s / aux_hcoer_tOf s = 2 * ((3 : ℝ) ^ k * s) := by
      unfold aux_hcoer_tOf; rw [← hkdef, div_inv_eq_mul]; ring
    rw [this]; linarith
  have hT : ∀ om, aux_hcoer_T d rho0 Kfun n m om = ((n : ℝ) ^ 5)⁻¹ * ∑ y ∈ Y, Kfun y k om := by
    intro om; unfold aux_hcoer_T; rw [if_pos ⟨hm1, hmn⟩]
  simp_rw [hT]
  have hS0 : ∀ om, 0 ≤ ∑ y ∈ Y, Kfun y k om := fun om => Finset.sum_nonneg fun y _ => hK0 _ _ _
  have hinv0 : 0 ≤ ((n : ℝ) ^ 5)⁻¹ := by positivity
  -- pull out the weight: ((n^5)⁻¹)^q ≤ (n^5)⁻¹
  have hw : ((n : ℝ) ^ 5)⁻¹ ^ q ≤ ((n : ℝ) ^ 5)⁻¹ := by
    refine Real.rpow_le_self_of_le_one hinv0 ?_ hq
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hn1)
  have hpt : ∀ om, ENNReal.ofReal ((((n : ℝ) ^ 5)⁻¹ * ∑ y ∈ Y, Kfun y k om) ^ q) ≤
      ENNReal.ofReal (((n : ℝ) ^ 5)⁻¹ * ((Y.card : ℝ) ^ (q - 1))) *
        ∑ y ∈ Y, ENNReal.ofReal (Kfun y k om ^ q) := by
    intro om
    rw [Real.mul_rpow hinv0 (hS0 om), ← ENNReal.ofReal_sum_of_nonneg
      (fun y _ => Real.rpow_nonneg (hK0 _ _ _) _), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := aux_hcoer_rpow_sum_le Y (fun y => Kfun y k om) (fun y => hK0 _ _ _) hq
    calc ((n : ℝ) ^ 5)⁻¹ ^ q * (∑ y ∈ Y, Kfun y k om) ^ q
        ≤ ((n : ℝ) ^ 5)⁻¹ * ((Y.card : ℝ) ^ (q - 1) * ∑ y ∈ Y, Kfun y k om ^ q) :=
          mul_le_mul hw h1 (Real.rpow_nonneg (hS0 om) _) hinv0
      _ = _ := by ring
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finset_sum' (f := fun y a => ENNReal.ofReal (Kfun y k a ^ q)) Y fun y _ =>
      (ENNReal.measurable_ofReal.comp ((hKm _ _).pow_const _)).aemeasurable]
  have hsum : ∑ y ∈ Y, ∫⁻ om, ENNReal.ofReal (Kfun y k om ^ q) ∂μ ≤
      ENNReal.ofReal ((Y.card : ℝ) * (Csub * 9 ^ k)) := by
    refine (Finset.sum_le_sum fun y hyY => hmom y k (hy y hyY) hk1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine (mul_le_mul_left' hsum _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- arithmetic: (n^5)⁻¹ · #Y^(q-1) · #Y · Csub · 9^k ≤ 36 · Cy^q · Csub · n⁻² · n⁻¹
  have h9 : (9 : ℝ) ^ k ≤ 36 * (n : ℝ) ^ 2 := by
    have : (9 : ℝ) ^ k = ((3 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    calc ((3 : ℝ) ^ k) ^ 2 ≤ (6 * n) ^ 2 := pow_le_pow_left₀ (by positivity) hT6 2
      _ = 36 * (n : ℝ) ^ 2 := by ring
  have hYq : (Y.card : ℝ) ^ (q - 1) * (Y.card : ℝ) ≤ (6 * rho0 + 14) ^ ((d : ℝ) * q) := by
    by_cases hY0 : Y.card = 0
    · rw [hY0]; simp; positivity
    · have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast Nat.pos_of_ne_zero hY0
      rw [← Real.rpow_add_one hYpos.ne', sub_add_cancel]
      calc (Y.card : ℝ) ^ q ≤ ((6 * rho0 + 14) ^ d) ^ q := Real.rpow_le_rpow hYpos.le hcard' hq0.le
        _ = (6 * rho0 + 14) ^ ((d : ℝ) * q) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hYq0 : 0 ≤ (Y.card : ℝ) ^ (q - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ((n : ℝ) ^ 5)⁻¹ * (Y.card : ℝ) ^ (q - 1) * ((Y.card : ℝ) * (Csub * 9 ^ k))
      = ((n : ℝ) ^ 5)⁻¹ * ((Y.card : ℝ) ^ (q - 1) * (Y.card : ℝ)) * Csub * 9 ^ k := by ring
    _ ≤ ((n : ℝ) ^ 5)⁻¹ * (6 * rho0 + 14) ^ ((d : ℝ) * q) * Csub * (36 * (n : ℝ) ^ 2) := by
        gcongr
    _ = 36 * (6 * rho0 + 14) ^ ((d : ℝ) * q) * Csub * ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ))⁻¹ := by
        field_simp

end Paper
end
end

-- ===== module HCoer.Sum2 =====
section
/-!
# hCoer: moment of the weighted supremum, and the unified subcube moment
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

section Generic
variable {Ω : Type*} [MeasurableSpace Ω]

/-- `Σ_{n≥1} n⁻² ≤ 2` in the form used below. -/
lemma aux_hcoer_tsum_inv_sq :
    ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have h := aux_hcoer_tsum_le (q := 1) le_rfl
  refine le_trans (le_of_eq (tsum_congr fun n => ?_)) h
  congr 1
  rw [show (3 : ℝ) - 5 * 1 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- **Moment of the weighted supremum.** -/
lemma aux_hcoer_K1E_moment (μ : Measure Ω) {rho0 : ℝ} (hrho : 1 ≤ rho0) {q : ℝ} (hq : 1 ≤ q)
    (Kfun : SpatialCoordinates d → ℕ → Ω → ℝ) (hKm : ∀ y k, Measurable (Kfun y k))
    (hK0 : ∀ y k om, 0 ≤ Kfun y k om) (Csub : ℝ) (hCsub : 0 ≤ Csub)
    (hmom : ∀ y k, ‖y‖ ≤ rho0 → 1 ≤ k →
      ∫⁻ om, ENNReal.ofReal (Kfun y k om ^ q) ∂μ ≤ ENNReal.ofReal (Csub * 9 ^ k)) :
    ∫⁻ om, aux_hcoer_K1E d rho0 Kfun om ^ q ∂μ ≤
      ENNReal.ofReal (72 * (6 * rho0 + 14) ^ ((d : ℝ) * q) * Csub) := by
  classical
  have hq0 : 0 < q := by linarith
  set C : ℝ := 36 * (6 * rho0 + 14) ^ ((d : ℝ) * q) * Csub with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; have : (0 : ℝ) ≤ 6 * rho0 + 14 := by linarith
                         positivity
  set F : ℕ → ℕ → Ω → ℝ≥0∞ := fun n m om =>
    ENNReal.ofReal (aux_hcoer_T d rho0 Kfun n m om ^ q) with hFdef
  have hFm : ∀ n m, Measurable (F n m) := fun n m =>
    ENNReal.measurable_ofReal.comp ((aux_hcoer_measurable_T rho0 Kfun hKm n m).pow_const q)
  -- pointwise
  have hpt : ∀ om, aux_hcoer_K1E d rho0 Kfun om ^ q ≤ ∑' n, ∑' m, F n m om := by
    intro om
    set X := ∑' n, ∑' m, F n m om
    have hle : aux_hcoer_K1E d rho0 Kfun om ≤ X ^ q⁻¹ := by
      unfold aux_hcoer_K1E
      refine iSup_le fun n => iSup_le fun m => ?_
      have hT0 := aux_hcoer_T_nonneg rho0 Kfun hK0 n m om
      have e : ENNReal.ofReal (aux_hcoer_T d rho0 Kfun n m om) = (F n m om) ^ q⁻¹ := by
        simp only [hFdef]
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hT0 _) (by positivity),
          ← Real.rpow_mul hT0, mul_inv_cancel₀ hq0.ne', Real.rpow_one]
      rw [e]
      refine ENNReal.rpow_le_rpow ?_ (by positivity)
      exact (ENNReal.le_tsum m).trans (ENNReal.le_tsum (f := fun n => ∑' m, F n m om) n)
    calc aux_hcoer_K1E d rho0 Kfun om ^ q ≤ (X ^ q⁻¹) ^ q := ENNReal.rpow_le_rpow hle hq0.le
      _ = X := ENNReal.rpow_inv_rpow hq0.ne' X
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_tsum fun n => (Measurable.ennreal_tsum fun m => hFm n m).aemeasurable]
  simp_rw [lintegral_tsum fun m => (hFm _ m).aemeasurable]
  -- per level
  have hlevel : ∀ n, ∑' m, ∫⁻ om, F n m om ∂μ ≤
      (if 1 ≤ n then ENNReal.ofReal (C * ((n : ℝ) ^ 2)⁻¹) else 0) := by
    intro n
    have hzero : ∀ m ∉ Finset.Icc 1 n, ∫⁻ om, F n m om ∂μ = 0 := by
      intro m hm
      have hnot : ¬(1 ≤ m ∧ m ≤ n) := fun h => hm (Finset.mem_Icc.2 h)
      refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun om => ?_)
      simp only [hFdef, aux_hcoer_T, hnot, if_false, Pi.zero_apply]
      rw [Real.zero_rpow hq0.ne', ENNReal.ofReal_zero]
    rw [tsum_eq_sum hzero]
    by_cases hn : 1 ≤ n
    · rw [if_pos hn]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      calc ∑ m ∈ Finset.Icc 1 n, ∫⁻ om, F n m om ∂μ
          ≤ ∑ m ∈ Finset.Icc 1 n, ENNReal.ofReal (C * ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ))⁻¹) := by
            refine Finset.sum_le_sum fun m hm => ?_
            obtain ⟨hm1, hmn⟩ := Finset.mem_Icc.1 hm
            exact aux_hcoer_T_moment μ hrho hq Kfun hKm hK0 Csub hCsub hmom hm1 hmn
        _ = ENNReal.ofReal (C * ((n : ℝ) ^ 2)⁻¹) := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            congr 1
            field_simp
    · rw [if_neg hn]
      have hn0 : n = 0 := by omega
      subst hn0
      have : Finset.Icc 1 0 = (∅ : Finset ℕ) := by rfl
      rw [this, Finset.sum_empty]
  refine (ENNReal.tsum_le_tsum hlevel).trans ?_
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [show ¬ (1 ≤ 0) from by omega, if_false, zero_add, show ∀ n : ℕ, 1 ≤ n + 1 from fun n => by omega,
    if_true]
  have hC : ∀ n : ℕ, ENNReal.ofReal (C * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) =
      ENNReal.ofReal C * ENNReal.ofReal (((n : ℝ) + 1) ^ 2)⁻¹ := by
    intro n; rw [← ENNReal.ofReal_mul hC0]; push_cast; ring_nf
  simp_rw [hC]
  rw [ENNReal.tsum_mul_left]
  calc ENNReal.ofReal C * ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) ^ 2)⁻¹
      ≤ ENNReal.ofReal C * 2 := mul_le_mul_left' aux_hcoer_tsum_inv_sq _
    _ = ENNReal.ofReal (72 * (6 * rho0 + 14) ^ ((d : ℝ) * q) * Csub) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul hC0, hCdef]; congr 1; ring

end Generic

end Paper
end
end

-- ===== module HCoer.Inputs =====
section
/-!
# hCoer: measurable input packages from `lem_coercivity` and `lem_extremes`
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

lemma aux_hcoer_lintegral_abs_rpow {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) {p : ℝ}
    (hp : 0 < p) (C : ℝ) (hC : 0 ≤ C) (hf : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) :
    ∫⁻ om, ENNReal.ofReal (|f om| ^ p) ∂μ ≤ ENNReal.ofReal (C ^ p) := by
  have h := HCut.aux_hcut_lintegral_ofReal_rpow_eq μ (f := fun om => |f om|) (fun om => abs_nonneg _) hp
  rw [h]
  have e : eLpNorm (fun om => |f om|) (ENNReal.ofReal p) μ = eLpNorm f (ENNReal.ofReal p) μ := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (f := f) (p := ENNReal.ofReal p) (μ := μ)
  rw [e, ← ENNReal.ofReal_rpow_of_nonneg hC hp.le]
  exact ENNReal.rpow_le_rpow hf hp.le

section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- **(Kr package)** from `lem_coercivity` at the origin unit cube. -/
lemma aux_hcoer_Kr_package (hd : 2 ≤ d) (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
      {H0 : BilateralField d → C(SpatialCoordinates d, ℝ)}, InfraredCharacterization M H0 →
      M.delta ≤ delta →
      ∃ (Kr : ℕ → BilateralField d → ℝ) (Cb2 : ℝ), 0 ≤ Cb2 ∧ (∀ n, Measurable (Kr n)) ∧
        (∀ n om, 0 ≤ Kr n om) ∧
        (∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          aux_hcoer_CoerMZ hd (cutoffPositiveCoefficient M H0 om n 0 one_pos) (Kr n om)) ∧
        (∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          aux_hcoer_CoerK hd (cutoffPositiveCoefficient M H0 om n 0 one_pos) (Kr n om)) ∧
        (∀ n, ∫⁻ om, ENNReal.ofReal (Kr n om ^ (2 * q)) ∂(chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal Cb2) := by
  obtain ⟨delta0, hdelta0, hmain⟩ := aux_lem_coercivity_compat d hd Jc Pc Sf
  refine ⟨delta0 (2 * q), hdelta0 _ (by linarith), ?_⟩
  intro M Rm H0 hH0 hM
  obtain ⟨K, hK, hKmom⟩ := hmain M Rm H0 hH0 0 1 one_pos le_rfl
  obtain ⟨Cb, hmem, hbd⟩ := hKmom (2 * q) (by linarith) hM
  set Cb' := max Cb 0 with hCb'
  refine ⟨fun n om => |(hmem n).1.mk (K n) om|, Cb' ^ (2 * q), Real.rpow_nonneg (le_max_right _ _) _,
    fun n => continuous_abs.measurable.comp (hmem n).1.stronglyMeasurable_mk.measurable,
    fun n om => abs_nonneg _, ?_, ?_, ?_⟩
  · intro n
    filter_upwards [(hmem n).1.ae_eq_mk] with om hom
    intro w
    have h := ((hK n om).2 w).2
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (sobolevCoefficientForm_nonneg _ _))
    rw [← hom]; exact le_abs_self _
  · intro n
    filter_upwards [(hmem n).1.ae_eq_mk] with om hom
    intro w
    have h := ((hK n om).1 w).2
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (sobolevCoefficientForm_nonneg _ _))
    rw [← hom]; exact le_abs_self _
  · intro n
    have hcongr : ∫⁻ om, ENNReal.ofReal (|(hmem n).1.mk (K n) om| ^ (2 * q)) ∂(chaosSampleLaw M).toMeasure =
        ∫⁻ om, ENNReal.ofReal (|K n om| ^ (2 * q)) ∂(chaosSampleLaw M).toMeasure :=
      lintegral_congr_ae ((hmem n).1.ae_eq_mk.mono fun om hom => by simp only [hom])
    rw [hcongr]
    exact aux_hcoer_lintegral_abs_rpow _ (K n) (by linarith) Cb' (le_max_right _ _)
      ((hbd n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))

/-- **(ml package)** from `lem_extremes` at the origin unit cube. -/
lemma aux_hcoer_ml_package (hd : 2 ≤ d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ Cml : ℝ, 0 ≤ Cml ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {H : BilateralField d → C(SpatialCoordinates d, ℝ)},
        InfraredCharacterization M H → M.delta ≤ delta →
        ∃ ml : ℕ → BilateralField d → ℝ, (∀ n, Measurable (ml n)) ∧ (∀ n om, 0 < ml n om) ∧
          (∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
              ml n om ≤ cutoffCoefficient M H om n x) ∧
          (∀ n, ∫⁻ om, ENNReal.ofReal ((ml n om)⁻¹ ^ (2 * q)) ∂(chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cml * 81 ^ n)) := by
  have hq2 : 1 ≤ 2 * q := by linarith
  obtain ⟨Cp, Cdx, cd, hCp, hCdx, hcd, hext⟩ :=
    aux_lem_extremes_compat d hd (0 : SpatialCoordinates d) 1 one_pos (2 * q) hq2
  have hlog : 0 < Real.log 81 := Real.log_pos (by norm_num)
  set delta : ℝ := min (cd / (2 * q)) (min 1 (Real.log 81 / (2 * q * (Cdx + Cp)))) with hdeltadef
  have hdelta : 0 < delta := lt_min (by positivity) (lt_min one_pos (by positivity))
  refine ⟨delta, hdelta, (1 + Cp) ^ (2 * q), by positivity, ?_⟩
  intro M H hH hM
  have hMcd : M.delta ≤ cd / (2 * q) := hM.trans (min_le_left _ _)
  have hM1 : M.delta ≤ 1 := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMlog : M.delta ≤ Real.log 81 / (2 * q * (Cdx + Cp)) :=
    hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ0 : 0 < M.delta := M.shellPrefix.delta_pos
  obtain ⟨D, mlow, mhigh, -, hae, -, hsum_mem, -, hsumbd⟩ := hext M H hH hMcd
  set g : ℕ → BilateralField d → ℝ := fun n => (hsum_mem n).1.mk (fun om => mhigh n om + (mlow n om)⁻¹)
    with hgdef
  have hgm : ∀ n, Measurable (g n) := fun n => (hsum_mem n).1.stronglyMeasurable_mk.measurable
  refine ⟨fun n om => (max (g n om) 1)⁻¹, fun n => ((hgm n).max measurable_const).inv,
    fun n om => inv_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _)), ?_, ?_⟩
  · intro n
    filter_upwards [hae, (hsum_mem n).1.ae_eq_mk] with om h1 h2 x hx
    obtain ⟨-, hlowpos, hbounds⟩ := h1 n
    have h0mem : (0 : SpatialCoordinates d) ∈
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
      change dist (0 : SpatialCoordinates d) 0 ≤ 1 / 2; simp
    have hhigh : 0 < mhigh n om :=
      lt_of_lt_of_le (cutoffCoefficient_pos M H om n 0) (hbounds 0 h0mem).2
    have hg : g n om = mhigh n om + (mlow n om)⁻¹ := by rw [hgdef]; exact h2.symm
    have hge : (mlow n om)⁻¹ ≤ max (g n om) 1 := by
      rw [hg]; exact le_trans (by linarith) (le_max_left _ _)
    calc (max (g n om) 1)⁻¹ ≤ ((mlow n om)⁻¹)⁻¹ :=
          inv_anti₀ (inv_pos.2 hlowpos) hge
      _ = mlow n om := inv_inv _
      _ ≤ cutoffCoefficient M H om n x := (hbounds x hx).1
  · intro n
    have hpt : ∀ om, ENNReal.ofReal (((max (g n om) 1)⁻¹)⁻¹ ^ (2 * q)) ≤
        ENNReal.ofReal ((1 + 1 * |g n om| + 0 * 0) ^ (2 * q)) := by
      intro om
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_ (by linarith))
      rw [inv_inv]
      refine max_le ?_ ?_ <;> nlinarith [le_abs_self (g n om), abs_nonneg (g n om)]
    refine (lintegral_mono hpt).trans ?_
    set E : ℝ := Real.exp ((Cdx * M.delta + Cp * M.delta ^ 2) * n) with hEdef
    have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
    have hgmom : ∫⁻ om, ENNReal.ofReal (|g n om| ^ (2 * q)) ∂(chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((Cp * E) ^ (2 * q)) := by
      refine aux_hcoer_lintegral_abs_rpow _ (g n) (by linarith) (Cp * E) (by positivity) ?_
      rw [eLpNorm_congr_ae (hsum_mem n).1.ae_eq_mk.symm]
      exact hsumbd n
    have h3 := aux_hcoer_lintegral_three (chaosSampleLaw M).toMeasure (fun om => |g n om|) (fun _ => 0)
      (continuous_abs.measurable.comp (hgm n)) measurable_const (fun om => abs_nonneg _) (fun _ => le_rfl)
      1 1 0 zero_le_one zero_le_one le_rfl hq2 ((Cp * E) ^ (2 * q)) 0 (by positivity) le_rfl hgmom
      (by simp [Real.zero_rpow (by linarith : (2 * q) ≠ 0)])
    refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
    have hroot : ((Cp * E) ^ (2 * q)) ^ (1 / (2 * q)) = Cp * E := by
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel (by linarith), Real.rpow_one]
    rw [hroot]
    simp only [one_mul, zero_mul, add_zero]
    -- (1 + Cp E)^{2q} ≤ (1+Cp)^{2q} E^{2q} ≤ (1+Cp)^{2q} 81^n
    have hE81 : E ^ (2 * q) ≤ 81 ^ n := by
      rw [hEdef, ← Real.exp_mul]
      have hlin : (Cdx * M.delta + Cp * M.delta ^ 2) * n * (2 * q) ≤ Real.log 81 * n := by
        have hδ2 : M.delta ^ 2 ≤ M.delta := by nlinarith
        have h1 : Cdx * M.delta + Cp * M.delta ^ 2 ≤ (Cdx + Cp) * M.delta := by nlinarith
        have h2' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * q * (Cdx + Cp))).1 hMlog
        have h2 : (Cdx + Cp) * M.delta * (2 * q) ≤ Real.log 81 := by
          have e : (Cdx + Cp) * M.delta * (2 * q) = M.delta * (2 * q * (Cdx + Cp)) := by ring
          rw [e]; exact h2'
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have h3 : (Cdx * M.delta + Cp * M.delta ^ 2) * (2 * q) ≤ Real.log 81 :=
          (mul_le_mul_of_nonneg_right h1 (by linarith)).trans h2
        calc (Cdx * M.delta + Cp * M.delta ^ 2) * n * (2 * q)
            = ((Cdx * M.delta + Cp * M.delta ^ 2) * (2 * q)) * n := by ring
          _ ≤ Real.log 81 * n := mul_le_mul_of_nonneg_right h3 hn
      calc Real.exp ((Cdx * M.delta + Cp * M.delta ^ 2) * n * (2 * q)) ≤ Real.exp (Real.log 81 * n) :=
            Real.exp_le_exp.2 hlin
        _ = 81 ^ n := by rw [Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
    calc (1 + Cp * E) ^ (2 * q) ≤ ((1 + Cp) * E) ^ (2 * q) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
      _ = (1 + Cp) ^ (2 * q) * E ^ (2 * q) := Real.mul_rpow (by positivity) (by positivity)
      _ ≤ (1 + Cp) ^ (2 * q) * 81 ^ n := by gcongr

end Laws

end Paper
end
end

-- ===== module HCoer.Supplier =====
section
/-!
# hCoer: the coercivity supplier of `tight_static` (clause 2), standalone with its own disorder threshold
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}


section Helpers
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hcoer_small_facts (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Q : ℝ} (hQ1 : 1 ≤ Q)
    (hM : M.delta ≤ 1 / (8 * Q)) :
    Real.exp ((4 * Q) ^ 2 * M.delta ^ 2 / 4 + (4 * Q) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 2 ∧
      2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ Real.log 3 := by
  have hδ := M.shellPrefix.delta_pos
  have hτ := M.G4.tauSq_pos
  have hτδ := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hQ0 : 0 < Q := by linarith
  have hδ2 : M.delta ^ 2 ≤ 1 / (64 * Q ^ 2) := by
    have h1 : M.delta ^ 2 ≤ (1 / (8 * Q)) ^ 2 := pow_le_pow_left₀ hδ.le hM 2
    calc M.delta ^ 2 ≤ (1 / (8 * Q)) ^ 2 := h1
      _ = 1 / (64 * Q ^ 2) := by field_simp; ring
  have hQ2 : 1 ≤ Q ^ 2 := by nlinarith
  have hδ2' : M.delta ^ 2 ≤ 1 / 64 := hδ2.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hτ' : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ 0.35 * M.delta ^ 2 := by nlinarith
  constructor
  · rw [abs_of_pos hτ]
    have h1 : (4 * Q) ^ 2 * M.delta ^ 2 / 4 ≤ 1 / 16 := by
      have : (4 * Q) ^ 2 * M.delta ^ 2 / 4 = 4 * (Q ^ 2 * M.delta ^ 2) := by ring
      rw [this]
      have : Q ^ 2 * M.delta ^ 2 ≤ 1 / 64 := by
        calc Q ^ 2 * M.delta ^ 2 ≤ Q ^ 2 * (1 / (64 * Q ^ 2)) := by gcongr
          _ = 1 / 64 := by field_simp
      linarith
    have h2 : (4 * Q) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ 1 / 16 := by
      have : (4 * Q) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ 4 * Q * (0.35 * (1 / (64 * Q ^ 2))) := by
        gcongr; exact hτ'.trans (by gcongr)
      refine this.trans ?_
      have : 4 * Q * (0.35 * (1 / (64 * Q ^ 2))) = 0.35 / (16 * Q) := by field_simp; ring
      rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc Real.exp ((4 * Q) ^ 2 * M.delta ^ 2 / 4 + (4 * Q) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  · have h3 : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    nlinarith


lemma aux_hcoer_rat (q' : ℚ) (h0 : 0 < q') (h1 : q' ≤ 1) :
    1 ≤ q'.num.toNat ∧ q'.num.toNat ≤ q'.den ∧ (q' : ℝ) = (q'.num.toNat : ℝ) / (q'.den : ℝ) := by
  have hnum : 0 < q'.num := Rat.num_pos.2 h0
  have hden : (0 : ℝ) < q'.den := by exact_mod_cast q'.den_pos
  have hcast : ((q'.num.toNat : ℕ) : ℝ) = (q'.num : ℝ) := by
    have : ((q'.num.toNat : ℕ) : ℤ) = q'.num := Int.toNat_of_nonneg hnum.le
    exact_mod_cast this
  have hq : (q' : ℝ) = (q'.num : ℝ) / (q'.den : ℝ) := Rat.cast_def q'
  refine ⟨by omega, ?_, by rw [hcast, hq]⟩
  have hle : (q'.num : ℝ) ≤ q'.den := by
    have : (q' : ℝ) ≤ 1 := by exact_mod_cast h1
    rw [hq, div_le_one hden] at this; exact this
  have : (q'.num.toNat : ℝ) ≤ q'.den := by rw [hcast]; exact hle
  exact_mod_cast this

/-- Unified subcube moment. -/
lemma aux_hcoer_Ksub_moment (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (R CH : ℝ) (hCH : ∀ (lam : ℝ), 0 ≤ lam → ∀ y : SpatialCoordinates d, ‖y‖ ≤ R →
        Integrable (fun om => Real.exp (lam * |H om y|)) (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * |H om y|) ∂(chaosSampleLaw M).toMeasure ≤
          2 * Real.exp (CH * lam ^ 2 * M.delta ^ 2))
    (Kr : ℕ → BilateralField d → ℝ) (hKrm : ∀ n, Measurable (Kr n)) (hKr0 : ∀ n om, 0 ≤ Kr n om)
    (q : ℝ) (hq : 1 ≤ q) (Cb2 : ℝ) (hCb2 : 0 ≤ Cb2)
    (hKb : ∀ n, ∫⁻ om, ENNReal.ofReal (Kr n om ^ (2 * q)) ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb2)
    (hsmall : Real.exp ((4 * q) ^ 2 * M.delta ^ 2 / 4 + (4 * q) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 2)
    (ml : ℕ → BilateralField d → ℝ) (hmlm : ∀ n, Measurable (ml n)) (hml0 : ∀ n om, 0 < ml n om)
    (Cml : ℝ) (hCml : 0 ≤ Cml)
    (hmlmom : ∀ n, ∫⁻ om, ENNReal.ofReal ((ml n om)⁻¹ ^ (2 * q)) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cml * 81 ^ n))
    (Kone : ℝ) (hKone0 : 0 ≤ Kone) (N : ℕ) (y : SpatialCoordinates d) (hy : ‖y‖ ≤ R) (k : ℕ) (hk : 1 ≤ k) :
    ∫⁻ om, ENNReal.ofReal (aux_hcoer_Ksub M H Kr ml Kone N y k om ^ q) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((2 * Real.exp (CH * (4 * q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * 2 * Cb2 ^ (1 / 2 : ℝ) +
        Kone ^ q * (2 * Real.exp (CH * (2 * q) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) * Cml ^ (1 / 2 : ℝ)) * 9 ^ k) := by
  have hq0 : 0 < q := by linarith
  have h9 : (1 : ℝ) ≤ 9 ^ k := one_le_pow₀ (by norm_num)
  set A1 : ℝ := (2 * Real.exp (CH * (4 * q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) with hA1
  set A2 : ℝ := Kone ^ q * (2 * Real.exp (CH * (2 * q) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) * Cml ^ (1 / 2 : ℝ)
    with hA2
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  unfold aux_hcoer_Ksub
  by_cases hkN : k ≤ N
  · simp only [hkN, if_true]
    refine (aux_hcoer_Kin_moment M Rm hH R CH hCH y hy hk Kr hKrm hKr0 q hq Cb2 hCb2 hKb hsmall).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h4 : (2 * (4 : ℝ) ^ k) ^ (1 / 4 : ℝ) ≤ 2 * 9 ^ k := by
      have h1 : (1 : ℝ) ≤ 2 * 4 ^ k := by have := one_le_pow₀ (M₀ := ℝ) (a := 4) (by norm_num) (n := k); linarith
      calc (2 * (4 : ℝ) ^ k) ^ (1 / 4 : ℝ) ≤ (2 * (4 : ℝ) ^ k) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = 2 * 4 ^ k := Real.rpow_one _
        _ ≤ 2 * 9 ^ k := by gcongr; norm_num
    have hB : 0 ≤ Cb2 ^ (1 / 2 : ℝ) := by positivity
    calc A1 * (2 * 4 ^ k) ^ (1 / 4 : ℝ) * Cb2 ^ (1 / 2 : ℝ) ≤ A1 * (2 * 9 ^ k) * Cb2 ^ (1 / 2 : ℝ) := by
          gcongr
      _ = A1 * 2 * Cb2 ^ (1 / 2 : ℝ) * 9 ^ k := by ring
      _ ≤ (A1 * 2 * Cb2 ^ (1 / 2 : ℝ) + A2) * 9 ^ k := by gcongr; linarith
  · simp only [hkN, if_false]
    have hkN' : N < k := by omega
    obtain ⟨hint, hbd⟩ := hCH (2 * q) (by positivity) y hy
    have hEH : ∫⁻ om, ENNReal.ofReal (Real.exp (2 * q * |H om y|)) ∂(chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (2 * Real.exp (CH * (2 * q) ^ 2 * M.delta ^ 2)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun om => (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal hbd
    refine (aux_hcoer_Kout_moment M hH y (ml N) (hmlm N) (hml0 N) Kone hKone0 q hq _ _ hEH (hmlmom N)).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hKone0 _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h81 : (Cml * 81 ^ N) ^ (1 / 2 : ℝ) = Cml ^ (1 / 2 : ℝ) * 9 ^ N := by
      rw [Real.mul_rpow hCml (by positivity)]
      congr 1
      rw [show (81 : ℝ) ^ N = (9 ^ N) ^ (2 : ℝ) by rw [Real.rpow_two, ← pow_mul, mul_comm, pow_mul]; norm_num,
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [h81]
    have h9N : (9 : ℝ) ^ N ≤ 9 ^ k := pow_le_pow_right₀ (by norm_num) hkN'.le
    calc Kone ^ q * ((2 * Real.exp (CH * (2 * q) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) *
          (Cml ^ (1 / 2 : ℝ) * 9 ^ N)) = A2 * 9 ^ N := by rw [hA2]; ring
      _ ≤ A2 * 9 ^ k := by gcongr
      _ ≤ (A1 * 2 * Cb2 ^ (1 / 2 : ℝ) + A2) * 9 ^ k := by
          gcongr; have : 0 ≤ A1 * 2 * Cb2 ^ (1 / 2 : ℝ) := by positivity
          linarith

end Helpers


/-- The coercivity constant. -/
def aux_hcoer_Kcoer (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Kr ml : ℕ → BilateralField d → ℝ) (Kone : ℝ) (N : ℕ) (rho0 Cd1 Cz a0 : ℝ) (j : ℕ)
    (om : BilateralField d) : ℝ :=
  a0 + Cd1 * (aux_hcoer_K1E d rho0 (fun y k om => aux_hcoer_Ksub M H Kr ml Kone N y k om) om).toReal +
    Cz * aux_hcoer_K0 M Kr N j om

/-- The almost-sure clause of the coercivity supplier. -/
lemma aux_hcoer_clause_ae [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    {H H0 : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (hH0 : InfraredCharacterization M H0) (N : ℕ) {rho0 : ℝ} (hrho : 1 ≤ rho0)
    (Cd1 : ℝ) (hCd1 : 0 < Cd1) (htr1 : aux_hcoer_TransferMZ hd Cd1)
    (Cd2 : ℝ) (hCd2 : 0 < Cd2) (htr2 : aux_hcoer_TransferK hd Cd2)
    (Kr : ℕ → BilateralField d → ℝ) (hKr0 : ∀ n om, 0 ≤ Kr n om)
    (hKrMZ : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      aux_hcoer_CoerMZ hd (cutoffPositiveCoefficient M H0 om n 0 one_pos) (Kr n om))
    (hKrK : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      aux_hcoer_CoerK hd (cutoffPositiveCoefficient M H0 om n 0 one_pos) (Kr n om))
    (ml : ℕ → BilateralField d → ℝ) (hml0 : ∀ n om, 0 < ml n om)
    (hmlb : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ml n om ≤ cutoffCoefficient M H om n x)
    (b1 : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hb1 : ∀ᵐ x ∂(volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      (b1.val : SpatialCoordinates d → ℝ) x = 1)
    (Kone : ℝ) (hKone0 : 0 ≤ Kone) (hKone : aux_hcoer_CoerMZ hd b1 Kone)
    (j : ℕ) (hrho3 : rho0 ≤ (3 : ℝ) ^ j) (Cz a0 : ℝ)
    (hCzdef : Cz = Cd2 * (((3 : ℝ) ^ j) ^ (1 / 2 : ℝ) + ((3 : ℝ) ^ j) ^ 2))
    (ha0def : a0 = 1 + aux_hcoer_C2 d rho0)
    (hK1fin : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      aux_hcoer_K1E d rho0 (fun y k om => aux_hcoer_Ksub M H Kr ml Kone N y k om) om ≠ ⊤) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ q' : ℚ, 0 < q' → q' ≤ 1 →
            (∀ v : Homogenization.H1Function
                (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2)),
              (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                      ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
                ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal (v.toFun x ^ 2) ≤
              ENNReal.ofReal (aux_hcoer_Kcoer M H Kr ml Kone N rho0 Cd1 Cz a0 j omega * (q'.den : ℝ) ^ (5 : ℝ)) *
                ((∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal ((cutoffCoefficient M H omega N x) *
                      Homogenization.vecDot (v.grad x) (v.grad x))) +
                  ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal (v.toFun x ^ 2))) ∧
            (∀ v : Homogenization.H10Function
                (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2)),
              (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                      ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
                ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal (v.toFun x ^ 2) ≤
              ENNReal.ofReal (aux_hcoer_Kcoer M H Kr ml Kone N rho0 Cd1 Cz a0 j omega * (q'.den : ℝ) ^ (5 : ℝ)) *
                ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal ((cutoffCoefficient M H omega N x) *
                    Homogenization.vecDot (v.grad x) (v.grad x)))  := by
  classical
  set Kfun : SpatialCoordinates d → ℕ → BilateralField d → ℝ :=
    fun y k om => aux_hcoer_Ksub M H Kr ml Kone N y k om with hKfundef
  have hKf0 : ∀ y k om, 0 ≤ Kfun y k om := fun y k om =>
    aux_hcoer_Ksub_nonneg M Rm H Kr hKr0 ml hml0 hKone0 N y k om
  set K1E := aux_hcoer_K1E d rho0 Kfun with hK1Edef
  set K0 := aux_hcoer_K0 M Kr N j with hK0def
  have hK00 : ∀ om, 0 ≤ K0 om := aux_hcoer_K0_nonneg M Rm Kr hKr0 N j
  have hX0 : ∀ om, 0 ≤ (K1E om).toReal := fun om => ENNReal.toReal_nonneg
  have hCz0 : 0 ≤ Cz := by rw [hCzdef]; positivity
  have ha0 : 1 ≤ a0 := by have := aux_hcoer_C2_nonneg d hrho; rw [ha0def]; linarith
  have hKcoer_eq : ∀ om, aux_hcoer_Kcoer M H Kr ml Kone N rho0 Cd1 Cz a0 j om =
      a0 + Cd1 * (K1E om).toReal + Cz * K0 om := fun om => rfl
  have hsubae : ∀ n m : ℕ, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, 1 ≤ m → m ≤ n →
      ∀ y ∈ aux_hcoer_Y d (rho0 * m / n),
        ∀ v : Homogenization.H1Function (Metric.ball y (aux_hcoer_tOf (rho0 * m / n) / 2)),
          aux_hcoer_gag v.toFun (Metric.ball y (aux_hcoer_tOf (rho0 * m / n) / 2)) ≤
            ENNReal.ofReal (Cd1 * Kfun y (aux_hcoer_kOf (rho0 * m / n)) om) *
              ∫⁻ x in Metric.ball y (aux_hcoer_tOf (rho0 * m / n) / 2),
                ENNReal.ofReal (cutoffCoefficient M H om N x *
                  Homogenization.vecDot (v.grad x) (v.grad x)) := by
    intro n m
    by_cases hnm : 1 ≤ m ∧ m ≤ n
    · obtain ⟨hs0, -, -, -⟩ := aux_hcoer_level_bounds hrho hnm.1 hnm.2
      obtain ⟨hk1, -, -⟩ := aux_hcoer_kOf_spec hs0
      have hall : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ y ∈ aux_hcoer_Y d (rho0 * m / n),
          ∀ v : Homogenization.H1Function (Metric.ball y (aux_hcoer_tOf (rho0 * m / n) / 2)),
            aux_hcoer_gag v.toFun (Metric.ball y (aux_hcoer_tOf (rho0 * m / n) / 2)) ≤
              ENNReal.ofReal (Cd1 * Kfun y (aux_hcoer_kOf (rho0 * m / n)) om) *
                ∫⁻ x in Metric.ball y (aux_hcoer_tOf (rho0 * m / n) / 2),
                  ENNReal.ofReal (cutoffCoefficient M H om N x *
                    Homogenization.vecDot (v.grad x) (v.grad x)) := by
        rw [Filter.eventually_all_finset]
        intro y _
        exact aux_hcoer_sub_ae hd M Rm hH hH0 Cd1 hCd1 htr1 Kr hKr0 hKrMZ ml hml0 hmlb b1 hb1 Kone
          hKone0 hKone N y _ hk1
      filter_upwards [hall] with om hom _ _
      exact hom
    · exact Eventually.of_forall fun om h1 h2 => absurd ⟨h1, h2⟩ hnm
  have hsubae' := ae_all_iff.2 fun n => ae_all_iff.2 fun m => hsubae n m
  have hzoom := aux_hcoer_zoom_ae hd M Rm hH hH0 Cd2 hCd2 htr2 Kr hKr0 hKrK N j
  filter_upwards [hK1fin, hsubae', hzoom] with om hfin hsub hz
  intro q' hq'0 hq'1
  obtain ⟨hm1, hmn, hcast⟩ := aux_hcoer_rat q' hq'0 hq'1
  have hs : rho0 * (q' : ℝ) = rho0 * (q'.num.toNat : ℕ) / (q'.den : ℕ) := by rw [hcast]; ring
  have hn1 : (1 : ℝ) ≤ (q'.den : ℝ) := by exact_mod_cast q'.den_pos
  have hn5 : (1 : ℝ) ≤ (q'.den : ℝ) ^ (5 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hKc1 : 1 ≤ aux_hcoer_Kcoer M H Kr ml Kone N rho0 Cd1 Cz a0 j om := by
    have := hX0 om; have := hK00 om
    rw [hKcoer_eq]; nlinarith
  refine ⟨fun v => ?_, fun v => ?_⟩
  · have hK1 : ((q'.den : ℝ) ^ 5)⁻¹ * ∑ y ∈ aux_hcoer_Y d (rho0 * (q' : ℝ)),
        Kfun y (aux_hcoer_kOf (rho0 * (q' : ℝ))) om ≤ (K1E om).toReal := by
      have h := aux_hcoer_T_le_K1E rho0 Kfun hKf0 q'.den q'.num.toNat om hfin
      unfold aux_hcoer_T at h
      rw [if_pos ⟨hm1, hmn⟩] at h
      rw [hs]; exact h
    have hsub' : ∀ y ∈ aux_hcoer_Y d (rho0 * (q' : ℝ)),
        ∀ v : Homogenization.H1Function (Metric.ball y (aux_hcoer_tOf (rho0 * (q' : ℝ)) / 2)),
          aux_hcoer_gag v.toFun (Metric.ball y (aux_hcoer_tOf (rho0 * (q' : ℝ)) / 2)) ≤
            ENNReal.ofReal (Cd1 * Kfun y (aux_hcoer_kOf (rho0 * (q' : ℝ))) om) *
              ∫⁻ x in Metric.ball y (aux_hcoer_tOf (rho0 * (q' : ℝ)) / 2),
                ENNReal.ofReal (cutoffCoefficient M H om N x *
                  Homogenization.vecDot (v.grad x) (v.grad x)) := by
      rw [hs]; exact hsub q'.den q'.num.toNat hm1 hmn
    have h := aux_hcoer_H1_omega Cd1 hCd1 hrho (cutoffCoefficient M H om N) (fun y k => Kfun y k om)
      (fun y k => hKf0 y k om) hm1 hmn (rho0 * (q' : ℝ)) hs hsub' _ hK1 v
    refine h.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _)
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have := hK00 om
    rw [hKcoer_eq]; nlinarith
  · have hsR : rho0 * (q' : ℝ) ≤ (3 : ℝ) ^ j := by
      have : (q' : ℝ) ≤ 1 := by exact_mod_cast hq'1
      nlinarith
    have h := aux_hcoer_H10_omega (cutoffCoefficient M H om N) hsR _ hz v
    refine h.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _)
    have hK0' : Cd2 * (((3 : ℝ) ^ j) ^ (1 / 2 : ℝ) + ((3 : ℝ) ^ j) ^ 2) * aux_hcoer_K0 M Kr N j om ≤
        aux_hcoer_Kcoer M H Kr ml Kone N rho0 Cd1 Cz a0 j om := by
      have := hX0 om; have := hK00 om
      rw [hKcoer_eq]; nlinarith
    calc _ ≤ aux_hcoer_Kcoer M H Kr ml Kone N rho0 Cd1 Cz a0 j om := hK0'
      _ ≤ aux_hcoer_Kcoer M H Kr ml Kone N rho0 Cd1 Cz a0 j om * (q'.den : ℝ) ^ (5 : ℝ) := by nlinarith


/-- Generic packaging of the final constant. -/
lemma aux_hcoer_Kcoer_generic {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ≥0∞) (Y : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y) (hY0 : ∀ om, 0 ≤ Y om)
    {q : ℝ} (hq : 1 ≤ q) (CX CY : ℝ) (hCX0 : 0 ≤ CX) (hCY0 : 0 ≤ CY)
    (hXmom : ∫⁻ om, X om ^ q ∂μ ≤ ENNReal.ofReal CX)
    (hYmom : ∫⁻ om, ENNReal.ofReal (Y om ^ q) ∂μ ≤ ENNReal.ofReal CY)
    (a0 Cd1 Cz : ℝ) (ha0 : 1 ≤ a0) (hCd1 : 0 ≤ Cd1) (hCz : 0 ≤ Cz) :
    Measurable (fun om => a0 + Cd1 * (X om).toReal + Cz * Y om) ∧
      (∀ om, 1 ≤ a0 + Cd1 * (X om).toReal + Cz * Y om) ∧
      ∫⁻ om, ENNReal.ofReal ((a0 + Cd1 * (X om).toReal + Cz * Y om) ^ q) ∂μ ≤
        ENNReal.ofReal ((a0 + Cd1 * CX ^ (1 / q) + Cz * CY ^ (1 / q)) ^ q + 1) ∧
      ∀ᵐ om ∂μ, X om ≠ ⊤ := by
  have hq0 : 0 < q := by linarith
  have hX0 : ∀ om, 0 ≤ (X om).toReal := fun om => ENNReal.toReal_nonneg
  refine ⟨(measurable_const.add (measurable_const.mul hXm.ennreal_toReal)).add (measurable_const.mul hYm),
    fun om => by have := hX0 om; have := hY0 om; nlinarith, ?_, ?_⟩
  · have hXmom' : ∫⁻ om, ENNReal.ofReal ((X om).toReal ^ q) ∂μ ≤ ENNReal.ofReal CX := by
      refine le_trans (lintegral_mono fun om => ?_) hXmom
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq0.le]
      exact ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le hq0.le
    exact (aux_hcoer_lintegral_three μ (fun om => (X om).toReal) Y hXm.ennreal_toReal hYm hX0 hY0 a0 Cd1 Cz
      (by linarith) hCd1 hCz hq CX CY hCX0 hCY0 hXmom' hYmom).trans (ENNReal.ofReal_le_ofReal (by linarith))
  · have hlt : ∫⁻ om, X om ^ q ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hXmom
    filter_upwards [ae_lt_top (hXm.pow_const q) hlt] with om hom
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos hq0] at hom
    exact lt_irrefl _ hom

/-- **The coercivity supplier of `tight_static`.** -/
theorem tight_static_coer [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Sf : Lane4.SobolevFoundationalInput d hd)
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M),
        M.delta ≤ delta0 →
      ∀ rho0 : ℝ, 1 ≤ rho0 → ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → ∀ N : ℕ,
      ∃ Kcoer : BilateralField d → ℝ, Measurable Kcoer ∧ (∀ omega, 1 ≤ Kcoer omega) ∧
        (∫⁻ omega, ENNReal.ofReal (Kcoer omega ^ q)
            ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal Ccoer ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ q' : ℚ, 0 < q' → q' ≤ 1 →
            (∀ v : Homogenization.H1Function
                (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2)),
              (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                      ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
                ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal (v.toFun x ^ 2) ≤
              ENNReal.ofReal (Kcoer omega * (q'.den : ℝ) ^ (5 : ℝ)) *
                ((∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal ((cutoffCoefficient M H omega N x) *
                      Homogenization.vecDot (v.grad x) (v.grad x))) +
                  ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal (v.toFun x ^ 2))) ∧
            (∀ v : Homogenization.H10Function
                (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2)),
              (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                      ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
                ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal (v.toFun x ^ 2) ≤
              ENNReal.ofReal (Kcoer omega * (q'.den : ℝ) ^ (5 : ℝ)) *
                ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal ((cutoffCoefficient M H omega N x) *
                    Homogenization.vecDot (v.grad x) (v.grad x))) := by
  classical
  obtain ⟨Cd1, hCd1, htr1⟩ := aux_hcoer_transfer_meanzero hd Sf
  obtain ⟨Cd2, hCd2, htr2⟩ := aux_hcoer_transfer_killed hd Sf
  obtain ⟨δK, hδK, hKr⟩ := aux_hcoer_Kr_package hd Jc Pc Sf q hq
  obtain ⟨δm, hδm, Cml, hCml, hml⟩ := aux_hcoer_ml_package hd q hq
  obtain ⟨b1, hb1⟩ := aux_hcoer_one_coefficient d
  obtain ⟨Cbes, hCbes, hbes⟩ := lane4_besov_h34_coercivity d hd Jc Pc Sf (1 / 8) ⟨by norm_num, by norm_num⟩
  set Kone : ℝ := Cbes * (Jc.lam 0 1 one_pos b1 0 1 (1 / 8) 1)⁻¹ with hKonedef
  have hKone0 : 0 ≤ Kone := mul_nonneg hCbes.le (inv_nonneg.2 (Jc.lam_pos _ _ _ _ _ _ _ _).le)
  have hKone : aux_hcoer_CoerMZ hd b1 Kone := fun w => ((hbes 0 one_pos b1).2 w).2
  have hq0 : 0 < q := by linarith
  refine ⟨min δK (min δm (1 / (8 * q))), lt_min hδK (lt_min hδm (by positivity)), ?_⟩
  intro M Rm hM rho0 hrho
  have hMK : M.delta ≤ δK := hM.trans (min_le_left _ _)
  have hMm : M.delta ≤ δm := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMs : M.delta ≤ 1 / (8 * q) := hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hsmall, -⟩ := aux_hcoer_small_facts M hq hMs
  obtain ⟨H0, hH0⟩ := exists_infraredCharacterization hd M
  obtain ⟨Kr, Cb2, hCb2, hKrm, hKr0, hKrMZ, hKrK, hKrmom⟩ := hKr M Rm hH0 hMK
  obtain ⟨CH, hCH0, hCHall⟩ := aux_hcut_exp_H_moment hd rho0
  obtain ⟨j0, hj0⟩ := pow_unbounded_of_one_lt rho0 (by norm_num : (1 : ℝ) < 3)
  set j : ℕ := j0 + 1 with hjdef
  have hj1 : 1 ≤ j := by omega
  have hrho3 : rho0 ≤ (3 : ℝ) ^ j := by
    rw [hjdef, pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) j0]
  obtain ⟨Csub, hCsubdef⟩ : ∃ c : ℝ, c = (2 * Real.exp (CH * (4 * q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * 2 *
      Cb2 ^ (1 / 2 : ℝ) + Kone ^ q * (2 * Real.exp (CH * (2 * q) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) *
      Cml ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hCsub0 : 0 ≤ Csub := by rw [hCsubdef]; positivity
  obtain ⟨CX, hCXdef⟩ : ∃ c : ℝ, c = 72 * (6 * rho0 + 14) ^ ((d : ℝ) * q) * Csub := ⟨_, rfl⟩
  have hCX0 : 0 ≤ CX := by
    have : (0 : ℝ) ≤ 6 * rho0 + 14 := by linarith
    rw [hCXdef]; positivity
  obtain ⟨CY, hCYdef⟩ : ∃ c : ℝ, c = (2 * (2 * Real.exp ((2 * q) ^ 2 * M.delta ^ 2 / 4 +
      (2 * q) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ j) ^ (1 / 2 : ℝ) * Cb2 ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hCY0 : 0 ≤ CY := by rw [hCYdef]; positivity
  obtain ⟨Cz, hCzdef⟩ : ∃ c : ℝ, c = Cd2 * (((3 : ℝ) ^ j) ^ (1 / 2 : ℝ) + ((3 : ℝ) ^ j) ^ 2) := ⟨_, rfl⟩
  have hCz0 : 0 ≤ Cz := by rw [hCzdef]; positivity
  obtain ⟨a0, ha0def⟩ : ∃ c : ℝ, c = 1 + aux_hcoer_C2 d rho0 := ⟨_, rfl⟩
  have ha0 : 1 ≤ a0 := by have := aux_hcoer_C2_nonneg d hrho; rw [ha0def]; linarith
  refine ⟨(a0 + Cd1 * CX ^ (1 / q) + Cz * CY ^ (1 / q)) ^ q + 1, by positivity, ?_⟩
  intro H hH N
  obtain ⟨ml, hmlm, hml0, hmlb, hmlmom⟩ := hml M hH hMm
  have hKfm : ∀ y k, Measurable (fun om => aux_hcoer_Ksub M H Kr ml Kone N y k om) := fun y k =>
    aux_hcoer_measurable_Ksub M hH Kr hKrm ml hmlm Kone N y k
  have hKf0 : ∀ y k om, 0 ≤ aux_hcoer_Ksub M H Kr ml Kone N y k om := fun y k om =>
    aux_hcoer_Ksub_nonneg M Rm H Kr hKr0 ml hml0 hKone0 N y k om
  have hKfmom : ∀ y k, ‖y‖ ≤ rho0 → 1 ≤ k →
      ∫⁻ om, ENNReal.ofReal (aux_hcoer_Ksub M H Kr ml Kone N y k om ^ q) ∂(chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Csub * 9 ^ k) := fun y k hy hk => by
    rw [hCsubdef]
    exact aux_hcoer_Ksub_moment M Rm hH rho0 CH (hCHall M H hH) Kr hKrm hKr0 q hq Cb2 hCb2 hKrmom hsmall ml hmlm hml0
      Cml hCml hmlmom Kone hKone0 N y hy k hk
  have hK1Em := aux_hcoer_measurable_K1E (d := d) rho0 (fun y k om => aux_hcoer_Ksub M H Kr ml Kone N y k om)
    hKfm
  have hK1Emom := aux_hcoer_K1E_moment (chaosSampleLaw M).toMeasure hrho hq
    (fun y k om => aux_hcoer_Ksub M H Kr ml Kone N y k om) hKfm hKf0 Csub hCsub0 hKfmom
  rw [← hCXdef] at hK1Emom
  have hK0mom : ∫⁻ om, ENNReal.ofReal (aux_hcoer_K0 M Kr N j om ^ q) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CY := by
    refine (aux_hcoer_K0_moment M Rm Kr hKrm hKr0 N j hj1 q hq Cb2 hKrmom).trans (le_of_eq ?_)
    rw [hCYdef, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg hCb2 (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  obtain ⟨hm, h1, hmom, hfin⟩ := aux_hcoer_Kcoer_generic (chaosSampleLaw M).toMeasure _ _ hK1Em
    (aux_hcoer_measurable_K0 M Kr hKrm N j) (aux_hcoer_K0_nonneg M Rm Kr hKr0 N j) hq CX CY hCX0 hCY0
    hK1Emom hK0mom a0 Cd1 Cz ha0 hCd1.le hCz0
  exact ⟨fun om => aux_hcoer_Kcoer M H Kr ml Kone N rho0 Cd1 Cz a0 j om, hm, h1, hmom,
    aux_hcoer_clause_ae hd M Rm hH hH0 N hrho Cd1 hCd1 htr1 Cd2 hCd2 htr2 Kr hKr0 hKrMZ hKrK ml hml0
      hmlb b1 hb1 Kone hKone0 hKone j hrho3 Cz a0 hCzdef ha0def hfin⟩

end Paper
end
end
