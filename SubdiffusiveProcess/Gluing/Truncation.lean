import Mathlib
import Homogenization.Sobolev.Truncation.Basic
import Homogenization.Sobolev.Truncation.H10Limit
import Homogenization.Sobolev.Truncation.LevelSets
import Homogenization.Sobolev.Truncation.WeakGradientLimit
import Homogenization.Sobolev.H1.Algebra.H1Function

/-!
# An `H¹` function that is continuous up to the boundary and vanishes there is `H¹₀`

For a bounded convex domain `U` and `w ∈ H¹(U)` which is continuous on `closure U` with
`w = 0` on `frontier U` (and `w = 0` outside `closure U`), the level-`ε` truncations
`max (w - ε) 0 - max (-w - ε) 0` are `H¹` functions supported in the compact set
`{ε ≤ |w|} ∩ closure U ⊆ U`, hence `H¹₀`, and they converge to `w` in `H¹`
(the gradient of `w` vanishes a.e. on `{w = 0}`).
-/

open MeasureTheory Set Filter Topology Homogenization
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Gluing

variable {d : ℕ}

/-- The level-`ε` truncation of an `H¹` function towards zero, as an `H¹` function. -/
theorem exists_h1_truncate {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ v : H1Function U,
      v.toFun = (fun x => max (u.toFun x - ε) 0 - max (-u.toFun x - ε) 0) ∧
      ∀ᵐ x ∂(volumeMeasureOn U), v.grad x = if ε < |u.toFun x| then u.grad x else 0 := by
  obtain ⟨A, hA1, hA2⟩ := exists_h1_max_sub_const hU u ε
  obtain ⟨B, hB1, hB2⟩ := exists_h1_max_sub_const hU (-u) ε
  refine ⟨A - B, ?_, ?_⟩
  · rw [H1Function.sub_toFun, hA1, hB1]
    funext x
    simp [H1Function.neg_toFun]
  · filter_upwards [hA2, hB2] with x hxA hxB
    rw [H1Function.sub_grad]
    show A.grad x - B.grad x = _
    rw [hxA, hxB]
    simp only [Set.indicator_apply, Set.mem_setOf_eq, H1Function.neg_grad, H1Function.neg_toFun]
    by_cases h1 : ε < u.toFun x
    · have h2 : ¬ ε < -u.toFun x := by
        intro h; linarith
      have h3 : ε < |u.toFun x| := lt_of_lt_of_le h1 (le_abs_self _)
      simp [h1, h2, h3]
    · by_cases h2 : ε < -u.toFun x
      · have h3 : ε < |u.toFun x| := by
          rw [← abs_neg]; exact lt_of_lt_of_le h2 (le_abs_self _)
        simp [h1, h2, h3]
      · have h3 : ¬ ε < |u.toFun x| := by
          rw [not_lt, abs_le]; constructor <;> linarith [not_lt.1 h1, not_lt.1 h2]
        simp [h1, h2, h3]

/-- **Continuous `H¹` functions vanishing on the boundary are `H¹₀`.** -/
theorem memH10_of_continuousOn_zero_frontier {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (w : H1Function U)
    (hc : ContinuousOn w.toFun (closure U)) (h0 : ∀ x ∈ frontier U, w.toFun x = 0)
    (hout : ∀ x, x ∉ closure U → w.toFun x = 0) : MemH10 U w.toFun := by
  classical
  haveI : IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose F hF1 hF2 using fun n => exists_h1_truncate hU w (hεpos n).le
  have hclosure : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  refine memH10_of_tendsto_H1 hU w F (fun n => ?_) ?_ ?_
  · -- compact support of the truncation
    have hcl : IsClosed (closure U ∩ {x | ε n ≤ |w.toFun x|}) :=
      hc.abs.preimage_isClosed_of_isClosed isClosed_closure (isClosed_Ici (a := ε n))
    have hK : IsCompact (closure U ∩ {x | ε n ≤ |w.toFun x|}) :=
      hclosure.of_isClosed_subset hcl inter_subset_left
    have hKU : closure U ∩ {x | ε n ≤ |w.toFun x|} ⊆ U := by
      rintro x ⟨hxc, hxe⟩
      by_contra hxU
      have hfr : x ∈ frontier U := by
        refine ⟨hxc, ?_⟩
        rwa [hU.isOpen.interior_eq]
      have := h0 x hfr
      have hxe' : ε n ≤ |w.toFun x| := hxe
      rw [this, abs_zero] at hxe'
      linarith [hεpos n]
    refine memH10_of_compactSupport hU (F n) hK hKU ?_
    intro x hx
    rw [hF1 n]
    dsimp only
    by_cases hxc : x ∈ closure U
    · have hlt : |w.toFun x| < ε n := by
        by_contra hge
        exact hx ⟨hxc, not_lt.1 hge⟩
      rw [abs_lt] at hlt
      have e1 : max (w.toFun x - ε n) 0 = 0 := max_eq_right (by linarith)
      have e2 : max (-w.toFun x - ε n) 0 = 0 := max_eq_right (by linarith)
      simp [e1, e2]
    · rw [hout x hxc]
      simp only [neg_zero, zero_sub, sub_self]
  · -- convergence of the values
    have hbd : ∀ n, ∀ x, ‖w.toFun x - (F n).toFun x‖ ≤ ε n := by
      intro n x
      rw [hF1 n, Real.norm_eq_abs]
      dsimp only
      set t := w.toFun x
      have hpos := hεpos n
      by_cases h1 : ε n < t
      · have e1 : max (t - ε n) 0 = t - ε n := max_eq_left (by linarith)
        have e2 : max (-t - ε n) 0 = 0 := max_eq_right (by linarith)
        rw [e1, e2, abs_le]; constructor <;> linarith
      · by_cases h2 : ε n < -t
        · have e1 : max (t - ε n) 0 = 0 := max_eq_right (by linarith)
          have e2 : max (-t - ε n) 0 = -t - ε n := max_eq_left (by linarith)
          rw [e1, e2, abs_le]; constructor <;> linarith
        · have e1 : max (t - ε n) 0 = 0 := max_eq_right (by linarith)
          have e2 : max (-t - ε n) 0 = 0 := max_eq_right (by linarith)
          rw [e1, e2, abs_le]; constructor <;> linarith [not_lt.1 h1, not_lt.1 h2]
    have hle : ∀ n, eLpNorm (fun x => w.toFun x - (F n).toFun x) 2 (volumeMeasureOn U) ≤
        (volumeMeasureOn U) univ ^ ((2 : ℝ≥0∞).toReal)⁻¹ * ENNReal.ofReal (ε n) := fun n =>
      eLpNorm_le_of_ae_bound (Eventually.of_forall (hbd n))
    have hfin : (volumeMeasureOn U) univ ^ ((2 : ℝ≥0∞).toReal)⁻¹ ≠ ⊤ := by
      refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
    have hlim : Tendsto (fun n => (volumeMeasureOn U) univ ^ ((2 : ℝ≥0∞).toReal)⁻¹ *
        ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal hεlim
        simpa using this
      have := ENNReal.Tendsto.const_mul h1 (Or.inr hfin)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => zero_le _) hle
  · -- convergence of the gradients
    intro i
    have hgi := w.gradMemL2 i
    have hsw := fun n => eLpNorm_sub_swap (μ := volumeMeasureOn U)
      (fun x => (F n).grad x i) (fun x => w.grad x i) (p := 2)
    have hlevel := grad_ae_zero_on_level_set hU w 0
    have hall : ∀ᵐ x ∂(volumeMeasureOn U), ∀ n, (F n).grad x = if ε n < |w.toFun x| then w.grad x else 0 :=
      ae_all_iff.2 hF2
    have key := tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
      (μ := volumeMeasureOn U) (f := fun n x => (F n).grad x i) (g := fun x => w.grad x i)
      (h := fun x => ‖w.grad x i‖)
      (fun n => ((F n).gradMemL2 i).1) hgi hgi.norm
      (fun n => by
        filter_upwards [hF2 n] with x hx
        rw [hx]
        by_cases hlt : ε n < |w.toFun x| <;> simp [hlt])
      (by
        filter_upwards [hall, hlevel] with x hx hx0
        by_cases hz : w.toFun x = 0
        · have hg0 : w.grad x = 0 := hx0 hz
          have : ∀ n, (F n).grad x i = 0 := by
            intro n
            rw [hx n]
            by_cases hlt : ε n < |w.toFun x| <;> simp [hlt, hg0]
          simp only [this, hg0, Pi.zero_apply]
          exact tendsto_const_nhds
        · have hpos : 0 < |w.toFun x| := abs_pos.2 hz
          have hev : ∀ᶠ n in atTop, ε n < |w.toFun x| :=
            (hεlim.eventually (gt_mem_nhds hpos))
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hev] with n hn
          rw [hx n, if_pos hn])
    refine (key.congr (fun n => (hsw n))).congr' ?_ |>.congr fun n => rfl
    exact Eventually.of_forall fun n => rfl

end SubdiffusiveProcess.Gluing
