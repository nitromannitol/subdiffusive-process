import SubdiffusiveProcess.PartProcess.GraphResolvent
import Mathlib.Topology.Order.MonotoneConvergence

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7

/-- Quadratic penalization converges to the constrained variational solution. -/
theorem quadratic_penalty_tendsto
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (E : DirichletForm.ClosedForm m)
    (T : Lp ℝ 2 m →L[ℝ] Y) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 m) (u : ℕ → Lp ℝ 2 m) (hu : ∀ n, u n ∈ E.domain)
    (heq : ∀ n v, v ∈ E.domain →
      α * inner ℝ (u n) v + E.form (u n) v +
        (n : ℝ) * inner ℝ (T (u n)) (T v) = inner ℝ f v)
    (h : Lp ℝ 2 m) (hh : h ∈ E.domain) (hTh : T h = 0)
    (hheq : ∀ v, v ∈ E.domain → T v = 0 →
      α * inner ℝ h v + E.form h v = inner ℝ f v) :
    Tendsto u atTop (𝓝 h) := by
  haveI := shCore E hα
  letI : NormedAddCommGroup (ShDom E α) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (ShDom E α) _ _ _ (shCore E hα)
  letI : InnerProductSpace ℝ (ShDom E α) :=
    InnerProductSpace.ofCore (shCore E hα).toCore
  haveI : CompleteSpace (ShDom E α) := complete_shiftedDomain E hα
  have hN : ∀ x : ShDom E α, ‖x‖ ^ 2 = α * ‖x.val‖ ^ 2 + E.form x.val x.val := by
    intro x
    rw [← real_inner_self_eq_norm_sq]
    change α * inner ℝ x.val x.val + E.form x.val x.val = _
    rw [real_inner_self_eq_norm_sq]
  let S : ShDom E α →L[ℝ] Lp ℝ 2 m := LinearMap.mkContinuous
    { toFun := ShDom.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (1 / Real.sqrt α) (by
      intro x
      have hx := hN x
      have hn := E.form_nonneg _ x.val_mem
      have hs := Real.sq_sqrt hα.le
      have hp := Real.sqrt_pos.2 hα
      change ‖x.val‖ ≤ _
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp]
      nlinarith [norm_nonneg x.val, norm_nonneg x])
  let z : ℕ → ShDom E α := fun n => ShDom.mk (u n) (hu n)
  let a : ℕ → ℝ := fun n => inner ℝ f (u n)
  have hz : ∀ (n : ℕ) (v : ShDom E α),
      inner ℝ (z n) v + (n : ℝ) * inner ℝ (T (u n)) (T v.val) = inner ℝ f v.val := by
    intro n v
    exact heq n v.val v.val_mem
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    have hn := hz n (z n)
    change inner ℝ (z n) (z n) + (n : ℝ) * inner ℝ (T (u n)) (T (u n)) = a n at hn
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hn
    nlinarith [sq_nonneg ‖z n‖,
      mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg ‖T (u n)‖)]
  have hdiff : ∀ k n, k ≤ n → ‖z k - z n‖ ^ 2 ≤ a k - a n := by
    intro k n hkn
    have hkk := hz k (z k)
    have hnn := hz n (z n)
    have hkn' := hz k (z n)
    change inner ℝ (z k) (z k) + (k : ℝ) * inner ℝ (T (u k)) (T (u k)) = a k at hkk
    change inner ℝ (z n) (z n) + (n : ℝ) * inner ℝ (T (u n)) (T (u n)) = a n at hnn
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hkk hnn
    have hsub := norm_sub_sq_real (z k) (z n)
    have hsubT := norm_sub_sq_real (T (u k)) (T (u n))
    change ‖z k‖ ^ 2 + (k : ℝ) * ‖T (u k)‖ ^ 2 = a k at hkk
    change ‖z n‖ ^ 2 + (n : ℝ) * ‖T (u n)‖ ^ 2 = a n at hnn
    change inner ℝ (z k) (z n) + (k : ℝ) * inner ℝ (T (u k)) (T (u n)) = a n at hkn'
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hn : (k : ℝ) ≤ n := Nat.cast_le.2 hkn
    nlinarith [mul_nonneg hk (sq_nonneg ‖T (u k) - T (u n)‖),
      mul_nonneg (sub_nonneg.2 hn) (sq_nonneg ‖T (u n)‖)]
  have hanti : Antitone a := fun k n hkn => by
    have := hdiff k n hkn
    nlinarith [sq_nonneg ‖z k - z n‖]
  have haC : CauchySeq a := (tendsto_atTop_ciInf hanti
    ⟨0, by rintro _ ⟨n, rfl⟩; exact ha n⟩).cauchySeq
  have hzC : CauchySeq z := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN'⟩ := Metric.cauchySeq_iff.1 haC (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun p hp q hq => ?_⟩
    have hsmall := hN' p hp q hq
    rw [Real.dist_eq] at hsmall
    have hb : ‖z p - z q‖ ^ 2 ≤ |a p - a q| := by
      rcases le_total p q with hpq | hqp
      · exact (hdiff p q hpq).trans (le_abs_self _)
      · rw [norm_sub_rev, abs_sub_comm]
        exact (hdiff q p hqp).trans (le_abs_self _)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (z p - z q)]
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hzC
  have huv : Tendsto u atTop (𝓝 v.val) := S.continuous.tendsto v |>.comp hv
  have hTv : T v.val = 0 := by
    have ht : Tendsto (fun n => ‖T (u n)‖ ^ 2) atTop (𝓝 (‖T v.val‖ ^ 2)) :=
      ((T.continuous.tendsto v.val).comp huv).norm.pow 2
    have hb : ∀ n : ℕ, (n : ℝ) * ‖T (u n)‖ ^ 2 ≤ a 0 := by
      intro n
      have hn := hz n (z n)
      change inner ℝ (z n) (z n) + (n : ℝ) * inner ℝ (T (u n)) (T (u n)) = a n at hn
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hn
      change ‖z n‖ ^ 2 + (n : ℝ) * ‖T (u n)‖ ^ 2 = a n at hn
      have := hanti (Nat.zero_le n)
      nlinarith [sq_nonneg ‖z n‖]
    have he : ‖T v.val‖ ^ 2 = 0 := by
      by_contra hne
      have hp : 0 < ‖T v.val‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have hlarge : ∀ᶠ n : ℕ in atTop, a 0 / (‖T v.val‖ ^ 2 / 2) < (n : ℝ) :=
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
          (eventually_gt_atTop _)
      have hpos : ∀ᶠ n in atTop, ‖T v.val‖ ^ 2 / 2 < ‖T (u n)‖ ^ 2 :=
        ht.eventually (eventually_gt_nhds (by linarith))
      obtain ⟨n, hn, hn'⟩ := (hlarge.and hpos).exists
      have hbig := (div_lt_iff₀ (by linarith : 0 < ‖T v.val‖ ^ 2 / 2)).1 hn
      have hmul := mul_le_mul_of_nonneg_left hn'.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have := hb n
      nlinarith
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (T v.val)])
  have heqv : ∀ b, b ∈ E.domain → T b = 0 →
      α * inner ℝ v.val b + E.form v.val b = inner ℝ f b := by
    intro b hb hTb
    have ht := (hv.inner tendsto_const_nhds :
      Tendsto (fun n => inner ℝ (z n) (ShDom.mk b hb)) atTop
        (𝓝 (inner ℝ v (ShDom.mk b hb))))
    have he : ∀ n, inner ℝ (z n) (ShDom.mk b hb) = inner ℝ f b := by
      intro n
      simpa only [ShDom.val_mk, hTb, inner_zero_right, mul_zero, add_zero] using hz n (ShDom.mk b hb)
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun n => (he n).symm))
  have heqh : v.val = h := by
    let b := v.val - h
    have hb : b ∈ E.domain := E.domain.sub_mem v.val_mem hh
    have hTb : T b = 0 := by simp [b, map_sub, hTv, hTh]
    have hzero : α * inner ℝ b b + E.form b b = 0 := by
      rw [show b = v.val - h by rfl, inner_sub_left, E.form_sub_left v.val_mem hh hb]
      have h1 := heqv b hb hTb
      have h2 := hheq b hb hTb
      linarith
    rw [real_inner_self_eq_norm_sq] at hzero
    have := E.form_nonneg _ hb
    have hs : ‖b‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hα).1 (by simpa using (show α * ‖b‖ ^ 2 ≤ 0 by linarith))
    have hnorm : ‖b‖ = 0 := by nlinarith [norm_nonneg b]
    exact sub_eq_zero.1 (norm_eq_zero.1 hnorm)
  simpa only [heqh] using huv

end SubdiffusiveProcess.PartProcess
