import SubdiffusiveProcess.DirichletForm.Resolvent
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Every closed form has a resolvent

For a closed form `E` on `L²(m)` and `α > 0` the domain with the inner product
`α⟪u, v⟫ + E(u, v)` is a Hilbert space (this is the closedness of `E`); the Riesz representation of
`v ↦ ⟪f, v⟫` is the resolvent `G_α f` (Fukushima–Oshima–Takeda, Thm 1.3.1's Lax–Milgram step).
-/
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.E7
open DirichletForm

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- The domain of a closed form with the inner product `α⟪u,v⟫ + E(u,v)` (type synonym). -/
def ShDom (E : ClosedForm m) (α : ℝ) : Type _ := ↥E.domain

instance (E : ClosedForm m) (α : ℝ) : AddCommGroup (ShDom E α) :=
  inferInstanceAs (AddCommGroup ↥E.domain)

instance (E : ClosedForm m) (α : ℝ) : Module ℝ (ShDom E α) :=
  inferInstanceAs (Module ℝ ↥E.domain)

namespace ShDom

variable {E : ClosedForm m} {α : ℝ}

def val (u : ShDom E α) : Lp ℝ 2 m := (u : ↥E.domain).1

theorem val_mem (u : ShDom E α) : u.val ∈ E.domain := (u : ↥E.domain).2

def mk (x : Lp ℝ 2 m) (hx : x ∈ E.domain) : ShDom E α := (⟨x, hx⟩ : ↥E.domain)

@[simp] theorem val_mk (x : Lp ℝ 2 m) (hx : x ∈ E.domain) : (mk (α := α) x hx).val = x := rfl

@[simp] theorem val_add (u v : ShDom E α) : (u + v).val = u.val + v.val := rfl
@[simp] theorem val_sub (u v : ShDom E α) : (u - v).val = u.val - v.val := rfl
@[simp] theorem val_neg (u : ShDom E α) : (-u).val = -u.val := rfl
@[simp] theorem val_smul (r : ℝ) (u : ShDom E α) : (r • u).val = r • u.val := rfl
@[simp] theorem val_zero : (0 : ShDom E α).val = 0 := rfl

theorem ext {u v : ShDom E α} (h : u.val = v.val) : u = v := Subtype.ext h

end ShDom

/-- The shifted inner product core. -/
def shCore (E : ClosedForm m) {α : ℝ} (hα : 0 < α) : InnerProductSpace.Core ℝ (ShDom E α) where
  inner u v := α * inner ℝ u.val v.val + E.form u.val v.val
  conj_inner_symm u v := by
    show (starRingEnd ℝ) (α * inner ℝ v.val u.val + E.form v.val u.val) =
      α * inner ℝ u.val v.val + E.form u.val v.val
    rw [conj_trivial, real_inner_comm, E.form_symm _ v.val_mem _ u.val_mem]
  re_inner_nonneg u := by
    show 0 ≤ RCLike.re (α * inner ℝ u.val u.val + E.form u.val u.val)
    rw [RCLike.re_to_real]
    exact add_nonneg (mul_nonneg hα.le real_inner_self_nonneg) (E.form_nonneg _ u.val_mem)
  add_left u v w := by
    show α * inner ℝ (u + v).val w.val + E.form (u + v).val w.val =
      (α * inner ℝ u.val w.val + E.form u.val w.val) +
        (α * inner ℝ v.val w.val + E.form v.val w.val)
    rw [ShDom.val_add, inner_add_left, E.form_add_left _ u.val_mem _ v.val_mem _ w.val_mem]
    ring
  smul_left u v r := by
    show α * inner ℝ (r • u).val v.val + E.form (r • u).val v.val =
      (starRingEnd ℝ) r * (α * inner ℝ u.val v.val + E.form u.val v.val)
    rw [ShDom.val_smul, real_inner_smul_left, E.form_smul_left _ _ u.val_mem _ v.val_mem, conj_trivial]
    ring
  definite u hu := by
    have hu' : α * inner ℝ u.val u.val + E.form u.val u.val = 0 := hu
    have h1 : 0 ≤ α * inner ℝ u.val u.val :=
      mul_nonneg hα.le real_inner_self_nonneg
    have h2 : 0 ≤ E.form u.val u.val := E.form_nonneg _ u.val_mem
    have h3 : inner ℝ u.val u.val = 0 := by
      have : α * inner ℝ u.val u.val = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hα.ne'
      · exact h
    exact ShDom.ext (inner_self_eq_zero.1 h3)


/-- **Every closed form has a resolvent at every positive parameter** (Riesz representation on the
Hilbert space `(D(E), α⟪·,·⟫ + E)`). -/
theorem exists_isResolvent (E : ClosedForm m) {α : ℝ} (hα : 0 < α) :
    ∃ G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m, IsResolvent E α G := by
  haveI := shCore E hα
  letI : NormedAddCommGroup (ShDom E α) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (ShDom E α) _ _ _ (shCore E hα)
  letI : InnerProductSpace ℝ (ShDom E α) :=
    InnerProductSpace.ofCore (shCore E hα).toCore
  have hN : ∀ x : ShDom E α, ‖x‖ ^ 2 = α * ‖x.val‖ ^ 2 + E.form x.val x.val := fun x => by
    rw [← real_inner_self_eq_norm_sq]
    show α * inner ℝ x.val x.val + E.form x.val x.val = _
    rw [real_inner_self_eq_norm_sq]
  have hE0 : ∀ x : ShDom E α, 0 ≤ E.form x.val x.val := fun x => E.form_nonneg _ x.val_mem
  haveI : CompleteSpace (ShDom E α) := by
    refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    have hc0 : 0 < min α 1 := lt_min hα one_pos
    obtain ⟨w, hw, hwt⟩ := E.complete (fun n => (u n).val) (fun n => (u n).val_mem) (by
      intro ε hε
      obtain ⟨N, hN'⟩ := Metric.cauchySeq_iff.1 hu (Real.sqrt (ε * min α 1)) (Real.sqrt_pos.2
        (mul_pos hε hc0))
      refine ⟨N, fun p hp q hq => ?_⟩
      have hd := hN' p hp q hq
      rw [dist_eq_norm] at hd
      have hsq : ‖u p - u q‖ ^ 2 < ε * min α 1 := by
        have := pow_lt_pow_left₀ hd (norm_nonneg _) (two_ne_zero)
        rwa [Real.sq_sqrt (mul_pos hε hc0).le] at this
      have h1 := hN (u p - u q)
      simp only [ShDom.val_sub] at h1
      have h2 : min α 1 * (E.form ((u p).val - (u q).val) ((u p).val - (u q).val) +
          ‖(u p).val - (u q).val‖ ^ 2) ≤ ‖u p - u q‖ ^ 2 := by
        rw [h1]
        have := hE0 (u p - u q)
        simp only [ShDom.val_sub] at this
        nlinarith [min_le_left α 1, min_le_right α 1, sq_nonneg ‖(u p).val - (u q).val‖]
      nlinarith)
    refine ⟨ShDom.mk w hw, ?_⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun n => ‖u n - ShDom.mk w hw‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_)
        (by simpa using hwt.const_mul (max α 1))
      rw [hN]
      simp only [ShDom.val_sub, ShDom.val_mk]
      have := hE0 (u n - ShDom.mk w hw)
      simp only [ShDom.val_sub, ShDom.val_mk] at this
      nlinarith [le_max_left α 1, le_max_right α 1, sq_nonneg ‖(u n).val - w‖]
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp]
    exact Real.sqrt_sq (norm_nonneg _)
  -- the representer
  have hex : ∀ f : Lp ℝ 2 m, ∃ w : ShDom E α, ∀ v : ShDom E α, inner ℝ w v = inner ℝ f v.val := by
    intro f
    let ℓ : ShDom E α →ₗ[ℝ] ℝ :=
      { toFun := fun v => inner ℝ f v.val
        map_add' := fun v w => by simp [inner_add_right]
        map_smul' := fun r v => by simp [real_inner_smul_right] }
    have hbd : ∀ v : ShDom E α, ‖ℓ v‖ ≤ (‖f‖ / Real.sqrt α) * ‖v‖ := by
      intro v
      have h1 : ‖ℓ v‖ ≤ ‖f‖ * ‖v.val‖ := by
        rw [Real.norm_eq_abs]
        exact abs_real_inner_le_norm f v.val
      have h2 : ‖v.val‖ * Real.sqrt α ≤ ‖v‖ := by
        have hsq : (‖v.val‖ * Real.sqrt α) ^ 2 ≤ ‖v‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hα.le, hN v]
          nlinarith [hE0 v]
        exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 hsq
      have hsα : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
      calc ‖ℓ v‖ ≤ ‖f‖ * ‖v.val‖ := h1
        _ = (‖f‖ / Real.sqrt α) * (‖v.val‖ * Real.sqrt α) := by field_simp
        _ ≤ (‖f‖ / Real.sqrt α) * ‖v‖ :=
            mul_le_mul_of_nonneg_left h2 (div_nonneg (norm_nonneg _) hsα.le)
    let ℓc : ShDom E α →L[ℝ] ℝ := ℓ.mkContinuous (‖f‖ / Real.sqrt α) hbd
    refine ⟨(InnerProductSpace.toDual ℝ (ShDom E α)).symm ℓc, fun v => ?_⟩
    exact InnerProductSpace.toDual_symm_apply
  choose W hW using hex
  have hlin_add : ∀ f g, W (f + g) = W f + W g := fun f g => by
    refine ext_inner_right ℝ fun v => ?_
    rw [inner_add_left, hW, hW, hW, inner_add_left]
  have hlin_smul : ∀ (r : ℝ) f, W (r • f) = r • W f := fun r f => by
    refine ext_inner_right ℝ fun v => ?_
    rw [inner_smul_left, hW, hW, inner_smul_left]
  let G0 : Lp ℝ 2 m →ₗ[ℝ] Lp ℝ 2 m :=
    { toFun := fun f => (W f).val
      map_add' := fun f g => by rw [hlin_add]; rfl
      map_smul' := fun r f => by rw [hlin_smul]; rfl }
  have hbound : ∀ f, ‖G0 f‖ ≤ (1 / α) * ‖f‖ := by
    intro f
    have h1 : ‖W f‖ ^ 2 = inner ℝ f (W f).val := by
      rw [← real_inner_self_eq_norm_sq, hW]
    have h2 : α * ‖(W f).val‖ ^ 2 ≤ ‖W f‖ ^ 2 := by
      rw [hN]; nlinarith [hE0 (W f)]
    have h3 : inner ℝ f (W f).val ≤ ‖f‖ * ‖(W f).val‖ := real_inner_le_norm _ _
    show ‖(W f).val‖ ≤ _
    rcases (norm_nonneg (W f).val).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have : α * ‖(W f).val‖ ≤ ‖f‖ := by
        by_contra hcon
        push_neg at hcon
        nlinarith [mul_lt_mul_of_pos_left hcon hpos]
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hα]
      linarith
  refine ⟨G0.mkContinuous (1 / α) hbound, fun f => ⟨(W f).val_mem, fun v hv => ?_⟩⟩
  have := hW f (ShDom.mk v hv)
  exact this

end SubdiffusiveProcess.E7
