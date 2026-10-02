import SubdiffusiveProcess.DirichletForm.Energy
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Energy-orthogonal projection for a coercive closed form

Let `E` be a closed form on `L²(m)` that is coercive, `‖v‖² ≤ C E(v,v)` on `D(E)`.  Then `D(E)` with the inner
product `E(u, v)` is a Hilbert space (`CfDom`): the energy norm `E(u,u)^{1/2}` is equivalent to the graph norm
`E₁(u)^{1/2}` for which `D(E)` is complete.  A subspace `V ≤ D(E)` that is closed for `E₁` is closed in this Hilbert
space, so the Hilbert projection theorem gives the unique energy-orthogonal representative
(`exists_unique_energy_orthogonal`).

The Riesz/Hilbert-space structure follows the construction of the shifted domain used for the resolvent of a closed
form (Fukushima–Oshima–Takeda, Thm 1.3.1).
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.CoerciveProjection

open DirichletForm

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- The domain of a closed form (type synonym carrying the energy inner product). -/
def CfDom (E : ClosedForm m) : Type _ := ↥E.domain

instance (E : ClosedForm m) : AddCommGroup (CfDom E) :=
  inferInstanceAs (AddCommGroup ↥E.domain)

instance (E : ClosedForm m) : Module ℝ (CfDom E) :=
  inferInstanceAs (Module ℝ ↥E.domain)

namespace CfDom

variable {E : ClosedForm m}

/-- The underlying element of `L²(m)`. -/
def val (u : CfDom E) : Lp ℝ 2 m := (u : ↥E.domain).1

theorem val_mem (u : CfDom E) : u.val ∈ E.domain := (u : ↥E.domain).2

/-- Build an element of `CfDom E` from an element of the domain. -/
def mk (x : Lp ℝ 2 m) (hx : x ∈ E.domain) : CfDom E := (⟨x, hx⟩ : ↥E.domain)

@[simp] theorem val_mk (x : Lp ℝ 2 m) (hx : x ∈ E.domain) : (mk x hx).val = x := rfl

@[simp] theorem val_add (u v : CfDom E) : (u + v).val = u.val + v.val := rfl
@[simp] theorem val_sub (u v : CfDom E) : (u - v).val = u.val - v.val := rfl
@[simp] theorem val_neg (u : CfDom E) : (-u).val = -u.val := rfl
@[simp] theorem val_smul (r : ℝ) (u : CfDom E) : (r • u).val = r • u.val := rfl
@[simp] theorem val_zero : (0 : CfDom E).val = 0 := rfl

theorem ext {u v : CfDom E} (h : u.val = v.val) : u = v := Subtype.ext h

end CfDom

/-- The energy inner product `E(u, v)` on the domain of a coercive closed form. -/
def cfCore (E : ClosedForm m) (C : ℝ) (hcoerc : ∀ v ∈ E.domain, ‖v‖ ^ 2 ≤ C * E.form v v) :
    InnerProductSpace.Core ℝ (CfDom E) where
  inner u v := E.form u.val v.val
  conj_inner_symm u v := by
    show (starRingEnd ℝ) (E.form v.val u.val) = E.form u.val v.val
    rw [conj_trivial, E.form_symm _ v.val_mem _ u.val_mem]
  re_inner_nonneg u := by
    show 0 ≤ RCLike.re (E.form u.val u.val)
    rw [RCLike.re_to_real]
    exact E.form_nonneg _ u.val_mem
  add_left u v w := by
    show E.form (u + v).val w.val = E.form u.val w.val + E.form v.val w.val
    rw [CfDom.val_add]
    exact E.form_add_left _ u.val_mem _ v.val_mem _ w.val_mem
  smul_left u v r := by
    show E.form (r • u).val v.val = (starRingEnd ℝ) r * E.form u.val v.val
    rw [CfDom.val_smul, conj_trivial]
    exact E.form_smul_left _ _ u.val_mem _ v.val_mem
  definite u hu := by
    have hu' : E.form u.val u.val = 0 := hu
    have h1 : ‖u.val‖ ^ 2 ≤ 0 := by simpa [hu'] using hcoerc u.val u.val_mem
    have h2 : ‖u.val‖ = 0 := by nlinarith [norm_nonneg u.val, sq_nonneg ‖u.val‖]
    exact CfDom.ext (norm_eq_zero.mp h2)


/-- **Hilbert projection in the energy space of a coercive closed form.**  If `V ≤ D(E)` is closed for the graph
norm `E₁` and `E` is coercive, then for every `b ∈ D(E)` there is exactly one `u ∈ D(E)` with `u - b ∈ V` and
`E(u, v) = 0` for all `v ∈ V`. -/
theorem exists_unique_energy_orthogonal (E : ClosedForm m) (V : Submodule ℝ (Lp ℝ 2 m))
    (_hV : V ≤ E.domain)
    (hclosed : ∀ (v : ℕ → Lp ℝ 2 m) (w : Lp ℝ 2 m),
      (∀ n, v n ∈ V) → w ∈ E.domain →
      Tendsto (fun n => E.energyNormSq (v n - w)) atTop (𝓝 0) → w ∈ V)
    (C : ℝ) (hC : 0 < C) (hcoerc : ∀ v ∈ E.domain, ‖v‖ ^ 2 ≤ C * E.form v v)
    (b : Lp ℝ 2 m) (hb : b ∈ E.domain) :
    ∃! u : Lp ℝ 2 m, u ∈ E.domain ∧ u - b ∈ V ∧ ∀ v ∈ V, E.form u v = 0 := by
  haveI := cfCore E C hcoerc
  letI : NormedAddCommGroup (CfDom E) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (CfDom E) _ _ _ (cfCore E C hcoerc)
  letI : InnerProductSpace ℝ (CfDom E) :=
    InnerProductSpace.ofCore (cfCore E C hcoerc).toCore
  have hN : ∀ x : CfDom E, ‖x‖ ^ 2 = E.form x.val x.val := fun x => by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  have hE0 : ∀ x : CfDom E, 0 ≤ E.form x.val x.val := fun x => E.form_nonneg _ x.val_mem
  -- the energy norm dominates the graph norm up to the constant `1 + C`
  have hgraph : ∀ x : CfDom E, E.energyNormSq x.val ≤ (1 + C) * ‖x‖ ^ 2 := by
    intro x
    rw [hN]
    have := hcoerc x.val x.val_mem
    simp only [ClosedForm.energyNormSq]
    nlinarith [hE0 x]
  have hC1 : 0 < 1 + C := by linarith
  haveI : CompleteSpace (CfDom E) := by
    refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    obtain ⟨w, hw, hwt⟩ := E.complete (fun n => (u n).val) (fun n => (u n).val_mem) (by
      intro ε hε
      obtain ⟨N, hN'⟩ := Metric.cauchySeq_iff.1 hu (Real.sqrt (ε / (1 + C)))
        (Real.sqrt_pos.2 (div_pos hε hC1))
      refine ⟨N, fun p hp q hq => ?_⟩
      have hd := hN' p hp q hq
      rw [dist_eq_norm] at hd
      have hsq : ‖u p - u q‖ ^ 2 < ε / (1 + C) := by
        have := pow_lt_pow_left₀ hd (norm_nonneg _) (two_ne_zero)
        rwa [Real.sq_sqrt (div_pos hε hC1).le] at this
      have h1 := hgraph (u p - u q)
      simp only [CfDom.val_sub, ClosedForm.energyNormSq] at h1
      have h2 : (1 + C) * ‖u p - u q‖ ^ 2 < ε := by
        have := mul_lt_mul_of_pos_left hsq hC1
        rwa [mul_div_cancel₀ _ hC1.ne'] at this
      linarith)
    refine ⟨CfDom.mk w hw, ?_⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun n => ‖u n - CfDom.mk w hw‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hwt
      rw [hN]
      simp only [CfDom.val_sub, CfDom.val_mk]
      nlinarith [sq_nonneg ‖(u n).val - w‖]
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp]
    exact Real.sqrt_sq (norm_nonneg _)
  -- the subspace `V` inside the Hilbert space
  let V' : Submodule ℝ (CfDom E) :=
    { carrier := {x | x.val ∈ V}
      add_mem' := fun {x y} hx hy => by
        show (x + y).val ∈ V
        rw [CfDom.val_add]; exact V.add_mem hx hy
      zero_mem' := by
        show (0 : CfDom E).val ∈ V
        rw [CfDom.val_zero]; exact V.zero_mem
      smul_mem' := fun c x hx => by
        show (c • x).val ∈ V
        rw [CfDom.val_smul]; exact V.smul_mem c hx }
  have hV'closed : IsClosed (V' : Set (CfDom E)) := by
    refine IsSeqClosed.isClosed fun x y hx hxy => ?_
    have hn : Tendsto (fun n => ‖x n - y‖) atTop (𝓝 0) := by
      rw [← tendsto_iff_norm_sub_tendsto_zero]; exact hxy
    have hn2 : Tendsto (fun n => ‖x n - y‖ ^ 2) atTop (𝓝 0) := by
      simpa using hn.pow 2
    refine hclosed (fun n => (x n).val) y.val (fun n => hx n) y.val_mem ?_
    refine squeeze_zero (fun n => ?_) (fun n => ?_) (by simpa using hn2.const_mul (1 + C))
    · have := E.energyNormSq_nonneg (E.domain.sub_mem (x n).val_mem y.val_mem)
      exact this
    · have := hgraph (x n - y)
      simpa only [CfDom.val_sub] using this
  haveI : CompleteSpace V' := hV'closed.completeSpace_coe
  haveI : V'.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace V'
  let x0 : CfDom E := CfDom.mk b hb
  let p : CfDom E := V'.starProjection x0
  have hp : p ∈ V' := V'.starProjection_apply_mem x0
  have horth : x0 - p ∈ V'ᗮ := V'.sub_starProjection_mem_orthogonal x0
  refine ⟨(x0 - p).val, ⟨(x0 - p).val_mem, ?_, ?_⟩, ?_⟩
  · -- `u - b = -p ∈ V`
    have : (x0 - p).val - b = -p.val := by
      simp [x0]
    rw [this]
    exact V.neg_mem hp
  · intro v hv
    have hv' : CfDom.mk v (_hV hv) ∈ V' := hv
    have := (Submodule.mem_orthogonal V' (x0 - p)).1 horth _ hv'
    have h2 : E.form v (x0 - p).val = 0 := this
    rw [E.form_symm _ (x0 - p).val_mem _ (_hV hv)]
    exact h2
  · rintro y ⟨hy, hyb, hyv⟩
    -- uniqueness: the difference lies in `V` and is energy-orthogonal to itself
    have hd : y - (x0 - p).val ∈ V := by
      have h1 : (x0 - p).val - b ∈ V := by
        have : (x0 - p).val - b = -p.val := by simp [x0]
        rw [this]; exact V.neg_mem hp
      have := V.sub_mem hyb h1
      simpa using this
    have hdd : y - (x0 - p).val ∈ E.domain := E.domain.sub_mem hy (x0 - p).val_mem
    have h0 : E.form (y - (x0 - p).val) (y - (x0 - p).val) = 0 := by
      have e1 := hyv _ hd
      have e2 : E.form (x0 - p).val (y - (x0 - p).val) = 0 := by
        rw [E.form_symm _ (x0 - p).val_mem _ hdd]
        have hv' : CfDom.mk (y - (x0 - p).val) (_hV hd) ∈ V' := hd
        exact (Submodule.mem_orthogonal V' (x0 - p)).1 horth _ hv'
      rw [E.form_sub_left hy (x0 - p).val_mem hdd, e1, e2]
      ring
    have h1 : ‖y - (x0 - p).val‖ ^ 2 ≤ 0 := by
      have := hcoerc _ hdd
      rw [h0] at this
      simpa using this
    have h2 : ‖y - (x0 - p).val‖ = 0 := by nlinarith [norm_nonneg (y - (x0 - p).val), sq_nonneg ‖y - (x0 - p).val‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)

end SubdiffusiveProcess.CoerciveProjection
