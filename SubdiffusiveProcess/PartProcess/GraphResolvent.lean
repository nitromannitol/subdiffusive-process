module

public import SubdiffusiveProcess.PartProcess.Data
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7
variable {X : Type*} [MeasurableSpace X] {m : Measure X}

theorem complete_shiftedDomain (E : DirichletForm.ClosedForm m) {α : ℝ} (hα : 0 < α) :
    letI : NormedAddCommGroup (ShDom E α) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℝ (ShDom E α) _ _ _ (shCore E hα)
    letI : InnerProductSpace ℝ (ShDom E α) :=
      InnerProductSpace.ofCore (shCore E hα).toCore
    CompleteSpace (ShDom E α) := by
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
  exact inferInstance

theorem exists_domainResolvent (E : DirichletForm.ClosedForm m)
    (D : Submodule ℝ (Lp ℝ 2 m)) (hD : GraphClosed E D) (α : ℝ) (hα : 0 < α) :
    ∃ G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m, IsDomainResolvent E D α G := by
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
  have hgraph : ∀ x : ShDom E α, E.energyNormSq x.val ≤
      (1 / min α 1) * ‖x‖ ^ 2 := by
    intro x
    rw [hN, DirichletForm.ClosedForm.energyNormSq]
    have hmin : 0 < min α 1 := lt_min hα one_pos
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hmin]
    have hn := E.form_nonneg _ x.val_mem
    have h1 := min_le_left α 1
    have h2 := min_le_right α 1
    nlinarith [sq_nonneg ‖x.val‖]
  let D' : Submodule ℝ (ShDom E α) :=
    { carrier := {x | x.val ∈ D}
      zero_mem' := D.zero_mem
      add_mem' := fun {x y} hx hy => D.add_mem hx hy
      smul_mem' := fun c x hx => D.smul_mem c hx }
  have hclosed : IsClosed (D' : Set (ShDom E α)) := by
    refine IsSeqClosed.isClosed fun u v hu hv => ?_
    have hn : Tendsto (fun n => ‖u n - v‖ ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hv).pow 2
    apply hD.2 (fun n => (u n).val) v.val hu v.val_mem
    refine squeeze_zero (fun n => E.energyNormSq_nonneg
      (E.domain.sub_mem (u n).val_mem v.val_mem)) (fun n => ?_)
      (by simpa using hn.const_mul (1 / min α 1))
    simpa only [ShDom.val_sub, one_div] using hgraph (u n - v)
  haveI : CompleteSpace D' := hclosed.completeSpace_coe
  haveI : D'.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace D'
  obtain ⟨R, hR⟩ := exists_isResolvent E hα
  let W : Lp ℝ 2 m → ShDom E α := fun f =>
    D'.starProjection (ShDom.mk (R f) (hR f).1)
  have hW : ∀ f, (W f).val ∈ D := fun f =>
    D'.starProjection_apply_mem (ShDom.mk (R f) (hR f).1)
  have heq : ∀ f, ∀ v ∈ D,
      α * inner ℝ (W f).val v + E.form (W f).val v = inner ℝ f v := by
    intro f v hv
    have hv' : ShDom.mk (α := α) v (hD.1 hv) ∈ D' := hv
    have ho := (Submodule.mem_orthogonal D'
      (ShDom.mk (R f) (hR f).1 - W f)).1
      (D'.sub_starProjection_mem_orthogonal (ShDom.mk (R f) (hR f).1)) _ hv'
    rw [real_inner_comm] at ho
    change α * inner ℝ (R f - (W f).val) v + E.form (R f - (W f).val) v = 0 at ho
    rw [inner_sub_left, E.form_sub_left (hR f).1 (hD.1 (hW f)) (hD.1 hv)] at ho
    have hr := (hR f).2 v (hD.1 hv)
    linarith
  have hadd : ∀ f g, (W (f + g)).val = (W f).val + (W g).val := by
    intro f g
    have hi : ShDom.mk (α := α) (R (f + g)) (hR (f + g)).1 =
        ShDom.mk (R f) (hR f).1 + ShDom.mk (R g) (hR g).1 := by
      apply ShDom.ext
      exact R.map_add f g
    change (D'.starProjection _).val = _
    rw [hi, map_add]
    rfl
  have hsmul : ∀ (a : ℝ) f, (W (a • f)).val = a • (W f).val := by
    intro a f
    have hi : ShDom.mk (α := α) (R (a • f)) (hR (a • f)).1 =
        a • ShDom.mk (R f) (hR f).1 := by
      apply ShDom.ext
      exact R.map_smul a f
    change (D'.starProjection _).val = _
    rw [hi, map_smul]
    rfl
  let G0 : Lp ℝ 2 m →ₗ[ℝ] Lp ℝ 2 m :=
    { toFun := fun f => (W f).val
      map_add' := hadd
      map_smul' := hsmul }
  have hbound : ∀ f, ‖G0 f‖ ≤ (1 / α) * ‖f‖ := by
    intro f
    have he := heq f (W f).val (hW f)
    rw [real_inner_self_eq_norm_sq] at he
    have hnonneg := E.form_nonneg _ (hD.1 (hW f))
    have hinner := real_inner_le_norm f (W f).val
    change ‖(W f).val‖ ≤ _
    rcases (norm_nonneg (W f).val).eq_or_lt with hzero | hpos
    · rw [← hzero]
      positivity
    · have hb : α * ‖(W f).val‖ ≤ ‖f‖ := by
        by_contra hn
        push_neg at hn
        nlinarith [mul_lt_mul_of_pos_left hn hpos]
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hα]
      simpa only [mul_comm] using hb
  exact ⟨G0.mkContinuous (1 / α) hbound, fun f => ⟨hW f, heq f⟩⟩

theorem domainResolvent_unique (E : DirichletForm.ClosedForm m)
    (D : Submodule ℝ (Lp ℝ 2 m)) (hD : D ≤ E.domain) (α : ℝ) (hα : 0 < α)
    (G H : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hG : IsDomainResolvent E D α G) (hH : IsDomainResolvent E D α H) : G = H := by
  apply ContinuousLinearMap.ext
  intro f
  have hg := hG f
  have hh := hH f
  have hz : G f - H f ∈ D := D.sub_mem hg.1 hh.1
  have hze : G f - H f ∈ E.domain := hD hz
  have hzero : α * inner ℝ (G f - H f) (G f - H f) +
      E.form (G f - H f) (G f - H f) = 0 := by
    rw [inner_sub_left, E.form_sub_left (hD hg.1) (hD hh.1) hze]
    have h1 := hg.2 _ hz
    have h2 := hh.2 _ hz
    linarith
  rw [real_inner_self_eq_norm_sq] at hzero
  have hnorm : ‖G f - H f‖ ^ 2 = 0 := by
    have := E.form_nonneg _ hze
    nlinarith [sq_nonneg ‖G f - H f‖]
  exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg (G f - H f)]))

end SubdiffusiveProcess.PartProcess
