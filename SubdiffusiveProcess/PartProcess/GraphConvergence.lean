import SubdiffusiveProcess.PartProcess.GraphResolvent

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7

/-- Variational resolvents converge under an increasing graph-dense exhaustion. -/
theorem domainResolvent_tendsto {X : Type*} [MeasurableSpace X] {m : Measure X}
    (E : DirichletForm.ClosedForm m) (D : Submodule ℝ (Lp ℝ 2 m))
    (Dn : ℕ → Submodule ℝ (Lp ℝ 2 m)) (hDn : ∀ n, Dn n ≤ D)
    (hdense : ∀ u ∈ D, ∀ ε : ℝ, 0 < ε →
      ∃ n v, v ∈ Dn n ∧ E.energyNormSq (u - v) < ε)
    (hmono : Monotone Dn) (hD : GraphClosed E D)
    (α : ℝ) (hα : 0 < α)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (hG : IsDomainResolvent E D α G)
    (Gn : ℕ → Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hGn : ∀ n, IsDomainResolvent E (Dn n) α (Gn n)) :
    ∀ f, Tendsto (fun n => Gn n f) atTop (𝓝 (G f)) := by
  haveI := shCore E hα
  letI : NormedAddCommGroup (ShDom E α) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (ShDom E α) _ _ _ (shCore E hα)
  letI : InnerProductSpace ℝ (ShDom E α) :=
    InnerProductSpace.ofCore (shCore E hα).toCore
  have hN : ∀ x : ShDom E α, ‖x‖ ^ 2 = α * ‖x.val‖ ^ 2 + E.form x.val x.val := by
    intro x
    rw [← real_inner_self_eq_norm_sq]
    change α * inner ℝ x.val x.val + E.form x.val x.val = _
    rw [real_inner_self_eq_norm_sq]
  intro f
  have hu := (hG f).1
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, v, hv, happ⟩ := hdense (G f) hu
    (α * ε ^ 2 / (max α 1 + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hvn : v ∈ Dn n := hmono hn hv
  have hve : v ∈ E.domain := hD.1 (hDn N hv)
  have hune : Gn n f ∈ E.domain := hD.1 (hDn n (hGn n f).1)
  let y : ShDom E α := ShDom.mk (G f) (hD.1 hu)
  let yn : ShDom E α := ShDom.mk (Gn n f) hune
  let b : ShDom E α := ShDom.mk v hve
  have horth : inner ℝ (yn - y) (yn - b) = 0 := by
    have hz : Gn n f - v ∈ Dn n := (Dn n).sub_mem (hGn n f).1 hvn
    have hze := hD.1 (hDn n hz)
    change α * inner ℝ (Gn n f - G f) (Gn n f - v) +
      E.form (Gn n f - G f) (Gn n f - v) = 0
    rw [inner_sub_left, E.form_sub_left hune (hD.1 hu) hze]
    have h1 := (hGn n f).2 _ hz
    have h2 := (hG f).2 _ (hDn n hz)
    linarith
  have hsq : ‖yn - y‖ ^ 2 ≤ ‖y - b‖ ^ 2 := by
    have h := norm_add_sq_real (y - yn) (yn - b)
    have hc : inner ℝ (y - yn) (yn - b) = 0 := by
      rw [show y - yn = -(yn - y) by abel, inner_neg_left, horth, neg_zero]
    rw [sub_add_sub_cancel, hc, norm_sub_rev y yn] at h
    nlinarith [sq_nonneg ‖yn - b‖]
  have hlower : α * ‖Gn n f - G f‖ ^ 2 ≤ ‖yn - y‖ ^ 2 := by
    rw [hN]
    change α * ‖Gn n f - G f‖ ^ 2 ≤
      α * ‖Gn n f - G f‖ ^ 2 + E.form (Gn n f - G f) (Gn n f - G f)
    exact le_add_of_nonneg_right (E.form_nonneg _ (E.domain.sub_mem hune (hD.1 hu)))
  have hupper : ‖y - b‖ ^ 2 ≤ max α 1 * E.energyNormSq (G f - v) := by
    rw [hN]
    change α * ‖G f - v‖ ^ 2 + E.form (G f - v) (G f - v) ≤ _
    rw [DirichletForm.ClosedForm.energyNormSq]
    have hf0 := E.form_nonneg _ (E.domain.sub_mem (hD.1 hu) hve)
    nlinarith [le_max_left α 1, le_max_right α 1, sq_nonneg ‖G f - v‖]
  have he0 := E.energyNormSq_nonneg (E.domain.sub_mem (hD.1 hu) hve)
  have hden : 0 < max α 1 + 1 := by positivity
  have hsmall := (lt_div_iff₀ hden).1 happ
  have hnorm : ‖Gn n f - G f‖ < ε := by
    have hs : ‖Gn n f - G f‖ ^ 2 < ε ^ 2 := by nlinarith
    nlinarith [norm_nonneg (Gn n f - G f)]
  exact hnorm

end SubdiffusiveProcess.PartProcess
