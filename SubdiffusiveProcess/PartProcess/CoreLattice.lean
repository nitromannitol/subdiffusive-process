import SubdiffusiveProcess.PartProcess.GraphClosure

open MeasureTheory Filter Topology Set
noncomputable section
namespace SubdiffusiveProcess.PartProcess
variable {X : Type*} [MeasurableSpace X] {m : Measure X}

theorem lipschitz_abs : LipschitzWith 1 (abs : ℝ → ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub a b

def absoluteLp (u : Lp ℝ 2 m) : Lp ℝ 2 m := lipschitz_abs.compLp abs_zero u

def lowerLp (u v : Lp ℝ 2 m) : Lp ℝ 2 m :=
  (1 / 2 : ℝ) • (u + v - absoluteLp (u - v))

def upperLp (u v : Lp ℝ 2 m) : Lp ℝ 2 m :=
  (1 / 2 : ℝ) • (u + v + absoluteLp (u - v))

def variableClipLp (b u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  upperLp (-absoluteLp b) (lowerLp u (absoluteLp b))

theorem absoluteLp_coe (u : Lp ℝ 2 m) : ⇑(absoluteLp u) =ᵐ[m] fun x => |u x| :=
  lipschitz_abs.coeFn_compLp abs_zero u

theorem lowerLp_coe (u v : Lp ℝ 2 m) :
    ⇑(lowerLp u v) =ᵐ[m] fun x => min (u x) (v x) := by
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (u + v - absoluteLp (u - v)),
    Lp.coeFn_sub (u + v) (absoluteLp (u - v)), Lp.coeFn_add u v,
    absoluteLp_coe (u - v), Lp.coeFn_sub u v] with x h1 h2 h3 h4 h5
  change ((1 / 2 : ℝ) • (u + v - absoluteLp (u - v)) : Lp ℝ 2 m) x = _
  simp only [h1, Pi.smul_apply, smul_eq_mul, h2, Pi.sub_apply, h3, Pi.add_apply,
    h4, h5]
  rcases le_total (u x) (v x) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]
    ring

theorem upperLp_coe (u v : Lp ℝ 2 m) :
    ⇑(upperLp u v) =ᵐ[m] fun x => max (u x) (v x) := by
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (u + v + absoluteLp (u - v)),
    Lp.coeFn_add (u + v) (absoluteLp (u - v)), Lp.coeFn_add u v,
    absoluteLp_coe (u - v), Lp.coeFn_sub u v] with x h1 h2 h3 h4 h5
  change ((1 / 2 : ℝ) • (u + v + absoluteLp (u - v)) : Lp ℝ 2 m) x = _
  simp only [h1, Pi.smul_apply, smul_eq_mul, h2, Pi.add_apply, h3, h4, h5,
    Pi.sub_apply]
  rcases le_total (u x) (v x) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_right h]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left h]
    ring

private theorem absoluteLp_mem_form_le (E : _root_.DirichletForm m) (u : Lp ℝ 2 m)
    (hu : u ∈ E.domain) : absoluteLp u ∈ E.domain ∧
      E.form (absoluteLp u) (absoluteLp u) ≤ E.form u u := by
  simpa only [NNReal.coe_one, one_pow, one_mul] using
    DirichletForm.lipschitz_comp_mem E lipschitz_abs abs_zero hu (absoluteLp_coe u)

theorem lowerLp_mem_form_le (E : _root_.DirichletForm m) (u v : Lp ℝ 2 m)
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    lowerLp u v ∈ E.domain ∧
      E.form (lowerLp u v) (lowerLp u v) ≤ 2 * E.form u u + 2 * E.form v v := by
  have hsum := E.domain.add_mem hu hv
  have hdiff := E.domain.sub_mem hu hv
  obtain ⟨ha, hEa⟩ := absoluteLp_mem_form_le E (u - v) hdiff
  have hsub := E.domain.sub_mem hsum ha
  refine ⟨E.domain.smul_mem (1 / 2 : ℝ) hsub, ?_⟩
  change E.form ((1 / 2 : ℝ) • (u + v - absoluteLp (u - v)))
    ((1 / 2 : ℝ) • (u + v - absoluteLp (u - v))) ≤ _
  rw [E.toClosedForm.form_smul_self _ hsub]
  have h1 := E.toClosedForm.form_sub_self_le hsum ha
  have h2 := E.toClosedForm.form_add_self_le hu hv
  have h3 := E.toClosedForm.form_sub_self_le hu hv
  norm_num only [one_div, inv_pow, one_pow] at *
  linarith

theorem upperLp_mem_form_le (E : _root_.DirichletForm m) (u v : Lp ℝ 2 m)
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    upperLp u v ∈ E.domain ∧
      E.form (upperLp u v) (upperLp u v) ≤ 2 * E.form u u + 2 * E.form v v := by
  have hsum := E.domain.add_mem hu hv
  have hdiff := E.domain.sub_mem hu hv
  obtain ⟨ha, hEa⟩ := absoluteLp_mem_form_le E (u - v) hdiff
  have hadd := E.domain.add_mem hsum ha
  refine ⟨E.domain.smul_mem (1 / 2 : ℝ) hadd, ?_⟩
  change E.form ((1 / 2 : ℝ) • (u + v + absoluteLp (u - v)))
    ((1 / 2 : ℝ) • (u + v + absoluteLp (u - v))) ≤ _
  rw [E.toClosedForm.form_smul_self _ hadd]
  have h1 := E.toClosedForm.form_add_self_le hsum ha
  have h2 := E.toClosedForm.form_add_self_le hu hv
  have h3 := E.toClosedForm.form_sub_self_le hu hv
  norm_num only [one_div, inv_pow, one_pow] at *
  linarith

theorem variableClipLp_coe (b u : Lp ℝ 2 m) :
    ⇑(variableClipLp b u) =ᵐ[m] fun x => max (-|b x|) (min (u x) |b x|) := by
  filter_upwards [upperLp_coe (-absoluteLp b) (lowerLp u (absoluteLp b)),
    Lp.coeFn_neg (absoluteLp b), lowerLp_coe u (absoluteLp b), absoluteLp_coe b]
    with x h1 h2 h3 h4
  change upperLp (-absoluteLp b) (lowerLp u (absoluteLp b)) x = _
  simp only [h1, h2, Pi.neg_apply, h3, h4]

theorem variableClipLp_mem_form_le (E : _root_.DirichletForm m) (b u : Lp ℝ 2 m)
    (hb : b ∈ E.domain) (hu : u ∈ E.domain) :
    variableClipLp b u ∈ E.domain ∧
      E.form (variableClipLp b u) (variableClipLp b u) ≤
        4 * E.form u u + 6 * E.form b b := by
  obtain ⟨ha, hEa⟩ := absoluteLp_mem_form_le E b hb
  obtain ⟨hl, hEl⟩ := lowerLp_mem_form_le E u (absoluteLp b) hu ha
  obtain ⟨hc, hEc⟩ := upperLp_mem_form_le E (-absoluteLp b)
    (lowerLp u (absoluteLp b)) (E.domain.neg_mem ha) hl
  refine ⟨hc, ?_⟩
  rw [E.toClosedForm.form_neg_left ha (E.domain.neg_mem ha),
    E.toClosedForm.form_neg_right ha ha, neg_neg] at hEc
  change E.form (variableClipLp b u) (variableClipLp b u) ≤ _ at hEc
  linarith

theorem variableClipLp_continuous (b : Lp ℝ 2 m) : Continuous (variableClipLp b) := by
  have habs : Continuous (absoluteLp : Lp ℝ 2 m → Lp ℝ 2 m) :=
    lipschitz_abs.continuous_compLp abs_zero
  have hlo : Continuous (fun u : Lp ℝ 2 m => lowerLp u (absoluteLp b)) :=
    (continuous_id.add continuous_const |>.sub
      (habs.comp (continuous_id.sub continuous_const))).const_smul (1 / 2 : ℝ)
  exact (continuous_const.add hlo |>.add
    (habs.comp (continuous_const.sub hlo))).const_smul (1 / 2 : ℝ)

theorem variableClipLp_eq_of_abs_le (b u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, |u x| ≤ |b x|) : variableClipLp b u = u := by
  apply Lp.ext
  filter_upwards [variableClipLp_coe b u, hu] with x hx hbound
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
  rw [hx, min_eq_left hhi, max_eq_right hlo]

theorem variableClipLp_memCore_inter [TopologicalSpace X]
    (E : _root_.DirichletForm m) (U V : Set X) (b u : Lp ℝ 2 m)
    (hb : E.toClosedForm.MemCoreOn U b) (hu : E.toClosedForm.MemCoreOn V u) :
    E.toClosedForm.MemCoreOn (U ∩ V) (variableClipLp b u) := by
  obtain ⟨f, hf, hcf, hsf, haf⟩ := hb.2
  obtain ⟨g, hg, hcg, hsg, hag⟩ := hu.2
  let c : X → ℝ := fun x => max (-|f x|) (min (g x) |f x|)
  have hcsf : Function.support c ⊆ Function.support f := by
    intro x hx
    by_contra hxf
    have hf0 : f x = 0 := not_ne_iff.mp hxf
    apply hx
    dsimp [c]
    rw [hf0, abs_zero, neg_zero, max_eq_left (min_le_right _ _)]
  have hcsg : Function.support c ⊆ Function.support g := by
    intro x hx
    by_contra hxg
    have hg0 : g x = 0 := not_ne_iff.mp hxg
    apply hx
    dsimp [c]
    rw [hg0, min_eq_left (abs_nonneg _), max_eq_right (neg_nonpos.mpr (abs_nonneg _))]
  refine ⟨(variableClipLp_mem_form_le E b u hb.1 hu.1).1, c,
    hf.abs.neg.max (hg.min hf.abs), hcf.mono hcsf, ?_, ?_⟩
  · exact subset_inter ((closure_mono hcsf).trans hsf) ((closure_mono hcsg).trans hsg)
  · filter_upwards [variableClipLp_coe b u, haf, hag] with x hx hfx hgx
    simpa only [c, hfx, hgx] using hx

end SubdiffusiveProcess.PartProcess
