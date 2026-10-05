module

public import SubdiffusiveProcess.PartProcess.PartFormConstruction
public import SubdiffusiveProcess.PartProcess.CoreDensity
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7

/-- Regularity supplies density in the restricted `L²` space. -/
theorem dense_restrictions_of_core (d : ℕ) (m : Measure (Fin d → ℝ))
    (hm : IsLocallyFiniteMeasure m) (_hpos : m.IsOpenPosMeasure)
    (E : _root_.SubdiffusiveProcess.DirichletForm m) (hE : _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    Dense {v : Lp ℝ 2 (m.restrict U) |
      ∃ u, E.toClosedForm.MemCoreOn U u ∧ restrictLp U u = v} := by
  let := hm
  let : IsLocallyFiniteMeasure (m.restrict U) :=
    Measure.isLocallyFiniteMeasure_of_le Measure.restrict_le_self
  obtain ⟨V, hVo, hVfull, C, hC⟩ := hE
  have hAfull : (m.restrict U) (U ∩ V)ᶜ = 0 := by
    have hmemV : ∀ᵐ x ∂m, x ∈ V := by rw [ae_iff]; exact hVfull
    have hmem : ∀ᵐ x ∂(m.restrict U), x ∈ U ∩ V :=
      (ae_restrict_mem hU.measurableSet).and (ae_restrict_of_ae hmemV)
    exact (ae_iff.1 hmem)
  rw [Metric.dense_iff]
  intro v ε hε
  obtain ⟨f, hfK, hfA, hferr, hfc, hfL⟩ :=
    exists_supportedCc_approx (inferInstance : IsLocallyFiniteMeasure (m.restrict U))
      (U ∩ V) (hU.inter hVo) hAfull v (Lp.memLp v)
      (ENNReal.ofReal (ε / 4)) (ne_of_gt (ENNReal.ofReal_pos.2 (by positivity)))
  let fLp : Lp ℝ 2 (m.restrict U) := hfL.toLp f
  have hvf : ‖v - fLp‖ ≤ ε / 4 := by
    rw [Lp.norm_def]
    have hae : ⇑(v - fLp) =ᵐ[m.restrict U] ⇑v - f :=
      (Lp.coeFn_sub v fLp).trans (EventuallyEq.rfl.sub hfL.coeFn_toLp)
    rw [eLpNorm_congr_ae hae]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hferr).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hKms : (m.restrict U) (tsupport f) ≠ ⊤ := hfK.measure_lt_top.ne
  let kLp : Lp ℝ 2 (m.restrict U) :=
    indicatorConstLp 2 isClosed_closure.measurableSet hKms (1 : ℝ)
  let δ : ℝ := ε / (4 * (‖kLp‖ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨u, hu, g, hgc, hgK, hgs, hug, herror⟩ :=
    exists_localCore_uniform E V C hC f hfc hfK (hfA.trans inter_subset_right)
      U (hfA.trans inter_subset_left) δ hδ
  let w := restrictLp U u
  have hwf : ‖w - fLp‖ ≤ δ * ‖kLp‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub w fLp, restrictLp_coe U u, hug.restrict,
      hfL.coeFn_toLp,
      (show ⇑kLp =ᵐ[m.restrict U] (tsupport f).indicator (fun _ => (1 : ℝ))
        from indicatorConstLp_coeFn)] with x hsub hwu hugx hfx hkx
    change ‖(w - fLp) x‖ ≤ δ * ‖kLp x‖
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hwu, hugx, hfx, hkx]
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx]
      simpa only [Real.norm_eq_abs, norm_one, mul_one] using (herror x).le
    · have hfz : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hgz : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hgs h))
      simp only [Set.indicator_of_notMem hx, hfz, hgz, sub_self, norm_zero, mul_zero, le_refl]
  have hδbound : δ * ‖kLp‖ < ε / 4 := by
    dsimp [δ]
    have hden : 0 < 4 * (‖kLp‖ + 1) := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [norm_nonneg kLp]
  refine ⟨w, ?_, u, hu, rfl⟩
  change dist w v < ε
  rw [dist_eq_norm]
  have htriangle : ‖w - v‖ ≤ ‖w - fLp‖ + ‖fLp - v‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (w - fLp) (fLp - v)
  rw [norm_sub_rev fLp v] at htriangle
  linarith

/-- The graph-closed ambient core closure descends through restriction. -/
theorem exists_partForm (d : ℕ) (m : Measure (Fin d → ℝ))
    (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (E : _root_.SubdiffusiveProcess.DirichletForm m) (hE : _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    ∃ F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (m.restrict U), IsPartFormOn E.toClosedForm U F := by
  exact exists_partForm_of_dense E.toClosedForm U hU.measurableSet
    (dense_restrictions_of_core d m hm hpos E hE U hU)

/-- The part-form resolvent, extended by zero, solves the ambient variational problem. -/
theorem part_resolvent_extension {d : ℕ} {m : Measure (Fin d → ℝ)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (m.restrict U)) (hF : IsPartFormOn E U F)
    (α : ℝ) (G : Lp ℝ 2 (m.restrict U) →L[ℝ] Lp ℝ 2 (m.restrict U))
    (hG : _root_.SubdiffusiveProcess.DirichletForm.IsResolvent F α G) :
    IsDomainResolvent E (E.killedCoreClosure U) α
      ((extension U hU.measurableSet).comp (G.comp (restriction U))) := by
  let r : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 (m.restrict U) := restriction U
  let e : Lp ℝ 2 (m.restrict U) →L[ℝ] Lp ℝ 2 m := extension U hU.measurableSet
  intro f
  have hg := hG (r f)
  obtain ⟨u, hu, hru⟩ := (hF.mem_domain_iff (G (r f))).1 hg.1
  have heu : e (G (r f)) = u := by
    rw [← hru]
    exact extend_restrict U hU.measurableSet u (zeroOutside_coreLimit E U u hu)
  constructor
  · change e (G (r f)) ∈ E.killedCoreClosure U
    rw [heu]
    exact (coreLimit_iff_mem_killedCoreClosure E U u).1 hu
  · intro v hv
    have hvc := (coreLimit_iff_mem_killedCoreClosure E U v).2 hv
    have hev : e (r v) = v :=
      extend_restrict U hU.measurableSet v (zeroOutside_coreLimit E U v hvc)
    have hrv : r v ∈ F.domain := (hF.mem_domain_iff (r v)).2 ⟨v, hvc, rfl⟩
    have heq := hg.2 (r v) hrv
    have hform : F.form (G (r f)) (r v) = E.form u v := by
      rw [← hru]
      exact hF.form_eq u v hu hvc
    have hinner : inner ℝ u v = inner ℝ (G (r f)) (r v) := by
      calc
        inner ℝ u v = inner ℝ (e (G (r f))) (e (r v)) := by rw [heu, hev]
        _ = inner ℝ (G (r f)) (r v) := inner_extend U hU.measurableSet (G (r f)) (r v)
    have hright : inner ℝ f v = inner ℝ (r f) (r v) := by
      calc
        inner ℝ f v = inner ℝ f (e (r v)) := by rw [hev]
        _ = inner ℝ (r f) (r v) := inner_restrict_extend U hU.measurableSet f (r v)
    change α * inner ℝ (e (G (r f))) v + E.form (e (G (r f))) v = inner ℝ f v
    rw [heu, hinner, hright, ← hform]
    exact heq

end SubdiffusiveProcess.PartProcess
