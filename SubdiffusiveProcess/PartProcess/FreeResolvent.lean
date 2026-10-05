module

public import SubdiffusiveProcess.PartProcess.Penalization
public import SubdiffusiveProcess.Processes.E7.Occupation
public import SubdiffusiveProcess.PartProcess.PotentialKernel
public import SubdiffusiveProcess.PartProcess.KernelAssociation
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

@[expose] public section

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

theorem potentialOcc_measurable
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    [IsSFiniteKernel K]
    (q : (Fin d → ℝ) → ℝ) (hq : Measurable q) (α : ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (potentialOcc K q α f) := by
  have heval : Measurable fun p : (ℝ × (Fin d → ℝ)) × ContinuousPath (Fin d → ℝ) =>
      p.2 (Real.toNNReal p.1.1) := aux_n8_measurable_eval.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hA : Measurable fun p : (ℝ × (Fin d → ℝ)) × ContinuousPath (Fin d → ℝ) =>
      SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional q (Real.toNNReal p.1.1) p.2 :=
    (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_real_toNNReal.comp (measurable_fst.comp measurable_fst)).prodMk
        measurable_snd)
  have hJ : Measurable fun p : ℝ × (Fin d → ℝ) =>
      ∫⁻ w, ENNReal.ofReal (Real.exp
        (-SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional q (Real.toNNReal p.1) w)) *
          ENNReal.ofReal (f (w (Real.toNNReal p.1))) ∂K p.2 := by
    exact ((Real.measurable_exp.comp hA.neg).ennreal_ofReal.mul
      (hf.comp heval).ennreal_ofReal).lintegral_kernel_prod_right'
        (κ := K.comap Prod.snd measurable_snd)
  have hW : Measurable fun p : ℝ × (Fin d → ℝ) =>
      ENNReal.ofReal (Real.exp (-α * p.1)) *
        ∫⁻ w, ENNReal.ofReal (Real.exp
          (-SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional q (Real.toNNReal p.1) w)) *
            ENNReal.ofReal (f (w (Real.toNNReal p.1))) ∂K p.2 :=
    ((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).ennreal_ofReal).mul hJ
  exact hW.lintegral_prod_left' (μ := volume.restrict (Ioi 0))

theorem potentialOcc_le_free
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    (q : (Fin d → ℝ) → ℝ) (hq0 : ∀ x, 0 ≤ q x) (α : ℝ)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    potentialOcc K q α f x ≤ potentialOcc K 0 α f x := by
  apply lintegral_mono
  intro t
  apply mul_le_mul_right
  apply lintegral_mono
  intro w
  have hA := SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional_nonneg hq0
    (Real.toNNReal t) w
  have he : ENNReal.ofReal (Real.exp
      (-SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional q (Real.toNNReal t) w)) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 hA)
  simpa [SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional_apply] using
    mul_le_mul_left he (ENNReal.ofReal (f (w (Real.toNNReal t))))

/-- Association on compact continuous tests extends to nonnegative `L²` data. -/
theorem free_association (hm : IsLocallyFiniteMeasure m) (_hpos : m.IsOpenPosMeasure)
    (D : Data d m) (α : ℝ) (hα : 0 < α)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hG : _root_.SubdiffusiveProcess.DirichletForm.IsResolvent D.form.toClosedForm α G)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : MemLp f 2 m) :
    (∀ᵐ x ∂m, potentialOcc D.law 0 α f x < ⊤) ∧
    (fun x => (potentialOcc D.law 0 α f x).toReal) =ᵐ[m] ⇑(G (hfL.toLp f)) := by
  let := hm
  let := D.markov
  let := isFiniteKernel_freeKernel D.law α hα
  have hC : CompactKernelAssociation (freeKernel D.law α hα) G := by
    intro g
    let b := ofCompactSupport g g.continuous g.hasCompactSupport
    have hbound : ∀ x, |g x| ≤ ‖b‖ := fun x => by
      simpa only [b, ofCompactSupport, Real.norm_eq_abs] using!
        BoundedContinuousFunction.norm_coe_le_norm b x
    have ha := D.associated α hα G hG g g.continuous g.hasCompactSupport
      (g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport)
    filter_upwards [ha] with x hx
    rw [integral_freeKernel D.law α hα g g.continuous.measurable ‖b‖ hbound x]
    exact hx
  have ha := compactKernelAssociation_Lp (freeKernel D.law α hα) G hC hG.inner_comm f hf hf0 hfL
  simpa only [lintegral_freeKernel D.law α hα f hf] using ha

theorem potentialOcc_memLp (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (D : Data d m) (q : (Fin d → ℝ) → ℝ) (hq : Measurable q)
    (hq0 : ∀ x, 0 ≤ q x) (α : ℝ) (hα : 0 < α)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : MemLp f 2 m) :
    (∀ᵐ x ∂m, potentialOcc D.law q α f x < ⊤) ∧
    MemLp (fun x => (potentialOcc D.law q α f x).toReal) 2 m := by
  obtain ⟨G, hG⟩ := SubdiffusiveProcess.E7.exists_isResolvent D.form.toClosedForm hα
  obtain ⟨hfin, heq⟩ := free_association hm hpos D α hα G hG f hf hf0 hfL
  have hle : ∀ x, potentialOcc D.law q α f x ≤ potentialOcc D.law 0 α f x :=
    potentialOcc_le_free D.law q hq0 α f
  refine ⟨hfin.mono (fun x hx => (hle x).trans_lt hx), ?_⟩
  let := D.markov
  apply (Lp.memLp (G (hfL.toLp f))).mono'
    (potentialOcc_measurable D.law q hq α f hf).ennreal_toReal.aestronglyMeasurable
  filter_upwards [hfin, heq] with x hx he
  simp only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [← he]
  exact ENNReal.toReal_mono hx.ne (hle x)

theorem potentialOcc_congr_ae (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (D : Data d m) (q : (Fin d → ℝ) → ℝ) (_hq : Measurable q)
    (_hq0 : ∀ x, 0 ≤ q x) (α : ℝ) (hα : 0 < α)
    (f g : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (_hf0 : ∀ x, 0 ≤ f x) (_hg0 : ∀ x, 0 ≤ g x)
    (hfL : MemLp f 2 m) (heq : f =ᵐ[m] g) :
    potentialOcc D.law q α f =ᵐ[m] potentialOcc D.law q α g := by
  let δ : (Fin d → ℝ) → ℝ := fun x => |f x - g x|
  have hδm : Measurable δ := (hf.sub hg).norm
  have hδ0 : ∀ x, 0 ≤ δ x := fun x => abs_nonneg _
  have hδL : MemLp δ 2 m := (hfL.sub ((memLp_congr_ae heq).1 hfL)).norm
  have hδeq : δ =ᵐ[m] (fun _ => 0) := heq.mono (fun x hx => by simp [δ, hx])
  have hδLp : hδL.toLp δ = 0 := by
    apply Lp.ext
    filter_upwards [hδL.coeFn_toLp, hδeq, Lp.coeFn_zero ℝ 2 m] with x h1 h2 h3
    simpa only [Pi.zero_apply] using (h1.trans h2).trans h3.symm
  obtain ⟨G, hG⟩ := SubdiffusiveProcess.E7.exists_isResolvent D.form.toClosedForm hα
  obtain ⟨hfin, hfree⟩ := free_association hm hpos D α hα G hG δ hδm hδ0 hδL
  have hz : ∀ᵐ x ∂m, potentialOcc D.law 0 α δ x = 0 := by
    filter_upwards [hfin, hfree, Lp.coeFn_zero ℝ 2 m] with x hx h1 h2
    rw [hδLp, map_zero, h2] at h1
    have hreal : (potentialOcc D.law 0 α δ x).toReal = 0 := by simpa using h1
    exact ((ENNReal.toReal_eq_zero_iff _).1 hreal).resolve_right hx.ne
  let := D.markov
  have hW : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-α * t)) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal
  filter_upwards [hz] with x hx
  let J : ℝ → ℝ≥0∞ := fun t => ∫⁻ w, ENNReal.ofReal (δ (w (Real.toNNReal t))) ∂D.law x
  have hJ : Measurable J := (hδm.comp aux_n8_measurable_eval).ennreal_ofReal.lintegral_prod_right'
  have hzero : (∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-α * t)) * J t) = 0 := by
    simpa [potentialOcc, SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional_apply, J] using hx
  have htime : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), J t = 0 := by
    filter_upwards [(lintegral_eq_zero_iff (hW.mul hJ)).1 hzero] with t ht
    exact (mul_eq_zero.1 ht).resolve_left
      ((ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
  apply lintegral_congr_ae
  filter_upwards [htime] with t ht
  congr 1
  apply lintegral_congr_ae
  have hpath := (lintegral_eq_zero_iff
    (hδm.comp (ContinuousPath.measurable_coordinateProcess (Real.toNNReal t))).ennreal_ofReal).1 ht
  filter_upwards [hpath] with w hw
  have hfg : f (w (Real.toNNReal t)) = g (w (Real.toNNReal t)) := by
    apply sub_eq_zero.1
    apply abs_eq_zero.1
    have hle := ENNReal.ofReal_eq_zero.1 hw
    exact le_antisymm hle (abs_nonneg _)
  rw [hfg]

end SubdiffusiveProcess.PartProcess
