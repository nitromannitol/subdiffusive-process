module

public import SubdiffusiveProcess.Processes.E7.Leaves
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput

@[expose] public section

/-!
# Killed occupation integrals: joint measurability, lintegral → Bochner, null-set invariance
-/
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.E7
open SubdiffusiveProcess.Probability.Diffusion.Input

variable {d : ℕ}

theorem aux_n8_measurable_stateAt (t : NNReal) :
    Measurable (stateAt (d := d) t) :=
  (measurable_id.sumElim measurable_const).comp (LifetimePath.measurable_coordinate t)

theorem aux_n8_stateAt_ofCP (t : NNReal) (ω : ContinuousPath (Fin d → ℝ)) :
    stateAt t (LifetimePath.ofContinuousPath ω) = ω t := by
  rw [stateAt, LifetimePath.coordinate_ofContinuousPath]
  rfl

theorem aux_n8_measurable_exitTime (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    Measurable (LifetimePath.exitTime (alpha := Fin d → ℝ) U) :=
  (LifetimePath.isStoppingTime_exitTime U hU).measurable'

/-- The live set `{ofReal t < τ_U}` is jointly measurable on `ℝ × C(ℝ≥0, ℝ^d)`. -/
theorem aux_n8_measurableSet_live (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    MeasurableSet {p : ℝ × ContinuousPath (Fin d → ℝ) |
      ENNReal.ofReal p.1 < LifetimePath.exitTime U (LifetimePath.ofContinuousPath p.2)} :=
  measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
    ((aux_n8_measurable_exitTime U hU).comp
      (LifetimePath.measurable_ofContinuousPath.comp measurable_snd))

/-- Joint measurability of `(t, ω) ↦ ω t`. -/
theorem aux_n8_measurable_eval :
    Measurable (fun p : ℝ × ContinuousPath (Fin d → ℝ) => p.2 (Real.toNNReal p.1)) :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (ω : ContinuousPath (Fin d → ℝ)) => ω (Real.toNNReal t))
    (fun ω => ω.continuous.comp continuous_real_toNNReal)
    (fun _t => ContinuousPath.measurable_coordinateProcess _)

/-- The time-`t` killed integral, transported to continuous-path space. -/
theorem aux_n8_J_eq (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (g : (Fin d → ℝ) → ℝ) (hg : Measurable g)
    (x : Fin d → ℝ) (t : ℝ) :
    ∫⁻ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
        ENNReal.ofReal (g (stateAt (Real.toNNReal t) w)) ∂(K.map LifetimePath.ofContinuousPath x) =
      ∫⁻ ω, {p : ℝ × ContinuousPath (Fin d → ℝ) |
          ENNReal.ofReal p.1 < LifetimePath.exitTime U (LifetimePath.ofContinuousPath p.2)}.indicator
        (fun p => ENNReal.ofReal (g (p.2 (Real.toNNReal p.1)))) (t, ω) ∂(K x) := by
  have hA : MeasurableSet {w : LifetimePath (Fin d → ℝ) |
      ENNReal.ofReal t < LifetimePath.exitTime U w} :=
    measurableSet_lt measurable_const (aux_n8_measurable_exitTime U hU)
  rw [Kernel.map_apply K LifetimePath.measurable_ofContinuousPath x,
    setLIntegral_map (f := fun w => ENNReal.ofReal (g (stateAt (Real.toNNReal t) w))) hA
      (ENNReal.measurable_ofReal.comp (hg.comp (aux_n8_measurable_stateAt _)))
      LifetimePath.measurable_ofContinuousPath]
  rw [← lintegral_indicator (hA.preimage LifetimePath.measurable_ofContinuousPath)]
  refine lintegral_congr fun ω => ?_
  simp only [Set.indicator, Set.mem_preimage, mem_ofPred_eq, aux_n8_stateAt_ofCP]

/-- The time-`t` killed integral is measurable in `t`. -/
theorem aux_n8_J_measurable (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    [IsMarkovKernel K] (U : Set (Fin d → ℝ)) (hU : IsOpen U) (g : (Fin d → ℝ) → ℝ)
    (hg : Measurable g) (x : Fin d → ℝ) :
    Measurable (fun t : ℝ => ∫⁻ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
        ENNReal.ofReal (g (stateAt (Real.toNNReal t) w)) ∂(K.map LifetimePath.ofContinuousPath x)) := by
  simp_rw [aux_n8_J_eq K U hU g hg x]
  exact ((ENNReal.measurable_ofReal.comp (hg.comp aux_n8_measurable_eval)).indicator
    (aux_n8_measurableSet_live U hU)).lintegral_prod_right'

/-- A finite killed occupation integral has finite time slices for a.e. time. -/
theorem aux_n8_ae_J_lt_top (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    [IsMarkovKernel K] (U : Set (Fin d → ℝ)) (hU : IsOpen U) (α : ℝ) (g : (Fin d → ℝ) → ℝ)
    (hg : Measurable g) (x : Fin d → ℝ) (h : killedOcc K U α g x < ⊤) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      (∫⁻ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
        ENNReal.ofReal (g (stateAt (Real.toNNReal t) w)) ∂(K.map LifetimePath.ofContinuousPath x)) < ⊤ := by
  have hm : AEMeasurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-α * t)) *
      ∫⁻ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
        ENNReal.ofReal (g (stateAt (Real.toNNReal t) w)) ∂(K.map LifetimePath.ofContinuousPath x))
      (volume.restrict (Ioi 0)) :=
    ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul measurable_id))).mul (aux_n8_J_measurable K U hU g hg x)).aemeasurable
  filter_upwards [ae_lt_top' hm h.ne] with t ht
  exact ENNReal.lt_top_of_mul_ne_top_right ht.ne (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/-- Bochner integral as the difference of the positive- and negative-part lintegrals. -/
theorem aux_n8_integral_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : Ω → ℝ)
    (hh : Measurable h) (hp : ∫⁻ w, ENNReal.ofReal (max (h w) 0) ∂μ < ⊤)
    (hm : ∫⁻ w, ENNReal.ofReal (max (-h w) 0) ∂μ < ⊤) :
    ∫ w, h w ∂μ = (∫⁻ w, ENNReal.ofReal (max (h w) 0) ∂μ).toReal -
      (∫⁻ w, ENNReal.ofReal (max (-h w) 0) ∂μ).toReal := by
  have hpm : Measurable fun w => max (h w) 0 := hh.max measurable_const
  have hmm : Measurable fun w => max (-h w) 0 := hh.neg.max measurable_const
  have hp0 : 0 ≤ᵐ[μ] fun w => max (h w) 0 := ae_of_all _ fun w => le_max_right _ _
  have hm0 : 0 ≤ᵐ[μ] fun w => max (-h w) 0 := ae_of_all _ fun w => le_max_right _ _
  have hpi : Integrable (fun w => max (h w) 0) μ :=
    ⟨hpm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hp0).mpr hp⟩
  have hmi : Integrable (fun w => max (-h w) 0) μ :=
    ⟨hmm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hm0).mpr hm⟩
  calc ∫ w, h w ∂μ = ∫ w, (max (h w) 0 - max (-h w) 0) ∂μ := by
        congr 1; funext w; exact (max_zero_sub_max_neg_zero_eq_self _).symm
    _ = _ := by
        rw [integral_sub hpi hmi, integral_eq_lintegral_of_nonneg_ae hp0 hpm.aestronglyMeasurable,
          integral_eq_lintegral_of_nonneg_ae hm0 hmm.aestronglyMeasurable]

/-- A weighted time integral of `toReal` slices, when the lintegral is finite. -/
theorem aux_n8_outer (μ : Measure ℝ) (e : ℝ → ℝ) (he : Measurable e) (he0 : ∀ t, 0 < e t)
    (J : ℝ → ℝ≥0∞) (hJ : Measurable J) (hfin : ∫⁻ t, ENNReal.ofReal (e t) * J t ∂μ < ⊤) :
    ∫ t, e t * (J t).toReal ∂μ = (∫⁻ t, ENNReal.ofReal (e t) * J t ∂μ).toReal ∧
      Integrable (fun t => e t * (J t).toReal) μ := by
  have hae : ∀ᵐ t ∂μ, J t < ⊤ := by
    filter_upwards [ae_lt_top' (((ENNReal.measurable_ofReal.comp he).mul hJ).aemeasurable)
      hfin.ne] with t ht
    exact ENNReal.lt_top_of_mul_ne_top_right ht.ne (ENNReal.ofReal_pos.mpr (he0 t)).ne'
  have hmeas : Measurable fun t => e t * (J t).toReal := he.mul hJ.ennreal_toReal
  have h0 : 0 ≤ᵐ[μ] fun t => e t * (J t).toReal :=
    ae_of_all _ fun t => mul_nonneg (he0 t).le ENNReal.toReal_nonneg
  have hlin : ∫⁻ t, ENNReal.ofReal (e t * (J t).toReal) ∂μ = ∫⁻ t, ENNReal.ofReal (e t) * J t ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with t ht
    rw [ENNReal.ofReal_mul (he0 t).le, ENNReal.ofReal_toReal ht.ne]
  refine ⟨?_, hmeas.aestronglyMeasurable, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae h0 hmeas.aestronglyMeasurable, hlin]
  · rw [hasFiniteIntegral_iff_ofReal h0, hlin]; exact hfin

/-- **Lintegral → Bochner for a Borel datum.**  If both the positive-part and the negative-part
killed occupation integrals of a Borel `f` are finite at `x`, the signed occupation resolvent is
`s⁻¹` times their difference. -/
theorem occupation_eq_toReal_sub {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (x : Fin d → ℝ)
    (hp : killedOcc K U s⁻¹ (fun y => max (f y) 0) x < ⊤)
    (hm : killedOcc K U s⁻¹ (fun y => max (-f y) 0) x < ⊤) :
    occupationResolvent (K.map LifetimePath.ofContinuousPath) U s f x =
      s⁻¹ * ((killedOcc K U s⁻¹ (fun y => max (f y) 0) x).toReal -
        (killedOcc K U s⁻¹ (fun y => max (-f y) 0) x).toReal) := by
  have he : Measurable fun t : ℝ => Real.exp (-s⁻¹ * t) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hfp : Measurable fun y => max (f y) 0 := hf.max measurable_const
  have hfm : Measurable fun y => max (-f y) 0 := hf.neg.max measurable_const
  obtain ⟨hIp, hintp⟩ := aux_n8_outer (volume.restrict (Ioi 0)) _ he (fun t => Real.exp_pos _) _
    (aux_n8_J_measurable K U hU _ hfp x) hp
  obtain ⟨hIm, hintm⟩ := aux_n8_outer (volume.restrict (Ioi 0)) _ he (fun t => Real.exp_pos _) _
    (aux_n8_J_measurable K U hU _ hfm x) hm
  have haep := aux_n8_ae_J_lt_top K U hU s⁻¹ _ hfp x hp
  have haem := aux_n8_ae_J_lt_top K U hU s⁻¹ _ hfm x hm
  have hinner : (fun t : ℝ => Real.exp (-t / s) *
      ∫ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
        f (stateAt (Real.toNNReal t) w) ∂(K.map LifetimePath.ofContinuousPath x))
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t =>
        Real.exp (-s⁻¹ * t) * (∫⁻ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
          ENNReal.ofReal (max (f (stateAt (Real.toNNReal t) w)) 0)
            ∂(K.map LifetimePath.ofContinuousPath x)).toReal -
        Real.exp (-s⁻¹ * t) * (∫⁻ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
          ENNReal.ofReal (max (-f (stateAt (Real.toNNReal t) w)) 0)
            ∂(K.map LifetimePath.ofContinuousPath x)).toReal := by
    filter_upwards [haep, haem] with t htp htm
    rw [aux_n8_integral_eq _ (fun w => f (stateAt (Real.toNNReal t) w))
      (hf.comp (aux_n8_measurable_stateAt _)) htp htm]
    have : -t / s = -s⁻¹ * t := by field_simp
    rw [this, mul_sub]
  unfold occupationResolvent
  congr 1
  rw [integral_congr_ae hinner, integral_sub hintp hintm, hIp, hIm]
  rfl

/-- **Null-set lemma.**  If the killed occupation integral of `1_N` vanishes at `x`, the signed
occupation resolvent at `x` does not see a modification of the datum on `N ∩ U`
(`f` need not be measurable). -/
theorem occupation_congr_of_killedOcc_null {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (s : ℝ) (_hs : 0 < s)
    (f f₀ : (Fin d → ℝ) → ℝ) (N : Set (Fin d → ℝ)) (hN : MeasurableSet N)
    (hff : ∀ y ∈ U, y ∉ N → f y = f₀ y) (x : Fin d → ℝ)
    (h0 : killedOcc K U s⁻¹ (N.indicator (fun _ => (1 : ℝ))) x = 0) :
    occupationResolvent (K.map LifetimePath.ofContinuousPath) U s f x =
      occupationResolvent (K.map LifetimePath.ofContinuousPath) U s f₀ x := by
  have hNm : Measurable (N.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hN
  have hm : AEMeasurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-s⁻¹ * t)) *
      ∫⁻ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
        ENNReal.ofReal (N.indicator (fun _ => (1 : ℝ)) (stateAt (Real.toNNReal t) w))
          ∂(K.map LifetimePath.ofContinuousPath x)) (volume.restrict (Ioi 0)) :=
    ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul measurable_id))).mul (aux_n8_J_measurable K U hU _ hNm x)).aemeasurable
  have hae0 := (lintegral_eq_zero_iff' hm).mp h0
  have hinner : (fun t : ℝ => Real.exp (-t / s) *
      ∫ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
        f (stateAt (Real.toNNReal t) w) ∂(K.map LifetimePath.ofContinuousPath x))
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => Real.exp (-t / s) *
      ∫ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
        f₀ (stateAt (Real.toNNReal t) w) ∂(K.map LifetimePath.ofContinuousPath x) := by
    filter_upwards [hae0] with t ht
    have hJ : ∫⁻ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
        ENNReal.ofReal (N.indicator (fun _ => (1 : ℝ)) (stateAt (Real.toNNReal t) w))
          ∂(K.map LifetimePath.ofContinuousPath x) = 0 :=
      (mul_eq_zero.mp ht).resolve_left (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hA : MeasurableSet {w : LifetimePath (Fin d → ℝ) |
        ENNReal.ofReal t < LifetimePath.exitTime U w} :=
      measurableSet_lt measurable_const (aux_n8_measurable_exitTime U hU)
    have hw0 := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp
      (hNm.comp (aux_n8_measurable_stateAt _)))).mp hJ
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hw0, ae_restrict_mem hA] with w hw hwA
    obtain ⟨y, hyU, hy⟩ := LifetimePath.exists_coordinate_eq_alive_of_lt_exitTime U w
      (Real.toNNReal t) hwA
    have hXU : stateAt (Real.toNNReal t) w = y := by rw [stateAt, hy]; rfl
    have hXN : stateAt (Real.toNNReal t) w ∉ N := by
      intro hmem
      simp [Set.indicator_of_mem hmem] at hw
    rw [hXU] at hXN ⊢
    exact hff y hyU hXN
  unfold occupationResolvent
  congr 1
  exact integral_congr_ae hinner

end SubdiffusiveProcess.E7
