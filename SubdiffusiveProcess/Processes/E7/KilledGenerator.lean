import SubdiffusiveProcess.Processes.E7.PartDomain
import SubdiffusiveProcess.Processes.E7.Occupation
import SubdiffusiveProcess.Processes.E7.Association
import SubdiffusiveProcess.Processes.E7.ResolventExists

/-!
# The killed generator from the part-process leaf (dimension `d ≥ 1`)
-/
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.E7
open SubdiffusiveProcess.Probability.Diffusion.Input

variable {d : ℕ}

/-- The killed occupation resolvent of a signed `L²` datum is the resolvent of the part form. -/
theorem occupation_ae_eq_resolvent (m : Measure (Fin d → ℝ))
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s)
    (G : Lp ℝ 2 (m.restrict U) →L[ℝ] Lp ℝ 2 (m.restrict U))
    (hocc : ∀ f : (Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
      ∀ hf : MemLp f 2 (m.restrict U),
        (∀ᵐ x ∂(m.restrict U), killedOcc K U s⁻¹ f x < ⊤) ∧
        (fun x => (killedOcc K U s⁻¹ f x).toReal) =ᵐ[m.restrict U] ⇑(G (hf.toLp f)))
    (f : (Fin d → ℝ) → ℝ) (hf : MemLp f 2 (m.restrict U)) :
    (fun x => s⁻¹ * (G (hf.toLp f)) x) =ᵐ[m.restrict U]
      occupationResolvent (K.map LifetimePath.ofContinuousPath) U s f := by
  classical
  set f₀ : (Fin d → ℝ) → ℝ := hf.1.mk f with hf₀
  have hf₀m : Measurable f₀ := hf.1.stronglyMeasurable_mk.measurable
  have hff₀ : f =ᵐ[m.restrict U] f₀ := hf.1.ae_eq_mk
  have hf₀mem : MemLp f₀ 2 (m.restrict U) := hf.ae_eq hff₀
  have hfpm : MemLp (fun y => max (f₀ y) 0) 2 (m.restrict U) :=
    hf₀mem.of_le (hf₀m.max measurable_const).aestronglyMeasurable (Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hfmm : MemLp (fun y => max (-f₀ y) 0) 2 (m.restrict U) :=
    hf₀mem.of_le (hf₀m.neg.max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (neg_le_abs _) (abs_nonneg _))
  have hp := hocc (fun y => max (f₀ y) 0) (hf₀m.max measurable_const)
    (fun y => le_max_right _ _) hfpm
  have hm := hocc (fun y => max (-f₀ y) 0) (hf₀m.neg.max measurable_const)
    (fun y => le_max_right _ _) hfmm
  have hlin : hf₀mem.toLp f₀ = hfpm.toLp (fun y => max (f₀ y) 0) -
      hfmm.toLp (fun y => max (-f₀ y) 0) := by
    apply Lp.ext
    filter_upwards [hf₀mem.coeFn_toLp, hfpm.coeFn_toLp, hfmm.coeFn_toLp,
      Lp.coeFn_sub (hfpm.toLp (fun y => max (f₀ y) 0)) (hfmm.toLp (fun y => max (-f₀ y) 0))]
      with x h1 h2 h3 h4
    rw [h1, h4, Pi.sub_apply, h2, h3]
    rcases le_total 0 (f₀ x) with h | h
    · simp [h]
    · simp [h]
  have hlinf : hf.toLp f = hf₀mem.toLp f₀ := MemLp.toLp_congr hf hf₀mem hff₀
  -- the null set
  set N : Set (Fin d → ℝ) := toMeasurable (m.restrict U) {y | f y ≠ f₀ y} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : (m.restrict U) N = 0 := by
    rw [hN, measure_toMeasurable]
    exact ae_iff.1 hff₀
  have hind : MemLp (N.indicator fun _ => (1 : ℝ)) 2 (m.restrict U) := by
    have : (N.indicator fun _ => (1 : ℝ)) =ᵐ[m.restrict U] 0 := by
      rw [indicator_ae_eq_zero]
      exact measure_mono_null inter_subset_left hN0
    exact (MemLp.zero).ae_eq this.symm
  have hi := hocc (N.indicator fun _ => (1 : ℝ)) (measurable_const.indicator hNm)
    (fun y => by by_cases hy : y ∈ N <;> simp [hy]) hind
  have hindzero : hind.toLp (N.indicator fun _ => (1 : ℝ)) = 0 := by
    apply Lp.ext
    have : (N.indicator fun _ => (1 : ℝ)) =ᵐ[m.restrict U] 0 := by
      rw [indicator_ae_eq_zero]
      exact measure_mono_null inter_subset_left hN0
    filter_upwards [hind.coeFn_toLp, Lp.coeFn_zero ℝ 2 (m.restrict U), this] with x h1 h2 h3
    rw [h1, h2, h3]
  filter_upwards [hp.1, hm.1, hp.2, hm.2, hi.1, hi.2,
    Lp.coeFn_sub (G (hfpm.toLp (fun y => max (f₀ y) 0))) (G (hfmm.toLp (fun y => max (-f₀ y) 0))),
    Lp.coeFn_zero ℝ 2 (m.restrict U)] with x hp1 hm1 hp2 hm2 hi1 hi2 hsub hzero
  have h0 : killedOcc K U s⁻¹ (N.indicator fun _ => (1 : ℝ)) x = 0 := by
    rw [hindzero, map_zero] at hi2
    have : (killedOcc K U s⁻¹ (N.indicator fun _ => (1 : ℝ)) x).toReal = 0 := by
      rw [hi2, hzero]; rfl
    rcases ENNReal.toReal_eq_zero_iff _ |>.1 this with h | h
    · exact h
    · exact absurd hi1 (by simp [h])
  have hff : ∀ y ∈ U, y ∉ N → f y = f₀ y := by
    intro y _ hyN
    by_contra hne
    exact hyN (subset_toMeasurable _ _ hne)
  rw [occupation_congr_of_killedOcc_null K U hU s hs f f₀ N hNm hff x h0,
    occupation_eq_toReal_sub K U hU s hs f₀ hf₀m x hp1 hm1]
  have hGx : (G (hf.toLp f)) x = (G (hfpm.toLp (fun y => max (f₀ y) 0))) x -
      (G (hfmm.toLp (fun y => max (-f₀ y) 0))) x := by
    rw [hlinf, hlin, map_sub, hsub, Pi.sub_apply]
  rw [hGx, ← hp2, ← hm2]


open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent in
/-- **The killed-generator identity from the part-process leaf** (dimension `d ≥ 1`). -/
theorem killedGenerator_of_leaf [NeZero d]
    {c ρ : (Fin d → ℝ) → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x)
    (P : SubMarkovKernelSemigroup (Fin d → ℝ)) (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup)
    (D : C0ResolventDatum (Fin d → ℝ)) (hweak : IsWeakEllipticResolvent c ρ D)
    (hlaplace : ∀ (mu : Semigroup.PositiveShift) (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ),
      D.solution mu f x = ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) f x)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (hFOT : FOTPartProcess) :
    KilledGenerator c ρ (K.map LifetimePath.ofContinuousPath) := by
  intro U hU hUb s hs f hf
  have hassoc := association_of_datum hc hρ hcpos hρpos P D hweak hlaplace K hfdd
  obtain ⟨F, hpart, hocc⟩ := hFOT d (wm ρ) (isLocallyFiniteMeasure_wm hρ) (isOpenPosMeasure_wm hρ hρpos)
    (gradDirichletForm hc hρ hcpos hρpos) (gradClosedForm_isRegular hc hρ hcpos hρpos) P hP hF
    K inferInstance hfdd hassoc U hU
  have hα : 0 < s⁻¹ := inv_pos.2 hs
  obtain ⟨G, hG⟩ := exists_isResolvent F hα
  have hf' : MemLp f 2 ((wm ρ).restrict U) := hf
  obtain ⟨u, Du, hBA, hu_ae, hweq⟩ := part_analytic hc hρ hcpos hρpos hU hUb F hpart G hG hf'
  refine ⟨u, Du, hBA, ?_, hweq⟩
  have hocc' := occupation_ae_eq_resolvent (wm ρ) K U hU s hs G
    (fun g hg hg0 hgL => hocc s⁻¹ hα G hG g hg hg0 hgL) f hf'
  exact hu_ae.trans hocc'

end SubdiffusiveProcess.E7
