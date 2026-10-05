module

public import SubdiffusiveProcess.Section10.KilledKernelDomainDomination
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderKilled

@[expose] public section

/-! Transfer a convex enclosing-domain resolvent estimate to an arbitrary
bounded open carrier, using its actual occupation kernels. Zero extension
occurs only in the input data; the supplied law, weight and clock are retained. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory MarkovProcess Set Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderKilled
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumUltracontractive
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- Extending the absolute input by zero preserves its exact weighted Lp norm. -/
theorem memLp_indicator_abs_enclosing {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {U V : Set X} (hU : MeasurableSet U) (hUV : U ⊆ V)
    {f : X → ℝ} {p : ENNReal} (hf : MemLp f p (mu.restrict U)) :
    MemLp (U.indicator (fun x ↦ |f x|)) p (mu.restrict V) ∧
      eLpNorm (U.indicator (fun x ↦ |f x|)) p (mu.restrict V) =
        eLpNorm f p (mu.restrict U) := by
  have hrestrict : (mu.restrict V).restrict U = mu.restrict U :=
    Measure.restrict_restrict_of_subset hUV
  constructor
  · apply (memLp_indicator_iff_restrict hU).mpr
    rw [hrestrict]
    simpa only [Real.norm_eq_abs] using hf.norm
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hU, hrestrict]
    simpa only [Real.norm_eq_abs] using! eLpNorm_norm f hf.aestronglyMeasurable

section Resolvent

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    [IsFiniteMeasure ((weightedMeasure rho).restrict V)]
    {s : ℝ} (hs : 0 < s)

include hD hU hUb hs in
/-- The actual raw killed resolvent preserves nonnegative data a.e. -/
theorem ae_nonneg_killedResolvent {f : Vec d → ℝ}
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U))
    (hf0 : ∀ᵐ x ∂((weightedMeasure rho).restrict U), 0 ≤ f x) :
    ∀ᵐ x ∂((weightedMeasure rho).restrict U), 0 ≤ killedResolvent law U s f x := by
  have hsub := resolventKernel_subinvariant hD hU hUb s hs
  filter_upwards [resolventKernel_integral_ae law U hU s hs _ hsub f
    (hf.integrable (by norm_num)), ae_ae_kernel_of_comp_le hsub hf0] with x hx hpos
  rw [← hx]
  exact integral_nonneg_of_ae hpos

include hD hU hV hUb hVb hs in
/-- Nested carriers compare actual killed resolvents on L² data a.e. -/
theorem ae_abs_killedResolvent_le_enclosing (hUV : U ⊆ V) {f g : Vec d → ℝ}
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U))
    (hg : MemLp g 2 ((weightedMeasure rho).restrict V))
    (hfg : ∀ᵐ x ∂((weightedMeasure rho).restrict U), |f x| ≤ g x)
    (hg0 : ∀ᵐ x ∂((weightedMeasure rho).restrict V), 0 ≤ g x) :
    ∀ᵐ x ∂((weightedMeasure rho).restrict U),
      |killedResolvent law U s f x| ≤ killedResolvent law V s g x := by
  have hmn : (weightedMeasure rho).restrict U ≤ (weightedMeasure rho).restrict V :=
    Measure.restrict_mono hUV le_rfl
  have hk := resolventKernel_subinvariant hD hU hUb s hs
  have he := resolventKernel_subinvariant hD hV hVb s hs
  have hcomp := ae_abs_kernelIntegral_le_of_kernel_le _ _ _ _ hmn
    (resolventKernel_le_of_subset law hU hV hUV s hs) hk he f g
    (hf.integrable (by norm_num)) (hg.integrable (by norm_num)) hfg hg0
  filter_upwards [hcomp, resolventKernel_integral_ae law U hU s hs _ hk f
    (hf.integrable (by norm_num)),
    (resolventKernel_integral_ae law V hV s hs _ he g
      (hg.integrable (by norm_num))).filter_mono
        (Measure.absolutelyContinuous_of_le hmn).ae_le] with x hx hfrow hgrow
  rwa [hfrow, hgrow] at hx

include hD hU hV hUb hVb hs in
/-- Every raw killed resolvent iterate has the same enclosing-domain domination. -/
theorem ae_abs_iterate_killedResolvent_le_enclosing (hUV : U ⊆ V)
    {f : Vec d → ℝ} (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) (N : ℕ) :
    ∀ᵐ x ∂((weightedMeasure rho).restrict U),
      |((killedResolvent law U s)^[N] f) x| ≤
        ((killedResolvent law V s)^[N] (U.indicator (fun y ↦ |f y|))) x := by
  have hbase := (memLp_indicator_abs_enclosing (weightedMeasure rho)
    hU.measurableSet hUV hf).1
  have hiter : ∀ n : ℕ,
      MemLp ((killedResolvent law U s)^[n] f) 2 ((weightedMeasure rho).restrict U) ∧
      MemLp ((killedResolvent law V s)^[n] (U.indicator (fun y ↦ |f y|)))
        2 ((weightedMeasure rho).restrict V) ∧
      (∀ᵐ x ∂((weightedMeasure rho).restrict V),
        0 ≤ ((killedResolvent law V s)^[n] (U.indicator (fun y ↦ |f y|))) x) ∧
      (∀ᵐ x ∂((weightedMeasure rho).restrict U),
        |((killedResolvent law U s)^[n] f) x| ≤
          ((killedResolvent law V s)^[n] (U.indicator (fun y ↦ |f y|))) x) := by
    intro n
    induction n with
    | zero =>
        refine ⟨hf, hbase, Filter.Eventually.of_forall (fun x ↦ ?_), ?_⟩
        · exact indicator_nonneg (fun y _hy ↦ abs_nonneg (f y)) x
        · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
          simp only [Function.iterate_zero_apply, indicator_of_mem hx, le_refl]
    | succ n ih =>
        simp only [Function.iterate_succ_apply']
        exact ⟨memLp_killedResolvent hD hU hUb hs ih.1,
          memLp_killedResolvent hD hV hVb hs ih.2.1,
          ae_nonneg_killedResolvent hD hV hVb hs ih.2.1 ih.2.2.1,
          ae_abs_killedResolvent_le_enclosing hD hU hV hUb hVb hs hUV
            ih.1 ih.2.1 ih.2.2.2 ih.2.2.1⟩
  exact (hiter N).2.2.2

/-- A proved convex-domain estimate transfers to every bounded open subdomain,
including the empty domain. The original L² operator is kept literally. -/
theorem exists_ae_sup_bound_killedResolventLp_pow_of_enclosing
    (hUV : U ⊆ V) (hVcvx : IsOpenBoundedConvexDomain V)
    (hm0 : (weightedMeasure rho) V ≠ 0) (hmtop : (weightedMeasure rho) V ≠ ∞)
    {p0 A F : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hF : 0 < F)
    (hSob : SobolevAssumption c rho V p0 A F) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
        ∀ᵐ x ∂((weightedMeasure rho).restrict U),
          |(((killedResolventLp hD hU hUb s hs) ^ N) f) x| ≤ C * ‖f‖ := by
  obtain ⟨N, hN, C, hC, hbound⟩ :=
    exists_rrk_sup_bound hD hVcvx hm0 hmtop hp0 hA hF hs hSob
  refine ⟨N, hN, C, hC, fun f ↦ ?_⟩
  have hext := memLp_indicator_abs_enclosing (weightedMeasure rho)
    hU.measurableSet hUV (Lp.memLp f)
  have hVnorm := hbound _ hext.1
  have hnorm : eLpNorm (⇑f) 2 ((weightedMeasure rho).restrict U) =
      ENNReal.ofReal ‖f‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  rw [hext.2, hnorm] at hVnorm
  have hiterU : ∀ n : ℕ, MemLp ((killedResolvent law U s)^[n] ⇑f) 2
      ((weightedMeasure rho).restrict U) := by
    intro n
    induction n with
    | zero => simpa only [Function.iterate_zero_apply] using Lp.memLp f
    | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using memLp_killedResolvent hD hU hUb hs ih
  have hUraw : eLpNorm ((killedResolvent law U s)^[N] ⇑f) ∞
      ((weightedMeasure rho).restrict U) ≤ ENNReal.ofReal (C * ‖f‖) := by
    calc
      _ ≤ eLpNorm ((killedResolvent law V s)^[N]
          (U.indicator (fun y ↦ |f y|))) ∞ ((weightedMeasure rho).restrict U) := by
        apply eLpNorm_mono_ae (hiterU N).aestronglyMeasurable
        filter_upwards [ae_abs_iterate_killedResolvent_le_enclosing
          hD hU hVcvx.isOpen hUb hVcvx.isBoundedDomain.isBounded hs hUV
            (Lp.memLp f) N] with x hx
        simpa only [Real.norm_eq_abs] using hx.trans (le_abs_self _)
      _ ≤ eLpNorm ((killedResolvent law V s)^[N]
          (U.indicator (fun y ↦ |f y|))) ∞ ((weightedMeasure rho).restrict V) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hUV le_rfl)
      _ ≤ ENNReal.ofReal (C * ‖f‖) := by
        simpa only [ENNReal.ofReal_mul hC.le] using hVnorm
  have hsup := ae_abs_le_of_eLpNorm_top (by positivity) hUraw
  filter_upwards [hsup, coeFn_killedResolventLp_pow
    (hD := hD) (hU := hU) (hUb := hUb) (hs := hs) N f] with x hx heq
  rwa [heq]

end Resolvent
end SubdiffusiveProcess.Section10
