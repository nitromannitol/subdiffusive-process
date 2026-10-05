module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.HilbertWeakMeasurability
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section

/-!
# Measurability of weak Hessians from measurable gradients

A weak derivative is a closed, unbounded operation on `L²`, so measurability
does not follow from continuity.  Smooth compactly supported weak tests are
dense in scalar `L²` by CoarseGraining's `TestSubmodule` API.  On those tests,
the weak derivative identity rewrites every scalar probe of the derivative as
a continuous scalar probe of the primal field.  Approximation of an arbitrary
`L²` probe and `measurable_of_forall_real_inner_right` then give strong Borel
measurability of the derivative class.

This is the missing closed-operator step for the manuscript's literal
Hessian observable `B_z`.
-/

open Filter MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/- `L²` is used as a Borel Hilbert carrier below.  CoarseGraining declares the
same instances for `HilbertVectorL2`; this scalar counterpart is needed for
the coordinatewise weak-Hessian argument. -/
noncomputable instance instMeasurableSpaceScalarL2
    {d : ℕ} {U : Set (Vec d)} : MeasurableSpace (ScalarL2 U) := borel _

noncomputable instance instBorelSpaceScalarL2
    {d : ℕ} {U : Set (Vec d)} : BorelSpace (ScalarL2 U) := ⟨rfl⟩

/-- Continuous restriction of a Hilbert-vector `L²` class to a smaller
domain.  The codomain measure is definitionally presented as
`volume.restrict V`; the proof identifies it with restricting
`volume.restrict U` once more. -/
def hilbertVectorL2RestrictCLM {d : ℕ} {U V : Set (Vec d)}
    (hVU : V ⊆ U) : HilbertVectorL2 U →L[ℝ] HilbertVectorL2 V := by
  have hmeasure : volumeMeasureOn V ≤ volumeMeasureOn U :=
    Measure.restrict_mono_set volume hVU
  let restrictFun : HilbertVectorL2 U → HilbertVectorL2 V := fun f =>
    ((Lp.memLp f).mono_measure hmeasure).toLp f
  refine @LinearMap.mkContinuous ℝ ℝ (HilbertVectorL2 U)
    (HilbertVectorL2 V) _ _ _ _ _ _ (RingHom.id ℝ)
    ⟨⟨restrictFun, ?_⟩, ?_⟩ 1 ?_
  · intro f g
    apply Lp.ext
    filter_upwards
        [(Lp.coeFn_add f g).filter_mono (ae_mono hmeasure),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure hmeasure),
          MemLp.coeFn_toLp ((Lp.memLp g).mono_measure hmeasure),
          MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_measure hmeasure),
          Lp.coeFn_add
            (((Lp.memLp f).mono_measure hmeasure).toLp f)
            (((Lp.memLp g).mono_measure hmeasure).toLp g)]
      with x hfg hf hg htarget htargetAdd
    simp only [restrictFun]
    rw [htarget, hfg, htargetAdd]
    simp only [Pi.add_apply, hf, hg]
  · intro c f
    apply Lp.ext
    filter_upwards
        [(Lp.coeFn_smul c f).filter_mono (ae_mono hmeasure),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure hmeasure),
          MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_measure hmeasure),
          Lp.coeFn_smul c (((Lp.memLp f).mono_measure hmeasure).toLp f)]
      with x hcf hf htarget htargetSmul
    simp only [restrictFun]
    rw [htarget, hcf]
    simp only [RingHom.id_apply]
    rw [htargetSmul]
    simp only [Pi.smul_apply, hf]
  · intro f
    change ‖((Lp.memLp f).mono_measure hmeasure).toLp f‖ ≤ 1 * ‖f‖
    rw [one_mul, Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
      (eLpNorm_mono_measure _ hmeasure)

/-- Restriction preserves Borel measurability of Hilbert-vector `L²`
families. -/
theorem Measurable.hilbertVectorL2_restrict
    {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {f : Omega → HilbertVectorL2 U} (hf : Measurable f) :
    Measurable fun omega => hilbertVectorL2RestrictCLM hVU (f omega) :=
  (hilbertVectorL2RestrictCLM hVU).continuous.measurable.comp hf

theorem hilbertVectorL2RestrictCLM_coeFn
    {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    (f : HilbertVectorL2 U) :
    hilbertVectorL2RestrictCLM hVU f =ᵐ[volumeMeasureOn V] f := by
  change
    ((Lp.memLp f).mono_measure
      (Measure.restrict_mono_set volume hVU)).toLp f =ᵐ[volumeMeasureOn V] f
  exact MemLp.coeFn_toLp _

/-- A pointwise restriction of a measurable Sobolev gradient remains a
measurable Hilbert `L²` family on the smaller domain. -/
theorem measurable_gradToHilbertVectorL2_of_grad_eq_restrict
    {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    (uU : Omega → H1Function U) (uV : Omega → H1Function V)
    (hgradU : Measurable fun omega => (uU omega).gradToHilbertVectorL2)
    (hgradEq : ∀ omega, (uV omega).grad = (uU omega).grad) :
    Measurable fun omega => (uV omega).gradToHilbertVectorL2 := by
  have heq : (fun omega => (uV omega).gradToHilbertVectorL2) =
      fun omega => hilbertVectorL2RestrictCLM hVU
        (uU omega).gradToHilbertVectorL2 := by
    funext omega
    apply Lp.ext
    filter_upwards
        [(uV omega).coeFn_gradToHilbertVectorL2,
          hilbertVectorL2RestrictCLM_coeFn hVU
            (uU omega).gradToHilbertVectorL2,
          ((uU omega).coeFn_gradToHilbertVectorL2.filter_mono
            (ae_mono (Measure.restrict_mono_set volume hVU)))]
      with x hV hrestrict hU
    rw [hV, hrestrict, hU, hgradEq omega]
  rw [heq]
  exact Measurable.hilbertVectorL2_restrict hVU hgradU

/-- If an `L²` family is measurable and has an `L²` weak partial derivative
in every sample, then the derivative classes form a measurable `L²` family.

The derivative representatives need not be selected measurably: uniqueness
of their scalar weak-test pairings and density force measurability of any
pointwise choice. -/
theorem measurable_weakPartialDerivativeScalarL2
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : volume U ≠ ⊤) (i : Fin d)
    (f g : Omega → Vec d → ℝ)
    (hfL2 : ∀ omega, MemScalarL2 U (f omega))
    (hgL2 : ∀ omega, MemScalarL2 U (g omega))
    (hfmeas : Measurable fun omega => toScalarL2 (hfL2 omega))
    (hweak : ∀ omega, HasWeakPartialDerivOn U i (f omega) (g omega)) :
    Measurable fun omega => toScalarL2 (hgL2 omega) := by
  let : MeasureTheory.IsSeparable (volumeMeasureOn U) := inferInstance
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (ScalarL2 U) :=
    MeasureTheory.Lp.SecondCountableTopology
  let F : Omega → ScalarL2 U := fun omega => toScalarL2 (hfL2 omega)
  let G : Omega → ScalarL2 U := fun omega => toScalarL2 (hgL2 omega)
  have htest : ∀ phi : H1WeakTestFunction U,
      Measurable fun omega => inner ℝ (G omega) phi.toScalarL2 := by
    intro phi
    have heq : (fun omega => inner ℝ (G omega) phi.toScalarL2) =
        fun omega => -inner ℝ (F omega) (phi.derivToScalarL2 i) := by
      funext omega
      have hGae := coeFn_toScalarL2 (hgL2 omega)
      have hFae := coeFn_toScalarL2 (hfL2 omega)
      have hphi := phi.coeFn_toScalarL2
      have hdphi := phi.coeFn_derivToScalarL2 i
      have hweak' := hweak omega phi phi.smooth phi.compactSupport phi.support_subset
      calc
        inner ℝ (G omega) phi.toScalarL2 =
            ∫ x in U, g omega x * phi x ∂volume := by
          rw [scalarInner_eq_integral]
          apply integral_congr_ae
          filter_upwards [hGae, hphi] with x hxg hxphi
          rw [hxg, hxphi]
        _ = -∫ x in U, f omega x * phi.deriv i x ∂volume := by
          have hweak'' :
              ∫ x in U, f omega x * phi.deriv i x ∂volume =
                -∫ x in U, g omega x * phi x ∂volume := by
            simpa [H1WeakTestFunction.deriv] using hweak'
          linarith
        _ = -inner ℝ (F omega) (phi.derivToScalarL2 i) := by
          rw [scalarInner_eq_integral]
          congr 1
          apply integral_congr_ae
          filter_upwards [hFae, hdphi] with x hxf hxdphi
          rw [hxf, hxdphi]
    rw [heq]
    exact ((continuous_id.inner continuous_const).measurable.comp hfmeas).neg
  apply measurable_of_forall_real_inner_right
  intro y
  have hy : y ∈ closure (Set.range fun phi : H1WeakTestFunction U => phi.toScalarL2) :=
    denseRange_h1WeakTestFunction_toScalarL2 hUopen hUfinite y
  have hnear : ∀ n : ℕ, ∃ phi : H1WeakTestFunction U,
      dist y phi.toScalarL2 < (1 : ℝ) / (n + 1) := by
    intro n
    obtain ⟨z, hz, hdist⟩ := (Metric.mem_closure_iff.1 hy)
      ((1 : ℝ) / (n + 1)) (by positivity)
    rcases hz with ⟨phi, rfl⟩
    exact ⟨phi, hdist⟩
  choose phi hphi using hnear
  have hphi_tendsto : Tendsto (fun n => (phi n).toScalarL2) atTop (nhds y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hnonneg : ∀ n, 0 ≤ dist ((phi n).toScalarL2) y := fun n => dist_nonneg
    have hupper : ∀ n, dist ((phi n).toScalarL2) y ≤ (1 : ℝ) / (n + 1) := by
      intro n
      rw [dist_comm]
      exact (hphi n).le
    exact squeeze_zero' (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hupper) tendsto_one_div_add_atTop_nhds_zero_nat
  apply measurable_of_tendsto_metrizable
    (f := fun n omega => inner ℝ (G omega) (phi n).toScalarL2)
  · exact fun n => htest (phi n)
  · rw [tendsto_pi_nhds]
    intro omega
    exact tendsto_const_nhds.inner hphi_tendsto

/-- Coordinatewise version for a sample-dependent weak Hessian witness. -/
theorem measurable_weakHessianCoordScalarL2
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : volume U ≠ ⊤) (u : Omega → H1Function U)
    (H : ∀ omega, HasWeakHessianOn U (u omega))
    (hgrad : Measurable fun omega => (u omega).gradToHilbertVectorL2)
    (i j : Fin d) :
    Measurable fun omega => (H omega).hessCoordToScalarL2 i j := by
  have hfmeas : Measurable fun omega =>
      toScalarL2 ((u omega).grad_memVectorL2.eval i) := by
    have hcoord : (fun omega =>
        toScalarL2 ((u omega).grad_memVectorL2.eval i)) =
        fun omega => hilbertVectorCoordToScalarL2 i
          (u omega).gradToHilbertVectorL2 := by
      funext omega
      apply MeasureTheory.Lp.ext
      filter_upwards
          [coeFn_toScalarL2 ((u omega).grad_memVectorL2.eval i),
            coeFn_hilbertVectorCoordToScalarL2 i
              (u omega).gradToHilbertVectorL2,
            (u omega).coeFn_gradToHilbertVectorL2]
        with x hleft hright hgradpoint
      rw [hleft, hright, hgradpoint]
      rfl
    rw [hcoord]
    exact (hilbertVectorCoordToScalarL2 i).continuous.measurable.comp hgrad
  exact measurable_weakPartialDerivativeScalarL2 hUopen hUfinite j
    (fun omega x => (u omega).grad x i)
    (fun omega => (H omega).hess i j)
    (fun omega => (u omega).grad_memVectorL2.eval i)
    (fun omega => (H omega).hess_memL2 i j)
    hfmeas (fun omega => (H omega).weak_second i j)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
