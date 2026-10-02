import SubdiffusiveProcess.Section10.TorsionExitConsumer
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerDensity
import Mathlib.Topology.Sequences

/-! Every-start killed density gives the starting-point regularity needed by
the upper mean-exit argument. Fatou is used twice; no boundary continuity,
kernel bound or identification with zero-mass torsion is required. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- A sequential Fatou inequality gives lower semicontinuity on the domain.
The proof uses Mathlib's closed-sublevel sequential criterion on the subtype. -/
theorem lowerSemicontinuousOn_of_seq_le_liminf {X : Type*}
    [TopologicalSpace X] [FirstCountableTopology X] {U : Set X} {f : X → ℝ≥0∞}
    (hseq : ∀ x ∈ U, ∀ xs : ℕ → X, (∀ n, xs n ∈ U) →
      Tendsto xs atTop (𝓝 x) → f x ≤ liminf (fun n => f (xs n)) atTop) :
    LowerSemicontinuousOn f U := by
  rw [← lowerSemicontinuous_restrict_iff]
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro B
  apply isSeqClosed_iff_isClosed.mp
  intro xs x hxs hlim
  exact (hseq x x.property (fun n => xs n) (fun n => (xs n).property)
    (continuous_subtype_val.tendsto x |>.comp hlim)).trans
    (liminf_le_of_frequently_le (Eventually.of_forall hxs).frequently)

/-- Fatou in the density variable controls weighted survival along any
sequence of interior starting points. The same weight may be used later for
the positive time discount. -/
theorem weighted_unitSurvival_le_liminf_of_density {d : ℕ}
    {law : Kernel (Vec d) (Path d)} {b : Vec d → ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) {p : ℝ → Vec d → Vec d → ℝ}
    (hp : IsKilledDensity law b U p)
    (hpc : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ U ×ˢ U)) {t : ℝ} (ht : 0 < t)
    {x : Vec d} (hx : x ∈ U) {xs : ℕ → Vec d}
    (hxs : ∀ n, xs n ∈ U) (hlim : Tendsto xs atTop (𝓝 x))
    (w : ℝ≥0∞) (hw : w ≠ ∞) :
    w * law x {q | ENNReal.ofReal t < LifetimePath.exitTime U q} ≤
      liminf (fun n => w * law (xs n)
        {q | ENNReal.ofReal t < LifetimePath.exitTime U q}) atTop := by
  let μ := (weightedMeasure b).restrict U
  have hmeas (z : Vec d) : Measurable (fun y => ENNReal.ofReal (p t z y)) :=
    measurable_density hp ht z
  have hsurv (z : Vec d) (hz : z ∈ U) :
      law z {q | ENNReal.ofReal t < LifetimePath.exitTime U q} =
        ∫⁻ y, ENNReal.ofReal (p t z y) ∂μ := by
    rw [← killedKernel_univ_eq_survival hU t z,
      killedKernel_apply_eq_density hU hp t ht z hz univ MeasurableSet.univ]
    exact setLIntegral_univ _
  have hpoint : ∀ᵐ y ∂μ, liminf (fun n => w * ENNReal.ofReal (p t (xs n) y)) atTop =
      w * ENNReal.ofReal (p t x y) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    have hwithin : Tendsto (fun n => ((t, xs n, y) : ℝ × Vec d × Vec d)) atTop
        (𝓝[Ioi 0 ×ˢ U ×ˢ U] (t, x, y)) := by
      refine tendsto_nhdsWithin_iff.mpr
        ⟨?_, Eventually.of_forall fun n => ⟨ht, hxs n, hy⟩⟩
      exact tendsto_const_nhds.prodMk_nhds (hlim.prodMk_nhds tendsto_const_nhds)
    have hdens := ((hpc (t, x, y) ⟨ht, hx, hy⟩).tendsto).comp hwithin
    exact (ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hdens) (Or.inr hw)).liminf_eq
  calc
    _ = ∫⁻ y, w * ENNReal.ofReal (p t x y) ∂μ := by
      rw [hsurv x hx, lintegral_const_mul w (hmeas x)]
    _ = ∫⁻ y, liminf (fun n => w * ENNReal.ofReal (p t (xs n) y)) atTop ∂μ :=
      (lintegral_congr_ae hpoint).symm
    _ ≤ liminf (fun n => ∫⁻ y, w * ENNReal.ofReal (p t (xs n) y) ∂μ) atTop :=
      lintegral_liminf_le (fun n => measurable_const.mul (hmeas (xs n)))
    _ = _ := by simp_rw [lintegral_const_mul w (hmeas _), ← hsurv _ (hxs _)]

/-- Joint interior continuity of the actual killed density implies lower
semicontinuity of its unnormalized discounted unit occupation at every start. -/
theorem discountedUnitOccupation_lowerSemicontinuousOn_of_density {d : ℕ}
    {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    {b : Vec d → ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    (hdensity : HasContinuousKilledDensityOn b law U) (s : ℝ) :
    LowerSemicontinuousOn (discountedUnitOccupation law U s) U := by
  obtain ⟨p, hp, hpc⟩ := hdensity
  apply lowerSemicontinuousOn_of_seq_le_liminf
  intro x hx xs hxs hlim
  let F : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (Real.exp (-t / s)) *
    law (xs n) {q | ENNReal.ofReal t < LifetimePath.exitTime U q}
  have hF (n : ℕ) : Measurable (F n) :=
    (Real.measurable_exp.comp (measurable_id.neg.div_const s)).ennreal_ofReal.mul
      (measurable_unitSurvival law hU (xs n))
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), liminf (fun n => F n t) atTop := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact weighted_unitSurvival_le_liminf_of_density hU hp hpc ht hx hxs hlim _
        ENNReal.ofReal_ne_top
    _ ≤ _ := lintegral_liminf_le hF

/-- The density route discharges the countable regularity slot without a
separate Feller occupation input. -/
theorem unitDiscountOccupationLSC_of_density {d : ℕ}
    {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    {b : Vec d → ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    (hdensity : HasContinuousKilledDensityOn b law U) :
    UnitDiscountOccupationLSC law U :=
  fun _ => discountedUnitOccupation_lowerSemicontinuousOn_of_density hU hdensity _

/-- Same-speed/energy LocalDiffusion consumer, now with the pointwise
regularity slot discharged by a genuine every-start killed density. -/
theorem localDiffusion_meanExit_le_of_density {d : ℕ}
    {A b : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    {U : Set (Vec d)} (hlocal : LocalDiffusion A b law)
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (hb : CoefficientOn U b) {p Ksob : ℝ} (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob)
    (hdensity : HasContinuousKilledDensityOn b law U) :
    ∀ x ∈ U, meanExit law U x ≤ ENNReal.ofReal
      (torsionConstant p * Ksob * (weightedMeasure b U).toReal ^ (1 - 2 / p)) :=
  localDiffusion_meanExit_le hlocal hU hne hb hp hKsob hSob
    (unitDiscountOccupationLSC_of_density hU.isOpen hdensity)

end SubdiffusiveProcess.Section10
