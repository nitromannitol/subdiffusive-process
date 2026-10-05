module

public import SubdiffusiveProcess.Probability.Diffusion.HuntCorrection
public import SubdiffusiveProcess.Probability.Diffusion.VariationalIdentification

@[expose] public section

/-!
# A continuous killed density from the precise Hunt inputs

The actual exit correction is subtracted from the free Gaussian. A positive
part gives a globally nonnegative representative; the equality of all set
integrals proves the density identity. Joint continuity follows from the
explicit interior-continuity input for the correction.

The final diffusion theorem remains conditional on the Brownian part-form
identification and the two Hunt inputs. These are not inhabited here.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The Gaussian minus the actual exit correction, with a nonnegative
totalization. Under Hunt's identity this is a density of the killed law. -/
def huntDensity (U : Set (Vec d)) (t : ℝ) (x y : Vec d) : ℝ :=
  max (laplacianDensity t x y - huntCorrection U t x y) 0

theorem huntDensity_nonneg (U : Set (Vec d)) (t : ℝ) (x y : Vec d) :
    0 ≤ huntDensity U t x y := le_max_right _ _

theorem measurable_uncurry_huntDensity (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ) :
    Measurable (Function.uncurry (huntDensity U t)) := by
  exact ((measurable_uncurry_laplacianDensity (d := d) t).sub
    (measurable_uncurry_huntCorrection U hU t)).max measurable_const

/-- Hunt's identity and the unconditional path partition give the additive
Gaussian decomposition at every starting point in the domain. -/
theorem lintegral_gaussian_eq_killed_add_hunt (hH : BrownianHuntIdentity d)
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U)
    (B : Set (Vec d)) (hB : MeasurableSet B) :
    (∫⁻ y in B ∩ U, ENNReal.ofReal (laplacianDensity t x y)) =
      killedKernel (laplacianLaw d) U hU (Real.toNNReal t) x B +
        ∫⁻ y in B ∩ U, ENNReal.ofReal (huntCorrection U t x y) := by
  have h := laplacianSemigroup_eq_killed_add_postExit U hU t x B hB
  rw [laplacianSemigroup_eq_withDensity ht x,
    withDensity_apply _ (hB.inter hU.measurableSet), hH U hU hUb t ht x hx B hB] at h
  exact h

/-- Equality of the set integrals forces domination of the correction density
almost everywhere. No pointwise density identification is assumed. -/
theorem huntCorrection_le_gaussian_ae (hH : BrownianHuntIdentity d)
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    (fun y => ENNReal.ofReal (huntCorrection U t x y)) ≤ᵐ[volume.restrict U]
      fun y => ENNReal.ofReal (laplacianDensity t x y) := by
  have hr : Measurable (fun y => ENNReal.ofReal (huntCorrection U t x y)) :=
    ((measurable_uncurry_huntCorrection U hU t).comp measurable_prodMk_left).ennreal_ofReal
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hr ?_
  intro B hB _
  rw [Measure.restrict_restrict hB]
  rw [lintegral_gaussian_eq_killed_add_hunt hH hU hUb ht hx B hB]
  exact le_add_left le_rfl

/-- Subtraction is legitimate: the correction has finite total mass on every
measurable subset, bounded by the Gaussian probability measure. -/
theorem lintegral_huntDensity_eq_killed (hH : BrownianHuntIdentity d)
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U)
    (B : Set (Vec d)) (hB : MeasurableSet B) :
    (∫⁻ y in B ∩ U, ENNReal.ofReal (huntDensity U t x y)) =
      killedKernel (laplacianLaw d) U hU (Real.toNNReal t) x B := by
  have hr : Measurable (fun y => ENNReal.ofReal (huntCorrection U t x y)) :=
    ((measurable_uncurry_huntCorrection U hU t).comp measurable_prodMk_left).ennreal_ofReal
  have hle : (fun y => ENNReal.ofReal (huntCorrection U t x y)) ≤ᵐ[volume.restrict (B ∩ U)]
      fun y => ENNReal.ofReal (laplacianDensity t x y) := by
    simpa only [Measure.restrict_restrict hB, Set.inter_comm] using!
      (ae_restrict_of_ae (s := B) (huntCorrection_le_gaussian_ae hH hU hUb ht hx))
  have hfinG : (∫⁻ y in B ∩ U, ENNReal.ofReal (laplacianDensity t x y)) ≠ ∞ := by
    rw [← withDensity_apply _ (hB.inter hU.measurableSet),
      ← laplacianSemigroup_eq_withDensity ht x]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      ((laplacianSemigroup d).isSubMarkovKernel _ |>.measure_le_one x (B ∩ U))
  have hfinR : (∫⁻ y in B ∩ U, ENNReal.ofReal (huntCorrection U t x y)) ≠ ∞ :=
    ne_top_of_le_ne_top hfinG (lintegral_mono_ae hle)
  have heq : (fun y => ENNReal.ofReal (huntDensity U t x y)) =
      fun y => ENNReal.ofReal (laplacianDensity t x y) -
        ENNReal.ofReal (huntCorrection U t x y) := by
    funext y
    rw [huntDensity, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (show (0 : ENNReal) ≤ _ from bot_le),
      ENNReal.ofReal_sub _ (huntCorrection_nonneg U t x y)]
  rw [heq, lintegral_sub hr hfinR hle,
    lintegral_gaussian_eq_killed_add_hunt hH hU hUb ht hx B hB]
  exact ENNReal.add_sub_cancel_right hfinR

/-- Hunt's fixed-horizon identity gives all three measurable killed-density
clauses, for the already constructed Brownian law. -/
theorem isKilledDensity_huntDensity (hH : BrownianHuntIdentity d)
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    IsKilledDensity (laplacianLaw d) (fun _ => 1) U (huntDensity U) := by
  refine ⟨fun t _ => measurable_uncurry_huntDensity U hU t,
    fun t _ x _ y _ => huntDensity_nonneg U t x y, ?_⟩
  intro t ht x hx B hB
  rw [← killedKernel_apply_law _ hU t x B hB]
  simpa only [weightedMeasure, ENNReal.ofReal_one, withDensity_const, one_smul] using
    (lintegral_huntDensity_eq_killed hH hU hUb ht hx B hB).symm

/-- The precise remaining Hunt theorems imply the complete continuous-density
target on every bounded open set and for every starting point. -/
theorem continuousKilledDensities_laplacianLaw_of_hunt
    (hH : BrownianHuntIdentity d) (hC : BrownianHuntContinuity d) :
    Input.ContinuousKilledDensities (fun _ => 1) (laplacianLaw d) := by
  intro U hU hUb
  obtain ⟨hmeas, hpos, hmass⟩ := isKilledDensity_huntDensity hH hU hUb
  refine ⟨huntDensity U, hmeas, hpos, hmass, ?_⟩
  have hg := (continuousOn_laplacianDensity (d := d)).mono
    (show Ioi (0 : ℝ) ×ˢ U ×ˢ U ⊆ Ioi 0 ×ˢ univ ×ˢ univ from
      fun _ hz => ⟨hz.1, mem_univ _, mem_univ _⟩)
  exact continuous_max.comp_continuousOn
    ((hg.sub (hC U hU hUb)).prodMk continuousOn_const)

/-- Conditional constant-coefficient witness with all three remaining
Brownian-specific inputs named. This is not an unconditional existence theorem. -/
theorem localDiffusionData_laplacianLaw_of_partForm_and_hunt
    (hpart : BrownianVariationalIdentification d)
    (hH : BrownianHuntIdentity d) (hC : BrownianHuntContinuity d) :
    LocalDiffusionData (fun _ => 1) (fun _ => 1) (laplacianLaw d) :=
  localDiffusionData_laplacianLaw_of_variationalIdentification hpart
    (continuousKilledDensities_laplacianLaw_of_hunt hH hC)

end SubdiffusiveProcess.Probability.Diffusion
