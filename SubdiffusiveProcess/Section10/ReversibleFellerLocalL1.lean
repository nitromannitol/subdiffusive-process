import SubdiffusiveProcess.Section10.ReversibleCubeKilledRowBound
import SubdiffusiveProcess.Section10.WholeKilledEndpointBound
import SubdiffusiveProcess.Section10.C0TestBoundBorel
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumCarrier

/-! The exact local rough-L1 supplier on the ORIGINAL whole-space semigroup.
Choose time/domain/constant first. Promote continuous tests on the interior
of a compact neighbourhood, then approximate in the finite SUM of each
actual row and the restricted weighted measure. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumCarrier
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open scoped ENNReal NNReal ZeroAtInfty
namespace SubdiffusiveProcess.Section10

/-- Feller plus actual early exit and the proved cube estimates supplies the
unchanged local approximation interface at every start. -/
theorem reversibleFellerLocalL1ApproximationSupplier :
    ReversibleFellerLocalL1ApproximationSupplier := by
  intro d hd a _hapos _ha P hP hF K hK hfdd hD hearly
  letI : IsMarkovKernel K := hK
  letI : IsMarkovKernel (K.map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  intro S hS eps delta heps hdelta
  obtain ⟨S', hS'c, hSS'⟩ := exists_compact_superset hS
  obtain ⟨z, L, hL, hS'W⟩ := exists_axisCube_enclosing_bounded hS'c.isBounded
  let W := axisCube z L
  have hW : IsOpen W := isOpen_axisCube z L
  have hWb : Bornology.IsBounded W := (isBoundedDomain_axisCube z L).isBounded
  have hrc : ∀ C : Set (Vec d), IsCompact C → CoefficientOn C a :=
    fun C hC ↦ (hD.2.1 C hC).2
  have hWtop : (weightedMeasure a) W ≠ ∞ :=
    (weightedMeasure_axisCube_lt_top hrc z L).ne
  letI : IsFiniteMeasure ((weightedMeasure a).restrict W) := isFiniteMeasure_restrict.mpr hWtop
  obtain ⟨eta, heta, hearly'⟩ := hearly W hW S' hS'c hS'W eps heps
  let s : NNReal := ⟨min delta eta / 2, (div_pos (lt_min hdelta heta) two_pos).le⟩
  have hs : 0 < s := by
    rw [← NNReal.coe_pos]
    exact div_pos (lt_min hdelta heta) two_pos
  have hsdelta : (s : ℝ) < delta := by
    change min delta eta / 2 < delta
    linarith [min_le_left delta eta, lt_min hdelta heta]
  have hseta : (s : ℝ) < eta := by
    change min delta eta / 2 < eta
    linarith [min_le_right delta eta, lt_min hdelta heta]
  obtain ⟨A, hA, hrow⟩ := exists_ae_killed_cube_row_bound hd hD z L hL s hs
  let Q := killedKernel (K.map LifetimePath.ofContinuousPath) W hW s
  let mu := (weightedMeasure a).restrict W
  letI : IsFiniteKernel Q := (killedKernel_subMarkov _ W hW s).isFiniteKernel
  have hfull : FullSupportOn mu W :=
    fullSupportOn_weightedMeasure_restrict hW (coefficientOn_axisCube hrc z L)
  have hOmW : interior S' ⊆ W := interior_subset.trans hS'W
  refine ⟨s, hs, hsdelta, W, hW, hWb, hWtop, A, hA, ?_⟩
  intro g hg F hboundF hgb x hx
  letI : IsFiniteKernel (P s) := (P.isSubMarkovKernel s).isFiniteKernel
  apply integral_abs_le_of_c0TestBound (P s x) mu hA hboundF ?_ hg hgb
  intro h hhb
  let H := F
  have hH : 0 ≤ H := hboundF
  let habs : C₀(Vec d, ℝ) :=
    { toFun := fun y ↦ |h y|
      continuous_toFun := continuous_abs.comp h.continuous
      zero_at_infty' := by
        simpa only [abs_zero] using
          (continuous_abs.continuousAt.tendsto.comp h.zero_at_infty') }
  have hhmeas : Measurable (fun y ↦ |h y|) := habs.continuous.measurable
  have hhint : Integrable (fun y ↦ |h y|) mu :=
    Integrable.of_bound hhmeas.aestronglyMeasurable H
      (ae_of_all _ fun y ↦ by simpa only [Real.norm_eq_abs, abs_abs] using hhb y)
  have hhQ : ∀ y, Integrable (fun v ↦ |h v|) (Q y) := fun y ↦
    Integrable.of_bound hhmeas.aestronglyMeasurable H
      (ae_of_all _ fun v ↦ by simpa only [Real.norm_eq_abs, abs_abs] using hhb v)
  have haeQ := ae_integral_le_of_ae_row_bound mu mu Q A hA hrow
    (fun y ↦ |h y|) hhmeas (fun y ↦ abs_nonneg _) hhint hhQ
  have hae : ∀ᵐ y ∂mu, y ∈ interior S' →
      kernelIntegral (P s) habs y ≤ A * (∫ v, |h v| ∂mu) + eps * H := by
    filter_upwards [haeQ] with y hy hyOm
    have hexit := hearly' s hseta y (interior_subset hyOm)
    have hexitR : (K y {w | ContinuousPath.exitTime W w ≤ (s : ENNReal)}).toReal ≤ eps := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hexit
      rwa [ENNReal.toReal_ofReal heps.le] at hh
    have hwhole := whole_integral_le_killed_add_early_exit P hP K hfdd W hW s
      (fun v ↦ |h v|) hhmeas H hH
      (fun v ↦ by simpa only [abs_abs] using hhb v) y
    change (∫ v, |h v| ∂P s y) ≤ _
    exact hwhole.trans (add_le_add hy (by nlinarith [mul_le_mul_of_nonneg_left hexitR hH]))
  have hpoint := le_of_ae_le isOpen_interior
    (fun V hV hVO hVne ↦ hfull V hV (hVO.trans hOmW) hVne)
    (hF.mapsC0 s habs).1.continuousOn hae
  exact hpoint x (hSS' hx)

end SubdiffusiveProcess.Section10
