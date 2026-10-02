import SubdiffusiveProcess.Section10.TorsionLevelEnergy
import SubdiffusiveProcess.Section10.TorsionIteration
import SubdiffusiveProcess.Section10.TorsionExistence

/-! The weak torsion bound from a pure all-H10 killed Sobolev estimate. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal
namespace SubdiffusiveProcess.Section10

/-- The unit-forcing torsion upper bound, with p>2 and exact mass exponent. -/
theorem weakTorsion_ae_le {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A b : Vec d → ℝ} (hb : CoefficientOn U b)
    {p Ksob : ℝ} (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob)
    (u : H10Function U) (hu : IsWeakTorsion A b U u) :
    ∀ᵐ x ∂(weightedMeasure b).restrict U, u.toFun x ≤
      torsionConstant p * Ksob * (weightedMeasure b U).toReal ^ (1 - 2 / p) := by
  let μ := (weightedMeasure b).restrict U
  letI : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  letI : IsFiniteMeasure μ := variational_weighted_isFiniteMeasure hU.isOpen.measurableSet hb
  have hM : 0 < (μ univ).toReal := ENNReal.toReal_pos
    (weightedMeasure_restrict_open_pos hU.isOpen hb univ isOpen_univ
      (by simpa only [univ_inter] using hne)).ne' (measure_ne_top μ univ)
  have hu2 : MemLp u.toFun 2 μ :=
    memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hb u.toH1Function.memL2
  have hlevel := torsion_positive_level_bound hU hb hKsob.le hSob u hu
  have hlevel' : ∀ h : ℝ, 0 ≤ h →
      (eLpNorm (fun x => max (u.toFun x - h) 0) (ENNReal.ofReal p) μ) ^ 2 ≤
      ENNReal.ofReal Ksob * ∫⁻ x, ENNReal.ofReal (max (u.toFun x - h) 0) ∂μ := by
    simpa only [abs_one, one_mul] using hlevel
  simpa only [μ, Measure.restrict_apply_univ] using
    torsion_ae_le_of_level_estimates μ hp hKsob hM hu2 hlevel'

/-- The same constant controls the absolute value; no nonnegativity premise
or previously bounded solution is required. -/
theorem weakTorsion_ae_abs_le {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A b : Vec d → ℝ} (hb : CoefficientOn U b)
    {p Ksob : ℝ} (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob)
    (u : H10Function U) (hu : IsWeakTorsion A b U u) :
    ∀ᵐ x ∂(weightedMeasure b).restrict U, |u.toFun x| ≤
      torsionConstant p * Ksob * (weightedMeasure b U).toReal ^ (1 - 2 / p) := by
  let μ := (weightedMeasure b).restrict U
  letI : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  letI : IsFiniteMeasure μ := variational_weighted_isFiniteMeasure hU.isOpen.measurableSet hb
  have hM : 0 < (μ univ).toReal := ENNReal.toReal_pos
    (weightedMeasure_restrict_open_pos hU.isOpen hb univ isOpen_univ
      (by simpa only [univ_inter] using hne)).ne' (measure_ne_top μ univ)
  have hn2 : MemLp (-u).toFun 2 μ :=
    memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hb (-u).toH1Function.memL2
  have hnsol : IsMassiveWeakSolutionOn A b 0 U (-u).toH1Function (fun _ => -1) :=
    isMassiveWeakSolutionOn_neg hu
  have hnlevel := torsion_positive_level_bound hU hb hKsob.le hSob (-u) hnsol
  have hnlevel' : ∀ h : ℝ, 0 ≤ h →
      (eLpNorm (fun x => max ((-u).toFun x - h) 0) (ENNReal.ofReal p) μ) ^ 2 ≤
      ENNReal.ofReal Ksob * ∫⁻ x, ENNReal.ofReal (max ((-u).toFun x - h) 0) ∂μ := by
    simpa only [abs_neg, abs_one, one_mul] using hnlevel
  have hneg := torsion_ae_le_of_level_estimates μ hp hKsob hM hn2 hnlevel'
  have hpos := weakTorsion_ae_le hU hne hb hp hKsob hSob u hu
  filter_upwards [hpos, hneg] with x hx hnx
  simp only [μ, Measure.restrict_apply_univ] at hnx
  change (-1 : ℝ) * u.toFun x ≤ _ at hnx
  rw [neg_one_mul] at hnx
  exact abs_le.mpr ⟨by linarith, hx⟩

/-- Essential-supremum bound on the native solution in the original speed measure. -/
theorem weakTorsion_eLpNorm_top_le {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A b : Vec d → ℝ} (hb : CoefficientOn U b)
    {p Ksob : ℝ} (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob)
    (u : H10Function U) (hu : IsWeakTorsion A b U u) :
    eLpNorm u.toFun ⊤ ((weightedMeasure b).restrict U) ≤
      ENNReal.ofReal (torsionConstant p * Ksob * (weightedMeasure b U).toReal ^ (1 - 2 / p)) :=
  eLpNormEssSup_le_of_ae_bound
    ((weakTorsion_ae_abs_le hU hne hb hp hKsob hSob u hu).mono
      fun _ hx => by simpa only [Real.norm_eq_abs] using hx)

/-- The signed essential supremum, on the extended-real carrier. -/
theorem weakTorsion_essSup_le {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A b : Vec d → ℝ} (hb : CoefficientOn U b)
    {p Ksob : ℝ} (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob)
    (u : H10Function U) (hu : IsWeakTorsion A b U u) :
    essSup (fun x => (u.toFun x : EReal)) ((weightedMeasure b).restrict U) ≤
      ((torsionConstant p * Ksob * (weightedMeasure b U).toReal ^ (1 - 2 / p) : ℝ) : EReal) := by
  apply essSup_le_of_ae_le
  filter_upwards [weakTorsion_ae_le hU hne hb hp hKsob hSob u hu] with x hx
  exact EReal.coe_le_coe_iff.mpr hx




end SubdiffusiveProcess.Section10
