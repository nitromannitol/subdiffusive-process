module

public import Mathlib
public import SubdiffusiveProcess.Sobolev.WeakGradient
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.Path.ExitTime
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Fix 10, `lim:sec-process-measure`: an indicator sandwich converts a positive test into a set bound. -/
theorem aux_lim_transition_domination_test_envelope
    {X : Type*} [MeasurableSpace X] (mu nu : Measure X) (K V : Set X)
    (hK : MeasurableSet K) (hV : MeasurableSet V) (f : X → ℝ≥0∞)
    (hlow : K.indicator (fun _ => 1) ≤ f) (hupp : f ≤ V.indicator (fun _ => 1))
    (h : (∫⁻ x, f x ∂mu) ≤ ∫⁻ x, f x ∂nu) : mu K ≤ nu V := by
  calc
    mu K = ∫⁻ x, K.indicator (fun _ => 1) x ∂mu := (lintegral_indicator_one hK).symm
    _ ≤ ∫⁻ x, f x ∂mu := lintegral_mono hlow
    _ ≤ ∫⁻ x, f x ∂nu := h
    _ ≤ ∫⁻ x, V.indicator (fun _ => 1) x ∂nu := lintegral_mono hupp
    _ = nu V := lintegral_indicator_one hV

/-- Fix 10, `lim:sec-process-measure`: a compact/open Urysohn test with both indicator bounds. -/
theorem aux_lim_transition_domination_bump_sandwich
    {d : ℕ} (K V : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) ∧ tsupport f ⊆ V ∧
      K.indicator (fun _ => (1 : ℝ≥0∞)) ≤ (fun x => ENNReal.ofReal (f x)) ∧
      (fun x => ENNReal.ofReal (f x)) ≤ V.indicator (fun _ => 1) := by
  obtain ⟨f, hfone, hfcompact, hfsupp, hf⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
  refine ⟨⟨f, hfcompact⟩, fun x => (hf x).1, hfsupp, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ K
    · simpa only [Set.indicator_of_mem hx] using!
        (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal (f x) by simp [hfone hx])
    · simp [hx]
  · intro x
    by_cases hx : x ∈ V
    · simp only [Set.indicator_of_mem hx]
      exact (ENNReal.ofReal_le_ofReal (hf x).2).trans_eq (by simp)
    · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hfsupp h))
      simpa only [Set.indicator_of_notMem hx] using!
        (show ENNReal.ofReal (f x) ≤ (0 : ℝ≥0∞) by simp [hz])

/-- Fix 10, `lim:sec-process-measure`: positive tests supported in U dominate all compact subsets of U. -/
theorem aux_lim_transition_domination_compact_of_tests
    {d : ℕ} (mu nu : Measure (SpatialCoordinates d)) [nu.OuterRegular]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (h : ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) → tsupport f ⊆ U →
      (∫⁻ x, ENNReal.ofReal (f x) ∂mu) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂nu)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hKU : K ⊆ U) :
    mu K ≤ nu K := by
  rw [Set.measure_eq_iInf_isOpen K nu]
  refine le_iInf fun V => le_iInf fun hKV => le_iInf fun hV => ?_
  obtain ⟨f, hf, hfsupp, hlo, hhi⟩ := aux_lim_transition_domination_bump_sandwich
    K (U ∩ V) hK (hU.inter hV) (fun x hx => ⟨hKU hx, hKV hx⟩)
  exact (aux_lim_transition_domination_test_envelope mu nu K (U ∩ V)
    hK.measurableSet (hU.inter hV).measurableSet _ hlo hhi
    (h f hf (hfsupp.trans inter_subset_left))).trans (measure_mono inter_subset_right)

/-- Fix 10, `lim:sec-process-measure`: the compact bounds give a local measure inequality. -/
theorem aux_lim_transition_domination_restrict_le_of_tests
    {d : ℕ} (mu nu : Measure (SpatialCoordinates d)) [mu.InnerRegular] [nu.OuterRegular]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (h : ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) → tsupport f ⊆ U →
      (∫⁻ x, ENNReal.ofReal (f x) ∂mu) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂nu) :
    mu.restrict U ≤ nu := by
  apply Measure.le_iff.2
  intro A hA
  rw [Measure.restrict_apply hA, (hA.inter hU.measurableSet).measure_eq_iSup_isCompact mu]
  refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hK => ?_
  exact (aux_lim_transition_domination_compact_of_tests mu nu U hU h K hK
    (hKA.trans inter_subset_right)).trans (measure_mono (hKA.trans inter_subset_left))

/-- Section 10, auditor Fixes 9/10, `lim:sec-process-measure`. -/
theorem aux_lim_transition_domination_ac_from_tests
    {d : ℕ} (mu nu : Measure (SpatialCoordinates d))
    [IsFiniteMeasure mu] [IsLocallyFiniteMeasure nu]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hsupp : mu.restrict U = mu)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) → tsupport f ⊆ U →
      (∫⁻ x, ENNReal.ofReal (f x) ∂mu) ≤ ENNReal.ofReal (C * ∫ x, f x ∂nu)) :
    mu ≪ nu := by
    have : IsFiniteMeasureOnCompacts nu := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    have hnu : nu.OuterRegular := inferInstance
    have hmu : mu.InnerRegular := inferInstance
    have hsmul : ((ENNReal.ofReal C) • nu).OuterRegular := Measure.OuterRegular.smul nu ENNReal.ofReal_ne_top
    have hle : mu.restrict U ≤ (ENNReal.ofReal C) • nu := by
      refine aux_lim_transition_domination_restrict_le_of_tests mu ((ENNReal.ofReal C) • nu) U hU ?_
      intro f hf0 hfsupp
      rw [MeasureTheory.lintegral_smul_measure]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (CompactlySupportedContinuousMap.integrable (μ := nu) f) (Filter.Eventually.of_forall hf0)]
      rw [smul_eq_mul, ← ENNReal.ofReal_mul hC]
      exact h f hf0 hfsupp
    rw [hsupp] at hle
    exact Measure.absolutelyContinuous_of_le_smul hle


end SubdiffusiveProcess.Paper
