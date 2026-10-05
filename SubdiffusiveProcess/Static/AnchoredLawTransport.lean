module

public import SubdiffusiveProcess.Static.LocalEstimateClauses
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SampleLawBridge
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section

/-! # Restriction of measurable moment suppliers to the anchored carrier -/

open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The exact sample law appearing in the static principal. -/
abbrev localAnchoredLaw {d : ℕ} (M : GMCModel d) : Measure (AnchoredC11Sample d) :=
  (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
    (measure_anchoredC11GoodSet_eq_one M)).toMeasure

/-- The anchored inclusion has exactly the original potential-sample law. -/
theorem measurePreserving_anchoredVal {d : ℕ} (M : GMCModel d) :
    MeasurePreserving (Subtype.val : AnchoredC11Sample d → PotentialSample d)
      (localAnchoredLaw M) M.P.toMeasure := by
  refine ⟨measurable_subtype_coe, ?_⟩
  ext S hS
  rw [Measure.map_apply measurable_subtype_coe hS]
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.anchoredC11SampleLaw_preimage M
    (measurableSet_anchoredC11GoodSet d) (measure_anchoredC11GoodSet_eq_one M) S

/-- Nonnegative moments are unchanged by restriction to the full anchored event. -/
theorem anchored_moment_eq {d : ℕ} (M : GMCModel d) (K : PotentialSample d → ℝ)
    (hK : Measurable K) (q : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (K ω.1 ^ q) ∂localAnchoredLaw M) =
      ∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂M.P.toMeasure := by
  exact (measurePreserving_anchoredVal M).lintegral_comp
    (ENNReal.measurable_ofReal.comp (hK.pow_const q))

/-- A common random factor and an arbitrary almost-sure estimate property
restrict to the anchored law without any moment loss. -/
theorem exists_anchored_randomConstant {d : ℕ} (M : GMCModel d)
    (q C : ℝ) (P : PotentialSample d → ℝ → Prop)
    (h : ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂M.P.toMeasure) ≤ ENNReal.ofReal C ∧
        ∀ᵐ ω ∂M.P.toMeasure, P ω (K ω)) :
    ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂localAnchoredLaw M) ≤ ENNReal.ofReal C ∧
        ∀ᵐ ω ∂localAnchoredLaw M, P ω.1 (K ω) := by
  obtain ⟨K, hK, hKone, hKmom, hP⟩ := h
  refine ⟨fun ω => K ω.1, hK.comp measurable_subtype_coe, fun ω => hKone ω.1, ?_, ?_⟩
  · rwa [anchored_moment_eq M K hK q]
  · exact (measurePreserving_anchoredVal M).quasiMeasurePreserving.ae hP

end SubdiffusiveProcess.Static
