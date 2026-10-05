module

public import SubdiffusiveProcess.Probability.CopyLayerBlock
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

@[expose] public section

/-! # Measurable limits under single-coordinate resampling

A real sequence defines a measurable limit version by its limsup. Almost sure
convergence passes from a represented field to its law and to every independently
resampled coordinate. These results do not supply any influence estimate.
-/

open Filter MeasureTheory
open scoped Topology ENNReal

namespace SubdiffusiveProcess.Probability
noncomputable section

variable {X Ω I : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- A canonical real-valued version of the limit, defined also off convergence. -/
def realSequenceLimit (f : ℕ → X → ℝ) (x : X) : ℝ :=
  limsup (fun n => f n x) atTop

/-- Measurable scalar sequences have a measurable canonical limit version. -/
theorem measurable_realSequenceLimit {f : ℕ → X → ℝ}
    (hf : ∀ n, Measurable (f n)) : Measurable (realSequenceLimit f) :=
  Measurable.limsup hf

omit [MeasurableSpace X] in
/-- On a convergent sequence the canonical version is its prescribed limit. -/
theorem realSequenceLimit_eq_of_tendsto {f : ℕ → X → ℝ} {x : X} {a : ℝ}
    (h : Tendsto (fun n => f n x) atTop (𝓝 a)) : realSequenceLimit f x = a :=
  h.limsup_eq

/-- Convergence on a measure-preserving representation supplies convergence on its law. -/
theorem ae_tendsto_realSequenceLimit_of_pullback
    {P : Measure Ω} {μ : Measure X} {field : Ω → X}
    (hfield : MeasurePreserving field P μ) {f : ℕ → X → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hconv : ∀ᵐ ω ∂P, ∃ a : ℝ, Tendsto (fun n => f n (field ω)) atTop (𝓝 a)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (realSequenceLimit f x)) := by
  have hex : ∀ᵐ x ∂μ, ∃ a : ℝ, Tendsto (fun n => f n x) atTop (𝓝 a) := by
    rw [← hfield.map_eq]
    exact (ae_map_iff hfield.measurable.aemeasurable
      (measurableSet_exists_tendsto hf)).2 hconv
  filter_upwards [hex] with x hx
  obtain ⟨a, ha⟩ := hx
  rw [realSequenceLimit_eq_of_tendsto ha]
  exact ha

omit [MeasurableSpace X] in
/-- The canonical law-space limit pulls back to any supplied almost sure limit. -/
theorem realSequenceLimit_comp_ae {P : Measure Ω} {field : Ω → X}
    {f : ℕ → X → ℝ} {L : Ω → ℝ}
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => f n (field ω)) atTop (𝓝 (L ω))) :
    realSequenceLimit f ∘ field =ᵐ[P] L :=
  hconv.mono fun _ h => realSequenceLimit_eq_of_tendsto h

/-- Replacing one coordinate by an independent copy preserves the product law. -/
theorem measurePreserving_update_infinitePi [DecidableEq I]
    (laws : I → Measure X) [∀ i, IsProbabilityMeasure (laws i)] (i : I) :
    MeasurePreserving
      (fun z : (I → X) × (I → X) => Function.update z.1 i (z.2 i))
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws))
      (Measure.infinitePi laws) := by
  have h := SubdiffusiveProcess.measurePreserving_copy_infinitePi_block laws {i}
  convert h using 1
  funext z j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, Set.mem_singleton_iff, ite_true]
  · simp only [Function.update_of_ne hji, Set.mem_singleton_iff, ite_eq_right hji]

/-- One event carries an almost sure property for the original and all copied coordinates. -/
theorem ae_forall_update_of_ae [Countable I] [DecidableEq I]
    (laws : I → Measure X) [∀ i, IsProbabilityMeasure (laws i)]
    {p : (I → X) → Prop} (hp : ∀ᵐ x ∂Measure.infinitePi laws, p x) :
    ∀ᵐ z ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)),
      p z.1 ∧ ∀ i, p (Function.update z.1 i (z.2 i)) := by
  have hfirst : ∀ᵐ z ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)), p z.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae hp
  have hupdate : ∀ i, ∀ᵐ z ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)),
      p (Function.update z.1 i (z.2 i)) := fun i =>
    (measurePreserving_update_infinitePi laws i).quasiMeasurePreserving.ae hp
  exact hfirst.and (ae_all_iff.2 hupdate)

/-- All single-coordinate differences converge on one event before taking moments. -/
theorem ae_tendsto_resampled_sub [Countable I] [DecidableEq I]
    (laws : I → Measure X) [∀ i, IsProbabilityMeasure (laws i)]
    {f : ℕ → (I → X) → ℝ} {L : (I → X) → ℝ}
    (hconv : ∀ᵐ x ∂Measure.infinitePi laws,
      Tendsto (fun n => f n x) atTop (𝓝 (L x))) :
    ∀ᵐ z ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)), ∀ i,
      Tendsto (fun n => f n z.1 - f n (Function.update z.1 i (z.2 i))) atTop
        (𝓝 (L z.1 - L (Function.update z.1 i (z.2 i)))) := by
  filter_upwards [ae_forall_update_of_ae laws hconv] with z hz i
  exact hz.1.sub (hz.2 i)

end
end SubdiffusiveProcess.Probability
