module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Bases

@[expose] public section

open MeasureTheory Topology TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess.Section9

/-- Equality at each parameter can be synchronized across countably many
continuous separable parameter families. -/
theorem ae_forall_eq_of_continuous_parameter
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : ℕ → Type*) [∀ i, TopologicalSpace (X i)]
    [∀ i, SeparableSpace (X i)] [∀ i, Nonempty (X i)]
    [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
    (F G : ∀ i, Ω → X i → Y i)
    (hcont : ∀ᵐ omega ∂P, ∀ i, Continuous (F i omega) ∧ Continuous (G i omega))
    (heq : ∀ i x, ∀ᵐ omega ∂P, F i omega x = G i omega x) :
    ∀ᵐ omega ∂P, ∀ i x, F i omega x = G i omega x := by
  have hdense : ∀ᵐ omega ∂P, ∀ i n,
      F i omega (TopologicalSpace.denseSeq (X i) n) =
        G i omega (TopologicalSpace.denseSeq (X i) n) := by
    simp only [ae_all_iff]
    exact fun i n => heq i _
  filter_upwards [hcont, hdense] with omega hc he
  intro i x
  exact congrFun ((TopologicalSpace.denseRange_denseSeq (X i)).equalizer
    (hc i).1 (hc i).2 (funext (he i))) x

end SubdiffusiveProcess.Section9
