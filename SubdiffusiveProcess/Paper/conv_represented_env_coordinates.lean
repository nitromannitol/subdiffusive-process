module

public import Mathlib
public import SubdiffusiveProcess.Paper.inputs_classical_countable_skorokhod_representation

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Coordinate types of the represented product: `none` carries the environment, `some i` the
`i`-th real coordinate. -/
abbrev aux_conv_represented_env_coordinates_S (E : Type) (ι : Type) : Option ι → Type :=
  fun o => Option.elim o E (fun _ => ℝ)

local instance aux_conv_represented_env_coordinates_top (E : Type) (ι : Type) [TopologicalSpace E] :
    ∀ o : Option ι, TopologicalSpace (aux_conv_represented_env_coordinates_S E ι o)
  | none => (inferInstance : TopologicalSpace E)
  | some _ => (inferInstance : TopologicalSpace ℝ)

local instance aux_conv_represented_env_coordinates_polish (E : Type) (ι : Type) [TopologicalSpace E]
    [PolishSpace E] :
    ∀ o : Option ι, @PolishSpace (aux_conv_represented_env_coordinates_S E ι o)
      (aux_conv_represented_env_coordinates_top E ι o)
  | none => (inferInstance : PolishSpace E)
  | some _ => (inferInstance : PolishSpace ℝ)

local instance aux_conv_represented_env_coordinates_meas (E : Type) (ι : Type) [MeasurableSpace E] :
    ∀ o : Option ι, MeasurableSpace (aux_conv_represented_env_coordinates_S E ι o)
  | none => (inferInstance : MeasurableSpace E)
  | some _ => (inferInstance : MeasurableSpace ℝ)

local instance aux_conv_represented_env_coordinates_borel (E : Type) (ι : Type) [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] :
    ∀ o : Option ι, @BorelSpace (aux_conv_represented_env_coordinates_S E ι o)
      (aux_conv_represented_env_coordinates_top E ι o) (aux_conv_represented_env_coordinates_meas E ι o)
  | none => (inferInstance : BorelSpace E)
  | some _ => (inferInstance : BorelSpace ℝ)


/-- **Represented coordinates for an environment and countably many real coordinates.**
Applies the classical countable Prokhorov/Skorokhod input to the countable Polish product
of the environment and the real coordinates `Y i n`. The environment coordinate is the same
random variable at every `n`, hence tight; each real coordinate is tight by hypothesis. On the
canonical representing space, at every index `n` the whole coordinate vector has the law of the
original vector at the extracted index `seq n` (no cross-index law is claimed), and all
coordinates converge almost surely. -/
theorem conv_represented_env_coordinates
    {E : Type} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type} [Countable ι]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → E) (hfield : Measurable field)
    (Y : ι → ℕ → Ω → ℝ) (hY : ∀ i n, Measurable (Y i n))
    (htight : ∀ i, IsTightMeasureSet (Set.range fun n => Measure.map (Y i n) P)) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh) (_ : IsProbabilityMeasure Ph)
        (env : ℕ → Ωh → E) (envLim : Ωh → E)
        (Yh : ι → ℕ → Ωh → ℝ) (Ylim : ι → Ωh → ℝ),
        (∀ n, Measurable (env n)) ∧ Measurable envLim ∧
        (∀ i n, Measurable (Yh i n)) ∧ (∀ i, Measurable (Ylim i)) ∧
        (∀ n, Measure.map (fun ω => (env n ω, fun i => Yh i n ω)) Ph =
          Measure.map (fun ω => (field ω, fun i => Y i (seq n) ω)) P) ∧
        ∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (envLim ω)) ∧
          ∀ i, Tendsto (fun n => Yh i n ω) atTop (𝓝 (Ylim i ω)) := by
  classical
  let S := aux_conv_represented_env_coordinates_S E ι
  let X : ℕ → Ω → ∀ o, S o := fun n ω o =>
    Option.casesOn (motive := fun o => S o) o (field ω) (fun i => Y i n ω)
  have hX : ∀ n, Measurable (X n) := fun n => by
    refine Measurable.of_eval (fun o => ?_)
    cases o
    · exact hfield
    · exact hY _ _
  let mu : ℕ → Measure (∀ o, S o) := fun n => Measure.map (X n) P
  have hprob : ∀ n, IsProbabilityMeasure (mu n) := fun n => by
    dsimp [mu]
    infer_instance
  have htight' : ∀ o, IsTightMeasureSet
      (Set.range (fun n => Measure.map (fun x : ∀ o, S o => x o) (mu n))) := by
    intro o
    cases o with
    | none =>
      have hsub : Set.range (fun n => Measure.map (fun x : ∀ o, S o => x none) (mu n)) ⊆
          {Measure.map field P} := by
        rintro _ ⟨n, rfl⟩
        simp only [mu]
        rw [Measure.map_map (measurable_pi_apply none) (hX n)]
        rfl
      exact (isTightMeasureSet_singleton_of_innerRegular (μ := Measure.map field P)).subset hsub
    | some i =>
      have hsub : Set.range (fun n => Measure.map (fun x : ∀ o, S o => x (some i)) (mu n)) ⊆
          Set.range (fun n => Measure.map (Y i n) P) := by
        rintro _ ⟨n, rfl⟩
        refine ⟨n, ?_⟩
        simp only [mu]
        rw [Measure.map_map (measurable_pi_apply (some i)) (hX n)]
        rfl
      exact (htight i).subset hsub
  obtain ⟨seq, hseq, Q, hQ, hlaw, hconv⟩ :=
    _root_.SubdiffusiveProcess.Paper.inputs_classical_countable_skorokhod_representation S mu hprob htight'
  refine ⟨seq, hseq, (ℕ → ∀ o, S o) × ∀ o, S o, inferInstance, Q, hQ,
    fun n ω => (ω.1 n none : E), fun ω => (ω.2 none : E),
    fun i n ω => (ω.1 n (some i) : ℝ), fun i ω => (ω.2 (some i) : ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (measurable_pi_apply none).comp ((measurable_pi_apply n).comp measurable_fst)
  · exact (measurable_pi_apply none).comp measurable_snd
  · intro i n
    exact (measurable_pi_apply (some i)).comp ((measurable_pi_apply n).comp measurable_fst)
  · intro i
    exact (measurable_pi_apply (some i)).comp measurable_snd
  · intro n
    let Φ : (∀ o, S o) → E × (ι → ℝ) := fun x => (x none, fun i => x (some i))
    have hΦ : Measurable Φ := by
      refine (measurable_pi_apply none).prodMk (Measurable.of_eval (fun i => ?_))
      exact measurable_pi_apply (some i)
    have hcomp : (fun ω : (ℕ → ∀ o, S o) × ∀ o, S o =>
        ((ω.1 n none : E), fun i => (ω.1 n (some i) : ℝ))) =
        Φ ∘ (fun ω => ω.1 n) := rfl
    have hcomp2 : (fun ω : Ω => (field ω, fun i => Y i (seq n) ω)) = Φ ∘ X (seq n) := rfl
    have hm1 : Measurable (fun ω : (ℕ → ∀ o, S o) × ∀ o, S o => ω.1 n) :=
      (measurable_pi_apply n).comp measurable_fst
    change Measure.map (Φ ∘ (fun ω => ω.1 n)) Q = Measure.map (Φ ∘ X (seq n)) P
    rw [← Measure.map_map hΦ hm1, ← Measure.map_map hΦ (hX (seq n)), hlaw n]
  · filter_upwards [hconv] with ω hω
    exact ⟨tendsto_pi_nhds.mp hω none, fun i => tendsto_pi_nhds.mp hω (some i)⟩


end SubdiffusiveProcess.Paper
