module

public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

@[expose] public section

/-! Full uniform convergence from a unique subsequential uniform cluster. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set UniformConvergence
open scoped Topology

namespace SubdiffusiveProcess.Compactness

variable {X Y : Type*} [UniformSpace Y]

/-- Uniform convergence follows if every subsequence has a further subsequence
converging uniformly to the same function. -/
theorem tendstoUniformlyOn_of_subseq_tendstoUniformlyOn
    (F : ℕ → X → Y) (f : X → Y) (s : Set X)
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, TendstoUniformlyOn (fun n => F (ns (ms n))) f atTop s) :
    TendstoUniformlyOn F f atTop s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  let U : ℕ → (s →ᵤ Y) := fun n => UniformFun.ofFun (fun x : s => F n x)
  let u : s →ᵤ Y := UniformFun.ofFun (fun x : s => f x)
  have hu : Tendsto U atTop (𝓝 u) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, hms⟩ := h ns hns
    refine ⟨ms, UniformFun.tendsto_iff_tendstoUniformly.mpr ?_⟩
    simpa only [U, u, Function.comp_def, UniformFun.toFun_ofFun] using
      (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hms)
  simpa only [U, u, Function.comp_def, UniformFun.toFun_ofFun] using
    (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

/-- A nonempty family of clusters with a proved uniqueness property supplies
an actual limit for the full sequence. The property `P` describes the cluster's
already proved analytic conclusions; it does not contain full convergence. -/
theorem exists_tendstoUniformlyOn_of_unique_clusters
    (F : ℕ → X → Y) (s : Set X) (P : (X → Y) → Prop)
    (hcompact : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ (ms : ℕ → ℕ) (g : X → Y),
        P g ∧ TendstoUniformlyOn (fun n => F (ns (ms n))) g atTop s)
    (hunique : ∀ f g, P f → P g → EqOn f g s) :
    ∃ f : X → Y, P f ∧ TendstoUniformlyOn F f atTop s := by
  obtain ⟨_, f, hf, _⟩ := hcompact id tendsto_id
  refine ⟨f, hf, tendstoUniformlyOn_of_subseq_tendstoUniformlyOn F f s ?_⟩
  intro ns hns
  obtain ⟨ms, g, hg, hconv⟩ := hcompact ns hns
  refine ⟨ms, ?_⟩
  exact hconv.congr_right (hunique g f hg hf)

end SubdiffusiveProcess.Compactness
