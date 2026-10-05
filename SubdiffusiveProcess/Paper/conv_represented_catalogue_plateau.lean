module

public import Mathlib

@[expose] public section

open Filter Set TopologicalSpace
open scoped Topology ContDiff Manifold

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Smooth plateau around a compact set (clause D9 of `conv_represented_estimates`).**  For a compact
set `K` inside an open set `W` of `ℝ^d` there is a smooth `θ : ℝ^d → ℝ` with values in `[0,1]`, an open set `V`
with `K ⊆ V ⊆ W`, `θ = 1` on `V` and `tsupport θ ⊆ W`. -/
theorem conv_represented_catalogue_plateau (d : ℕ) (K W : Set (Fin d → ℝ))
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ theta : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ theta ∧
      (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) ∧
      ∃ V : Set (Fin d → ℝ), IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ (∀ x ∈ V, theta x = 1) ∧
        tsupport theta ⊆ W := by
  have hd : Disjoint Wᶜ K := by
    rw [Set.disjoint_left]
    intro x hx hxK
    exact hx (hKW hxK)
  obtain ⟨f, hf0, hf1, hfI⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, Fin d → ℝ)) (M := Fin d → ℝ) hW.isClosed_compl hK.isClosed hd
  obtain ⟨U, hUo, hWU, hUf⟩ := mem_nhdsSet_iff_exists.mp hf0
  obtain ⟨V, hVo, hKV, hVf⟩ := mem_nhdsSet_iff_exists.mp hf1
  have hcd : ContDiff ℝ ∞ (f : (Fin d → ℝ) → ℝ) := f.contMDiff.contDiff
  refine ⟨f, hcd, fun x => ⟨(hfI x).1, (hfI x).2⟩, V, hVo, hKV, ?_, hVf, ?_⟩
  · intro x hx
    by_contra hxW
    have h0 : f x = 0 := hUf (hWU hxW)
    have h1 : f x = 1 := hVf hx
    rw [h0] at h1
    exact zero_ne_one h1
  · have hsupp : Function.support (f : (Fin d → ℝ) → ℝ) ⊆ Uᶜ := by
      intro x hx hxU
      exact hx (hUf hxU)
    have hcl : tsupport (f : (Fin d → ℝ) → ℝ) ⊆ Uᶜ :=
      closure_minimal hsupp hUo.isClosed_compl
    intro x hx
    by_contra hxW
    exact hcl hx (hWU hxW)

end SubdiffusiveProcess.Paper
