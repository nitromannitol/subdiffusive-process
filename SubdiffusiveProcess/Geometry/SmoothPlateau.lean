module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular

@[expose] public section

/-! Smooth compactly supported plateau functions between compact and open sets.
This is independent of coefficients, meshes, forms, and probability. -/
open Set Filter Topology
open scoped ContDiff Manifold
namespace SubdiffusiveProcess

/-- A compact subset of an open set admits a smooth compactly supported plateau in that open set. -/
theorem exists_smooth_compact_plateau
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K O : Set E) (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ theta : E → ℝ, ∃ V : Set E,
      ContDiff ℝ ∞ theta ∧ HasCompactSupport theta ∧ tsupport theta ⊆ O ∧
      IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
      (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) ∧ ∀ x ∈ V, theta x = 1 := by
  obtain ⟨L, hLc, hLcl, hKL, hLO⟩ := exists_compact_closed_between hK hO hKO
  obtain ⟨f, hf1, hf0, hfr⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, E)) hK.isClosed hKL
  obtain ⟨U, hU, hKU, hUf⟩ := mem_nhdsSet_iff_exists.mp hf1
  have hs : Function.support (fun x => f x) ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hf0 x hxL)
  refine ⟨(fun x => f x), U ∩ O, f.contMDiff.contDiff,
    HasCompactSupport.of_support_subset_isCompact hLc hs,
    (closure_minimal hs hLcl).trans hLO, hU.inter hO,
    (fun x hx => ⟨hKU hx, hKO hx⟩), inter_subset_right, hfr, ?_⟩
  exact fun x hx => hUf hx.1

end SubdiffusiveProcess
