module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import SubdiffusiveProcess.Analysis.LpExponentCompact

@[expose] public section

/-!
# Compactness transfer for a bounded, index-dependent scalar multiplier

Two small, general-purpose topological facts used to lift an `L¹`-relative-compactness result
from the unit root cell to an arbitrary triadic sub-cube `R`: multiplying a relatively compact
family by a DETERMINISTIC (not random) scalar sequence that stays within a fixed bounded interval
keeps it relatively compact (`isCompact_closure_range_bounded_scalar_smul`), and shifting the
index of a relatively compact family by a fixed constant amount keeps it relatively compact
(`isCompact_closure_range_reindex_add`). Neither claims anything about a random or unbounded
multiplier -- that is a separate, measure-theoretic tool.
-/

open Set Filter Topology MeasureTheory

noncomputable section

/-- Multiplying a relatively compact family by a scalar sequence bounded within a fixed interval
`[-C, C]` keeps it relatively compact: the range lies inside the continuous image of a compact
product `[-C, C] × closure (range h)` under scalar multiplication. -/
theorem isCompact_closure_range_bounded_scalar_smul {X : Type*}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [T2Space X] [ContinuousSMul ℝ X]
    (h : ℕ → X) (hcompact : IsCompact (closure (Set.range h)))
    (c : ℕ → ℝ) (C : ℝ) (hbound : ∀ n, |c n| ≤ C) :
    IsCompact (closure (Set.range (fun n => c n • h n))) := by
  have hprod : IsCompact ((Set.Icc (-C) C) ×ˢ (closure (Set.range h))) :=
    isCompact_Icc.prod hcompact
  have hcont : Continuous (fun p : ℝ × X => p.1 • p.2) := continuous_fst.smul continuous_snd
  have himg : IsCompact ((fun p : ℝ × X => p.1 • p.2) ''
      ((Set.Icc (-C) C) ×ˢ (closure (Set.range h)))) := hprod.image hcont
  have hsub : Set.range (fun n => c n • h n) ⊆
      (fun p : ℝ × X => p.1 • p.2) '' ((Set.Icc (-C) C) ×ˢ (closure (Set.range h))) := by
    rintro x ⟨n, rfl⟩
    exact ⟨(c n, h n), ⟨Set.mem_Icc.2 (abs_le.mp (hbound n)), subset_closure ⟨n, rfl⟩⟩, rfl⟩
  exact IsCompact.of_isClosed_subset himg isClosed_closure
    (closure_minimal hsub himg.isClosed)

/-- Shifting the index of a relatively compact family by a fixed constant amount keeps it
relatively compact: the shifted range is a subset of the original range. -/
theorem isCompact_closure_range_reindex_add {X : Type*} [TopologicalSpace X]
    (h : ℕ → X) (hcompact : IsCompact (closure (Set.range h))) (shift : ℕ) :
    IsCompact (closure (Set.range (fun n => h (n + shift)))) := by
  have hsub : Set.range (fun n => h (n + shift)) ⊆ Set.range h := by
    rintro x ⟨n, rfl⟩; exact ⟨n + shift, rfl⟩
  exact IsCompact.of_isClosed_subset hcompact isClosed_closure (closure_mono hsub)

/-- The converse direction needed to patch finitely many small indices back in: if the
`shift`-forward-shifted family is relatively compact, so is the FULL family (the missing indices
`< shift` contribute only a finite, hence compact, extra piece). -/
theorem isCompact_closure_range_of_shifted_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    (h : ℕ → X) (shift : ℕ)
    (hshifted : IsCompact (closure (Set.range (fun n => h (n + shift))))) :
    IsCompact (closure (Set.range h)) := by
  have hsplit : Set.range h =
      (h '' Set.Iio shift) ∪ Set.range (fun n => h (n + shift)) := by
    ext x
    simp only [Set.mem_range, Set.mem_union, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨K, rfl⟩
      rcases lt_or_ge K shift with hK | hK
      · exact Or.inl ⟨K, hK, rfl⟩
      · exact Or.inr ⟨K - shift, by rw [Nat.sub_add_cancel hK]⟩
    · rintro (⟨K, -, rfl⟩ | ⟨n, rfl⟩)
      · exact ⟨K, rfl⟩
      · exact ⟨n + shift, rfl⟩
  have hfin : (h '' Set.Iio shift).Finite := (Set.finite_Iio shift).image h
  rw [hsplit, closure_union, hfin.isClosed.closure_eq]
  exact hfin.isCompact.union hshifted

/-- Composing a relatively compact `L¹` family with a measure-preserving self-map keeps it
relatively compact: `MeasureTheory.Lp.compMeasurePreserving` is a (continuous) isometry, and
`lp_compact_image` transports compactness through any continuous map. -/
theorem aux_compact_comp_measurePreserving {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    (S : Ω → Ω) (hS : MeasurePreserving S μ ν) (g : ℕ → Ω → ℝ) (hmem : ∀ n, MemLp (g n) 1 ν)
    (hcompact : IsCompact (closure (Set.range (fun n => (hmem n).toLp (g n))))) :
    IsCompact (closure (Set.range
      (fun n => ((hmem n).comp_measurePreserving hS).toLp (fun om => g n (S om))))) := by
  have hcont : Continuous (MeasureTheory.Lp.compMeasurePreserving S hS : Lp ℝ 1 ν → Lp ℝ 1 μ) :=
    (MeasureTheory.Lp.isometry_compMeasurePreserving hS).continuous
  have hkey := lp_compact_image (fun n => (hmem n).toLp (g n)) hcompact _ hcont
  have heq : (fun n => (MeasureTheory.Lp.compMeasurePreserving S hS) ((hmem n).toLp (g n))) =
      (fun n => ((hmem n).comp_measurePreserving hS).toLp (fun om => g n (S om))) := by
    funext n
    exact MeasureTheory.Lp.toLp_compMeasurePreserving (hmem n) hS
  rwa [heq] at hkey

end
