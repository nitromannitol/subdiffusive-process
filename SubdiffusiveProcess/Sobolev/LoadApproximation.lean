import SubdiffusiveProcess.Sobolev.ResponseSpace

/-!
# Canonical mean-zero load approximation

This file records the deterministic part of the load approximation argument
(source Lemma 17 / (E026)).  The two solutions are the selected solutions of
the concrete Sobolev response space, and the weak equation for their
difference is derived from the two canonical defining equations rather than
assumed.  The fractional trace estimate needed to construct the particular
face-smoothed load remains a separate Lemma 16 dependency, and no
probabilistic `L^p` estimate is claimed here.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- The difference of two canonical solutions solves the difference load. -/
theorem responseSolution_sub_spec (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L L' : S.space →L[ℝ] ℝ) (v : S.space) :
    responseForm S a (responseSolution S a L - responseSolution S a L') v = (L - L') v := by
  rw [map_sub (responseForm S a) (responseSolution S a L) (responseSolution S a L'),
    ContinuousLinearMap.sub_apply, responseSolution_spec, responseSolution_spec,
    ContinuousLinearMap.sub_apply]

/-- Energy of the solution difference under a quantitative dual load bound.

If `|(L - L') z| ≤ δ √E(z,z)` for every `z`, then the canonical solutions of
`L` and `L'` differ by at most `δ²` in energy.  No sign assumption on `δ` is
needed: the bound forces `δ ≥ 0` whenever the difference is nonzero. -/
theorem responseSolution_energy_difference_le
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L L' : S.space →L[ℝ] ℝ) (δ : ℝ)
    (hload : ∀ z : S.space,
      |(L - L') z| ≤ δ * Real.sqrt (responseForm S a z z)) :
    responseForm S a
        (responseSolution S a L - responseSolution S a L')
        (responseSolution S a L - responseSolution S a L') ≤ δ ^ 2 := by
  let w := responseSolution S a L - responseSolution S a L'
  have hn : 0 ≤ responseForm S a w w := responseForm_nonneg S a w
  have hs : (Real.sqrt (responseForm S a w w)) ^ 2 = responseForm S a w w :=
    Real.sq_sqrt hn
  have hl : responseForm S a w w ≤ δ * Real.sqrt (responseForm S a w w) :=
    calc responseForm S a w w = (L - L') w := responseSolution_sub_spec S a L L' w
      _ ≤ |(L - L') w| := le_abs_self _
      _ ≤ δ * Real.sqrt (responseForm S a w w) := hload w
  nlinarith [Real.sqrt_nonneg (responseForm S a w w)]

/-- The corresponding inverse responses are actual variational maxima. -/
theorem inverseResponse_load_difference_le
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L L' : S.space →L[ℝ] ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hload : ∀ z : S.space,
      |(L - L') z| ≤ δ * Real.sqrt (responseForm S a z z)) :
    |inverseResponse S a L - inverseResponse S a L'| ≤
      2 * δ * (Real.sqrt (inverseResponse S a L) +
        Real.sqrt (inverseResponse S a L')) := by
  let u := responseSolution S a L
  let v := responseSolution S a L'
  have hRu : inverseResponse S a L = responseForm S a u u := by
    rfl
  have hRv : inverseResponse S a L' = responseForm S a v v := by
    rfl
  have hmax₁ := (inverseResponse_isGreatest S a L').2
    (show 2 * L' u - responseForm S a u u ∈
      Set.range (fun z : S.space => 2 * L' z - responseForm S a z z) from ⟨u, rfl⟩)
  have hmax₂ := (inverseResponse_isGreatest S a L).2
    (show 2 * L v - responseForm S a v v ∈
      Set.range (fun z : S.space => 2 * L z - responseForm S a z z) from ⟨v, rfl⟩)
  have hLu : L u = responseForm S a u u := (inverseResponse_eq_load S a L).symm
  have hLv : L' v = responseForm S a v v := (inverseResponse_eq_load S a L').symm
  have hu : inverseResponse S a L - inverseResponse S a L' ≤
      2 * δ * Real.sqrt (inverseResponse S a L) := by
    have hh := hload u
    rw [← hRu] at hh
    rw [← hLu] at hmax₁
    have hthis : L u - L' u ≤ δ * Real.sqrt (inverseResponse S a L) := by
      simpa only [hRu] using (le_abs_self (L u - L' u)).trans hh
    linarith
  have hv : inverseResponse S a L' - inverseResponse S a L ≤
      2 * δ * Real.sqrt (inverseResponse S a L') := by
    have hh := hload v
    rw [← hRv] at hh
    rw [← hLv] at hmax₂
    have hthis : L' v - L v ≤ δ * Real.sqrt (inverseResponse S a L') := by
      have hh' : |(L' - L) v| ≤ δ * Real.sqrt (inverseResponse S a L') := by
        simpa only [map_sub, ContinuousLinearMap.sub_apply, abs_neg, abs_sub_comm] using hh
      exact (le_abs_self _).trans hh'
    linarith
  have hnonneg₁ := inverseResponse_nonneg S a L
  have hnonneg₂ := inverseResponse_nonneg S a L'
  have hδu : 0 ≤ δ * Real.sqrt (inverseResponse S a L) :=
    mul_nonneg hδ (Real.sqrt_nonneg _)
  have hδv : 0 ≤ δ * Real.sqrt (inverseResponse S a L') :=
    mul_nonneg hδ (Real.sqrt_nonneg _)
  rw [abs_le]
  constructor <;> linarith

end SubdiffusiveProcess
