import SubdiffusiveProcess.Sobolev.CountableSmoothSources
import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative
import Mathlib.LinearAlgebra.Countable

/-! Countable smooth source catalogues may include any prescribed countable
smooth bank. This module asserts L2 density; derivative approximation comes from the bank. -/

open MeasureTheory Set TopologicalSpace
open scoped NNReal ENNReal ContDiff

namespace SubdiffusiveProcess.SmoothSources
noncomputable section

/-- Continuous representatives supported in one open set are determined globally by their restricted almost-everywhere class. -/
theorem eq_of_continuous_supported_ae_eq {d : ℕ} {U : Set (SpatialCoordinates d)}
    (hU : IsOpen U) {f g : SpatialCoordinates d → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfs : tsupport f ⊆ U) (hgs : tsupport g ⊆ U)
    (hfg : f =ᵐ[volume.restrict U] g) : f = g := by
  funext x
  by_cases hx : x ∈ U
  · exact eqOn_closure_of_ae_eq_restrict hU hf.continuousOn hg.continuousOn hfg
      (subset_closure hx)
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hfs h)),
      image_eq_zero_of_notMem_tsupport (fun h => hx (hgs h))]

/-- Cube L2 classes with smooth compactly supported representatives form a rational submodule. -/
def compactSmoothSourceSubmodule {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Submodule ℚ (DomainL2 (centeredCube z r hr)) where
  carrier := {f | ∃ fc : SpatialCoordinates d → ℝ,
    ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
      tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (f : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc}
  zero_mem' := by
    refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
    · rw [show tsupport (fun _ : SpatialCoordinates d => (0 : ℝ)) = ∅ from tsupport_zero]
      exact Set.empty_subset _
    · exact Lp.coeFn_zero ℝ 2 _
  add_mem' := by
    rintro a b ⟨f, hf, hc, hs, ha⟩ ⟨g, hg, hgc, hgs, hb⟩
    exact ⟨f + g, hf.add hg, hc.add hgc, (tsupport_add f g).trans (Set.union_subset hs hgs),
      (Lp.coeFn_add a b).trans (ha.add hb)⟩
  smul_mem' := by
    rintro c a ⟨f, hf, hc, hs, ha⟩
    refine ⟨(c : ℝ) • f, hf.const_smul (c : ℝ), hc.smul_left,
      (tsupport_smul_subset_right (fun _ => (c : ℝ)) f).trans hs, ?_⟩
    rw [show c • a = (c : ℝ) • a from (Rat.cast_smul_eq_qsmul ℝ c a).symm]
    exact (Lp.coeFn_smul (c : ℝ) a).trans (ha.const_smul (c : ℝ))

/-- A dense countable rational smooth catalogue can be enlarged to contain a prescribed countable bank. -/
theorem exists_countable_dense_smooth_submodule_containing {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : ℕ → DomainL2 (centeredCube z r hr))
    (hf : ∀ n, f n ∈ compactSmoothSourceSubmodule z r hr) :
    ∃ D : Submodule ℚ (DomainL2 (centeredCube z r hr)),
      Countable D ∧ Dense (D : Set (DomainL2 (centeredCube z r hr))) ∧
      D ≤ compactSmoothSourceSubmodule z r hr ∧ ∀ n, f n ∈ D := by
  classical
  obtain ⟨D0, hD0c, hD0d, hD0s⟩ := exists_countable_dense_smooth_submodule z r hr
  haveI countableBase : Countable D0 := hD0c.to_subtype
  let X : D0 ⊕ ℕ → DomainL2 (centeredCube z r hr) := Sum.elim Subtype.val f
  let D := Submodule.span ℚ (Set.range X)
  have hD0 : D0 ≤ D := by
    intro x hx
    exact Submodule.subset_span ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  refine ⟨D, inferInstance, hD0d.mono hD0, ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    cases i with
    | inl u => exact hD0s u
    | inr n => exact hf n
  · intro n
    exact Submodule.subset_span ⟨Sum.inr n, rfl⟩

end
end SubdiffusiveProcess.SmoothSources
