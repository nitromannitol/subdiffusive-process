import SubdiffusiveProcess.Sobolev.SmoothSourceDensity
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Sobolev.ResponseSpace
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Data.Finsupp.Encodable
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Countable dense rational catalogues of smooth compactly supported sources.
No resolvent or limiting-energy assertion is made here. -/

open MeasureTheory Filter Set Topology SubdiffusiveProcess
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.SmoothSources
noncomputable section

/-- Every dense rational submodule of cube L2 contains a countable dense submodule. -/
theorem countable_dense_submodule_le {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (hS : Dense (S : Set (DomainL2 (centeredCube z r hr)))) :
    ∃ D : Submodule ℚ (DomainL2 (centeredCube z r hr)), D ≤ S ∧
      (D : Set (DomainL2 (centeredCube z r hr))).Countable ∧
      Dense (D : Set (DomainL2 (centeredCube z r hr))) := by
  classical
  letI exponentAtLeastOne : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  letI finiteExponent : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  haveI domainSecondCountable : SecondCountableTopology (DomainL2 (centeredCube z r hr)) := by
    change SecondCountableTopology
      (Lp ℝ 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    infer_instance
  have hIsep : TopologicalSpace.IsSeparable (S : Set (DomainL2 (centeredCube z r hr))) := by
    exact TopologicalSpace.IsSeparable.of_separableSpace _
  obtain ⟨T, hTS, hTc, hST⟩ :=
    TopologicalSpace.IsSeparable.exists_countable_dense_subset hIsep
  haveI countableDenseSubset : Countable T := hTc.to_subtype
  have hTdense : Dense (T : Set (DomainL2 (centeredCube z r hr))) := by
    rw [dense_iff_closure_eq]
    have h1 : closure (S : Set (DomainL2 (centeredCube z r hr))) ⊆
        closure (T : Set (DomainL2 (centeredCube z r hr))) := by
      simpa only [closure_closure] using closure_mono hST
    rw [dense_iff_closure_eq.mp hS] at h1
    exact top_le_iff.mp h1
  refine ⟨Submodule.span ℚ (Set.range (fun t : T => (t : DomainL2 (centeredCube z r hr)))),
    ?_, ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨t, rfl⟩
    exact hTS t.2
  · refine Countable.mono ?_ (Set.countable_range
      (fun c : T →₀ ℚ => c.sum fun i a => a • (i : DomainL2 (centeredCube z r hr))))
    intro x hx
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp (SetLike.mem_coe.mp hx)
  · refine Dense.mono ?_ hTdense
    intro x hx
    exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

/-- A countable dense smooth-source catalogue follows from smooth-source density. -/
theorem exists_smooth_dense_submodule_of_dense {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hdense : Dense {f : DomainL2 (centeredCube z r hr) | ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc})
    (hsub : ∀ S : Submodule ℚ (DomainL2 (centeredCube z r hr)),
      Dense (S : Set (DomainL2 (centeredCube z r hr))) →
      ∃ D : Submodule ℚ (DomainL2 (centeredCube z r hr)), D ≤ S ∧
        (D : Set (DomainL2 (centeredCube z r hr))).Countable ∧ Dense (D : Set (DomainL2 (centeredCube z r hr)))) :
    ∃ D : Submodule ℚ (DomainL2 (centeredCube z r hr)),
      (D : Set (DomainL2 (centeredCube z r hr))).Countable ∧
      Dense (D : Set (DomainL2 (centeredCube z r hr))) ∧
      ∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc := by
  let S : Submodule ℚ (DomainL2 (centeredCube z r hr)) :=
    { carrier := {f : DomainL2 (centeredCube z r hr) | ∃ fc : SpatialCoordinates d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
            tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
            (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc},
      zero_mem' := by
        refine ⟨fun _ : SpatialCoordinates d => (0 : ℝ), contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
        · rw [show tsupport (fun _ : SpatialCoordinates d => (0 : ℝ)) = ∅ from tsupport_zero]
          exact Set.empty_subset _
        · exact Lp.coeFn_zero ℝ 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      add_mem' := by
        intro a b ha hb
        rcases ha with ⟨fc, hdiff, hsupp, hts, heq⟩
        rcases hb with ⟨gc, gdiff, gsupp, gts, geq⟩
        refine ⟨fc + gc, hdiff.add gdiff, hsupp.add gsupp, ?_, ?_⟩
        · exact (tsupport_add fc gc).trans (Set.union_subset hts gts)
        · exact (Lp.coeFn_add a b).trans (heq.add geq),
      smul_mem' := by
        intro c x hx
        rcases hx with ⟨fc, hdiff, hsupp, hts, heq⟩
        refine ⟨(c : ℝ) • fc, hdiff.const_smul (c : ℝ), hsupp.smul_left, ?_, ?_⟩
        · exact (tsupport_smul_subset_right (fun _ : SpatialCoordinates d => (c : ℝ)) fc).trans hts
        · have h1 : (c : ℚ) • x = (c : ℝ) • x := (Rat.cast_smul_eq_qsmul ℝ c x).symm
          rw [h1]
          exact (Lp.coeFn_smul (c : ℝ) x).trans (heq.const_smul (c : ℝ)) }
  have hSdense : Dense (S : Set (DomainL2 (centeredCube z r hr))) := hdense
  obtain ⟨D, hDS, hDc, hDd⟩ := hsub S hSdense
  exact ⟨D, hDc, hDd, fun f => hDS f.2⟩

/-- Every cube has a countable dense rational catalogue of smooth compactly supported sources. -/
theorem exists_countable_dense_smooth_submodule {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ D : Submodule ℚ (DomainL2 (centeredCube z r hr)),
      (D : Set (DomainL2 (centeredCube z r hr))).Countable ∧
      Dense (D : Set (DomainL2 (centeredCube z r hr))) ∧
      ∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧
        HasCompactSupport fc ∧ tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc := by
  apply exists_smooth_dense_submodule_of_dense z r hr
  · exact dense_smooth_compact_support (centeredCube z r hr).isOpen
      (centeredCube_isBounded z hr).measure_lt_top.ne
  · exact countable_dense_submodule_le z r hr

end
end SubdiffusiveProcess.SmoothSources
