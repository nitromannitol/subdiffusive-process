module

public import SubdiffusiveProcess.Paper.prop_locality_recovery
public import SubdiffusiveProcess.Sobolev.NativeH10Reverse
public import SubdiffusiveProcess.Sobolev.NativeHarmonicData
public import SubdiffusiveProcess.Sobolev.SmoothSourceDensity
public import Homogenization.Sobolev.H1.Algebra.Membership

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal ContDiff Manifold
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Restricting a weak Sobolev datum supported on a compact subset gives a killed datum. -/
theorem killed_restriction_compact_support
    {d : ℕ} {Q q : Opens (SpatialCoordinates d)} (hqQ : q ≤ Q)
    (hq : IsOpenBoundedConvexDomain (q : Set (SpatialCoordinates d)))
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hKq : K ⊆ q)
    (w : SobolevData Q) (hw : w ∈ weakSobolevGraph Q)
    (hzero : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), x ∉ K → w.1 x = 0) :
    sobolevDataRestrict hqQ w ∈ killedSobolevGraph q := by
  obtain ⟨L, hLcompact, hLclosed, hKL, hLq⟩ :=
    exists_compact_closed_between hK q.isOpen hKq
  obtain ⟨eta, hetaOne, hetaZero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, SpatialCoordinates d)) hK.isClosed hKL
  have hetaSupport : Function.support eta ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hetaZero x hxL)
  have hetaCompact : HasCompactSupport eta :=
    HasCompactSupport.of_support_subset_isCompact hLcompact hetaSupport
  have hetaSub : tsupport eta ⊆ (q : Set (SpatialCoordinates d)) :=
    (closure_minimal hetaSupport hLclosed).trans hLq
  let wr : weakSobolevGraph q := ⟨sobolevDataRestrict hqQ w, sobolevDataRestrict_mem_weak hqQ hw⟩
  obtain ⟨u, hu, _⟩ := exists_nativeH1Function_of_weakSobolevGraph wr
  obtain ⟨v, hv⟩ := memH10_mul_of_contDiff_hasCompactSupport hq
    eta.contMDiff.contDiff hetaCompact hetaSub u.memH1
  obtain ⟨vdata, hvdata, hvval, _⟩ := exists_killedSobolevGraph_of_h10Function v
  have hval : vdata.1 = wr.val.1 := by
    apply Lp.ext
    filter_upwards [hvval, domainLpRestrict_coeFn hqQ w.1,
      ae_restrict_of_ae_restrict_of_subset hqQ hzero] with x hx hxr hxzero
    rw [hv] at hx
    change vdata.1 x = (sobolevDataRestrict hqQ w).1 x
    change (domainLpRestrict hqQ w.1) x = w.1 x at hxr
    rw [hx]
    change eta x * u.toFun x = (domainLpRestrict hqQ w.1) x
    have hux : u.toFun x = (domainLpRestrict hqQ w.1) x := congrFun hu x
    rw [hux]
    by_cases hxK : x ∈ K
    · rw [hetaOne.self_of_nhdsSet x hxK, one_mul]
    · rw [hxr, hxzero hxK, mul_zero]
  have heq := weakSobolevGraph_eq_of_fst_eq
    (⟨vdata, killedSobolevGraph_le_weakSobolevGraph hvdata⟩ : weakSobolevGraph q) wr hval
  have hdata : vdata = sobolevDataRestrict hqQ w := congrArg Subtype.val heq
  exact hdata ▸ hvdata

end Paper
