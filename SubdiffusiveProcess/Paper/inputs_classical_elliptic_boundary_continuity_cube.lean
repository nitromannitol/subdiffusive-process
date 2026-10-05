module

public import SubdiffusiveProcess.Sobolev.CubeContinuousBoundary
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import Homogenization.Geometry.ConvexDomain
public import SubdiffusiveProcess.Geometry.Cube

@[expose] public section

/-! # Boundary continuity for continuous-coefficient killed minimizers on a centered cube

The centered-cube (`d ≥ 2`) case of `inputs_classical_elliptic_boundary_continuity`: the same
statement with the convexity hypothesis `hΩ` replaced by `Ω = centeredCube z r hr` and `2 ≤ d`,
which is exactly the scope of its consumer `goodext_harmonic_trace_compact_continuous`.
The proof uses
`SubdiffusiveProcess.cellDirichletBoundaryContinuity` (smooth data on centered cubes),
datum approximation and the weak maximum principle.
-/

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ContDiff ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Boundary continuity of the killed Dirichlet minimizer on a centered cube, `d ≥ 2`. -/
theorem inputs_classical_elliptic_boundary_continuity_cube
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) {Ω : Opens (SpatialCoordinates d)}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hcube : Ω = centeredCube z r hr)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (a : PositiveCoefficient Ω) (b : weakSobolevGraph Ω)
    (A bRep : SpatialCoordinates d → ℝ)
    (hA : Continuous A)
    (haA : a.val =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] A)
    (hApos : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ closure (Ω : Set (SpatialCoordinates d)),
      c ≤ A x)
    (hbRep : ContinuousOn bRep (closure (Ω : Set (SpatialCoordinates d))))
    (hb : ((b : SobolevData Ω).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] bRep) :
    ∃ V : SpatialCoordinates d → ℝ,
      ContinuousOn V (closure (Ω : Set (SpatialCoordinates d))) ∧
      (((dirichletMinimizer (killedResponseSpace hP) a b).val :
        SobolevData Ω).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] V ∧
      ∀ x ∈ frontier (Ω : Set (SpatialCoordinates d)), V x = bRep x := by
  classical
  subst Ω
  let W : Set (SpatialCoordinates d) := centeredCube z r hr
  have hW : Homogenization.IsOpenBoundedConvexDomain W :=
    isOpenBoundedConvexDomain_centeredCube z hr
  have hWne : W.Nonempty := ⟨z, Metric.mem_ball_self (half_pos hr)⟩
  have hK : IsCompact (closure W) := (centeredCube_isBounded z hr).isCompact_closure
  let f : C(closure W, ℝ) := ⟨fun x => bRep x, hbRep.domRestrict⟩
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq isClosed_closure f
  have hFeq : ∀ x ∈ closure W, F x = bRep x := by
    intro x hx
    exact DFunLike.congr_fun hF ⟨x, hx⟩
  have hbF : (b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict W] F := by
    filter_upwards [hb, self_mem_ae_restrict hW.isOpen.measurableSet] with x hx hxW
    exact hx.trans (hFeq x (subset_closure hxW)).symm
  obtain ⟨beta, hbeta, hbetaData⟩ := exists_nativeH1Function_of_ae_representative b F hbF
  obtain ⟨lam, hlam, hAlower⟩ := hApos
  obtain ⟨Lam, hAupper⟩ := hK.exists_bound_of_continuousOn hA.continuousOn
  have hbounds : ∀ x ∈ W, lam ≤ A x ∧ A x ≤ Lam := by
    intro x hx
    exact ⟨hAlower x (subset_closure hx),
      (le_abs_self (A x)).trans (by simpa only [Real.norm_eq_abs] using
        (hAupper x (subset_closure hx)))⟩
  have hEll := isEllipticFieldOn_scalar hW.isOpen.measurableSet hA.measurable hlam hbounds
  obtain ⟨u, htrace, hharm⟩ := exists_weaklyHarmonic_of_zeroTrace hW hWne hEll beta
  obtain ⟨V, hVcont, hVrep, hVtrace⟩ :=
    continuous_boundary_representative_of_native_cube_datum hd z r hr A hA lam Lam
      hlam hbounds beta u (by rw [hbeta]; exact F.continuous) hharm htrace
  have hbNative : (b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict W] beta.toFun := by
    rw [← hbetaData]
    exact sobolevDataOfH1_fst_coeFn beta
  have hmin := native_harmonic_minimizer_eq_of_ae_datum hP a A haA beta u b
    hbNative htrace hharm
  have hminData : (dirichletMinimizer (killedResponseSpace hP) a b).val =
      sobolevDataOfH1 u := (congrArg Subtype.val hmin).symm
  refine ⟨V, hVcont, ?_, ?_⟩
  · rw [hminData]
    exact (sobolevDataOfH1_fst_coeFn u).trans hVrep
  · intro x hx
    exact (hVtrace x hx).trans ((congrFun hbeta x).trans
      (hFeq x (frontier_subset_closure hx)))

end SubdiffusiveProcess.Paper
end


