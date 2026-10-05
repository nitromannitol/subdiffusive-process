module

public import SubdiffusiveProcess.VariationalResponses.CellAssembly
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshError
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- The result gives actual closed-cell continuity of normalized coefficient (`in_normalization`) and finite-cutoff ellipticity, sources for reflection/test transport listed in existing deps; all three outputs remain.   -/
theorem cell_boundary_continuity [NeZero d] (hd : 2 ≤ d)
    (c : SpatialCoordinates d) (h : ℝ) (hh : 0 < h)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam)
    (ha : ContinuousOn a
      (closure (centeredCube c h hh : Set (SpatialCoordinates d))))
    (habounds : ∀ x ∈ (centeredCube c h hh : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam)
    (φ u : H1Function (centeredCube c h hh : Set (SpatialCoordinates d)))
    (hφ : ContDiff ℝ ∞ φ.toFun)
    (hharm : IsWeaklyHarmonicOn a
      (centeredCube c h hh : Set (SpatialCoordinates d)) u)
    (htrace : HasZeroTraceDifferenceOn
      (centeredCube c h hh : Set (SpatialCoordinates d)) u φ) :
    ∃ v : SpatialCoordinates d → ℝ,
      ContinuousOn v
        (closure (centeredCube c h hh : Set (SpatialCoordinates d))) ∧
      v =ᵐ[volume.restrict
        (centeredCube c h hh : Set (SpatialCoordinates d))] u.toFun ∧
      ∀ x ∈ frontier (centeredCube c h hh : Set (SpatialCoordinates d)),
        v x = φ.toFun x := by
  let K : Set (SpatialCoordinates d) :=
    closure (centeredCube c h hh : Set (SpatialCoordinates d))
  have hK : IsClosed K := by
    exact isClosed_closure
  let fK : C(K, ℝ) :=
    ⟨(fun x : K => a x), by
      exact continuousOn_iff_continuous_domRestrict.mp (by simpa [K] using! ha)⟩
  obtain ⟨A, -, hA⟩ :=
    ContinuousMap.exists_restrict_eq_forall_mem_of_closed fK
      (t := (Set.univ : Set ℝ)) (fun _ => Set.mem_univ _)
      Set.univ_nonempty hK
  let a' : SpatialCoordinates d → ℝ := A
  have ha' : Continuous a' := by
    exact A.continuous
  have haeq : ∀ x ∈ K, a' x = a x := by
    intro x hx
    have hxA := congrArg (fun F : C(K, ℝ) => F ⟨x, hx⟩) hA
    simpa [a', fK] using! hxA
  have habounds' : ∀ x ∈ (centeredCube c h hh : Set (SpatialCoordinates d)),
      lam ≤ a' x ∧ a' x ≤ Lam := by
    intro x hx
    rw [haeq x (subset_closure hx)]
    exact habounds x hx
  have hharm' : IsWeaklyHarmonicOn a'
      (centeredCube c h hh : Set (SpatialCoordinates d)) u := by
    intro ψ
    rw [← hharm ψ]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (centeredCube c h hh).isOpen.measurableSet]
      with x hx
    rw [haeq x (subset_closure hx)]
  exact
    (SubdiffusiveProcess.lane2_cellDirichletBoundaryContinuity hd).continuous_up_to_boundary
      c h hh a' lam Lam hlam ha' habounds' φ u hφ hharm' htrace

end SubdiffusiveProcess.Paper
