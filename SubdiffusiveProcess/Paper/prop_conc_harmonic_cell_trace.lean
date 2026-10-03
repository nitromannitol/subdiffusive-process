module

public import SubdiffusiveProcess.Paper.cell_boundary_continuity
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative

@[expose] public section

/-! Identify the continuous trace of a native harmonic cell solution.
This is a finite-coefficient statement and asserts no limiting boundary theorem. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ContDiff
namespace Paper

/-- A continuous harmonic representative has the smooth datum's pointwise boundary values. -/
theorem prop_conc_harmonic_cell_trace {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a) (hpos : ∀ x, 0 < a x)
    (phi u : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hphi : ContDiff ℝ ∞ phi.toFun)
    (hu : IsWeaklyHarmonicOn a (centeredCube z r hr : Set (SpatialCoordinates d)) u)
    (htrace : HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d)) u phi)
    (huc : ContinuousOn u.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), u.toFun x = phi.toFun x := by
  haveI dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨lam, Lam, hlam, hb⟩ := aux_lem_cutoffs_pos_bounds a ha hpos
    (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
    (lane2_isCompact_closure_centeredCube z hr)
  obtain ⟨v, hvc, hvae, hvb⟩ := cell_boundary_continuity hd z r hr a lam Lam hlam
    ha.continuousOn (fun x hx => hb x (subset_closure hx)) phi u hphi hu htrace
  have heq := eqOn_closure_of_ae_eq_restrict (centeredCube z r hr).isOpen huc hvc hvae.symm
  intro x hx
  exact (heq (frontier_subset_closure hx)).trans (hvb x hx)

end Paper
