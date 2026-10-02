import SubdiffusiveProcess.Paper.Support.KillingIntegralMinimizer
import SubdiffusiveProcess.Paper.Support.KillingTraceStructure
import SubdiffusiveProcess.Paper.Support.KillingTraceObjective
import SubdiffusiveProcess.Paper.Support.KillingFormContinuity
import SubdiffusiveProcess.Paper.Support.UniformResolventTraceLinearity
import SubdiffusiveProcess.Paper.car_variational
import SubdiffusiveProcess.Analysis.ClosedSourceLp
import SubdiffusiveProcess.Section9.KilledDualNormCoercivity

/-! Supports: mfd_lem_killing.
Actual completed-trace and dual-energy application: shift/source continuity of
the produced continuous minimizer, over the full finite-energy domain.
-/
open Filter MeasureTheory Topology TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Section9 SubdiffusiveProcess.Analysis
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_mfd_lem_killing_minimizer_parameter_continuity
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hsym : ∀ x y, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (G x))
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (hsupp : ∀ᵐ x ∂nu, x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)))
    (Ktr Ctr : ℝ)
    (T : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder → Lp ℝ 2 nu)
    (hT : CubeTraceCharacterization hd z hr nu Ktr Ctr T)
    (lift : ∀ u : DomainL2 (centeredCube z r hr), (limitFormEnergy G u).toENNReal ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    (hlift : ∀ u hu, (lift u hu).val 0 = u)
    (J : DomainL2 (centeredCube z r hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ u hu, J u =ᵐ[nu] (T (lift u hu) : SpatialCoordinates d → ℝ))
    (ustar : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 (centeredCube z r hr))
    (hdata : ∀ lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      let E := fun u => (limitFormEnergy G u).toENNReal
      let Func := fun u => (E u).toReal + lam * (∫ x, J u x ^ 2 ∂nu) - 2 * (∫ x, f x * J u x ∂nu)
      E (ustar lam f) ≠ ⊤ ∧ (∀ u, E u ≠ ⊤ → Func (ustar lam f) ≤ Func u)) :
    letI : CompactSpace (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      isCompact_iff_compactSpace.mp (centeredCube_isBounded z hr).isCompact_closure
    Continuous (fun a : Set.Ioi (0 : ℝ) × C(closure (centeredCube z r hr : Set (SpatialCoordinates d)), ℝ) =>
      ustar a.1.1 (closedSourceExtension (centeredCube z r hr) a.2)) := by
  classical
  letI : CompactSpace (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    isCompact_iff_compactSpace.mp (centeredCube_isBounded z hr).isCompact_closure
  let E := fun u : DomainL2 (centeredCube z r hr) => (limitFormEnergy G u).toENNReal
  let A := fun u : DomainL2 (centeredCube z r hr) => if hu : E u ≠ ⊤ then T (lift u hu) else 0
  obtain ⟨hE0, hclosed, hpara, hscale, hAlin, hcoer⟩ :=
    aux_mfd_lem_killing_trace_structure hd z r hr G hsym hpos nu hsupp
      Ktr Ctr T hT lift hlift
  have hJA (v : DomainL2 (centeredCube z r hr)) (hv : E v ≠ ⊤) : J v =ᵐ[nu] (A v : SpatialCoordinates d → ℝ) := by
    dsimp only [A]
    rw [dif_pos hv]
    exact hJ v hv
  exact aux_mfd_lem_killing_integral_minimizer_continuous
    (centeredCube z r hr : Set (SpatialCoordinates d)) nu hsupp E A J
    hE0 hclosed hpara hscale hAlin (max 1 ‖G‖)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _))
    hcoer hJA ustar hdata

end Paper
