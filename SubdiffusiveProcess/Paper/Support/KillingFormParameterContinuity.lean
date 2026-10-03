module

public import SubdiffusiveProcess.Paper.Support.KillingMinimizerParameters
public import SubdiffusiveProcess.Paper.Support.UniformResolventTraceLinearity
public import SubdiffusiveProcess.Paper.car_variational
public import SubdiffusiveProcess.Analysis.ClosedSourceLp
public import SubdiffusiveProcess.Analysis.ContinuousLpRepresentative
public import SubdiffusiveProcess.Section9.KilledDualNormCoercivity

@[expose] public section

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

theorem aux_mfd_lem_killing_form_parameter_continuity
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
    (R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → C(SpatialCoordinates d, ℝ))
    (Khol : ℝ)
    (hdata : ∀ lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      let E := fun u => (limitFormEnergy G u).toENNReal
      let Func := fun u => (E u).toReal + lam * (∫ x, J u x ^ 2 ∂nu) - 2 * (∫ x, f x * J u x ∂nu)
      E (ustar lam f) ≠ ⊤ ∧
      (R lam f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] ustar lam f ∧
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          |R lam f x - R lam f y| ≤ Khol * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
      (∀ u, E u ≠ ⊤ → Func (ustar lam f) ≤ Func u)) :
    letI : CompactSpace (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      isCompact_iff_compactSpace.mp (centeredCube_isBounded z hr).isCompact_closure
    Continuous (fun a : Set.Ioi (0 : ℝ) × C(closure (centeredCube z r hr : Set (SpatialCoordinates d)), ℝ) =>
      fun x : centeredCube z r hr => R a.1.1 (closedSourceExtension (centeredCube z r hr) a.2) x) := by
  classical
  letI : CompactSpace (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    isCompact_iff_compactSpace.mp (centeredCube_isBounded z hr).isCompact_closure
  let X := Set.Ioi (0 : ℝ) × C(closure (centeredCube z r hr : Set (SpatialCoordinates d)), ℝ)
  let u : X → DomainL2 (centeredCube z r hr) := fun a =>
    ustar a.1.1 (closedSourceExtension (centeredCube z r hr) a.2)
  have huc : Continuous u := aux_mfd_lem_killing_minimizer_parameter_continuity
    hd z r hr G hsym hpos nu hsupp Ktr Ctr T hT lift hlift J hJ ustar
    (fun lam hlam f => ⟨(hdata lam hlam f).1, (hdata lam hlam f).2.2.2⟩)
  apply continuous_pi
  intro x
  have hνpos : ∀ y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ delta : ℝ, 0 < delta → 0 < (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) (Metric.ball y delta) := by
    intro y hy delta hdelta
    rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet]
    exact (Metric.isOpen_ball.inter (centeredCube z r hr).isOpen).measure_pos volume
      ⟨y, Metric.mem_ball_self hdelta, hy⟩
  exact continuous_representative_readout_of_continuous_Lp
    (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) (centeredCube z r hr)
    (centeredCube z r hr).isOpen hνpos u huc
    (fun a y => R a.1.1 (closedSourceExtension (centeredCube z r hr) a.2) y)
    (fun a => (hdata a.1.1 a.1.2 _).2.1)
    (fun a : X => Khol * ‖a.2‖) (continuous_const.mul continuous_snd.norm)
    (fun r : ℝ => r ^ (1 / 4 : ℝ)) (Real.zero_rpow (by norm_num))
    (Real.continuousAt_rpow_const 0 (1 / 4) (.inr (by norm_num)))
    (fun r hr => Real.rpow_nonneg hr _)
    (fun a y hy y' hy' => by
      have h := (hdata a.1.1 a.1.2 (closedSourceExtension (centeredCube z r hr) a.2)).2.2.1 y (subset_closure hy) y' (subset_closure hy')
      rwa [norm_closedSourceExtension] at h) x x.2

end Paper
