import SubdiffusiveProcess.Lnorm.CutoffPotentialProxy

/-!
# Measurability of the actual cutoff potentials

The normalized potential used by `proxy_pot_eq_coefficient` is a measurable
continuous function on each compact cube. Its restriction to L∞ is strongly
measurable, even though the full L∞ space need not be separable.
-/

open MeasureTheory TopologicalSpace
open scoped ENNReal
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

namespace SubdiffusiveProcess.Lnorm

/-- The actual cutoff potential on a compact cube is measurable. -/
theorem measurable_cutoffPotential_compact
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    @Measurable _ _ _ (borel C(closedCube z r hr, ℝ))
      (fun omega => proxy_contFn (H omega) M N omega z r hr) := by
  letI : MeasurableSpace C(closedCube z r hr, ℝ) := borel _
  letI : BorelSpace C(closedCube z r hr, ℝ) := ⟨rfl⟩
  unfold proxy_contFn
  refine (continuous_id.sub (continuous_const (y := ContinuousMap.const _
    (Real.log (prop16_kap M N))))).measurable.comp ?_
  refine (ContinuousMap.continuous_restrict _).measurable.comp ?_
  exact hH.add (Finset.measurable_sum _ fun j _ => measurable_pi_apply _)

/-- The actual bounded cutoff potential is measurable for the norm Borel structure. -/
theorem measurable_cutoffPotential_Lp
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    @Measurable _ _ _ (borel (Lp ℝ ∞ (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)))))
      (fun omega => proxy_pot (H omega) M N omega z r hr) := by
  exact (proxy_cp_lipschitz z r hr).continuous.borel_measurable.comp
    (measurable_cutoffPotential_compact M H hH N z r hr)

/-- The bounded cutoff potential has separable range in its norm topology, through
its continuous compact-cube representation. -/
theorem stronglyMeasurable_cutoffPotential_Lp
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    StronglyMeasurable (fun omega => proxy_pot (H omega) M N omega z r hr) := by
  letI : MeasurableSpace C(closedCube z r hr, ℝ) := borel _
  letI : BorelSpace C(closedCube z r hr, ℝ) := ⟨rfl⟩
  exact (proxy_cp_lipschitz z r hr).continuous.comp_stronglyMeasurable
    (measurable_cutoffPotential_compact M H hH N z r hr).stronglyMeasurable

end SubdiffusiveProcess.Lnorm
