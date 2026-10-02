import SubdiffusiveProcess.Sobolev.GradientEnergyMass
import SubdiffusiveProcess.Analysis.BoundedSetBallGrowth

/-! Interior-centre local gradient estimates imply whole-space ball estimates
with one fixed cube-dependent factor. No probabilistic compactness is asserted. -/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace SubdiffusiveProcess

/-- Every positive cube has a geometric factor converting local gradient growth to all-centre energy-measure growth. -/
theorem gradient_energy_measure_growth_all_centres
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (a : PositiveCoefficient (centeredCube z r hr))
        (g : HilbertGradient (centeredCube z r hr)) (K s : ℝ), 0 ≤ K → 0 ≤ s →
      (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        localGradientEnergy a (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet g ≤
          K * rho ^ s) →
      ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho → rho ≤ 1 →
        gradientEnergyMeasure a g (Metric.ball x rho) ≤
          ENNReal.ofReal ((2 ^ s * A * K) * rho ^ s) := by
  let Q := centeredCube z r hr
  obtain ⟨A, hA, hgeom⟩ := boundedSet_measure_ball_growth
    (Q : Set (SpatialCoordinates d)) (centeredCube_isBounded z hr).isCompact_closure
  refine ⟨A, hA, ?_⟩
  intro a g K s hK hs hg x rho hrho hrho1
  let mu := gradientEnergyMeasure a g
  haveI energyFinite : IsFiniteMeasure mu := (gradientEnergyMeasure_finite_and_real a g).1
  have hsupport : mu (Q : Set (SpatialCoordinates d))ᶜ = 0 := by
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply Q.isOpen.measurableSet.compl, Set.compl_inter_self, measure_empty]
  have hlocal (y : SpatialCoordinates d) (hy : y ∈ Q) (rr : ℝ) (hrr : 0 < rr) (hrr1 : rr ≤ 1) :
      mu (Metric.ball y rr ∩ (Q : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal (K * rr ^ s) := by
    rw [measure_inter_conull hsupport]
    apply (ENNReal.toReal_le_toReal (measure_ne_top mu _) ENNReal.ofReal_ne_top).mp
    rw [(gradientEnergyMeasure_finite_and_real a g).2 _ Metric.isOpen_ball.measurableSet,
      ENNReal.toReal_ofReal (mul_nonneg hK (Real.rpow_nonneg hrr.le _))]
    exact hg y hy rr hrr hrr1
  have hout := (hgeom mu K s hK hs hlocal).2 x rho hrho hrho1
  rw [measure_inter_conull hsupport] at hout
  simpa only [mul_assoc] using hout

end SubdiffusiveProcess
