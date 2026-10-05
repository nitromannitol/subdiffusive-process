module

public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasureIntegral
public import SubdiffusiveProcess.ResponseMoments.LocalEnergyAux
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

/-! Support and total mass of native coefficient-gradient energy measures. -/
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- Native energy measures have no mass outside the closure of their coefficient domain. -/
theorem gradientEnergyMeasure_support
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (g : HilbertGradient Q) :
    gradientEnergyMeasure a g (closure (Q : Set (SpatialCoordinates d)))ᶜ = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply isClosed_closure.measurableSet.compl]
  have hempty : (closure (Q : Set (SpatialCoordinates d)))ᶜ ∩
      (Q : Set (SpatialCoordinates d)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (subset_closure hx.2)
  rw [hempty, measure_empty]

/-- The total mass of the native energy measure is the coefficient quadratic form. -/
theorem gradientEnergyMeasure_univ_toReal
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (u : SobolevData Q) :
    (gradientEnergyMeasure a (sobolevGradient u) Set.univ).toReal =
      sobolevCoefficientForm a u u := by
  rw [(gradientEnergyMeasure_finite_and_real a (sobolevGradient u)).2 _ MeasurableSet.univ,
    _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ]
  rfl

/-- A coefficient energy bound is equivalently a bound on the finite energy measure's total mass. -/
theorem gradientEnergyMeasure_univ_le
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (u : SobolevData Q) (E : ℝ)
    (hE : sobolevCoefficientForm a u u ≤ E) :
    gradientEnergyMeasure a (sobolevGradient u) Set.univ ≤ ENNReal.ofReal E := by
  let hfinite : IsFiniteMeasure (gradientEnergyMeasure a (sobolevGradient u)) :=
    (gradientEnergyMeasure_finite_and_real a (sobolevGradient u)).1
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [gradientEnergyMeasure_univ_toReal, ENNReal.toReal_ofReal]
  · exact hE
  · exact (sobolevCoefficientForm_nonneg a u).trans hE

end SubdiffusiveProcess
