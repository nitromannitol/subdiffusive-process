import SubdiffusiveProcess.Paper.Support.UniformResolventHalfLift
import SubdiffusiveProcess.Analysis.LimitEnergyCoercivity
import SubdiffusiveProcess.Section9.RepresentedComparisonDraft
import SubdiffusiveProcess.Lane4.Inputs

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology Set SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Section9
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- Choose a total finite-energy lifting carrier by replacing an exceptional
inverse by zero. This does not alter its original convergence in probability. -/
theorem aux_mfd_prop_uniform_resolvent_masked_inverse
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Sf : SobolevFoundationalInput d hd)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (G : KilledInverseFamily d (BilateralField d)) (hmeas : ∀ i, Measurable (G i))
    (hconv : ∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N omega => volumeResponseOperator (determiningResponseSpace d i)
        (cutoffPositiveCoefficient M H omega N
          (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))) atTop (G i))
    (hhalf : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i (u : DomainL2 (determiningCube d i)),
      (limitFormEnergy (G i omega) u).toENNReal ≠ ∞ →
        ∃ w : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i)
            (rationalTriadicSide d i) (rationalTriadicSide_pos d i) halfFractionalOrder,
          w.val 0 = u) :
    ∃ G' : KilledInverseFamily d (BilateralField d), (∀ i, Measurable (G' i)) ∧
      (∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N omega => volumeResponseOperator (determiningResponseSpace d i)
          (cutoffPositiveCoefficient M H omega N
            (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))) atTop (G' i)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i, G' i omega = G i omega) ∧
      ∀ i omega (u : DomainL2 (determiningCube d i)),
        (limitFormEnergy (G' i omega) u).toENNReal ≠ ∞ →
          ∃ w : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i)
              (rationalTriadicSide d i) (rationalTriadicSide_pos d i) halfFractionalOrder,
            w.val 0 = u := by
  classical
  let P := (chaosSampleLaw M).toMeasure
  let p : BilateralField d → Prop := fun omega => ∀ i (u : DomainL2 (determiningCube d i)),
    (limitFormEnergy (G i omega) u).toENNReal ≠ ∞ →
      ∃ w : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i)
        (rationalTriadicSide d i) (rationalTriadicSide_pos d i) halfFractionalOrder,
        w.val 0 = u
  let Good := (toMeasurable P {omega | ¬ p omega})ᶜ
  have hGood : MeasurableSet Good := (measurableSet_toMeasurable P _).compl
  have hGoodae : ∀ᵐ omega ∂P, omega ∈ Good := by
    rw [ae_iff]
    change P Goodᶜ = 0
    rw [show Good = (toMeasurable P {omega | ¬ p omega})ᶜ from rfl,
      compl_compl, measure_toMeasurable]
    exact ae_iff.mp hhalf
  have hGoodp : ∀ omega ∈ Good, p omega := by
    intro omega hω
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  let G' : KilledInverseFamily d (BilateralField d) :=
    fun i omega => if omega ∈ Good then G i omega else 0
  have heq : ∀ᵐ omega ∂P, ∀ i, G' i omega = G i omega := by
    filter_upwards [hGoodae] with omega hω i
    exact if_pos hω
  refine ⟨G', fun i => Measurable.ite hGood (hmeas i) measurable_const,
    fun i => TendstoInMeasure.congr_right (heq.mono fun _ h => (h i).symm) (hconv i), heq, ?_⟩
  intro i omega u hu
  by_cases hω : omega ∈ Good
  · rw [show G' i omega = G i omega from if_pos hω] at hu
    exact hGoodp omega hω i u hu
  · rw [show G' i omega = 0 from if_neg hω] at hu
    have hu0 := SubdiffusiveProcess.Analysis.eq_zero_of_zero_limitEnergy_finite (determiningCube d i) u hu
    subst u
    let v : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i)
        (rationalTriadicSide d i) (rationalTriadicSide_pos d i) threeQuarterOrder :=
      ⟨fun _ => (0 : SobolevData (determiningCube d i)).1,
        Sf.h1_fractional_finite (rationalTriadicCenter d i) (rationalTriadicSide d i)
          (rationalTriadicSide_pos d i) 0⟩
    exact aux_mfd_prop_uniform_resolvent_half_lift hd (rationalTriadicCenter d i)
      (rationalTriadicSide d i) (rationalTriadicSide_pos d i) v

end Paper
