module

public import SubdiffusiveProcess.Paper.lem_as_regularity

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper




theorem mfd_cor_neumann_source :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (_Cp : CampanatoInput d) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ)
          (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N z hr) F v →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha
                (closedCube z r hr :
                  Set (SpatialCoordinates d)) U ∧
            ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha
                (closedCube z r hr :
                  Set (SpatialCoordinates d)) U ≤ K N om * Kf) ∧
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
            0 < rad → rad ≤ 1 →
            localGradientEnergy
                (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
              K N om * Kf ^ 2 * rad ^ t) := by
  intro d hd _ _ E P X W D Cp t alpha k ps htlo hthi ha0 ha1 hps
  exact aux_lem_as_regularity_neumann_cube
    d hd E P X W D Cp t alpha k ps htlo hthi ha0 ha1 hps

end SubdiffusiveProcess.Paper
