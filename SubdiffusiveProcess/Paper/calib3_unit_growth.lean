import Mathlib
import SubdiffusiveProcess.Paper.calib3_HT
import SubdiffusiveProcess.Paper.calib3_energy_assembly
import SubdiffusiveProcess.Paper.calib3_holder_assembly
import SubdiffusiveProcess.Paper.prop_growth_admissible
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Stage 3 (calibration): energy growth `rad^t` and Hölder bound at all radii on the unit cube for the top-block-removed model
`HT_j` (coefficient level `N + j`), with one random constant of all prescribed moments.  Analogue of
`aux_prop_growth_admissible_trunc` (`prop_growth_admissible`) at unit cubes. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem calib3_unit_growth :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M), M.delta ≤ delta0 →
      ∀ (j : ℕ), 0 < j → ∀ (z : SpatialCoordinates d),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z 1 one_pos)),
          ((b : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z 1 one_pos →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos)
                (s := Metric.ball x rad ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z 1 one_pos).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z 1 one_pos))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z 1 one_pos : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z 1 one_pos : Set (SpatialCoordinates d)) U ≤
              K N om * (Kf + Cphi)) := by
  intro d hd _ _ E P X W Cp S t alpha k ps htlow hthi ha0 ha1 hps
  obtain ⟨δE, hδE, hE⟩ :=
    calib3_energy_assembly d hd E P X W Cp S t alpha k ps
      htlow hthi ha0 ha1 hps
  obtain ⟨δH, hδH, hH⟩ :=
    calib3_holder_assembly d hd E P X W Cp S t alpha k ps
      htlow hthi ha0 ha1 hps
  refine ⟨min δE δH, lt_min hδE hδH, ?_⟩
  intro M Rm hδ j hj z
  obtain ⟨KE, CE, hmemE, hnormE, hgeE, henergy⟩ :=
    hE M Rm (hδ.trans (min_le_left _ _)) j hj z
  obtain ⟨KH, CH, hmemH, hnormH, hgeH, hholder⟩ :=
    hH M Rm (hδ.trans (min_le_right _ _)) j hj z
  obtain ⟨K, C, hmem, hnorm, hdom⟩ :=
    aux_prop_growth_pair_majorant (chaosSampleLaw M).toMeasure k ps hps
      KE KH CE CH hmemE hmemH hnormE hnormH hgeE hgeH
  refine ⟨K, C, hmem, hnorm, ?_, ?_⟩
  · filter_upwards [hdom] with om hom
    intro N
    exact (hom N).1
  · filter_upwards [henergy, hholder, hdom] with om he hh hdK
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have hCphi0 : 0 ≤ Cphi :=
      (aux_prop_growth_c2Norm_nonneg (closedCube z 1 one_pos :
        Set (SpatialCoordinates d)) phi).trans hCphi
    have hdata0 : 0 ≤ Kf + Cphi := add_nonneg hKf hCphi0
    constructor
    · intro x rad hx hrad hrad1
      have hbase := he N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
        x rad hx hrad hrad1
      have hfactor : 0 ≤ (Kf + Cphi) ^ 2 * rad ^ t :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hrad.le _)
      calc
        _ ≤ KE N om * (Kf + Cphi) ^ 2 * rad ^ t := hbase
        _ = KE N om * ((Kf + Cphi) ^ 2 * rad ^ t) := by ring
        _ ≤ K N om * ((Kf + Cphi) ^ 2 * rad ^ t) :=
          mul_le_mul_of_nonneg_right (hdK N).2.1 hfactor
        _ = K N om * (Kf + Cphi) ^ 2 * rad ^ t := by ring
    · obtain ⟨U, hUcont, hUae, hUholder, hUnorm⟩ :=
        hh N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
      refine ⟨U, hUcont, hUae, hUholder, hUnorm.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (hdK N).2.2 hdata0

end Paper
