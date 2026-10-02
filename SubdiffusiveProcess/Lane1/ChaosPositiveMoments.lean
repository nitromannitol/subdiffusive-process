import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.ChaosCutoff
import SubdiffusiveProcess.Main.WeightedChaosCutoff
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.ConditionalFineFiltration
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Lane1.ChaosBasic
import SubdiffusiveProcess.Lane1.WeightedIndep
import SubdiffusiveProcess.Lane1.ChaosMoment
import SubdiffusiveProcess.Probability.ChaosCutoffLocalFinite
import SubdiffusiveProcess.Probability.CubeMassMartingale
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Martingale.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open Filter MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

theorem chaos_positive_moments_and_martingales
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (p : ℕ) (hp : 1 ≤ p) :
  ∃ Cexponent cSmall : ℝ, 0 < Cexponent ∧ 0 < cSmall ∧
    ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
      ∃ Cmass : ℝ, 0 < Cmass ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (hH : InfraredCharacterization M H), M.delta ≤ cSmall →
          (∀ (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            r ≤ 1 → (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ R →
            Measurable (fun omega ↦
              ((weightedChaosCutoff M H N omega)
                (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p) ∧
            Integrable (fun omega ↦
              ((weightedChaosCutoff M H N omega)
                (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
              (chaosSampleLaw M).toMeasure ∧
            ∫ omega, ((weightedChaosCutoff M H N omega)
                (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p
              ∂(chaosSampleLaw M).toMeasure ≤
              Cmass * r ^ ((d : ℝ) * p - Cexponent * M.delta ^ 2)) ∧
          (∀ N omega, IsLocallyFiniteMeasure (chaosCutoff M N omega)) ∧
          (∀ N omega, IsLocallyFiniteMeasure (weightedChaosCutoff M H N omega)) ∧
          (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            Martingale
              (fun N omega ↦ ((chaosCutoff M N omega)
                (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
              (conditionalFineFiltration (fun _ ↦ 0) measurable_const)
              (chaosSampleLaw M).toMeasure ∧
            (∀ N omega, 0 ≤ ((chaosCutoff M N omega)
              (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)) ∧
          (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            Martingale
              (fun N omega ↦ ((weightedChaosCutoff M H N omega)
                (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
              (conditionalFineFiltration H hH.1) (chaosSampleLaw M).toMeasure ∧
            (∀ N omega, 0 ≤ ((weightedChaosCutoff M H N omega)
              (centeredCube z r hr : Set (SpatialCoordinates d))).toReal))

 := by
  -- Block (A), paper D:36-64, eq. (38).  The ONLY remaining obligation.
  obtain ⟨Cexponent, cSmall, hCe, hcS, hA⟩ :
      ∃ Cexponent cSmall : ℝ, 0 < Cexponent ∧ 0 < cSmall ∧
        ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ Cmass : ℝ, 0 < Cmass ∧
            ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
              (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
              InfraredCharacterization M H → M.delta ≤ cSmall →
              ∀ (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
                r ≤ 1 → (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ R →
                Measurable (fun omega ↦
                  ((weightedChaosCutoff M H N omega)
                    (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p) ∧
                Integrable (fun omega ↦
                  ((weightedChaosCutoff M H N omega)
                    (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
                  (chaosSampleLaw M).toMeasure ∧
                ∫ omega, ((weightedChaosCutoff M H N omega)
                    (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p
                  ∂(chaosSampleLaw M).toMeasure ≤
                  Cmass * r ^ ((d : ℝ) * p - Cexponent * M.delta ^ 2) :=
    chaos_moment_block hd p hp
  refine ⟨Cexponent, cSmall, hCe, hcS, ?_⟩
  intro R hR
  obtain ⟨Cmass, hCm, hA'⟩ := hA R hR
  refine ⟨Cmass, hCm, ?_⟩
  intro M H hH hdelta
  exact ⟨fun N z r hr hr1 hsub => hA' M H hH hdelta N z r hr hr1 hsub,
    fun N omega => chaosCutoff_isLocallyFinite M N omega,
    fun N omega => weightedChaosCutoff_isLocallyFinite M H N omega,
    chaosCutoff_centeredCube_martingale_nonnegative M,
    weightedChaosCutoff_centeredCube_martingale_nonnegative hd M H hH⟩

end SubdiffusiveProcess
