import SubdiffusiveProcess.Section9.RepresentedComparisonDraft
import SubdiffusiveProcess.Section9.CubeTrace
import SubdiffusiveProcess.Analysis.KilledOccupationResolvent
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import SubdiffusiveProcess.Main.MeasuresConvergeLocally
import SubdiffusiveProcess.Main.HasStrongMarkovRestart
import SubdiffusiveProcess.Main.SemigroupSymmetric
import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
import SubdiffusiveProcess.Main.PathLevyProkhorovDist

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open SubdiffusiveProcess SubdiffusiveProcess.Section9 SubdiffusiveProcess.Analysis
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section9

/-! Form and process resolvent identification over the fixed determining family.
Exact produced form-resolvent data: all inverse/trace/minimizer properties are
conclusions. The last event also identifies the path resolvent of the actual
limiting kernel with that minimizer. This predicate has no supplied analytic
hypothesis. -/
def KilledFormResolventIdentification
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (muFull : BilateralField d → Measure (SpatialCoordinates d)) : Prop :=
  letI : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  let P := (chaosSampleLaw M).toMeasure
    ∃ (G : KilledInverseFamily d (BilateralField d)),
      (∀ i, Measurable (G i)) ∧
      (∀ i, TendstoInMeasure P
        (fun N omega => volumeResponseOperator (determiningResponseSpace d i)
          (Lane4.cutoffPositiveCoefficient M H omega N
            (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))) atTop (G i)) ∧
      (∀ᵐ omega ∂P, MeasuresConvergeLocally
          (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
        IsLocallyFiniteMeasure (muFull omega) ∧ (muFull omega).IsOpenPosMeasure ∧
        NoAtoms (muFull omega) ∧
        ∀ i, muFull omega (frontier (determiningCube d i : Set (SpatialCoordinates d))) = 0) ∧
      let mu := fun i omega => (muFull omega).restrict
        (closure (determiningCube d i : Set (SpatialCoordinates d)))
      let Elim := fun i omega u => (limitFormEnergy (G i omega) u).toENNReal
      ∃ (T : ∀ i omega, CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i)
            (rationalTriadicSide d i) (rationalTriadicSide_pos d i) halfFractionalOrder →
          Lp ℝ 2 (mu i omega))
        (Ktrace Ctrace : ℕ → BilateralField d → ℝ)
        (lift : ∀ i omega (u : DomainL2 (determiningCube d i)), Elim i omega u ≠ ∞ →
          CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i)
            (rationalTriadicSide d i) (rationalTriadicSide_pos d i) halfFractionalOrder)
        (J : ∀ i, BilateralField d → DomainL2 (determiningCube d i) → SpatialCoordinates d → ℝ)
        (ustar : ∀ i, BilateralField d → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (determiningCube d i))
        (R : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          BilateralField d → C(SpatialCoordinates d, ℝ))
        (KQ : ℕ → BilateralField d → ℝ),
        (∀ᵐ omega ∂P, ∀ i, 0 ≤ Ktrace i omega ∧ 0 ≤ Ctrace i omega ∧
          CubeTraceCharacterization hd (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)
            (mu i omega) (Ktrace i omega) (Ctrace i omega) (T i omega) ∧
          ∀ (u : DomainL2 (determiningCube d i)) (hu : Elim i omega u ≠ ∞),
            (lift i omega u hu).val 0 = u ∧
            J i omega u =ᵐ[mu i omega] (T i omega (lift i omega u hu) : SpatialCoordinates d → ℝ)) ∧
        (∀ i lam, 0 < lam → ∀ f, Measurable (R i lam f)) ∧
        (∀ i lam, 0 < lam → ∀ f, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            P {omega | ∃ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
              eps ≤ |killedOccupationResolvent (determiningCube d i) KN N omega lam f x -
                R i lam f omega x|} ≤ ENNReal.ofReal rho) ∧
        (∀ i, Measurable (KQ i) ∧ MemLp (KQ i) 2 P) ∧
        ∀ᵐ omega ∂P, ∀ i,
          (∀ N lam, 0 < lam → ∀ f,
            ContinuousOn (killedOccupationResolvent (determiningCube d i) KN N omega lam f)
              (closure (determiningCube d i : Set (SpatialCoordinates d))) ∧
            ∀ x ∈ frontier (determiningCube d i : Set (SpatialCoordinates d)),
              killedOccupationResolvent (determiningCube d i) KN N omega lam f x = 0) ∧
          0 ≤ KQ i omega ∧
          ∀ lam, 0 < lam → ∀ f,
            Elim i omega (ustar i omega lam f) ≠ ∞ ∧
            (R i lam f omega : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (determiningCube d i : Set (SpatialCoordinates d))]
              (ustar i omega lam f : SpatialCoordinates d → ℝ) ∧
            (∀ x ∉ (determiningCube d i : Set (SpatialCoordinates d)), R i lam f omega x = 0) ∧
            (∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
              |R i lam f omega x| ≤ ‖f‖ / lam ∧ |R i lam f omega x| ≤ KQ i omega * ‖f‖) ∧
            (∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
                |R i lam f omega x - R i lam f omega y| ≤
                  KQ i omega * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
            let Func := fun u => (Elim i omega u).toReal +
              lam * (∫ x, J i omega u x ^ 2 ∂(mu i omega)) -
              2 * (∫ x, f x * J i omega u x ∂(mu i omega))
            (∀ u, Elim i omega u ≠ ∞ →
              Integrable (fun x => J i omega u x ^ 2) (mu i omega) ∧
              Integrable (fun x => f x * J i omega u x) (mu i omega) ∧
              Func (ustar i omega lam f) ≤ Func u) ∧
            (∀ u, Elim i omega u ≠ ∞ →
              (∀ v, Elim i omega v ≠ ∞ → Func u ≤ Func v) → u = ustar i omega lam f) ∧
            ∀ x ∈ (determiningCube d i : Set (SpatialCoordinates d)),
              R i lam f omega x =
                killedOccupationResolvent (determiningCube d i) (fun _ => K) 0 omega lam f x


end SubdiffusiveProcess.Section9
