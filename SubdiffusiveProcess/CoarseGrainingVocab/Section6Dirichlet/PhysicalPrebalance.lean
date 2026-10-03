module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszTranslatedCell
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DirichletPrebalance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalEnergyPrice

@[expose] public section

/-!
# Physical cutoff composition of the Dirichlet prebalance theorem

This file discharges the weak-equation, common-boundary, descendant-energy,
and positive fractional datum carriers of the general prebalance endpoint.
Only the two full response bounds and the parent energy bound remain as
numerical inputs.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private theorem aCutoffFamily_isSymmetric
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    ∀ Q, Ch02.CoeffOn.IsSymmetric ((aCutoffFamily M L omega).coeffOn Q) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.fluxRowRiesz_aCutoffFamily_isSymmetric (d := d) (M := M) (L := L) (omega := omega)

/-- The real descendant-energy upper bound generated from a parent energy
bound `S`. -/
noncomputable def cutoffDirichletWeightedEnergyBound
    (s1 s : ℝ) (S : ℝ) : ℝ :=
  dirichletWeightedEnergyFactor s1 s * S

/-- The physical cutoff instantiation of `e.Dirichlet.prebalance`. -/
theorem exists_cutoffDirichletPrebalance_of_response_energy_bounds
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N k : ℕ), 0 < k →
        ∀ (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
          (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
        ∀ {u v : H1Function (openCubeSet (originCube d 0))}
          (h : H2Datum (originCube d 0)) {f : Vec d → ℝ}
          (F : CubeVectorH1Function (originCube d 0))
          (hu : IsScalarDirichletSolutionOn
              (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
              (originCube d 0) u h.toH1 f)
          (_hv : IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
              (originCube d 0) v h.toH1 f)
          (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
            ∫ x in openCubeSet (originCube d 0),
                f x * psi.toH1Function.toFun x ∂volume =
              -∫ x in openCubeSet (originCube d 0),
                vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume),
          ∀ E1 E2 S : ℝ, 0 ≤ E1 → 0 ≤ E2 → 0 ≤ S →
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) s1.1
              .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal E1 →
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) (s1.1 / 2)
              .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal E2 →
          dirichletForcedSolutionEnergyNorm
              (originCube d (N : ℤ)) (aCutoffFamily M L omega)
              (cutoffPhysicalDirichletForcedCubeSolution M L N omega F
                hu hF) ≤ S →
          paperNegativeFractionalDual (originCube d 0) s
                FiniteLpExponent.two
                (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
                  (centeredCubeScale (N : ℤ))
                  (centeredCubeGradientDifferenceL2Field (N : ℤ)
                    (centeredCubeRawDilation (N : ℤ) u)
                    (centeredCubeRawDilation (N : ℤ) v))) +
              paperNegativeFractionalDual (originCube d 0) s
                FiniteLpExponent.two
                (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
                  (centeredCubeScale (N : ℤ) * (ahom M L)⁻¹)
                  (centeredCubeFluxDifferenceL2Field (N : ℤ)
                    ((aCutoffFamily M L omega).coeffOn (originCube d (N : ℤ)))
                    (ahom M L) (centeredCubeRawDilation (N : ℤ) u)
                    (centeredCubeRawDilation (N : ℤ) v))) ≤
            ENNReal.ofReal
              (centeredCubeScale (N : ℤ) * (ahom M L)⁻¹ *
                dirichletCoarseGrainingRHS C (ahom M L) s.1 s2.1
                  (Real.rpow 3 (s1.1 * (k : ℝ)) * E1)
                  (Real.rpow 3 ((s1.1 / 2) * (k : ℝ)) * E2)
                  (cutoffDirichletWeightedEnergyBound s1.1 s.1 S)
                  (scaledVectorDatumFractionalBound
                    (ahom M L) (N : ℤ) s2 F)
                  ((N : ℤ) - (k : ℤ))) := by
  obtain ⟨C, hC, hpre⟩ := exists_unit_dirichletPrebalance_of_carrier_bounds d hd
  refine ⟨C, hC, ?_⟩
  intro M L N k hk omega s1 s s2 hs1s hss2 u v h f F hu _hv hF
    E1 E2 S hE10 hE20 hS0 hE1 hE2 henergy
  let uN := centeredCubeRawDilation (N : ℤ) u
  let vN := centeredCubeRawDilation (N : ℤ) v
  let gN := centeredCubeScaledVectorDilation (ahom M L) (N : ℤ) F
  let vp := cutoffPhysicalDirichletForcedCubeSolution M L N omega F hu hF
  let SW := cutoffDirichletWeightedEnergyBound s1.1 s.1 S
  let D := scaledVectorDatumFractionalBound (ahom M L) (N : ℤ) s2 F
  have huN : IsForcedEquation (originCube d (N : ℤ))
      ((aCutoffFamily M L omega).coeffOn (originCube d (N : ℤ))) uN gN.toField := by
    simpa only [uN, gN] using
      isForcedEquation_aCutoff_centeredCubeRawDilation M L N omega F hu hF
  have hvN : IsScalarForcedEquation (originCube d (N : ℤ)) (ahom M L)
      vN gN.toField := by
    simpa only [vN, gN] using
      isScalarForcedEquation_ahom_centeredCubeRawDilation M L N F _hv hF
  have huvN : HasH10Difference (originCube d (N : ℤ)) uN vN := by
    simpa only [uN, vN] using
      hasH10Difference_cutoff_ahom_centeredCubeRawDilation M L N omega hu _hv
  have hparent : localSymmetricEnergyENorm (originCube d (N : ℤ))
      ((aCutoffFamily M L omega).coeffOn (originCube d (N : ℤ))) uN ≤
        ENNReal.ofReal S := by
    have := localSymmetricEnergyENorm_le_of_dirichletEnergy_le vp henergy
    simpa only [vp, cutoffPhysicalDirichletForcedCubeSolution_toH1, uN] using this
  have hweighted : weightedLocalSymmetricEnergyLp (originCube d (N : ℤ))
      ((N : ℤ) - (k : ℤ)) (by simp [originCube])
      ((aCutoffFamily M L omega).coeffOn (originCube d (N : ℤ))) uN
      s1 s FiniteLpExponent.two ≤ ENNReal.ofReal SW := by
    simpa only [SW, cutoffDirichletWeightedEnergyBound] using
      weightedLocalSymmetricEnergyLp_two_le_realBound
        (originCube d (N : ℤ)) ((N : ℤ) - (k : ℤ)) (by simp [originCube])
        ((aCutoffFamily M L omega).coeffOn (originCube d (N : ℤ)))
        uN s1 s (sub_pos.mpr hs1s) hparent
  have hD : paperFractionalSeminorm (originCube d (N : ℤ)) s2
      FiniteLpExponent.two gN.toField ≤ ENNReal.ofReal D := by
    simpa only [D, gN] using
      paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_realBound
        (ahom M L) (N : ℤ) s2 F
  have hSW0 : 0 ≤ SW := mul_nonneg
    (dirichletWeightedEnergyFactor_nonneg s1.1 s.1) hS0
  have hD0 : 0 ≤ D :=
    scaledVectorDatumFractionalBound_nonneg (ahom M L) (N : ℤ) s2 F
  exact hpre N k hk (aCutoffFamily M L omega)
    (aCutoffFamily_isSymmetric M L omega) (ahom M L)
    s.1 s1.1 s2.1 (ahom_pos M L) s1.2.1 hs1s hss2 s2.2.2
    s rfl s2 rfl
    (centeredCubeScaledVectorDilationWspField (ahom M L) (N : ℤ) s2 F)
    uN vN huN hvN huvN E1 E2 SW D hE10 hE20 hSW0 hD0
    hE1 hE2 hweighted hD

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
