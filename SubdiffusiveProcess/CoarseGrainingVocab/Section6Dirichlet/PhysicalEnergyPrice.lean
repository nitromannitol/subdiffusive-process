module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyConsequence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.H2BoundaryBesovPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalDatumRegularity

@[expose] public section

/-!
# Source-facing energy price for the physical cutoff Dirichlet solution

This is the deterministic datum composition below
`e.Dirichlet.energy.factor`: the signed divergence lift and the dilated
`H²` boundary datum discharge both regularity and both quantitative positive
Besov premises of the coefficient-envelope energy theorem.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

theorem neg_centeredCubeScaledVectorDilation_toField
    {d : ℕ} (alpha : ℝ) (m : ℤ)
    (F : CubeVectorH1Function (originCube d 0)) :
    (fun x ↦ -(centeredCubeScaledVectorDilation alpha m F).toField x) =
      (centeredCubeScaledVectorDilation (-alpha) m F).toField := by
  funext x
  rw [centeredCubeScaledVectorDilation_toField,
    centeredCubeScaledVectorDilation_toField]
  module

/-- The public real Dirichlet energy and the coarse-graining extended-real
local symmetric energy are the same parent-cube carrier. -/
theorem ofReal_dirichletForcedSolutionEnergyNorm_eq_localSymmetricEnergyENorm
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g) :
    ENNReal.ofReal (dirichletForcedSolutionEnergyNorm Q a v) =
      Book.Ch03.ABK26.localSymmetricEnergyENorm Q (a.coeffOn Q) v.toH1 := by
  have havg :
      cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a) v.toH1.grad) =
        cubeAverage Q
          (coefficientEnergyDensity (a.coeffOn Q).toCoeffField v.toH1.grad) := by
    calc
      _ = localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v.toH1 :=
        cubeAverage_coefficientEnergyDensity_publicCoeffField_eq_localizedCoeffEnergyValue
          Q a v.toH1
      _ = _ := by
        rw [localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity]
        simp [cubeAverage, volumeAverage, volume_openCubeSet_eq_volume_cubeSet,
          volume_cubeSet_toReal, setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  have havg_nonneg :
      0 ≤ cubeAverage Q
        (coefficientEnergyDensity (a.coeffOn Q).toCoeffField v.toH1.grad) := by
    rw [← havg]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      _ v.toH1.grad (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
  have he : Book.Ch03.ABK26.localSymmetricEnergyENorm Q (a.coeffOn Q) v.toH1 =
      (ENNReal.ofReal
        (cubeAverage Q (coefficientEnergyDensity (a.coeffOn Q).toCoeffField v.toH1.grad))) ^
          (1 / 2 : ℝ) := by
    simpa only using!
      Book.Ch03.ABK26.localSymmetricEnergyENorm_eq_ofReal_cubeAverage_coefficientEnergyDensity
        Q (a.coeffOn Q) v.toH1
  rw [dirichletForcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField,
    havg, he]
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg]
  · exact havg_nonneg
  · norm_num

theorem localSymmetricEnergyENorm_le_of_dirichletEnergy_le
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    {S : ℝ} (hS : dirichletForcedSolutionEnergyNorm Q a v ≤ S) :
    Book.Ch03.ABK26.localSymmetricEnergyENorm Q (a.coeffOn Q) v.toH1 ≤
      ENNReal.ofReal S := by
  rw [← ofReal_dirichletForcedSolutionEnergyNorm_eq_localSymmetricEnergyENorm v]
  exact ENNReal.ofReal_le_ofReal hS

/-- Almost surely, the concrete physical cutoff solution has the exact
energy bound obtained from the two explicit datum prices.  The only
stochastic assumption is the already-source-facing second response moment
which constructs the universal ellipticity envelope. -/
theorem exists_ae_cutoffPhysicalDirichletEnergy_le_datumPrices
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
        (s s2 : FractionalOrder) {p B : ℝ}, s.1 < s2.1 → 0 < p →
        paperENNRealLpNorm M.P.toMeasure p
            (fun omega ↦ paperHomogenizationError
              (originCube d (N : ℤ)) (N : ℤ) (s.1 / 2)
              .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) ≤
          ENNReal.ofReal B →
        ∀ᵐ omega ∂M.P.toMeasure,
          ∀ {u : H1Function (openCubeSet (originCube d 0))}
            (h : H2Datum (originCube d 0)) {f : Vec d → ℝ}
            (F : CubeVectorH1Function (originCube d 0))
            (hu : IsScalarDirichletSolutionOn
              (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
              (originCube d 0) u h.toH1 f)
            (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
              ∫ x in openCubeSet (originCube d 0),
                  f x * psi.toH1Function.toFun x ∂volume =
                -∫ x in openCubeSet (originCube d 0),
                  vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume),
            dirichletForcedSolutionEnergyNorm
                (originCube d (N : ℤ)) (aCutoffFamily M L omega)
                (cutoffPhysicalDirichletForcedCubeSolution
                  M L N omega F hu hF) ≤
              C * Real.rpow s.1 (-(3 / 2 : ℝ)) *
                  (dirichletEllipticityEnvelope M L N s.1 omega *
                    Real.sqrt (ahom M L)⁻¹) *
                  scaledVectorDatumPositiveBesovSeminormBound
                    (-(ahom M L)) (N : ℤ) s F +
                C * Real.rpow s.1 (-(1 / 2 : ℝ)) *
                  (dirichletEllipticityEnvelope M L N s.1 omega *
                    Real.sqrt (ahom M L)) *
                  h2BoundaryPositiveBesovBound (N : ℤ) s h := by
  obtain ⟨C, hC, henergy⟩ :=
    exists_ae_dirichletForcedSolutionEnergyNorm_le_envelope d
  refine ⟨C, hC, ?_⟩
  intro M L N s s2 p B hss2 hp hmoment
  have hrow := henergy M L N s.2.1 s.2.2 hp hmoment
  filter_upwards [hrow] with omega homega
  intro u h f F hu hF
  let v := cutoffPhysicalDirichletForcedCubeSolution M L N omega F hu hF
  have hgReg : ForceBesovRegularity (originCube d (N : ℤ)) s.1
      (fun x ↦ -(centeredCubeScaledVectorDilation
        (ahom M L) (N : ℤ) F).toField x) :=
    forceBesovRegularity_neg_centeredCubeScaledVectorDilation_of_lt
      (ahom M L) (N : ℤ) s s2 hss2 F
  have hG : scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d (N : ℤ)) s.1
        (fun x ↦ -(centeredCubeScaledVectorDilation
          (ahom M L) (N : ℤ) F).toField x) ≤
      scaledVectorDatumPositiveBesovSeminormBound
        (-(ahom M L)) (N : ℤ) s F := by
    rw [neg_centeredCubeScaledVectorDilation_toField]
    exact scaleNormalizedPositiveBesovVectorSeminormTwo_scaledVectorDatum_le
      (-(ahom M L)) (N : ℤ) s F
  have hhReg : ForceBesovRegularity (originCube d (N : ℤ)) s.1
      (dirichletBoundaryGradientField v) := by
    exact forceBesovRegularity_cutoffPhysicalDirichlet_boundaryGradient
      M L N omega h F hu hF s
  have hH : scaleNormalizedPositiveBesovVectorNormTwo
      (originCube d (N : ℤ)) s.1 (dirichletBoundaryGradientField v) ≤
      h2BoundaryPositiveBesovBound (N : ℤ) s h := by
    rw [cutoffPhysicalDirichlet_boundaryGradient_eq_h2DatumDilation]
    exact
      scaleNormalizedPositiveBesovVectorNormTwo_h2DatumGradientDilation_le
        (N : ℤ) s h
  exact homega v hgReg hG hhReg hH

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
