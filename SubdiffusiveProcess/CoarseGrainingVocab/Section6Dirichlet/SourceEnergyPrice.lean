module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalEnergyPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceForcingPrice

@[expose] public section

/-!
# Source-scale form of the physical Dirichlet energy price

The coefficient-normalized forcing and boundary prices have the same
physical factor: coefficient envelope times `sqrt ahom` times inverse cube
scale.  This file records that cancellation before the stochastic
prebalance assembly.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The deterministic unit-cube datum price in the physical energy row. -/
noncomputable def sourceDirichletEnergyDatumPrice
    {d : ℕ} (C : ℝ) (s : FractionalOrder)
    (F : CubeVectorH1Function (originCube d 0))
    (h : H2Datum (originCube d 0)) : ℝ :=
  C * Real.rpow s.1 (-(3 / 2 : ℝ)) *
      sourceForcingPositiveBesovConstant d s *
        (unitCubeVectorH1ENormBudget F).toReal +
    C * Real.rpow s.1 (-(1 / 2 : ℝ)) *
      sourceBoundaryPositiveBesovConstant d s * h.norm.toReal

theorem sourceDirichletEnergyDatumPrice_nonneg
    {d : ℕ} [NeZero d] {C : ℝ} (hC : 0 ≤ C)
    (s : FractionalOrder) (F : CubeVectorH1Function (originCube d 0))
    (h : H2Datum (originCube d 0)) :
    0 ≤ sourceDirichletEnergyDatumPrice C s F h := by
  unfold sourceDirichletEnergyDatumPrice
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg s.2.1.le _))
        (sourceForcingPositiveBesovConstant_nonneg d s))
      ENNReal.toReal_nonneg)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg s.2.1.le _))
        (sourceBoundaryPositiveBesovConstant_nonneg d s))
      ENNReal.toReal_nonneg)

/-- Dimension/order coefficient after inserting the canonical divergence
lift into the two-term physical energy price. -/
noncomputable def sourceDirichletEnergyConstant
    (d : ℕ) [NeZero d] (C : ℝ) (s : FractionalOrder) : ℝ :=
  C * Real.rpow s.1 (-(3 / 2 : ℝ)) *
      sourceForcingPositiveBesovConstant d s * unitDivergenceLiftConstant d +
    C * Real.rpow s.1 (-(1 / 2 : ℝ)) *
      sourceBoundaryPositiveBesovConstant d s

theorem sourceDirichletEnergyConstant_nonneg
    (d : ℕ) [NeZero d] {C : ℝ} (hC : 0 ≤ C) (s : FractionalOrder) :
    0 ≤ sourceDirichletEnergyConstant d C s := by
  unfold sourceDirichletEnergyConstant
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg s.2.1.le _))
        (sourceForcingPositiveBesovConstant_nonneg d s))
      (unitDivergenceLiftConstant_nonneg d))
    (mul_nonneg
      (mul_nonneg hC (Real.rpow_nonneg s.2.1.le _))
      (sourceBoundaryPositiveBesovConstant_nonneg d s))

/-- The unit lift budget turns the physical energy datum price into a fixed
constant times the real source and boundary sizes. -/
theorem sourceDirichletEnergyDatumPrice_le_sourceSizes
    {d : ℕ} [NeZero d] {C : ℝ} (hC : 0 ≤ C)
    (s : FractionalOrder) (F : CubeVectorH1Function (originCube d 0))
    (h : H2Datum (originCube d 0)) {sourceSize : ℝ}
    (hsource : 0 ≤ sourceSize)
    (hbudget : (unitCubeVectorH1ENormBudget F).toReal ≤
      unitDivergenceLiftConstant d * sourceSize) :
    sourceDirichletEnergyDatumPrice C s F h ≤
      sourceDirichletEnergyConstant d C s * (sourceSize + h.norm.toReal) := by
  have hA : 0 ≤ C * Real.rpow s.1 (-(3 / 2 : ℝ)) *
      sourceForcingPositiveBesovConstant d s := by
    exact mul_nonneg
      (mul_nonneg hC (Real.rpow_nonneg s.2.1.le _))
      (sourceForcingPositiveBesovConstant_nonneg d s)
  have hB : 0 ≤ C * Real.rpow s.1 (-(1 / 2 : ℝ)) *
      sourceBoundaryPositiveBesovConstant d s := by
    exact mul_nonneg
      (mul_nonneg hC (Real.rpow_nonneg s.2.1.le _))
      (sourceBoundaryPositiveBesovConstant_nonneg d s)
  have hLift : 0 ≤ unitDivergenceLiftConstant d :=
    unitDivergenceLiftConstant_nonneg d
  unfold sourceDirichletEnergyDatumPrice sourceDirichletEnergyConstant
  calc
    _ ≤ (C * Real.rpow s.1 (-(3 / 2 : ℝ)) *
          sourceForcingPositiveBesovConstant d s) *
          (unitDivergenceLiftConstant d * sourceSize) +
        (C * Real.rpow s.1 (-(1 / 2 : ℝ)) *
          sourceBoundaryPositiveBesovConstant d s) * h.norm.toReal := by
      gcongr
    _ ≤ _ := by
      calc
        _ ≤ (C * Real.rpow s.1 (-(3 / 2 : ℝ)) *
                sourceForcingPositiveBesovConstant d s *
                unitDivergenceLiftConstant d) *
                (sourceSize + h.norm.toReal) +
              (C * Real.rpow s.1 (-(1 / 2 : ℝ)) *
                sourceBoundaryPositiveBesovConstant d s) *
                (sourceSize + h.norm.toReal) := by
          exact add_le_add
            (by
              simpa only [mul_assoc] using
                (mul_le_mul_of_nonneg_left
                  (le_add_of_nonneg_right
                    (show 0 ≤ h.norm.toReal from ENNReal.toReal_nonneg))
                  (mul_nonneg hA hLift)))
            (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_left hsource) hB)
        _ = _ := by ring

/-- The canonical divergence lift simultaneously satisfies the weak identity
and the source-size energy price needed by the physical solution. -/
theorem exists_unitDivergenceLift_with_sourceEnergyPrice
    (d : ℕ) [NeZero d] {C : ℝ} (hC : 0 ≤ C)
    (s : FractionalOrder) (h : H2Datum (originCube d 0))
    (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0)))) :
    ∃ F : CubeVectorH1Function (originCube d 0),
      (∀ phi : H10Function (openCubeSet (originCube d 0)),
        ∫ x in openCubeSet (originCube d 0),
            f x * phi.toH1Function.toFun x ∂volume =
          -∫ x in openCubeSet (originCube d 0),
            vecDot (F.toField x) (phi.toH1Function.grad x) ∂volume) ∧
      sourceDirichletEnergyDatumPrice C s F h ≤
        sourceDirichletEnergyConstant d C s *
          (‖toScalarL2 hf‖ + h.norm.toReal) := by
  obtain ⟨F, hpair, hbudget⟩ :=
    exists_unitDivergenceLift_with_real_budget d f hf
  refine ⟨F, hpair, ?_⟩
  exact sourceDirichletEnergyDatumPrice_le_sourceSizes hC s F h
    (norm_nonneg _) hbudget

private theorem inv_sqrt_mul_self_eq_sqrt {a : ℝ} (ha : 0 < a) :
    (Real.sqrt a)⁻¹ * a = Real.sqrt a := by
  have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  calc
    (Real.sqrt a)⁻¹ * a =
        (Real.sqrt a)⁻¹ * (Real.sqrt a * Real.sqrt a) := by
      rw [Real.mul_self_sqrt ha.le]
    _ = Real.sqrt a := by field_simp

/-- Exact common-factor form of the two physical datum prices. -/
theorem cutoffDirichletDatumEnergyPrice_eq_sourceScale
    {d : ℕ} [NeZero d] (C Y a : ℝ) (ha : 0 < a) (m : ℤ)
    (s : FractionalOrder) (F : CubeVectorH1Function (originCube d 0))
    (h : H2Datum (originCube d 0)) :
    C * Real.rpow s.1 (-(3 / 2 : ℝ)) *
          (Y * Real.sqrt a⁻¹) *
          scaledVectorDatumPositiveBesovSeminormBound (-a) m s F +
        C * Real.rpow s.1 (-(1 / 2 : ℝ)) *
          (Y * Real.sqrt a) * h2BoundaryPositiveBesovBound m s h =
      Y * Real.sqrt a * (centeredCubeScale m)⁻¹ *
        sourceDirichletEnergyDatumPrice C s F h := by
  rw [scaledVectorDatumPositiveBesovSeminormBound_eq_sourceDatum,
    h2BoundaryPositiveBesovBound_eq_sourceDatum]
  rw [abs_neg, abs_of_pos ha, Real.sqrt_inv]
  have hcancel := inv_sqrt_mul_self_eq_sqrt ha
  have hcancel' : a * (Real.sqrt a)⁻¹ = Real.sqrt a := by
    rw [mul_comm, hcancel]
  unfold sourceDirichletEnergyDatumPrice
  calc
    _ = (a * (Real.sqrt a)⁻¹) *
          (C * Real.rpow s.1 (-(3 / 2 : ℝ)) * Y *
            (centeredCubeScale m)⁻¹ *
            sourceForcingPositiveBesovConstant d s *
              (unitCubeVectorH1ENormBudget F).toReal) +
        Real.sqrt a *
          (C * Real.rpow s.1 (-(1 / 2 : ℝ)) * Y *
            (centeredCubeScale m)⁻¹ *
            sourceBoundaryPositiveBesovConstant d s * h.norm.toReal) := by ac_rfl
    _ = Real.sqrt a *
          (C * Real.rpow s.1 (-(3 / 2 : ℝ)) * Y *
            (centeredCubeScale m)⁻¹ *
            sourceForcingPositiveBesovConstant d s *
              (unitCubeVectorH1ENormBudget F).toReal) +
        Real.sqrt a *
          (C * Real.rpow s.1 (-(1 / 2 : ℝ)) * Y *
            (centeredCubeScale m)⁻¹ *
            sourceBoundaryPositiveBesovConstant d s * h.norm.toReal) := by
      rw [hcancel']
    _ = _ := by ring

/-- Source-facing version of the almost-sure physical energy estimate. -/
theorem exists_ae_cutoffPhysicalDirichletEnergy_le_sourcePrice
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
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
              dirichletEllipticityEnvelope M L N s.1 omega *
                Real.sqrt (ahom M L) * (centeredCubeScale (N : ℤ))⁻¹ *
                  sourceDirichletEnergyDatumPrice C s F h := by
  obtain ⟨C, hC, henergy⟩ :=
    exists_ae_cutoffPhysicalDirichletEnergy_le_datumPrices d
  refine ⟨C, hC, ?_⟩
  intro M L N s s2 p B hss2 hp hmoment
  filter_upwards [henergy M L N s s2 hss2 hp hmoment] with omega homega
  intro u h f F hu hF
  rw [← cutoffDirichletDatumEnergyPrice_eq_sourceScale C
    (dirichletEllipticityEnvelope M L N s.1 omega) (ahom M L)
    (ahom_pos M L) (N : ℤ) s F h]
  exact homega h F hu hF

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
