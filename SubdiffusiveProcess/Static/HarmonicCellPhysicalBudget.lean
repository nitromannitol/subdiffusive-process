import SubdiffusiveProcess.Static.HarmonicDatumHolderBounds
import SubdiffusiveProcess.Static.CutoffDirichletEnergyMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DilationWeakEquation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CoarseAffineDirichletPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.EnergyReadout

/-! # Native physical energy and weak equation of a harmonic unit cell -/
open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Zero forcing turns the literal harmonic equation into the native unit problem. -/
theorem harmonicCell_scalarDirichlet {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (z : Vec d) (omega : PotentialSample d)
    {u h : H1Function (openCubeSet (originCube d 0))}
    (hu : IsWeaklyHarmonicOn
      (fun x => (ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ)^k • x))
      (openCubeSet (originCube d 0)) u)
    (hh : HasZeroTraceDifferenceOn (openCubeSet (originCube d 0)) u h) :
    IsScalarDirichletSolutionOn
      (scalarCoeffField (rescaledCutoffCoefficient M j k (translatePotentialSample z omega)))
      (originCube d 0) u h (fun _ => 0) := by
  refine ⟨hh, ?_⟩
  intro psi
  simpa only [rescaledCutoffCoefficient, scalarCoeffField, matVecMul_scalarMatrix,
    Section6Covariance.aCutoff_translatePotentialSample, add_comm,
    zero_mul, integral_zero] using hu psi

/-- The same zero-force equation and trace hold on the physical cube. -/
theorem harmonicCell_physicalDirichlet {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (omega : PotentialSample d)
    {u h : H1Function (openCubeSet (originCube d 0))}
    (hu : IsScalarDirichletSolutionOn
      (scalarCoeffField (rescaledCutoffCoefficient M j k omega))
      (originCube d 0) u h (fun _ => 0)) :
    IsDirichletSolutionOn (aCutoff M j omega) (originCube d (k : ℤ))
      (centeredCubeRawDilation (k : ℤ) u) (centeredCubeRawDilation (k : ℤ) h)
      (fun _ => 0) := by
  let F : CubeVectorH1Function (originCube d 0) := ⟨fun _ => 0⟩
  have hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
      ∫ x in openCubeSet (originCube d 0), (0 : ℝ) * psi.toFun x =
      -∫ x in openCubeSet (originCube d 0), vecDot (F.toField x) (psi.grad x) := by
    intro psi
    simp [F, CubeVectorH1Function.toField, vecDot]
  refine ⟨hasZeroTraceDifferenceOn_centeredCubeRawDilation (k : ℤ) hu.1, ?_⟩
  have hv := isDivFormWeakSolutionOn_centeredCubeRawDilation (k : ℤ)
    (ahom_pos M j) (aCutoff M j omega) F
    (by simpa only [rescaledCutoffCoefficient, centeredCubeScale, zpow_natCast] using hu.2) hF
  have hfield : (centeredCubeScaledVectorDilation (ahom M j) (k : ℤ) F).toField =
      fun _ => 0 := by
    funext x
    rw [centeredCubeScaledVectorDilation_toField]
    have hz : F.toField ((centeredCubeScale (k : ℤ))⁻¹ • x) = 0 := by
      ext i
      change (0 : H1Function (openCubeSet (originCube d 0))).toFun _ = 0
      rfl
    rw [hz, smul_zero]
  rwa [hfield] at hv

/-- Literal identification of the physical Dirichlet energy norm. -/
theorem harmonicCell_physicalEnergyNorm_eq {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (omega : PotentialSample d) {u : H1Function (openCubeSet (originCube d 0))}
    (h : H2Datum (originCube d 0)) (F : CubeVectorH1Function (originCube d 0))
    (hu : IsScalarDirichletSolutionOn
      (scalarCoeffField (rescaledCutoffCoefficient M j k omega))
      (originCube d 0) u h.toH1 (fun _ => 0))
    (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
      ∫ x in openCubeSet (originCube d 0), (0 : ℝ) * psi.toFun x =
      -∫ x in openCubeSet (originCube d 0), vecDot (F.toField x) (psi.grad x)) :
    dirichletForcedSolutionEnergyNorm (originCube d (k : ℤ)) (aCutoffFamily M j omega)
      (cutoffPhysicalDirichletForcedCubeSolution M j k omega F hu hF) =
    vectorNormalizedL2On (cube d (k : ℤ))
      (fun x => Real.sqrt (aCutoff M j omega x) •
        (centeredCubeRawDilation (k : ℤ) u).grad x) := by
  rw [Section6Holder.vectorNormalizedL2On_sqrt_aCutoff_eq]
  change Real.sqrt (localizedCoeffEnergyValue _ _ _) = _
  rw [Section6HarmonicBoundary.localizedCoeffEnergyValue_aCutoffFamily_eq_volumeAverage]
  rfl

/-- A zero source has a divergence lift with a price controlled by the smooth datum. -/
theorem harmonicCell_zeroLift_price {d : ℕ} [NeZero d] {C : ℝ} (hC : 0 ≤ C)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hb : HarmonicCutoffDatumSizeBound f B) :
    ∃ F : CubeVectorH1Function (originCube d 0),
      (∀ psi : H10Function (openCubeSet (originCube d 0)),
        ∫ x in openCubeSet (originCube d 0), (0 : ℝ) * psi.toFun x =
        -∫ x in openCubeSet (originCube d 0), vecDot (F.toField x) (psi.grad x)) ∧
      sourceDirichletEnergyDatumPrice C ⟨1/16, by norm_num⟩ F
        (cutoffHarmonicCellH2Datum f hf hc) ≤
      sourceDirichletEnergyConstant d C ⟨1/16, by norm_num⟩ *
        (1 + (d : ℝ) + (d : ℝ)^2) * B := by
  have hzero : MemLp (fun _ : Vec d => (0 : ℝ)) 2
      (volume.restrict (openCubeSet (originCube d 0))) := MemLp.zero
  obtain ⟨F, hF, hprice⟩ := exists_unitDivergenceLift_with_sourceEnergyPrice d hC
    ⟨1/16, by norm_num⟩ (cutoffHarmonicCellH2Datum f hf hc) (fun _ => 0) hzero
  refine ⟨F, hF, ?_⟩
  have hz : ‖toScalarL2 hzero‖ = (0 : ℝ) := by
    simp [toScalarL2]
  rw [hz, zero_add] at hprice
  have hnorm := cutoffHarmonicCellH2Datum_norm_le f hf hc hB hb
  have hreal : (cutoffHarmonicCellH2Datum f hf hc).norm.toReal ≤
      (1 + (d : ℝ) + (d : ℝ)^2) * B :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hnorm
  exact hprice.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hreal (sourceDirichletEnergyConstant_nonneg d hC _))

end SubdiffusiveProcess.Static
