import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.NegativeNormReadout
import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.ContinuousKRegularity

/-!
# Unit-cube spectral `L²` readout

The Dirichlet inverse Laplacian supplies an `H¹` vector divergence lift of a
zero-trace scalar function.  Pairing this lift with the function's gradient
identifies the squared `L²` norm, after which the manuscript negative dual
controls the pairing.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- Package the unit-cube gradient as the Euclidean `L²` field consumed by
the manuscript dual. -/
noncomputable def unitH10GradientEuclideanL2Field {d : ℕ}
    (w : H10Function (openCubeSet (originCube d 0))) :
    CubeEuclideanLpField (originCube d 0) FiniteLpExponent.two where
  toField := w.toH1Function.grad
  euclideanMemLp := by
    rw [memLp_piLp_iff]
    intro i
    simpa only [FiniteLpExponent.two_exponent, HilbertVec.ofVec,
      PiLp.toLp_apply] using
      w.toH1Function.grad_memL2_normalizedCubeMeasure (Q := originCube d 0) i

@[simp] theorem unitH10GradientEuclideanL2Field_toField {d : ℕ}
    (w : H10Function (openCubeSet (originCube d 0))) :
    (unitH10GradientEuclideanL2Field w).toField = w.toH1Function.grad :=
  rfl

/-- A unit-cube vector `H¹` field, regarded as a completed fractional
`W^{s,2}` test field with its redundant `L²` certificate retained. -/
noncomputable def unitCubeVectorH1WspL2Field {d : ℕ}
    (s : FractionalOrder) (V : CubeVectorH1Function (originCube d 0)) :
    CubeEuclideanWspL2Field (originCube d 0) s FiniteLpExponent.two := by
  let G := centeredCubeScaledVectorDilationWspField (1 : ℝ) 0 s V
  exact
    { toField := G.toField
      euclideanMemLp := G.euclideanMemLp
      euclideanMemWsp := G.euclideanMemWsp
      euclideanMemL2 := by
        simpa only [FiniteLpExponent.two_exponent] using G.euclideanMemLp }

@[simp] theorem unitCubeVectorH1WspL2Field_toField {d : ℕ}
    (s : FractionalOrder) (V : CubeVectorH1Function (originCube d 0)) :
    (unitCubeVectorH1WspL2Field s V).toField = V.toField := by
  funext x
  change (centeredCubeScaledVectorDilation (1 : ℝ) 0 V).toField x = V.toField x
  rw [centeredCubeScaledVectorDilation_toField]
  simp

/-- Finite factor converting the divergence lift's `H¹` budget to the
power-form completed fractional norm used by the field-pairing theorem. -/
noncomputable def spectralPositiveReadoutConstant
    (s : FractionalOrder) (d : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal s.1) ^ (-(FiniteLpExponent.two.exponent.toReal)⁻¹) *
    (scaledVectorDatumFractionalConstant s d + 1)

theorem spectralPositiveReadoutConstant_lt_top
    (s : FractionalOrder) (d : ℕ) :
    spectralPositiveReadoutConstant s d < ∞ := by
  unfold spectralPositiveReadoutConstant
  exact ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_ne_zero_iff.mpr s.2.1) ENNReal.ofReal_ne_top))
    (ENNReal.add_lt_top.mpr
      ⟨scaledVectorDatumFractionalConstant_lt_top s d, ENNReal.one_lt_top⟩)

theorem cubeEuclideanWspFullENorm_unitCubeVectorH1_le
    {d : ℕ} (s : FractionalOrder)
    (V : CubeVectorH1Function (originCube d 0)) :
    cubeEuclideanWspFullENorm (originCube d 0) s FiniteLpExponent.two V.toField ≤
      spectralPositiveReadoutConstant s d * unitCubeVectorH1ENormBudget V := by
  have hsemi : paperFractionalSeminorm (originCube d 0) s
      FiniteLpExponent.two V.toField ≤
      scaledVectorDatumFractionalConstant s d * unitCubeVectorH1ENormBudget V := by
    have hfield :
        (centeredCubeScaledVectorDilation (1 : ℝ) 0 V).toField = V.toField := by
      funext x
      rw [centeredCubeScaledVectorDilation_toField]
      simp
    rw [← hfield]
    have h := paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_h1Budget
      (1 : ℝ) 0 s V
    simpa [scaledVectorDatumFractionalENormBound] using h
  have hL2 :
      (cubeBoundedMeasurableDomain (originCube d 0)).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) V.toField ≤ unitCubeVectorH1ENormBudget V := by
    unfold unitCubeVectorH1ENormBudget
    exact le_add_right le_rfl
  calc
    cubeEuclideanWspFullENorm (originCube d 0) s FiniteLpExponent.two V.toField ≤
      (ENNReal.ofReal s.1) ^ (-(FiniteLpExponent.two.exponent.toReal)⁻¹) *
        paperFractionalFullNorm (originCube d 0) s FiniteLpExponent.two V.toField :=
      cubeEuclideanWspFullENorm_le_paperFractionalFullNorm
        (originCube d 0) s FiniteLpExponent.two V.toField
    _ ≤ (ENNReal.ofReal s.1) ^ (-(FiniteLpExponent.two.exponent.toReal)⁻¹) *
        ((scaledVectorDatumFractionalConstant s d + 1) *
          unitCubeVectorH1ENormBudget V) := by
      apply mul_le_mul_right
      rw [paperFractionalFullNorm]
      simp only [cubeScaleFactor_originCube, zpow_zero, ENNReal.ofReal_one,
        ENNReal.one_rpow, one_mul]
      calc
        paperFractionalSeminorm (originCube d 0) s FiniteLpExponent.two V.toField +
            (cubeBoundedMeasurableDomain (originCube d 0)).normalizedEuclideanLpENorm
              (2 : ℝ≥0∞) V.toField ≤
          scaledVectorDatumFractionalConstant s d * unitCubeVectorH1ENormBudget V +
            unitCubeVectorH1ENormBudget V := add_le_add hsemi hL2
        _ = (scaledVectorDatumFractionalConstant s d + 1) *
            unitCubeVectorH1ENormBudget V := by ring
    _ = spectralPositiveReadoutConstant s d * unitCubeVectorH1ENormBudget V := by
      unfold spectralPositiveReadoutConstant
      ring

/-- The finite real constant selected by the landed unit-cube divergence
lift. -/
noncomputable def unitDivergenceLiftConstant (d : ℕ) [NeZero d] : ℝ :=
  (exists_unitCubeVectorH1Function_divergence_lift_h1ENormBudget d).choose

theorem unitDivergenceLiftConstant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ unitDivergenceLiftConstant d :=
  (exists_unitCubeVectorH1Function_divergence_lift_h1ENormBudget d).choose_spec.1

private theorem exists_unitDivergenceLift_with_budget
    (d : ℕ) [NeZero d]
    (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0)))) :
    ∃ V : CubeVectorH1Function (originCube d 0),
      (∀ phi : H10Function (openCubeSet (originCube d 0)),
        ∫ x in openCubeSet (originCube d 0),
            f x * phi.toH1Function.toFun x ∂volume =
          -∫ x in openCubeSet (originCube d 0),
            vecDot (V.toField x) (phi.toH1Function.grad x) ∂volume) ∧
      unitCubeVectorH1ENormBudget V ≤
        ENNReal.ofReal (unitDivergenceLiftConstant d * ‖toScalarL2 hf‖) :=
  (exists_unitCubeVectorH1Function_divergence_lift_h1ENormBudget d).choose_spec.2 f hf

/-- Finite dimension/order coefficient in the spectral `L²` readout. -/
noncomputable def dirichletSpectralReadoutConstant
    (s : FractionalOrder) (d : ℕ) [NeZero d] : ℝ≥0∞ :=
  2 * spectralPositiveReadoutConstant s d *
    ENNReal.ofReal (unitDivergenceLiftConstant d)

theorem dirichletSpectralReadoutConstant_lt_top
    (s : FractionalOrder) (d : ℕ) [NeZero d] :
    dirichletSpectralReadoutConstant s d < ∞ := by
  unfold dirichletSpectralReadoutConstant
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by norm_num) (spectralPositiveReadoutConstant_lt_top s d))
    ENNReal.ofReal_lt_top

/-- Spectral unit-cube readout: the unnormalized scalar `L²` size of a
zero-trace function is controlled by the manuscript negative fractional dual
of its gradient. -/
theorem l2Size_le_paperNegativeFractionalDual_gradient
    {d : ℕ} [NeZero d] (s : FractionalOrder)
    (w : H10Function (openCubeSet (originCube d 0))) :
    l2Size (originCube d 0) w.toH1Function.toFun ≤
      dirichletSpectralReadoutConstant s d *
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (unitH10GradientEuclideanL2Field w) := by
  let L : ℝ≥0∞ := l2Size (originCube d 0) w.toH1Function.toFun
  let D : ℝ≥0∞ := paperNegativeFractionalDual (originCube d 0) s
    FiniteLpExponent.two (unitH10GradientEuclideanL2Field w)
  obtain ⟨V, hV, hbudget⟩ :=
    exists_unitDivergenceLift_with_budget d w.toH1Function.toFun w.toH1Function.memL2
  let G := unitCubeVectorH1WspL2Field s V
  let Gc : CubeEuclideanWspL2Field (originCube d 0) s
      FiniteLpExponent.two.conjugate :=
    { toField := G.toField
      euclideanMemLp := by simpa using G.euclideanMemLp
      euclideanMemWsp := by simpa using G.euclideanMemWsp
      euclideanMemL2 := G.euclideanMemL2 }
  have hpairBound :
      ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing
          (unitH10GradientEuclideanL2Field w) G| ≤
        2 * D * cubeEuclideanWspFullENorm (originCube d 0) s
          FiniteLpExponent.two G.toField := by
    have hpEq : cubeEuclideanNormalizedFieldPairing
        (unitH10GradientEuclideanL2Field w) G =
        cubeEuclideanNormalizedFieldPairing
          (unitH10GradientEuclideanL2Field w) Gc := rfl
    rw [hpEq]
    simpa only [Gc, FiniteLpExponent.conjugate_two, D] using
      (ofReal_abs_normalizedFieldPairing_le_two_mul_paperNegativeFractionalDual
        (p := FiniteLpExponent.two) (unitH10GradientEuclideanL2Field w) Gc)
  have hpairReal : cubeEuclideanNormalizedFieldPairing
      (unitH10GradientEuclideanL2Field w) G =
      -(∫ x in openCubeSet (originCube d 0),
          w.toH1Function.toFun x ^ 2 ∂volume) := by
    have hw := hV w
    unfold cubeEuclideanNormalizedFieldPairing
    rw [normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
    calc
      (∫ x in openCubeSet (originCube d 0),
          vecDot ((unitH10GradientEuclideanL2Field w).toField x) (G.toField x)
            ∂volume) =
        ∫ x in openCubeSet (originCube d 0),
          vecDot (V.toField x) (w.toH1Function.grad x) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          rw [unitH10GradientEuclideanL2Field_toField,
            unitCubeVectorH1WspL2Field_toField]
          exact vecDot_comm _ _
      _ = -(∫ x in openCubeSet (originCube d 0),
          w.toH1Function.toFun x ^ 2 ∂volume) := by
        have hw' : (∫ x in openCubeSet (originCube d 0),
            w.toH1Function.toFun x ^ 2 ∂volume) =
            -(∫ x in openCubeSet (originCube d 0),
              vecDot (V.toField x) (w.toH1Function.grad x) ∂volume) := by
          simpa only [pow_two] using hw
        linarith
  have hIntegralNonneg : 0 ≤ ∫ x in openCubeSet (originCube d 0),
      w.toH1Function.toFun x ^ 2 ∂volume := by
    exact integral_nonneg (fun x ↦ sq_nonneg _)
  have hLtop : L ≠ ∞ := w.toH1Function.memL2.eLpNorm_ne_top
  have hLnorm : L = ENNReal.ofReal ‖toScalarL2 w.toH1Function.memL2‖ := by
    unfold L l2Size
    exact (MeasureTheory.Lp.enorm_toLp w.toH1Function.memL2).symm.trans
      (ofReal_norm_eq_enorm (toScalarL2 w.toH1Function.memL2)).symm
  have hLsq : L ^ 2 = ENNReal.ofReal
      (∫ x in openCubeSet (originCube d 0),
        w.toH1Function.toFun x ^ 2 ∂volume) := by
    have hreal := toReal_eLpNorm_two_sq_eq_integral_sq w.toH1Function.memL2
    rw [← hreal]
    unfold L l2Size at hLtop ⊢
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hLtop]
  have hpairL : L ^ 2 ≤ 2 * D *
      cubeEuclideanWspFullENorm (originCube d 0) s FiniteLpExponent.two G.toField := by
    rw [hLsq, ← abs_of_nonneg hIntegralNonneg, ← abs_neg, ← hpairReal]
    exact hpairBound
  have hfull := cubeEuclideanWspFullENorm_unitCubeVectorH1_le s V
  rw [unitCubeVectorH1WspL2Field_toField] at hpairL
  have hmain : L * L ≤ dirichletSpectralReadoutConstant s d * D * L := by
    calc
      L * L ≤ 2 * D * cubeEuclideanWspFullENorm
          (originCube d 0) s FiniteLpExponent.two V.toField := by
        simpa only [pow_two] using hpairL
      _ ≤ 2 * D * (spectralPositiveReadoutConstant s d *
          unitCubeVectorH1ENormBudget V) := by
        exact mul_le_mul_right hfull (2 * D)
      _ ≤ 2 * D * (spectralPositiveReadoutConstant s d *
          ENNReal.ofReal (unitDivergenceLiftConstant d *
            ‖toScalarL2 w.toH1Function.memL2‖)) := by
        exact mul_le_mul_right
          (mul_le_mul_right hbudget (spectralPositiveReadoutConstant s d)) (2 * D)
      _ = dirichletSpectralReadoutConstant s d * D * L := by
        rw [ENNReal.ofReal_mul (unitDivergenceLiftConstant_nonneg d), ← hLnorm]
        unfold dirichletSpectralReadoutConstant
        ring
  by_cases hL0 : L = 0
  · simp [L, hL0]
  · change L ≤ dirichletSpectralReadoutConstant s d * D
    calc
      L = L⁻¹ * (L * L) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hL0 hLtop, one_mul]
      _ ≤ L⁻¹ * (dirichletSpectralReadoutConstant s d * D * L) :=
        mul_le_mul_right hmain L⁻¹
      _ = dirichletSpectralReadoutConstant s d * D := by
        calc
          L⁻¹ * (dirichletSpectralReadoutConstant s d * D * L) =
              (dirichletSpectralReadoutConstant s d * D) * (L⁻¹ * L) := by ring
          _ = dirichletSpectralReadoutConstant s d * D := by
            rw [ENNReal.inv_mul_cancel hL0 hLtop, mul_one]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
