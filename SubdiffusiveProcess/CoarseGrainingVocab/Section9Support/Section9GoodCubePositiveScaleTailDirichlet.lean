module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePositiveScaleTailParameters
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeResponseOrders
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeDirichletThreshold
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.DiscountBounds
@[expose] public section

/-!
# Actual positive-scale Dirichlet comparison

The response moment supplies the finite square-error moment required by the
unit-cube Dirichlet theorem. One small actual response test then pays both
error orders. Stationarity transports the entire almost-everywhere statement,
including its uniform quantification over forcing, boundary data, and solutions.
-/

set_option autoImplicit false
open Homogenization Homogenization.Book Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Section9
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
/-- Both Dirichlet response orders are controlled at the actual outer cutoff. -/
theorem goodCube_actual_response_orders_le_observable
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ) (hmn : m ≤ n)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) (1 / 4) .infinity (.finite 1)
        (aCutoffFamily M n omega) (ahom M n) ≤
      ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) *
        ellipticityMomentObservable M n (m : ℤ) (1 / 8) omega ∧
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) (1 / 8) .infinity (.finite 2)
        (aCutoffFamily M n omega) (ahom M n) ≤
      ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) *
        ellipticityMomentObservable M n (m : ℤ) (1 / 8) omega := by
  have hbase := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.sourceCell_paperError_le_ellipticityMomentObservable
    M n 0 m hmn (1 / 8) omega
  rw [Nat.add_zero, tailCoefficientCubeAverage_self] at hbase
  have horders := goodCube_response_orders_le_one (originCube d (m : ℤ)) (m : ℤ)
    (aCutoffFamily M n omega) (ahom M n) .infinity
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)
  exact ⟨horders.1.trans (mul_le_mul' le_rfl hbase), horders.2.trans (mul_le_mul' le_rfl hbase)⟩

/-- Actual response moments give a finite positive-order square-error moment. -/
theorem exists_goodCube_positiveScale_qtwo_moment (d J : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ c →
      ∀ n m : ℕ, m ≤ n → n - m ≤ J →
        ∃ p B : ℝ, 0 < p ∧
          paperENNRealLpNorm M.P.toMeasure p
            (fun omega => paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ)
              (1 / 8) .infinity (.finite 2) (aCutoffFamily M n omega) (ahom M n)) ≤
            ENNReal.ofReal B := by
  obtain ⟨a, delta0, -, hd0, hpar⟩ :=
    exists_goodCube_positiveScale_moment_parameters d J 1 1 (by norm_num) (by norm_num)
  refine ⟨delta0, hd0, fun M hM n m hmn hnm => ?_⟩
  have hp2 : 2 ≤ smallDisorderExponent a M.delta := (hpar M hM).1
  obtain ⟨-, hz⟩ := (hpar M hM).2.2 n m hmn hnm (0 : Vec d)
  simp only [SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.translatePotentialSample_zero] at hz
  have hD : 0 < Ch02.geometricDiscount (1 / 8) 1 :=
    Ch02.book_geometricDiscount_pos (by norm_num : 0 < (1 / 8 : ℝ) * 1)
  have hDpos : 0 < (Ch02.geometricDiscount (1 / 8) 1)⁻¹ := inv_pos.mpr hD
  have hpt : ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) (1 / 8) .infinity (.finite 2)
        (aCutoffFamily M n omega) (ahom M n) ≤
        ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) *
          ellipticityMomentObservable M n (m : ℤ) (1 / 8) omega :=
    fun omega => (goodCube_actual_response_orders_le_observable M n m hmn omega).2
  refine ⟨smallDisorderExponent a M.delta, (Ch02.geometricDiscount (1 / 8) 1)⁻¹,
    by linarith, ?_⟩
  have hae : ∀ᵐ omega ∂M.P.toMeasure,
      paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) (1 / 8) .infinity (.finite 2)
        (aCutoffFamily M n omega) (ahom M n) ≤
        ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) *
          ellipticityMomentObservable M n (m : ℤ) (1 / 8) omega :=
    Filter.Eventually.of_forall hpt
  calc paperENNRealLpNorm M.P.toMeasure (smallDisorderExponent a M.delta)
        (fun omega => paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) (1 / 8)
          .infinity (.finite 2) (aCutoffFamily M n omega) (ahom M n)) ≤
      paperENNRealLpNorm M.P.toMeasure (smallDisorderExponent a M.delta)
        (fun omega => ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) *
          ellipticityMomentObservable M n (m : ℤ) (1 / 8) omega) :=
        paperENNRealLpNorm_mono_ae M.P.toMeasure (le_of_lt (by linarith)) hae
    _ = ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) *
          paperENNRealLpNorm M.P.toMeasure (smallDisorderExponent a M.delta)
            (ellipticityMomentObservable M n (m : ℤ) (1 / 8)) :=
        paperENNRealLpNorm_const_mul_eq M.P.toMeasure (by linarith) _
          (ellipticityMomentObservable M n (m : ℤ) (1 / 8))
          (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.measurable_ellipticityMomentObservable M n (m : ℤ) (1 / 8))
    _ ≤ ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) * ENNReal.ofReal (1 / 4) :=
        mul_le_mul' le_rfl hz
    _ ≤ ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) := by
        have h1 : ENNReal.ofReal ((1 / 4 : ℝ)) ≤ 1 :=
          ENNReal.ofReal_le_one.mpr (by norm_num : (1 / 4 : ℝ) ≤ 1)
        calc ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) * ENNReal.ofReal (1 / 4)
            ≤ ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) * 1 :=
              mul_le_mul' le_rfl h1
          _ = ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) := by ring

/-- A dimensional response tolerance gives the translated unit-cube comparison,
with no residual moment assumption and with the cutoff fixed at `n`. -/
theorem exists_goodCube_positiveScale_dirichlet_comparison
    (d J : ℕ) [NeZero d] (hd : 2 ≤ d) (eps : ℝ) (heps : 0 < eps) :
    ∃ c e : ℝ, 0 < c ∧ 0 < e ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ c →
      ∀ n m : ℕ, m ≤ n → n - m ≤ J → ∀ z : Vec d,
        ∀ᵐ omega ∂M.P.toMeasure,
          ellipticityMomentObservable M n (m : ℤ) (1 / 8)
              (translatePotentialSample z omega) ≤ ENNReal.ofReal e →
          ∀ (f : Vec d → ℝ)
            (_hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))))
            (h : H2Datum (originCube d 0))
            (u v : H1Function (openCubeSet (originCube d 0))),
            IsScalarDirichletSolutionOn
              (scalarCoeffField (rescaledCutoffCoefficient M n m (translatePotentialSample z omega)))
              (originCube d 0) u h.toH1 f →
            IsScalarDirichletSolutionOn (fun _ => (1 : Mat d))
              (originCube d 0) v h.toH1 f →
            l2Size (originCube d 0) (fun x => u.toFun x - v.toFun x) ≤
              ENNReal.ofReal eps * (l2Size (originCube d 0) f + h.norm) := by
  obtain ⟨zeta, hzeta_pos, hthresh⟩ :=
    exists_goodCube_dirichlet_comparison_threshold d hd eps heps
  have hg : 0 < Ch02.geometricDiscount (1 / 8) 1 :=
    Ch02.book_geometricDiscount_pos (by norm_num : 0 < (1 / 8 : ℝ) * 1)
  have hg0 : Ch02.geometricDiscount (1 / 8) 1 ≠ 0 := ne_of_gt hg
  obtain ⟨c, hcpos, hcM⟩ := exists_goodCube_positiveScale_qtwo_moment d J
  refine ⟨c, zeta * Ch02.geometricDiscount (1 / 8) 1, hcpos, mul_pos hzeta_pos hg, ?_⟩
  intro M hM n m hmn hnm z
  obtain ⟨p, B, hp, hB⟩ := hcM M hM n m hmn hnm
  have hAE := (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.measurePreserving_translatePotentialSample M z).quasiMeasurePreserving.ae
    (hthresh M n m hp hB)
  filter_upwards [hAE] with omega homega
  intro hobs f _hf h u v hu hv
  obtain ⟨k1, k2⟩ := goodCube_actual_response_orders_le_observable M n m hmn (translatePotentialSample z omega)
  have hζ : ENNReal.ofReal ((Ch02.geometricDiscount (1 / 8) 1)⁻¹) *
      ENNReal.ofReal (zeta * Ch02.geometricDiscount (1 / 8) 1) = ENNReal.ofReal zeta := by
    rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hg))]
    congr 1
    field_simp [hg0]
  exact homega
    ((k1.trans (mul_le_mul' le_rfl hobs)).trans (le_of_eq hζ))
    ((k2.trans (mul_le_mul' le_rfl hobs)).trans (le_of_eq hζ)) f _hf h u v hu hv


end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
