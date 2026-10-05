module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DirichletSpectralReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum

@[expose] public section

/-!
# Uniform smooth-dual unit-cube `L²` readout

For fractional orders `s ≤ 1/4`, the unnormalized `L²` size of a zero-trace
function on the unit cube is bounded by a dimension-only multiple of the
library smooth negative dual `cubeEuclideanNegativeWspSmoothDualENorm` of its
gradient.  The divergence-lift test field is measured once, at the fixed order
`1/4`; the completed full norm at every smaller order is controlled by the one
at `1/4` through the pointwise kernel comparison
`r^{-(s+d/2)} ≤ (d+1)^{1/4} r^{-(1/4+d/2)}` for `r ≤ d`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal NNReal

noncomputable section

namespace UniformSmoothReadout

/-- The fixed reference fractional order `1/4`. -/
def quarterOrder : FractionalOrder := ⟨1 / 4, by norm_num, by norm_num⟩

@[simp] theorem quarterOrder_val : quarterOrder.1 = 1 / 4 := rfl

/-- Two points of the half-open unit cube are at Euclidean distance at most
`d`. -/
theorem euclideanDist_le_of_mem_unitCube {d : ℕ} {x y : Vec d}
    (hx : x ∈ cubeSet (originCube d 0)) (hy : y ∈ cubeSet (originCube d 0)) :
    euclideanDist x y ≤ (d : ℝ) := by
  simp only [cubeSet, Set.mem_ofPred_eq] at hx hy
  have hdist : dist x y ≤ 1 := by
    refine (dist_pi_le_iff zero_le_one).2 fun i => ?_
    have hxi := hx i
    have hyi := hy i
    have hidx : ((originCube d 0).index i : ℝ) = 0 := by simp [originCube]
    simp only [hidx, cubeScaleFactor_originCube, zpow_zero, mul_one] at hxi hyi
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]
  calc
    euclideanDist x y ≤ (d : ℝ) * dist x y := euclideanDist_le_dimension_mul_dist x y
    _ ≤ (d : ℝ) * 1 := mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg d)
    _ = d := mul_one _

/-- Pointwise comparison of Gagliardo kernel weights of two orders on a set
of diameter at most `D ≥ 1`. -/
theorem rpow_neg_le_of_order_le {r D a b e k : ℝ} (hr : 0 ≤ r) (hrD : r ≤ D)
    (hD : 1 ≤ D) (ha : 0 < a) (hab : a ≤ b) (hbe : b ≤ e) (hk : 0 ≤ k) :
    r ^ (-(a + k)) ≤ D ^ e * r ^ (-(b + k)) := by
  rcases hr.eq_or_lt with hr0 | hrpos
  · subst hr0
    rw [Real.zero_rpow (by linarith)]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg le_rfl _)
  · have hsplit : r ^ (-(a + k)) = r ^ (b - a) * r ^ (-(b + k)) := by
      rw [← Real.rpow_add hrpos]
      congr 1
      ring
    rw [hsplit]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr _)
    calc
      r ^ (b - a) ≤ D ^ (b - a) := Real.rpow_le_rpow hr hrD (by linarith)
      _ ≤ D ^ e := Real.rpow_le_rpow_of_exponent_le hD (by linarith)

/-- Almost every pair for the Gagliardo cube measure has both points in the
cube. -/
theorem ae_mem_cubeSet_prod {d : ℕ} (Q : TriadicCube d) :
    ∀ᵐ z ∂Gagliardo.gagliardoCubeMeasure Q,
      z.1 ∈ cubeSet Q ∧ z.2 ∈ cubeSet Q := by
  have hs : MeasurableSet (cubeSet Q ×ˢ cubeSet Q) :=
    (measurableSet_cubeSet Q).prod (measurableSet_cubeSet Q)
  have h1 : ∀ᵐ x ∂normalizedCubeMeasure Q, x ∈ cubeSet Q := by
    unfold normalizedCubeMeasure cubeMeasure
    exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_cubeSet Q)) _
  have h2 : ∀ᵐ y ∂cubeMeasure Q, y ∈ cubeSet Q := by
    unfold cubeMeasure
    exact ae_restrict_mem (measurableSet_cubeSet Q)
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have hprod : ∀ᵐ z ∂Gagliardo.gagliardoCubeMeasure Q,
      z ∈ cubeSet Q ×ˢ cubeSet Q := by
    rw [Gagliardo.gagliardoCubeMeasure, Measure.ae_prod_mem_iff_ae_ae_mem hs]
    filter_upwards [h1] with x hx
    filter_upwards [h2] with y hy
    exact ⟨hx, hy⟩
  filter_upwards [hprod] with z hz
  exact hz

/-- Literal pre-guard full fractional norm. -/
def rawCubeEuclideanWspFullENorm {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d) : ℝ≥0∞ :=
  (cubeEuclideanWspScalePowerWeight Q s p *
      (SubdiffusiveProcess.RawLp.eLpNorm (fun x => euclideanNorm (F x)) p.exponent
        (cubeBoundedMeasurableDomain Q).normalizedVolume) ^ p.exponent.toReal +
    (rawCubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal) ^ p.exponent.toReal⁻¹

theorem rawCubeEuclideanWspFullENorm_eq_guarded {d : ℕ} {Q : TriadicCube d}
    (s : FractionalOrder) (p : FiniteLpExponent) {F : Vec d → Vec d}
    (hf : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent (normalizedCubeMeasure Q)) :
    rawCubeEuclideanWspFullENorm Q s p F = cubeEuclideanWspFullENorm Q s p F := by
  have hnorm : AEStronglyMeasurable (fun x => euclideanNorm (F x))
      (cubeBoundedMeasurableDomain Q).normalizedVolume := by
    simpa only [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      euclideanNorm_eq_norm_ofVec] using! hf.aestronglyMeasurable.norm
  simp only [rawCubeEuclideanWspFullENorm, cubeEuclideanWspFullENorm,
    rawCubeEuclideanWspESeminorm, cubeEuclideanWspESeminorm,
    BoundedMeasurableDomain.normalizedEuclideanLpENorm, BoundedMeasurableDomain.normalizedLpENorm,
    SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hnorm,
    SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (aestronglyMeasurable_cubeEuclideanWspKernel_of_memLp hf)]

/-- On the unit cube, the Euclidean Gagliardo seminorm at a smaller order is
bounded by a dimension-only multiple of the seminorm at a larger order
`t ≤ 1`, with the factor `(d+1)^t` independent of the smaller order. -/
theorem cubeEuclideanWspESeminorm_unitCube_le_of_order_le {d : ℕ}
    {s t : FractionalOrder} (hst : s.1 ≤ t.1) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    rawCubeEuclideanWspESeminorm (originCube d 0) s p F ≤
      ENNReal.ofReal (((d : ℝ) + 1) ^ t.1) *
        rawCubeEuclideanWspESeminorm (originCube d 0) t p F := by
  unfold rawCubeEuclideanWspESeminorm
  simp only [SubdiffusiveProcess.RawLp.eLpNorm, ite_eq_right (ne_of_gt (lt_trans zero_lt_one p.one_lt)), ite_eq_right p.lt_top.ne]
  let c : ℝ≥0 := ⟨((d : ℝ) + 1) ^ t.1, Real.rpow_nonneg (by positivity) _⟩
  rw [show ENNReal.ofReal (((d : ℝ) + 1) ^ t.1) = (c : ℝ≥0∞) from
    by change ENNReal.ofReal (c : ℝ) = (c : ℝ≥0∞); exact ENNReal.ofReal_coe_nnreal]
  change eLpNorm' (cubeEuclideanWspKernel s p F) p.exponent.toReal
    (Gagliardo.gagliardoCubeMeasure (originCube d 0)) ≤ c •
    eLpNorm' (cubeEuclideanWspKernel t p F) p.exponent.toReal
      (Gagliardo.gagliardoCubeMeasure (originCube d 0))
  apply eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul _ (ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne)
  apply Filter.Eventually.mono (ae_mem_cubeSet_prod (originCube d 0))
  intro z hz
  change ‖cubeEuclideanWspKernel s p F z‖ ≤ ((d : ℝ) + 1) ^ t.1 * ‖cubeEuclideanWspKernel t p F z‖
  rw [norm_cubeEuclideanWspKernel, norm_cubeEuclideanWspKernel, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (euclideanNorm_nonneg _)
  have hdist := euclideanDist_le_of_mem_unitCube hz.1 hz.2
  exact rpow_neg_le_of_order_le (euclideanDist_nonneg _ _) (by linarith)
    (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) s.2.1 hst le_rfl
    (div_nonneg (Nat.cast_nonneg d) ENNReal.toReal_nonneg)

/-- The library scale weight is `1` on the unit cube. -/
theorem cubeEuclideanWspScalePowerWeight_unitCube {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) :
    cubeEuclideanWspScalePowerWeight (originCube d 0) s p = 1 := by
  unfold cubeEuclideanWspScalePowerWeight
  simp only [cubeScaleFactor_originCube, zpow_zero, ENNReal.ofReal_one,
    ENNReal.one_rpow]

/-- On the unit cube, the library's completed full `W^{s,p}` norm at a
smaller order is bounded by `(d+1)^t` times the full norm at order `t`. -/
theorem cubeEuclideanWspFullENorm_unitCube_le_of_order_le {d : ℕ}
    {s t : FractionalOrder} (hst : s.1 ≤ t.1) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    rawCubeEuclideanWspFullENorm (originCube d 0) s p F ≤
      ENNReal.ofReal (((d : ℝ) + 1) ^ t.1) *
        rawCubeEuclideanWspFullENorm (originCube d 0) t p F := by
  have hS := cubeEuclideanWspESeminorm_unitCube_le_of_order_le hst p F
  unfold rawCubeEuclideanWspFullENorm
  rw [cubeEuclideanWspScalePowerWeight_unitCube, cubeEuclideanWspScalePowerWeight_unitCube,
    one_mul]
  set A : ℝ≥0∞ := ENNReal.ofReal (((d : ℝ) + 1) ^ t.1) with hAdef
  set q : ℝ := p.exponent.toReal with hqdef
  set L := SubdiffusiveProcess.RawLp.eLpNorm (fun x => euclideanNorm (F x)) p.exponent
    (cubeBoundedMeasurableDomain (originCube d 0)).normalizedVolume
  have hq : 0 < q := ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hA : 1 ≤ A := by
    rw [hAdef, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (Real.one_le_rpow (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) t.2.1.le)
  have hAq : 1 ≤ A ^ q := ENNReal.one_le_rpow hA hq
  calc
    (L ^ q + rawCubeEuclideanWspESeminorm (originCube d 0) s p F ^ q) ^ q⁻¹ ≤
        (A ^ q * L ^ q + A ^ q * rawCubeEuclideanWspESeminorm (originCube d 0) t p F ^ q) ^
          q⁻¹ := by
      apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr hq.le)
      apply add_le_add
      · exact le_mul_of_one_le_left' hAq
      · rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
        exact ENNReal.rpow_le_rpow hS hq.le
    _ = (A ^ q) ^ q⁻¹ *
        (L ^ q + rawCubeEuclideanWspESeminorm (originCube d 0) t p F ^ q) ^ q⁻¹ := by
      rw [← mul_add, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hq.le)]
    _ = A * (L ^ q + rawCubeEuclideanWspESeminorm (originCube d 0) t p F ^ q) ^ q⁻¹ := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hq.ne', ENNReal.rpow_one]

/-! ### The uniform smooth-dual readout -/

/-- The dimension-only coefficient of the uniform smooth-dual readout: the
order-comparison factor `(d+1)^{1/4}`, the order-`1/4` divergence-lift
conversion factor, and the divergence-lift constant. -/
noncomputable def uniformSmoothDualReadoutConstant (d : ℕ) [NeZero d] : ℝ≥0∞ :=
  ENNReal.ofReal (((d : ℝ) + 1) ^ (1 / 4 : ℝ)) *
    spectralPositiveReadoutConstant quarterOrder d *
      ENNReal.ofReal (unitDivergenceLiftConstant d)

theorem uniformSmoothDualReadoutConstant_lt_top (d : ℕ) [NeZero d] :
    uniformSmoothDualReadoutConstant d < ∞ := by
  unfold uniformSmoothDualReadoutConstant
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (spectralPositiveReadoutConstant_lt_top quarterOrder d))
    ENNReal.ofReal_lt_top

/-- The divergence lift's completed full norm at any order `s ≤ 1/4` is
bounded by an order-independent multiple of its `H¹` budget. -/
theorem cubeEuclideanWspFullENorm_unitCubeVectorH1_le_uniform {d : ℕ}
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4)
    (V : CubeVectorH1Function (originCube d 0)) :
    cubeEuclideanWspFullENorm (originCube d 0) s FiniteLpExponent.two V.toField ≤
      ENNReal.ofReal (((d : ℝ) + 1) ^ (1 / 4 : ℝ)) *
        (spectralPositiveReadoutConstant quarterOrder d *
          unitCubeVectorH1ENormBudget V) := by
  have hst : s.1 ≤ quarterOrder.1 := by simpa only [quarterOrder_val] using! hs
  calc
    cubeEuclideanWspFullENorm (originCube d 0) s FiniteLpExponent.two V.toField ≤
        ENNReal.ofReal (((d : ℝ) + 1) ^ quarterOrder.1) *
          cubeEuclideanWspFullENorm (originCube d 0) quarterOrder
            FiniteLpExponent.two V.toField :=
      by
        have hf : MemLp (fun x => HilbertVec.ofVec (V.toField x))
            FiniteLpExponent.two.exponent (normalizedCubeMeasure (originCube d 0)) := by
          simpa only [FiniteLpExponent.two_exponent, unitEuclideanL2FieldOfCubeVectorH1_apply,
            ← normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume] using!
            (unitEuclideanL2FieldOfCubeVectorH1 V).euclideanMemL2
        simpa only [rawCubeEuclideanWspFullENorm_eq_guarded s FiniteLpExponent.two hf,
          rawCubeEuclideanWspFullENorm_eq_guarded quarterOrder FiniteLpExponent.two hf] using!
          cubeEuclideanWspFullENorm_unitCube_le_of_order_le hst FiniteLpExponent.two V.toField
    _ ≤ ENNReal.ofReal (((d : ℝ) + 1) ^ (1 / 4 : ℝ)) *
        (spectralPositiveReadoutConstant quarterOrder d *
          unitCubeVectorH1ENormBudget V) := by
      rw [quarterOrder_val]
      gcongr
      exact cubeEuclideanWspFullENorm_unitCubeVectorH1_le quarterOrder V

/-- Uniform smooth-dual unit-cube readout: for every fractional order
`s ≤ 1/4`, the unnormalized `L²` size of a zero-trace function is bounded by
the dimension-only constant `uniformSmoothDualReadoutConstant d` times the
library smooth negative fractional dual of its gradient. -/
theorem l2Size_le_uniformSmoothDualReadoutConstant_mul_smoothDual
    {d : ℕ} [NeZero d] (s : FractionalOrder) (hs : s.1 ≤ 1 / 4)
    (w : H10Function (openCubeSet (originCube d 0))) :
    l2Size (originCube d 0) w.toH1Function.toFun ≤
      uniformSmoothDualReadoutConstant d *
        cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s
          FiniteLpExponent.two (unitH10GradientEuclideanL2Field w) := by
  let L : ℝ≥0∞ := l2Size (originCube d 0) w.toH1Function.toFun
  let D : ℝ≥0∞ := cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s
    FiniteLpExponent.two (unitH10GradientEuclideanL2Field w)
  let C : ℝ≥0∞ := uniformSmoothDualReadoutConstant d
  have hlift : ∃ V : CubeVectorH1Function (originCube d 0),
      (∀ phi : H10Function (openCubeSet (originCube d 0)),
        ∫ x in openCubeSet (originCube d 0),
            w.toH1Function.toFun x * phi.toH1Function.toFun x ∂volume =
          -∫ x in openCubeSet (originCube d 0),
            vecDot (V.toField x) (phi.toH1Function.grad x) ∂volume) ∧
      unitCubeVectorH1ENormBudget V ≤
        ENNReal.ofReal (unitDivergenceLiftConstant d *
          ‖toScalarL2 w.toH1Function.memL2‖) :=
    (exists_unitCubeVectorH1Function_divergence_lift_h1ENormBudget d).choose_spec.2
      w.toH1Function.toFun w.toH1Function.memL2
  obtain ⟨V, hV, hbudget⟩ := hlift
  let G := unitCubeVectorH1WspL2Field s V
  let Gc : CubeEuclideanWspL2Field (originCube d 0) s
      FiniteLpExponent.two.conjugate :=
    { toField := G.toField
      euclideanMemLp := by simpa using! G.euclideanMemLp
      euclideanMemWsp := by simpa using! G.euclideanMemWsp
      euclideanMemL2 := G.euclideanMemL2 }
  have hpairBound :
      ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing
          (unitH10GradientEuclideanL2Field w) G| ≤
        D * cubeEuclideanWspFullENorm (originCube d 0) s
          FiniteLpExponent.two G.toField := by
    have hpEq : cubeEuclideanNormalizedFieldPairing
        (unitH10GradientEuclideanL2Field w) G =
        cubeEuclideanNormalizedFieldPairing
          (unitH10GradientEuclideanL2Field w) Gc := rfl
    rw [hpEq]
    simpa only [Gc, FiniteLpExponent.conjugate_two, D] using!
      (ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le
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
          simpa only [pow_two] using! hw
        linarith
  have hIntegralNonneg : 0 ≤ ∫ x in openCubeSet (originCube d 0),
      w.toH1Function.toFun x ^ 2 ∂volume :=
    integral_nonneg (fun x ↦ sq_nonneg _)
  have hLtop : L ≠ ∞ := w.toH1Function.memL2.eLpNorm_ne_top
  have hLnorm : L = ENNReal.ofReal ‖toScalarL2 w.toH1Function.memL2‖ := by
    unfold L l2Size
    exact (MeasureTheory.Lp.enorm_toLp w.toH1Function.memL2).symm.trans
      (ofReal_norm (toScalarL2 w.toH1Function.memL2)).symm
  have hLsq : L ^ 2 = ENNReal.ofReal
      (∫ x in openCubeSet (originCube d 0),
        w.toH1Function.toFun x ^ 2 ∂volume) := by
    have hreal := toReal_eLpNorm_two_sq_eq_integral_sq w.toH1Function.memL2
    rw [← hreal]
    unfold L l2Size at hLtop ⊢
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hLtop]
  have hpairL : L ^ 2 ≤ D *
      cubeEuclideanWspFullENorm (originCube d 0) s FiniteLpExponent.two G.toField := by
    rw [hLsq, ← abs_of_nonneg hIntegralNonneg, ← abs_neg, ← hpairReal]
    exact hpairBound
  rw [unitCubeVectorH1WspL2Field_toField] at hpairL
  have hfull := cubeEuclideanWspFullENorm_unitCubeVectorH1_le_uniform s hs V
  have hmain : L * L ≤ C * D * L := by
    calc
      L * L ≤ D * cubeEuclideanWspFullENorm
          (originCube d 0) s FiniteLpExponent.two V.toField := by
        simpa only [pow_two] using! hpairL
      _ ≤ D * (ENNReal.ofReal (((d : ℝ) + 1) ^ (1 / 4 : ℝ)) *
          (spectralPositiveReadoutConstant quarterOrder d *
            unitCubeVectorH1ENormBudget V)) := by
        gcongr
      _ ≤ D * (ENNReal.ofReal (((d : ℝ) + 1) ^ (1 / 4 : ℝ)) *
          (spectralPositiveReadoutConstant quarterOrder d *
            ENNReal.ofReal (unitDivergenceLiftConstant d *
              ‖toScalarL2 w.toH1Function.memL2‖))) := by
        gcongr
      _ = C * D * L := by
        rw [ENNReal.ofReal_mul (unitDivergenceLiftConstant_nonneg d), ← hLnorm]
        simp only [C, uniformSmoothDualReadoutConstant]
        ring
  by_cases hL0 : L = 0
  · change L ≤ C * D
    rw [hL0]
    exact zero_le
  · change L ≤ C * D
    calc
      L = L⁻¹ * (L * L) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hL0 hLtop, one_mul]
      _ ≤ L⁻¹ * (C * D * L) := by gcongr
      _ = C * D := by
        calc
          L⁻¹ * (C * D * L) = (C * D) * (L⁻¹ * L) := by ring
          _ = C * D := by rw [ENNReal.inv_mul_cancel hL0 hLtop, mul_one]

/-- Witness-first form: one finite dimension-only constant, chosen before
the order and the function, controls every order `s ≤ 1/4`. -/
theorem exists_uniform_smoothDual_l2Size_readout (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ s : FractionalOrder, s.1 ≤ 1 / 4 →
        ∀ w : H10Function (openCubeSet (originCube d 0)),
          l2Size (originCube d 0) w.toH1Function.toFun ≤
            C * cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s
              FiniteLpExponent.two (unitH10GradientEuclideanL2Field w) :=
  ⟨uniformSmoothDualReadoutConstant d, uniformSmoothDualReadoutConstant_lt_top d,
    fun s hs w => l2Size_le_uniformSmoothDualReadoutConstant_mul_smoothDual s hs w⟩

/-- Real positive witness-first form. -/
theorem exists_pos_real_uniform_smoothDual_l2Size_readout (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : FractionalOrder, s.1 ≤ 1 / 4 →
        ∀ w : H10Function (openCubeSet (originCube d 0)),
          l2Size (originCube d 0) w.toH1Function.toFun ≤
            ENNReal.ofReal C *
              cubeEuclideanNegativeWspSmoothDualENorm (originCube d 0) s
                FiniteLpExponent.two (unitH10GradientEuclideanL2Field w) := by
  refine ⟨(uniformSmoothDualReadoutConstant d).toReal + 1, by positivity, ?_⟩
  intro s hs w
  refine (l2Size_le_uniformSmoothDualReadoutConstant_mul_smoothDual s hs w).trans ?_
  gcongr
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
    ENNReal.ofReal_toReal (uniformSmoothDualReadoutConstant_lt_top d).ne]
  exact le_self_add

end UniformSmoothReadout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
