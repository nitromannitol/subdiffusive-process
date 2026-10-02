import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductComparisonPrice

/-!
# Theta-perturbed ladder: uniform product-energy prices

Once the product homogenization error is at most one, every ellipticity and
Caccioppoli factor in the two-scale comparison is dimension-only.  The error
itself remains visible only in the linear flat-comparator slot.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03

noncomputable section

/-- Uniform local ellipticity cap on the range `0 ≤ E ≤ 1`. -/
def productUniformEllipticityCap (d : ℕ) : ℝ := 4 * (d : ℝ)

/-- Uniform root-energy prefactor after replacing the local product error by
one. -/
def productUniformRootPrefactor (d : ℕ) [NeZero d] : ℝ :=
  (4 * max 1 (productCaccioppoliConstant d)) ^ (8 : ℕ) * 8 *
    ((productUniformEllipticityCap d) ^ 2) ^ (3 : ℕ)

/-- Square-root coefficient in the uniform weighted-energy price. -/
def productUniformEnergySqrtConstant (d : ℕ) [NeZero d] : ℝ :=
  Real.sqrt
    (productUniformRootPrefactor d * productUniformEllipticityCap d)

/-- Fixed weighted-energy coefficient after the root-price square root. -/
def productUniformWeightedConstant (d : ℕ) [NeZero d] : ℝ :=
  Section6Dirichlet.dirichletWeightedEnergyFactor
      productLowOrder.1 productMiddleOrder.1 *
    productUniformEnergySqrtConstant d

theorem productUniformEllipticityCap_nonneg (d : ℕ) :
    0 ≤ productUniformEllipticityCap d := by
  unfold productUniformEllipticityCap
  positivity

theorem productUniformRootPrefactor_nonneg (d : ℕ) [NeZero d] :
    0 ≤ productUniformRootPrefactor d := by
  unfold productUniformRootPrefactor
  positivity

theorem productLocalEllipticityCap_nonneg (d : ℕ) (E : ℝ) :
    0 ≤ productLocalEllipticityCap d E := by
  unfold productLocalEllipticityCap
  positivity

/-- The error-dependent ellipticity cap is uniformly dimension-only below
unit error. -/
theorem productLocalEllipticityCap_le_uniform {d : ℕ} {E : ℝ}
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    productLocalEllipticityCap d E ≤ productUniformEllipticityCap d := by
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hEsq : E ^ 2 ≤ 1 := by nlinarith
  unfold productLocalEllipticityCap productUniformEllipticityCap
  nlinarith

/-- The Caccioppoli prefactor is uniformly dimension-only below unit error. -/
theorem productRootEnergyPrefactor_le_uniform
    {d : ℕ} [NeZero d] {E : ℝ} (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    productRootEnergyPrefactor d (productCaccioppoliConstant d) E ≤
      productUniformRootPrefactor d := by
  have hB := productLocalEllipticityCap_le_uniform (d := d) hE0 hE1
  have hB0 := productLocalEllipticityCap_nonneg d E
  have hU0 := productUniformEllipticityCap_nonneg d
  have hsq : productLocalEllipticityCap d E ^ 2 ≤
      productUniformEllipticityCap d ^ 2 :=
    pow_le_pow_left₀ hB0 hB 2
  have hcub : (productLocalEllipticityCap d E ^ 2) ^ 3 ≤
      (productUniformEllipticityCap d ^ 2) ^ 3 :=
    pow_le_pow_left₀ (sq_nonneg _) hsq 3
  unfold productRootEnergyPrefactor productUniformRootPrefactor
  exact mul_le_mul_of_nonneg_left hcub (by positivity)

/-- Uniformization of the exact root price. -/
theorem productComparisonRootPrice_le_uniform
    {d : ℕ} [NeZero d] {alpha E c : ℝ} {m : ℤ}
    {u : H1Function (openCubeSet (originCube d (m + 2)))}
    (halpha : 0 < alpha) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    productComparisonRootPrice d alpha E c m u ≤
      productUniformRootPrefactor d *
        (productUniformEllipticityCap d * alpha * Real.rpow (3 : ℝ)
          (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) *
          normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
            (fun x ↦ u.toFun x - c)) := by
  have hP := productRootEnergyPrefactor_le_uniform (d := d) hE0 hE1
  have hB := productLocalEllipticityCap_le_uniform (d := d) hE0 hE1
  have hs : 0 ≤ Real.rpow (3 : ℝ)
      (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hn : 0 ≤ normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
      (fun x ↦ u.toFun x - c) :=
    normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet _)
  have hinner :
      productLocalEllipticityCap d E * alpha *
          Real.rpow (3 : ℝ)
            (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) *
          normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
            (fun x ↦ u.toFun x - c) ≤
        productUniformEllipticityCap d * alpha *
          Real.rpow (3 : ℝ)
            (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) *
          normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
            (fun x ↦ u.toFun x - c) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hB halpha.le) hs) hn
  unfold productComparisonRootPrice
  exact mul_le_mul hP hinner
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (productLocalEllipticityCap_nonneg d E)
          halpha.le) hs) hn)
    (productUniformRootPrefactor_nonneg d)

/-- Square-root form of the uniform root price.  The parent scale appears
with its natural inverse length and the centered oscillation appears as the
normalized `L²` norm. -/
theorem sqrt_productComparisonRootPrice_le_uniform
    {d : ℕ} [NeZero d] {alpha E c : ℝ} {m : ℤ}
    {u : H1Function (openCubeSet (originCube d (m + 2)))}
    (halpha : 0 < alpha) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    Real.sqrt (productComparisonRootPrice d alpha E c m u) ≤
      productUniformEnergySqrtConstant d * Real.sqrt alpha *
        Real.rpow (3 : ℝ)
          (-(((originCube d (m + 2)).scale : ℤ) : ℝ)) *
        normalizedL2On (openCubeSet (originCube d (m + 2)))
          (fun x ↦ u.toFun x - c) := by
  have hroot := productComparisonRootPrice_le_uniform
    (d := d) (alpha := alpha) (E := E) (c := c) (m := m) (u := u)
      halpha hE0 hE1
  have hP : 0 ≤ productUniformRootPrefactor d :=
    productUniformRootPrefactor_nonneg d
  have hB : 0 ≤ productUniformEllipticityCap d :=
    productUniformEllipticityCap_nonneg d
  have hK : 0 ≤ productUniformRootPrefactor d *
      productUniformEllipticityCap d := mul_nonneg hP hB
  have hs : 0 ≤ Real.rpow (3 : ℝ)
      (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hn : 0 ≤ normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
      (fun x ↦ u.toFun x - c) :=
    normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet _)
  have hsqrtScale : Real.sqrt (Real.rpow (3 : ℝ)
      (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ))) =
      Real.rpow (3 : ℝ)
        (-(((originCube d (m + 2)).scale : ℤ) : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (Real.rpow (3 : ℝ)
          (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ))).rpow
            (1 / 2 : ℝ) =
          Real.rpow (3 : ℝ)
            ((-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) *
              (1 / 2 : ℝ)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
      _ = _ := by
        congr 1
        ring
  have hsqrtNorm : Real.sqrt
      (normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
        (fun x ↦ u.toFun x - c)) =
      normalizedL2On (openCubeSet (originCube d (m + 2)))
        (fun x ↦ u.toFun x - c) := by
    rfl
  calc
    Real.sqrt (productComparisonRootPrice d alpha E c m u) ≤
        Real.sqrt (productUniformRootPrefactor d *
          (productUniformEllipticityCap d * alpha * Real.rpow (3 : ℝ)
            (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
              (fun x ↦ u.toFun x - c))) := Real.sqrt_le_sqrt hroot
    _ = Real.sqrt (productUniformRootPrefactor d *
          productUniformEllipticityCap d) * Real.sqrt alpha *
        Real.sqrt (Real.rpow (3 : ℝ)
          (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ))) *
        Real.sqrt (normalizedL2SqOnSet
          (openCubeSet (originCube d (m + 2)))
          (fun x ↦ u.toFun x - c)) := by
      rw [show productUniformRootPrefactor d *
          (productUniformEllipticityCap d * alpha * Real.rpow (3 : ℝ)
            (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
              (fun x ↦ u.toFun x - c)) =
        (productUniformRootPrefactor d * productUniformEllipticityCap d) *
          (alpha * (Real.rpow (3 : ℝ)
            (-2 * (((originCube d (m + 2)).scale : ℤ) : ℝ)) *
          normalizedL2SqOnSet (openCubeSet (originCube d (m + 2)))
            (fun x ↦ u.toFun x - c))) by ring]
      rw [Real.sqrt_mul hK, Real.sqrt_mul halpha.le,
        Real.sqrt_mul hs]
      ring
    _ = _ := by
      rw [hsqrtScale, hsqrtNorm]
      rfl

theorem productComparisonWeightedPrice_le_uniform
    {d : ℕ} [NeZero d] {alpha E c : ℝ} {m : ℤ}
    {u : H1Function (openCubeSet (originCube d (m + 2)))}
    (halpha : 0 < alpha) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    productComparisonWeightedPrice d alpha E c m u ≤
      productUniformWeightedConstant d * Real.sqrt alpha *
        Real.rpow (3 : ℝ)
          (-(((originCube d (m + 2)).scale : ℤ) : ℝ)) *
        normalizedL2On (openCubeSet (originCube d (m + 2)))
          (fun x ↦ u.toFun x - c) := by
  have hroot := sqrt_productComparisonRootPrice_le_uniform
    (d := d) (alpha := alpha) (E := E) (c := c) (m := m) (u := u)
      halpha hE0 hE1
  have hfactor : 0 ≤ Section6Dirichlet.dirichletWeightedEnergyFactor
      productLowOrder.1 productMiddleOrder.1 :=
    Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _
  have hmul := mul_le_mul_of_nonneg_left hroot hfactor
  simpa only [productComparisonWeightedPrice,
    productUniformWeightedConstant, mul_assoc] using hmul

/-- The outer scale and the parent inverse scale differ by exactly the fixed
two-scale factor `1/9`. -/
theorem centeredCubeScale_mul_productParentInvScale {d : ℕ} (m : ℤ) :
    centeredCubeScale m * Real.rpow (3 : ℝ)
      (-(((originCube d (m + 2)).scale : ℤ) : ℝ)) = 1 / 9 := by
  simp only [centeredCubeScale, originCube]
  rw [← Real.rpow_intCast (3 : ℝ) m]
  change Real.rpow (3 : ℝ) (m : ℝ) *
      Real.rpow (3 : ℝ) (-((m + 2 : ℤ) : ℝ)) = 1 / 9
  have hexp : (m : ℝ) + -((m + 2 : ℤ) : ℝ) = -2 := by
    push_cast
    ring
  calc
    _ = Real.rpow (3 : ℝ) ((m : ℝ) + -((m + 2 : ℤ) : ℝ)) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
    _ = Real.rpow (3 : ℝ) (-2 : ℝ) := by rw [hexp]
    _ = 1 / 9 := by
      have hneg : Real.rpow (3 : ℝ) (-2 : ℝ) =
          (Real.rpow (3 : ℝ) (2 : ℝ))⁻¹ := by
        simpa only using Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) (2 : ℝ)
      have htwo : Real.rpow (3 : ℝ) (2 : ℝ) = 9 := by
        calc
          Real.rpow (3 : ℝ) (2 : ℝ) = (3 : ℝ) ^ (2 : ℕ) :=
            Real.rpow_two 3
          _ = 9 := by norm_num
      rw [hneg, htwo]
      norm_num

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
