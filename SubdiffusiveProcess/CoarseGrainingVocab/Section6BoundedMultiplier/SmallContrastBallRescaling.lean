module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastScalarBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.EquationRestriction
public import Homogenization.Book.Ch01.Theorems.NormScaling
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel

@[expose] public section

/-!
# Ball rescaling for the bounded-multiplier small-contrast step

This file transports scalar weak harmonicity through the translation and
positive dilation that send a physical Euclidean ball to the unit ball.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-- Scalar weak harmonicity is covariant under translation. -/
theorem isWeaklyHarmonicOn_translate
    {s : Vec d → ℝ} {U : Set (Vec d)} {u : H1Function U} (z : Vec d)
    (hu : IsWeaklyHarmonicOn s U u) :
    IsWeaklyHarmonicOn (fun x ↦ s (x - z)) (translateSet z U)
      (u.translate z) := by
  intro phi
  have hzero := hu (H10Function.untranslate z phi)
  have hchange := setIntegral_comp_subRight_translateSet z U
    (fun y ↦ vecDot (s y • u.grad y)
      (phi.toH1Function.grad (y + z)))
  calc
    ∫ x in translateSet z U,
        vecDot (s (x - z) • (u.translate z).grad x)
          (phi.toH1Function.grad x) ∂volume =
        ∫ y in U, vecDot (s y • u.grad y)
          (phi.toH1Function.grad (y + z)) ∂volume := by
            simpa only [H1Function.translate_grad, sub_add_cancel] using hchange
    _ = 0 := by
      simpa only [H10Function.untranslate_toH1Function,
        H1Function.untranslate_grad] using hzero

/-- Scalar weak harmonicity is covariant under the value-normalized positive
dilation supplied by `CoerciveH1Dilation`. -/
theorem isWeaklyHarmonicOn_dilate {s : Vec d → ℝ} {U : Set (Vec d)}
    {u : H1Function U} {a : ℝ} (ha : 0 < a)
    (hu : IsWeaklyHarmonicOn s U u) :
    IsWeaklyHarmonicOn (fun x ↦ s (a⁻¹ • x)) (a • U) (u.dilate ha) := by
  intro phi
  have htest := hu (phi.unscale ha)
  have hfactor :
      a * ∫ y in U, vecDot (s y • u.grad y)
          (phi.toH1Function.grad (a • y)) ∂volume = 0 := by
    calc
      a * ∫ y in U, vecDot (s y • u.grad y)
          (phi.toH1Function.grad (a • y)) ∂volume =
          ∫ y in U, vecDot (s y • u.grad y)
            ((phi.unscale ha).toH1Function.grad y) ∂volume := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards with y
              rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
              simp only [vecDot_smul_right]
      _ = 0 := htest
  have hbase :
      ∫ y in U, vecDot (s y • u.grad y)
          (phi.toH1Function.grad (a • y)) ∂volume = 0 := by
    exact (mul_eq_zero.mp hfactor).resolve_left ha.ne'
  have hchange := Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos
    (d := d) (E := ℝ) ha U
    (fun x ↦ vecDot (s (a⁻¹ • x) • (u.dilate ha).grad x)
      (phi.toH1Function.grad x))
  rw [hchange]
  have ha0 : a ≠ 0 := ha.ne'
  simp only [H1Function.dilate_grad, smul_smul, inv_mul_cancel₀ ha0,
    one_smul, hbase, smul_eq_mul, mul_zero]

/-- Multiplying a scalar coefficient by a constant does not change its
homogeneous weak equation.  The inverse spelling matches the normalization
used below. -/
theorem IsWeaklyHarmonicOn.const_inv_mul {s : Vec d → ℝ} {U : Set (Vec d)}
    {u : H1Function U} (kappa : ℝ) (hu : IsWeaklyHarmonicOn s U u) :
    IsWeaklyHarmonicOn (fun x ↦ kappa⁻¹ * s x) U u := by
  intro phi
  have hzero := hu phi
  calc
    ∫ x in U, vecDot ((kappa⁻¹ * s x) • u.grad x)
        (phi.toH1Function.grad x) ∂volume =
        kappa⁻¹ * ∫ x in U, vecDot (s x • u.grad x)
          (phi.toH1Function.grad x) ∂volume := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with x
            simp only [mul_smul, vecDot_smul_left]
    _ = 0 := by rw [hzero, mul_zero]

/-- Transport a scalar weak equation across an equality of its carrier sets. -/
theorem IsWeaklyHarmonicOn.castDomain {s : Vec d → ℝ} {U V : Set (Vec d)}
    (hUV : U = V) {u : H1Function U} (hu : IsWeaklyHarmonicOn s U u) :
    IsWeaklyHarmonicOn s V (hUV ▸ u) := by
  subst V
  exact hu

/-- Translating a radius-`rho` ball to the origin and then dilating by
`rho⁻¹` gives the unit Euclidean ball exactly. -/
theorem inv_smul_translateSet_neg_euclideanBall_eq_unitBall
    (x : Vec d) {rho : ℝ} (hrho : 0 < rho) :
    rho⁻¹ • translateSet (-x) (euclideanBall x rho) =
      smallContrastUnitBall d := by
  rw [euclideanBall_eq_translateSet_smul_unit_of_pos x hrho,
    translateSet_translateSet]
  simp [smallContrastUnitBall, hrho.ne']

/-- The canonical value-normalized pullback from `B(x,rho)` to the unit ball.
Its gradient is the unscaled pullback of the physical gradient. -/
noncomputable def ballToUnitH1 (x : Vec d) {rho : ℝ} (hrho : 0 < rho)
    (u : H1Function (euclideanBall x rho)) :
    H1Function (smallContrastUnitBall d) := by
  let v := (u.translate (-x)).dilate (inv_pos.mpr hrho)
  exact inv_smul_translateSet_neg_euclideanBall_eq_unitBall x hrho ▸ v

@[simp] theorem ballToUnitH1_toFun (x : Vec d) {rho : ℝ} (hrho : 0 < rho)
    (u : H1Function (euclideanBall x rho)) (y : Vec d) :
    (ballToUnitH1 x hrho u).toFun y =
      rho⁻¹ * u.toFun (rho • y + x) := by
  have hcast {U V : Set (Vec d)} (he : U = V) (w : H1Function U) :
      (he ▸ w).toFun = w.toFun := by
    cases he
    rfl
  unfold ballToUnitH1
  rw [hcast]
  simp [sub_eq_add_neg]

@[simp] theorem ballToUnitH1_grad (x : Vec d) {rho : ℝ} (hrho : 0 < rho)
    (u : H1Function (euclideanBall x rho)) (y : Vec d) :
    (ballToUnitH1 x hrho u).grad y = u.grad (rho • y + x) := by
  have hcast {U V : Set (Vec d)} (he : U = V) (w : H1Function U) :
      (he ▸ w).grad = w.grad := by
    cases he
    rfl
  unfold ballToUnitH1
  rw [hcast]
  simp [sub_eq_add_neg]

/-- The normalized scalar coefficient seen on the unit ball. -/
def ballToUnitCoefficient (s : Vec d → ℝ) (x : Vec d) (rho kappa : ℝ) :
    Vec d → ℝ :=
  fun y ↦ kappa⁻¹ * s (rho • y + x)

/-- The physical homogeneous scalar equation on a Euclidean ball becomes the
zero-forcing matrix equation on the unit ball after translation, dilation,
and constant coefficient normalization. -/
theorem isMatrixDivFormWeakSolutionOn_ballToUnit_zero
    {s : Vec d → ℝ} {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    {u : H1Function (euclideanBall x rho)} (kappa : ℝ)
    (hu : IsWeaklyHarmonicOn s (euclideanBall x rho) u) :
    IsMatrixDivFormWeakSolutionOn
      (scalarCoeffField (ballToUnitCoefficient s x rho kappa))
      (smallContrastUnitBall d) (ballToUnitH1 x hrho u) (fun _ ↦ 0) := by
  have htrans := isWeaklyHarmonicOn_translate (-x) hu
  have hdilate := isWeaklyHarmonicOn_dilate (inv_pos.mpr hrho) htrans
  have hnormalized := IsWeaklyHarmonicOn.const_inv_mul kappa hdilate
  have hcoeff :
      (fun y ↦ kappa⁻¹ * s ((rho⁻¹)⁻¹ • y - -x)) =
        ballToUnitCoefficient s x rho kappa := by
    funext y
    simp [ballToUnitCoefficient, sub_eq_add_neg]
  rw [hcoeff] at hnormalized
  have hcast := IsWeaklyHarmonicOn.castDomain
    (inv_smul_translateSet_neg_euclideanBall_eq_unitBall x hrho)
    hnormalized
  exact isMatrixDivFormWeakSolutionOn_zero_of_isWeaklyHarmonicOn hcast

/-- Restrict an ambient scalar equation to an interior Euclidean ball and
then apply the canonical unit-ball normalization. -/
theorem isMatrixDivFormWeakSolutionOn_restrict_ballToUnit_zero
    {s : Vec d → ℝ} {W : Set (Vec d)} (hW : IsOpen W)
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (hball : euclideanBall x rho ⊆ W) {u : H1Function W} (kappa : ℝ)
    (hu : IsWeaklyHarmonicOn s W u) :
    IsMatrixDivFormWeakSolutionOn
      (scalarCoeffField (ballToUnitCoefficient s x rho kappa))
      (smallContrastUnitBall d)
      (ballToUnitH1 x hrho
        (u.restrict (isOpen_euclideanBall x rho) hball))
      (fun _ ↦ 0) := by
  exact isMatrixDivFormWeakSolutionOn_ballToUnit_zero hrho kappa
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.isWeaklyHarmonicOn_restrict
      hW (isOpen_euclideanBall x rho) hball hu)

/-- Continuous scalar coefficients remain continuous after the affine
unit-ball pullback and constant normalization. -/
theorem continuousOn_ballToUnitCoefficient
    {s : Vec d → ℝ} {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (kappa : ℝ) (hs : ContinuousOn s (euclideanBall x rho)) :
    ContinuousOn (ballToUnitCoefficient s x rho kappa)
      (smallContrastUnitBall d) := by
  have haffine : Continuous (fun y : Vec d ↦ rho • y + x) :=
    (continuous_const_smul rho).add continuous_const
  have hmap : Set.MapsTo (fun y : Vec d ↦ rho • y + x)
      (smallContrastUnitBall d) (euclideanBall x rho) := by
    intro y hy
    exact (affine_mem_euclideanBall_iff_of_pos x y hrho).2 hy
  exact continuousOn_const.mul (hs.comp haffine.continuousOn hmap)

/-- The concrete cutoff-times-multiplier coefficient is continuous on the
normalized unit ball whenever the multiplier is continuous on the ambient
open window containing the physical ball. -/
theorem continuousOn_ballToUnitCoefficient_aCutoff_mul
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {B : Set (Vec d)} {theta : Vec d → ℝ} (htheta : ContinuousOn theta B)
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (hball : euclideanBall x rho ⊆ B) (kappa : ℝ) :
    ContinuousOn
      (ballToUnitCoefficient
        (fun y ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega y * theta y)
        x rho kappa)
      (smallContrastUnitBall d) := by
  apply continuousOn_ballToUnitCoefficient hrho kappa
  exact (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).continuousOn.mul
    (htheta.mono hball)

/-- A pointwise physical-ball contrast estimate pulls back verbatim to the
unit-ball coefficient carrier. -/
theorem ballToUnitCoefficient_close_of_physical
    {s : Vec d → ℝ} {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    {kappa delta : ℝ}
    (hclose : ∀ y ∈ euclideanBall x rho,
      |kappa⁻¹ * s y - 1| ≤ delta) :
    ∀ y ∈ smallContrastUnitBall d,
      |ballToUnitCoefficient s x rho kappa y - 1| ≤ delta := by
  intro y hy
  exact hclose _ ((affine_mem_euclideanBall_iff_of_pos x y hrho).2 hy)

/-- The four small-contrast input carriers on the normalized unit ball. -/
theorem ballToUnit_smallContrastCarriers [NeZero d]
    {s : Vec d → ℝ} {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    {u : H1Function (euclideanBall x rho)} (kappa delta : ℝ)
    (hdelta : delta < 1)
    (hcont : ContinuousOn (ballToUnitCoefficient s x rho kappa)
      (smallContrastUnitBall d))
    (hclose : ∀ y ∈ smallContrastUnitBall d,
      |ballToUnitCoefficient s x rho kappa y - 1| ≤ delta)
    (hu : IsWeaklyHarmonicOn s (euclideanBall x rho) u) :
    IsEllipticFieldOn (1 - delta) (1 + delta) (smallContrastUnitBall d)
        (scalarCoeffField (ballToUnitCoefficient s x rho kappa)) ∧
      CoefficientIdentityDistanceLE (smallContrastUnitBall d)
        (scalarCoeffField (ballToUnitCoefficient s x rho kappa)) delta ∧
      IsMatrixDivFormWeakSolutionOn
        (scalarCoeffField (ballToUnitCoefficient s x rho kappa))
        (smallContrastUnitBall d) (ballToUnitH1 x hrho u) (fun _ ↦ 0) ∧
      MemVectorLpOn (smallContrastUnitBall d) 1 (fun _ ↦ (0 : Vec d)) := by
  have hbounds : ∀ y ∈ smallContrastUnitBall d,
      1 - delta ≤ ballToUnitCoefficient s x rho kappa y ∧
        ballToUnitCoefficient s x rho kappa y ≤ 1 + delta := by
    intro y hy
    have habs := (abs_le.mp (hclose y hy))
    constructor <;> linarith
  refine ⟨isEllipticFieldOn_scalarCoeffField_of_continuousOn
      (isOpen_euclideanBall (0 : Vec d) 1).measurableSet hcont
      (by linarith) hbounds,
    coefficientIdentityDistanceLE_scalarCoeffField
      (isOpen_euclideanBall (0 : Vec d) 1).measurableSet hclose,
    isMatrixDivFormWeakSolutionOn_ballToUnit_zero hrho kappa hu,
    memVectorLpOn_zero _ 1⟩

/-- Invoke the proved small-contrast Schauder theorem on a normalized
physical ball.  The only coefficient-smallness input is the literal
pointwise distance `hclose`. -/
theorem smallContrastSchauder_ballToUnit [NeZero d]
    {s : Vec d → ℝ} {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    {u : H1Function (euclideanBall x rho)} (kappa delta alpha : ℝ)
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ smallContrastThreshold d alpha) (hdelta1 : delta < 1)
    (hcont : ContinuousOn (ballToUnitCoefficient s x rho kappa)
      (smallContrastUnitBall d))
    (hclose : ∀ y ∈ smallContrastUnitBall d,
      |ballToUnitCoefficient s x rho kappa y - 1| ≤ delta)
    (hu : IsWeaklyHarmonicOn s (euclideanBall x rho) u) :
    SmallContrastSchauderConclusion alpha
      (smallContrastSchauderConstant d *
        smallContrastDataSize d alpha (ballToUnitH1 x hrho u) (fun _ ↦ 0))
      (ballToUnitH1 x hrho u) := by
  obtain ⟨hEll, ha, heq, _⟩ := ballToUnit_smallContrastCarriers
    hrho kappa delta hdelta1 hcont hclose hu
  exact smallContrastSchauder hd halpha hdelta0 hdelta hEll ha heq
    (memVectorLpOn_zero _ (schauderSourceExponent d alpha))

/-- At exponent two, the rescaled gradient datum is exactly the square root
of the physical energy times the dilation Jacobian. -/
theorem vectorLpSizeOn_two_ballToUnit_grad_eq [NeZero d]
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (u : H1Function (euclideanBall x rho)) :
    vectorLpSizeOn (smallContrastUnitBall d) 2
        (ballToUnitH1 x hrho u).grad =
      Real.sqrt ((rho ^ d)⁻¹ *
        ∫ y in euclideanBall x rho, vecNormSq (u.grad y) ∂volume) := by
  have hvec : MemVectorL2 (smallContrastUnitBall d)
      (ballToUnitH1 x hrho u).grad :=
    (ballToUnitH1 x hrho u).grad_memVectorL2
  have hhilbert : MemLp (fun y ↦ HilbertVec.ofVec
      ((ballToUnitH1 x hrho u).grad y)) 2
      (volume.restrict (smallContrastUnitBall d)) :=
    memHilbertVectorL2_hilbertifyVecField hvec
  have hscalar : MemLp (fun y ↦ euclideanNorm
      ((ballToUnitH1 x hrho u).grad y)) 2
      (volume.restrict (smallContrastUnitBall d)) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using hhilbert.norm
  have hsq := Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hscalar
  have hnormNonneg : 0 ≤ (eLpNorm (fun y ↦ euclideanNorm
      ((ballToUnitH1 x hrho u).grad y)) 2
      (volume.restrict (smallContrastUnitBall d))).toReal := ENNReal.toReal_nonneg
  have hsize : vectorLpSizeOn (smallContrastUnitBall d) 2
      (ballToUnitH1 x hrho u).grad =
      Real.sqrt (∫ y in smallContrastUnitBall d,
        vecNormSq ((ballToUnitH1 x hrho u).grad y) ∂volume) := by
    unfold vectorLpSizeOn
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hscalar.aestronglyMeasurable]
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    rw [← Real.sqrt_sq hnormNonneg, hsq]
    congr 2
    funext y
    exact euclideanNorm_sq _
  have hchange := setIntegral_comp_smul_add_of_pos (d := d) (E := ℝ)
    hrho x (smallContrastUnitBall d) (fun y ↦ vecNormSq (u.grad y))
  have hball : translateSet x (rho • smallContrastUnitBall d) =
      euclideanBall x rho := by
    exact (euclideanBall_eq_translateSet_smul_unit_of_pos x hrho).symm
  have hchange' :
      ∫ y in smallContrastUnitBall d, vecNormSq (u.grad (rho • y + x)) ∂volume =
        (rho ^ d)⁻¹ * ∫ y in euclideanBall x rho,
          vecNormSq (u.grad y) ∂volume := by
    simpa only [hball, smul_eq_mul] using hchange
  rw [hsize]
  congr 1
  simpa only [ballToUnitH1_grad] using hchange'

/-- With zero forcing, the Schauder datum contains only the rescaled gradient
norm. -/
theorem smallContrastDataSize_ballToUnit_zero [NeZero d]
    {x : Vec d} {rho alpha : ℝ} (hrho : 0 < rho)
    (u : H1Function (euclideanBall x rho)) :
    smallContrastDataSize d alpha (ballToUnitH1 x hrho u) (fun _ ↦ 0) =
      Real.sqrt ((rho ^ d)⁻¹ *
        ∫ y in euclideanBall x rho, vecNormSq (u.grad y) ∂volume) := by
  rw [smallContrastDataSize, vectorLpSizeOn_two_ballToUnit_grad_eq hrho]
  simp only [vectorLpSizeOn, euclideanNorm_zero]
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (show AEStronglyMeasurable (fun _ : Vec d => (0 : ℝ)) (volume.restrict (smallContrastUnitBall d)) from aestronglyMeasurable_const)]
  simp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
