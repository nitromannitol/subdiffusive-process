import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastBallRescaling
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.FinitePResidualLift




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open scoped ENNReal Pointwise

noncomputable section

variable {d : ℕ}

/-- Scalar divergence-form weak equations are covariant under translation. -/
theorem isDivFormWeakSolutionOn_translate
    {s : Vec d → ℝ} {U : Set (Vec d)} {u : H1Function U}
    {g : Vec d → Vec d} (z : Vec d)
    (hu : IsDivFormWeakSolutionOn s U u g) :
    IsDivFormWeakSolutionOn (fun x ↦ s (x - z)) (translateSet z U)
      (u.translate z) (fun x ↦ g (x - z)) := by
  intro phi
  have heq := hu (H10Function.untranslate z phi)
  have hleft := setIntegral_comp_subRight_translateSet z U
    (fun y ↦ vecDot (s y • u.grad y) (phi.toH1Function.grad (y + z)))
  have hright := setIntegral_comp_subRight_translateSet z U
    (fun y ↦ vecDot (g y) (phi.toH1Function.grad (y + z)))
  calc
    ∫ x in translateSet z U,
        vecDot (s (x - z) • (u.translate z).grad x)
          (phi.toH1Function.grad x) ∂volume =
        ∫ y in U, vecDot (s y • u.grad y)
          (phi.toH1Function.grad (y + z)) ∂volume := by
            simpa only [H1Function.translate_grad, sub_add_cancel] using hleft
    _ = -∫ y in U, vecDot (g y)
          (phi.toH1Function.grad (y + z)) ∂volume := by
            simpa only [H10Function.untranslate_toH1Function,
              H1Function.untranslate_grad] using heq
    _ = -∫ x in translateSet z U,
          vecDot (g (x - z)) (phi.toH1Function.grad x) ∂volume := by
            simpa only [sub_add_cancel] using
              congrArg (fun t : ℝ ↦ -t) hright.symm

/-- Scalar divergence-form weak equations are covariant under the
value-normalized positive dilation used by `ballToUnitH1`. -/
theorem isDivFormWeakSolutionOn_dilate
    {s : Vec d → ℝ} {U : Set (Vec d)} {u : H1Function U}
    {g : Vec d → Vec d} {a : ℝ} (ha : 0 < a)
    (hu : IsDivFormWeakSolutionOn s U u g) :
    IsDivFormWeakSolutionOn (fun x ↦ s (a⁻¹ • x)) (a • U)
      (u.dilate ha) (fun x ↦ g (a⁻¹ • x)) := by
  intro phi
  have heq := hu (phi.unscale ha)
  have hbase :
      ∫ y in U, vecDot (s y • u.grad y)
          (phi.toH1Function.grad (a • y)) ∂volume =
        -∫ y in U, vecDot (g y)
          (phi.toH1Function.grad (a • y)) ∂volume := by
    have hscaled :
        a * ∫ y in U, vecDot (s y • u.grad y)
            (phi.toH1Function.grad (a • y)) ∂volume =
          a * (-∫ y in U, vecDot (g y)
            (phi.toH1Function.grad (a • y)) ∂volume) := by
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
        _ = -∫ y in U, vecDot (g y)
              ((phi.unscale ha).toH1Function.grad y) ∂volume := heq
        _ = -(a * ∫ y in U, vecDot (g y)
              (phi.toH1Function.grad (a • y)) ∂volume) := by
                congr 1
                rw [← integral_const_mul]
                apply integral_congr_ae
                filter_upwards with y
                rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
                simp only [vecDot_smul_right]
        _ = a * (-∫ y in U, vecDot (g y)
              (phi.toH1Function.grad (a • y)) ∂volume) := by ring
    exact mul_left_cancel₀ ha.ne' hscaled
  have hleft := Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos
    (d := d) (E := ℝ) ha U
    (fun x ↦ vecDot (s (a⁻¹ • x) • (u.dilate ha).grad x)
      (phi.toH1Function.grad x))
  have hright := Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos
    (d := d) (E := ℝ) ha U
    (fun x ↦ vecDot (g (a⁻¹ • x)) (phi.toH1Function.grad x))
  rw [hleft, hright]
  simp only [H1Function.dilate_grad, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  rw [hbase]
  simp only [smul_eq_mul]
  ring

/-- Multiplying both the scalar coefficient and the vector source by the same
constant preserves the divergence-form equation. -/
theorem IsDivFormWeakSolutionOn.const_inv_mul
    {s : Vec d → ℝ} {U : Set (Vec d)} {u : H1Function U}
    {g : Vec d → Vec d} (kappa : ℝ)
    (hu : IsDivFormWeakSolutionOn s U u g) :
    IsDivFormWeakSolutionOn (fun x ↦ kappa⁻¹ * s x) U u
      (fun x ↦ kappa⁻¹ • g x) := by
  intro phi
  have heq := hu phi
  calc
    ∫ x in U, vecDot ((kappa⁻¹ * s x) • u.grad x)
        (phi.toH1Function.grad x) ∂volume =
        kappa⁻¹ * ∫ x in U, vecDot (s x • u.grad x)
          (phi.toH1Function.grad x) ∂volume := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with x
            simp only [mul_smul, vecDot_smul_left]
    _ = kappa⁻¹ * (-∫ x in U, vecDot (g x)
          (phi.toH1Function.grad x) ∂volume) := by rw [heq]
    _ = -(kappa⁻¹ * ∫ x in U, vecDot (g x)
          (phi.toH1Function.grad x) ∂volume) := by ring
    _ = -∫ x in U, vecDot (kappa⁻¹ • g x)
          (phi.toH1Function.grad x) ∂volume := by
            apply congrArg (fun t : ℝ ↦ -t)
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with x
            simp only [vecDot_smul_left]

/-- Transport a scalar divergence-form equation across an equality of carrier
sets. -/
theorem IsDivFormWeakSolutionOn.castDomain
    {s : Vec d → ℝ} {U V : Set (Vec d)} (hUV : U = V)
    {u : H1Function U} {g : Vec d → Vec d}
    (hu : IsDivFormWeakSolutionOn s U u g) :
    IsDivFormWeakSolutionOn s V (hUV ▸ u) g := by
  subst V
  exact hu

/-- The normalized pullback of a physical vector source. -/
def ballToUnitSource (g : Vec d → Vec d) (x : Vec d) (rho kappa : ℝ) :
    Vec d → Vec d :=
  fun y ↦ kappa⁻¹ • g (rho • y + x)

/-- A physical scalar divergence-form equation becomes the normalized matrix
equation on the unit ball. -/
theorem isMatrixDivFormWeakSolutionOn_ballToUnit
    {s : Vec d → ℝ} {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    {u : H1Function (euclideanBall x rho)} {g : Vec d → Vec d}
    (kappa : ℝ) (hu : IsDivFormWeakSolutionOn s (euclideanBall x rho) u g) :
    IsMatrixDivFormWeakSolutionOn
      (scalarCoeffField (ballToUnitCoefficient s x rho kappa))
      (smallContrastUnitBall d) (ballToUnitH1 x hrho u)
      (ballToUnitSource g x rho kappa) := by
  have htrans := isDivFormWeakSolutionOn_translate (-x) hu
  have hdilate := isDivFormWeakSolutionOn_dilate (inv_pos.mpr hrho) htrans
  have hnormalized := IsDivFormWeakSolutionOn.const_inv_mul kappa hdilate
  have hcoeff :
      (fun y ↦ kappa⁻¹ * s ((rho⁻¹)⁻¹ • y - -x)) =
        ballToUnitCoefficient s x rho kappa := by
    funext y
    simp [ballToUnitCoefficient, sub_eq_add_neg]
  have hsource :
      (fun y ↦ kappa⁻¹ • g ((rho⁻¹)⁻¹ • y - -x)) =
        ballToUnitSource g x rho kappa := by
    funext y
    simp [ballToUnitSource, sub_eq_add_neg]
  rw [hcoeff, hsource] at hnormalized
  have hcast := IsDivFormWeakSolutionOn.castDomain
    (inv_smul_translateSet_neg_euclideanBall_eq_unitBall x hrho)
    hnormalized
  intro phi
  have heq := hcast phi
  simpa only [scalarCoeffField, Homogenization.matVecMul_scalarMatrix] using heq

/-- Finite vector `L^p` membership is preserved by the physical-ball
pullback and constant coefficient normalization. -/
theorem memVectorLpOn_ballToUnitSource
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho) {kappa p : ℝ}
    {g : Vec d → Vec d}
    (hg : MemVectorLpOn (euclideanBall x rho) p g) :
    MemVectorLpOn (smallContrastUnitBall d) p
      (ballToUnitSource g x rho kappa) := by
  let T : Vec d → Vec d := fun y ↦ rho • y + x
  let scale : ℝ≥0∞ := ENNReal.ofReal ((rho ^ d)⁻¹)
  have hmeasSmul : Measurable (fun y : Vec d ↦ rho • y) :=
    measurable_const_smul rho
  have hmeasAdd : Measurable (fun y : Vec d ↦ y + x) :=
    measurable_id.add measurable_const
  have hmap : Measure.map T (volume.restrict (smallContrastUnitBall d)) =
      scale • volume.restrict (euclideanBall x rho) := by
    calc
      Measure.map T (volume.restrict (smallContrastUnitBall d)) =
          Measure.map (fun y : Vec d ↦ y + x)
            (Measure.map (fun y : Vec d ↦ rho • y)
              (volume.restrict (smallContrastUnitBall d))) := by
                rw [Measure.map_map hmeasAdd hmeasSmul]
                rfl
      _ = Measure.map (fun y : Vec d ↦ y + x)
            (scale • volume.restrict (rho • smallContrastUnitBall d)) := by
              rw [map_smul_volume_restrict hrho]
      _ = scale • Measure.map (fun y : Vec d ↦ y + x)
            (volume.restrict (rho • smallContrastUnitBall d)) := by
              rw [Measure.map_smul]
      _ = scale • volume.restrict
            (translateSet x (rho • smallContrastUnitBall d)) := by
              rw [(measurePreserving_addRight_restrict_translateSet x
                (rho • smallContrastUnitBall d)).map_eq]
      _ = scale • volume.restrict (euclideanBall x rho) := by
              simp only [smallContrastUnitBall]
              rw [euclideanBall_eq_translateSet_smul_unit_of_pos x hrho]
  have hgScaled : MemLp (fun y ↦ HilbertVec.ofVec (g y)) (ENNReal.ofReal p)
      (scale • volume.restrict (euclideanBall x rho)) :=
    hg.smul_measure ENNReal.ofReal_ne_top
  have hcomp : MemLp
      ((fun y ↦ HilbertVec.ofVec (g y)) ∘ T) (ENNReal.ofReal p)
      (volume.restrict (smallContrastUnitBall d)) := by
    apply MemLp.comp_of_map
    · rwa [hmap]
    · exact (hmeasAdd.comp hmeasSmul).aemeasurable
  have hscaled := hcomp.const_smul kappa⁻¹
  simpa only [MemVectorLpOn, ballToUnitSource, T, Function.comp_apply,
    ← (HilbertVec.ofVecL d).map_smul] using hscaled

/-- The inhomogeneous physical-ball equation satisfies the unit-ball
small-contrast Schauder conclusion. -/
theorem smallContrastSchauder_ballToUnit_inhomogeneous [NeZero d]
    {s : Vec d → ℝ} {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    {u : H1Function (euclideanBall x rho)} {g : Vec d → Vec d}
    (kappa delta alpha : ℝ)
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ smallContrastThreshold d alpha) (hdelta1 : delta < 1)
    (hcont : ContinuousOn (ballToUnitCoefficient s x rho kappa)
      (smallContrastUnitBall d))
    (hclose : ∀ y ∈ smallContrastUnitBall d,
      |ballToUnitCoefficient s x rho kappa y - 1| ≤ delta)
    (hu : IsDivFormWeakSolutionOn s (euclideanBall x rho) u g)
    (hg : MemVectorLpOn (euclideanBall x rho)
      (schauderSourceExponent d alpha) g) :
    SmallContrastSchauderConclusion alpha
      (smallContrastSchauderConstant d *
        smallContrastDataSize d alpha (ballToUnitH1 x hrho u)
          (ballToUnitSource g x rho kappa))
      (ballToUnitH1 x hrho u) := by
  have hbounds : ∀ y ∈ smallContrastUnitBall d,
      1 - delta ≤ ballToUnitCoefficient s x rho kappa y ∧
        ballToUnitCoefficient s x rho kappa y ≤ 1 + delta := by
    intro y hy
    have habs := abs_le.mp (hclose y hy)
    constructor <;> linarith
  have hEll : IsEllipticFieldOn (1 - delta) (1 + delta)
      (smallContrastUnitBall d)
      (scalarCoeffField (ballToUnitCoefficient s x rho kappa)) :=
    isEllipticFieldOn_scalarCoeffField_of_continuousOn
      (isOpen_euclideanBall (0 : Vec d) 1).measurableSet hcont
      (by linarith) hbounds
  have ha : CoefficientIdentityDistanceLE (smallContrastUnitBall d)
      (scalarCoeffField (ballToUnitCoefficient s x rho kappa)) delta :=
    coefficientIdentityDistanceLE_scalarCoeffField
      (isOpen_euclideanBall (0 : Vec d) 1).measurableSet hclose
  exact smallContrastSchauder hd halpha hdelta0 hdelta hEll ha
    (isMatrixDivFormWeakSolutionOn_ballToUnit hrho kappa hu)
    (memVectorLpOn_ballToUnitSource hrho hg)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
