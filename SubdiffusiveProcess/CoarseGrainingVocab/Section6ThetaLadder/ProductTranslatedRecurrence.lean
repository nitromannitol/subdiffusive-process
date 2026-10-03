module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductGoodRecurrence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductTranslation

@[expose] public section

/-!
# Theta-perturbed ladder: product recurrence on a translated cube

This is the physical-coordinate form of the origin recurrence.  It translates
the sample, multiplier, solution, and affine minimizer together, applies the
origin theorem, and translates only the two excess terms back.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- Product-coefficient recurrence on a physical translated cube, with the
product-error slot already replaced by a supplied cap. -/
theorem productTranslated_excessRecurrence_of_errorCap
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {b epsilon alpha Ebase Ecap : ℝ}
    (theta : Vec d → ℝ) (n : ℤ) (z : Vec d)
    (htheta : ContinuousOn theta (translatedCube d n z))
    (hb : 0 < b) (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ translatedCube d n z,
      |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (k : ℕ) (hk : 6 ≤ k)
    (u : H1Function (translatedCube d n z))
    (hu : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (translatedCube d n z) u)
    (hbaseParent : paperHomogenizationError
      (originCube d n) n ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L (translatePotentialSample z omega)) alpha ≤
        ENNReal.ofReal Ebase)
    (hbaseInner : paperHomogenizationError
      (originCube d (n - 2)) (n - 2) ((3 / 16 : ℝ) / 6)
      .infinity (.finite 2)
      (aCutoffFamily M L (translatePotentialSample z omega)) alpha ≤
        ENNReal.ofReal Ebase)
    (hparentOne :
      (paperHomogenizationError (originCube d n) n
        ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
        (localizedThetaCoeffFamily M L (translatePotentialSample z omega)
          (measurableSet_openCubeSet (originCube d n)) (translatedMultiplier z theta)
          (continuousOn_translatedMultiplier htheta) hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num))
          (translatedMultiplier_near_one hnear)) alpha).toReal ≤ 1)
    (hproductError :
      (paperHomogenizationError (originCube d (n - 2)) (n - 2)
        ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
        (localizedThetaCoeffFamily M L (translatePotentialSample z omega)
          (measurableSet_openCubeSet (originCube d n)) (translatedMultiplier z theta)
          (continuousOn_translatedMultiplier htheta) hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num))
          (translatedMultiplier_near_one hnear)) alpha).toReal ≤ Ecap)
    (ell : Affine d)
    (hell : ell ∈ affineMinimizers (translatedCube d n z) u.toFun) :
    excess (n - (k : ℤ)) (translatedCube d (n - (k : ℤ)) z) u.toFun ≤
      oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
          excess n (translatedCube d n z) u.toFun +
        productOriginRecurrenceErrorConstant d hd k * Ecap *
          (excess n (translatedCube d n z) u.toFun +
            Real.sqrt (d : ℝ) / 2 * Real.sqrt (vecNormSq ell.slope)) := by
  let uT : H1Function (translateSet z (cube d n)) :=
    Homogenization.Book.Ch03.castH1Domain
      (translatedCube_eq_translateSet d n z) u
  let u0 : H1Function (cube d n) := H1Function.untranslate z uT
  let ell0 : Affine d := ⟨ell.constant + vecDot ell.slope z, ell.slope⟩
  have hu0 : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
          (translatePotentialSample z omega) x * translatedMultiplier z theta x)
      (cube d n) u0 := by
    exact isWeaklyHarmonicOn_product_untranslate M L omega n z theta u hu
  have hfun : u0.toFun = fun x ↦ u.toFun (x + z) := by
    funext x
    simp only [u0, uT, H1Function.untranslate_toFun,
      Homogenization.Book.Ch03.castH1Domain_toFun]
  have hell0 : ell0 ∈ affineMinimizers (cube d n) u0.toFun := by
    have htransport := (mem_affineMinimizers_translateSet_iff z (cube d n)
      u.toFun ell.constant ell.slope).1 (by
        rw [← translatedCube_eq_translateSet d n z]
        exact hell)
    rw [hfun]
    simpa only [ell0] using htransport
  have hraw := productOrigin_excessRecurrence_of_errorCap d hd M L
    (translatePotentialSample z omega) (measurableSet_openCubeSet (originCube d n))
    (translatedMultiplier z theta) (continuousOn_translatedMultiplier htheta)
    hb hepsilon hepsilonHalf (translatedMultiplier_near_one hnear) halpha n k hk
    (Set.Subset.rfl) u0 hu0 hbaseParent hbaseInner hparentOne hproductError ell0 hell0
  have hinner : excess (n - (k : ℤ))
      (translatedCube d (n - (k : ℤ)) z) u.toFun =
      excess (n - (k : ℤ)) (cube d (n - (k : ℤ))) u0.toFun := by
    rw [translatedCube_eq_translateSet, excess_translateSet, hfun]
  have hparent : excess n (translatedCube d n z) u.toFun =
      excess n (cube d n) u0.toFun := by
    calc
      excess n (translatedCube d n z) u.toFun =
          excess n (translateSet z (cube d n)) u.toFun :=
        congrArg (fun W : Set (Vec d) ↦ excess n W u.toFun)
          (translatedCube_eq_translateSet d n z)
      _ = excess n (cube d n) (fun x ↦ u.toFun (x + z)) :=
        excess_translateSet n z (cube d n) u.toFun
      _ = excess n (cube d n) u0.toFun := by rw [hfun]
  simpa only [hinner, hparent, ell0] using hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
