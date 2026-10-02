import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/GoodEvents/ObservableTranslate.lean




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance

open MeasureTheory Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-! ### The pointwise root: the cutoff coefficient -/

/-- The cutoff coefficient is translation covariant: it is an unanchored
functional of the layers. -/
theorem aCutoff_translatePotentialSample
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L (translatePotentialSample z ω) x =
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω (x + z) :=
  aCutoff_translatePotentialSequence M L z ω x

/-- The tail coefficient `b_{L,m}` is translation covariant.  Its prefactor
`ahom M (min m L)` is deterministic, hence untouched. -/
theorem tailCoefficient_translatePotentialSample
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) (z : Vec d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    tailCoefficient M L m (translatePotentialSample z ω) x =
      tailCoefficient M L m ω (x + z) := by
  unfold tailCoefficient
  rw [aCutoff_translatePotentialSample, aCutoff_translatePotentialSample]

/-! ### Windows: translating a set and its volume average -/

/-- Translating a set by `z` is back-translating by `-z`. -/
theorem image_add_left_eq_preimage (z : Vec d) (W : Set (Vec d)) :
    (fun p => z + p) '' W = (fun p => p + -z) ⁻¹' W := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    show z + p + -z ∈ W
    rwa [add_comm z p, add_assoc, add_neg_cancel, add_zero]
  · intro hq
    refine ⟨q + -z, hq, ?_⟩
    show z + (q + -z) = q
    rw [← add_assoc, add_comm z q, add_assoc, add_neg_cancel, add_zero]

/-- Back-translating the translate of a window recovers the window. -/
theorem preimage_add_right_image_add_left (z : Vec d) (W : Set (Vec d)) :
    (fun p => p + z) ⁻¹' ((fun p => z + p) '' W) = W := by
  rw [image_add_left_eq_preimage, ← Set.preimage_comp]
  ext p
  show p + z + -z ∈ W ↔ p ∈ W
  rw [add_assoc, add_neg_cancel, add_zero]

theorem volume_image_add_left (z : Vec d) (W : Set (Vec d)) :
    volume ((fun p => z + p) '' W) = volume W := by
  rw [image_add_left_eq_preimage]
  exact measure_preimage_add_right volume (-z) W

/-- Set integrals over a translated window.  Lebesgue measure on `Vec d` is
translation invariant, so the integral moves to the untranslated window with
the integrand precomposed. -/
theorem setIntegral_image_add_left (z : Vec d) (W : Set (Vec d))
    (f : Vec d → ℝ) :
    ∫ x in (fun p => z + p) '' W, f x ∂volume =
      ∫ x in W, f (x + z) ∂volume := by
  have hmap : Measure.map (fun p : Vec d => p + z) volume = volume :=
    map_add_right_eq_self volume z
  have hequiv := setIntegral_map_equiv (μ := (volume : Measure (Vec d)))
    (MeasurableEquiv.addRight (G := Vec d) z) f ((fun p => z + p) '' W)
  rw [show ⇑(MeasurableEquiv.addRight (G := Vec d) z) = fun p : Vec d => p + z from rfl,
    hmap, preimage_add_right_image_add_left] at hequiv
  exact hequiv

/-- The normalized volume average over a translated window. -/
theorem volumeAverage_image_add_left (z : Vec d) (W : Set (Vec d))
    (f : Vec d → ℝ) :
    volumeAverage ((fun p => z + p) '' W) f =
      volumeAverage W (fun x => f (x + z)) := by
  unfold volumeAverage
  rw [volume_image_add_left, setIntegral_image_add_left]

/-! ### `tailAverage` -/

/-- Translating the sample by `z` translates the window of `tailAverage`
by `z`. -/
theorem tailAverage_translatePotentialSample
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) (z : Vec d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (W : Set (Vec d)) :
    tailAverage M L m (translatePotentialSample z ω) W =
      tailAverage M L m ω ((fun p => z + p) '' W) := by
  have hfun : tailCoefficient M L m (translatePotentialSample z ω) =
      fun x => tailCoefficient M L m ω (x + z) :=
    funext (fun x => tailCoefficient_translatePotentialSample M L m z ω x)
  unfold tailAverage
  rw [volumeAverage_image_add_left, hfun]

/-- A translate of the centred cube is the centred cube at the shifted
centre. -/
theorem image_add_left_translatedCube (z : Vec d) (k : ℤ) (y : Vec d) :
    (fun p => z + p) '' translatedCube d k y = translatedCube d k (z + y) := by
  simp only [translatedCube, Set.image_image, ← add_assoc]

/-- `tailAverage` on the frozen translated-cube windows. -/
theorem tailAverage_translatePotentialSample_translatedCube
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) (k : ℤ) (z y : Vec d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    tailAverage M L m (translatePotentialSample z ω) (translatedCube d k y) =
      tailAverage M L m ω (translatedCube d k (z + y)) := by
  rw [tailAverage_translatePotentialSample, image_add_left_translatedCube]

/-- The frozen anchored normalizer `(b_{L,m})_{□_m}` is a *cube* average at the
origin, so translating the sample moves its window off the origin: the frozen
carrier is covariant only jointly with the sample, which is exactly how
`section6HomogenizationError` uses it. -/
theorem tailCoefficientCubeAverage_translatePotentialSample
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) (z : Vec d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    tailCoefficientCubeAverage M L m (translatePotentialSample z ω) =
      tailAverage M L m ω (translatedCube d (m : ℤ) z) := by
  have hcube : tailCoefficientCubeAverage M L m (translatePotentialSample z ω) =
      tailAverage M L m (translatePotentialSample z ω) (cube d (m : ℤ)) := by
    unfold tailCoefficientCubeAverage tailAverage Ch02.average volumeAverage
    rw [Ch02.cubeDomain_coe]
    rfl
  rw [hcube, tailAverage_translatePotentialSample]
  rfl

/-! ### `section6Response` and `section6HomogenizationError` -/

/-- The response observable is translation covariant: its translate argument
composes with the sample translate. -/
theorem section6Response_translatePotentialSample
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cubeScale cutoff : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z y e : Vec d) :
    section6Response M cubeScale cutoff (translatePotentialSample z ω) y e =
      section6Response M cubeScale cutoff ω (z + y) e := by
  unfold section6Response
  rw [translatePotentialSample_translate]

/-- The response at a translate `z` of the sample `ω` is the response at
translate `0` of the translated sample.  This is the form the Section 6
consumers need: every anchor proved at translate `0` reads at any translate. -/
theorem section6Response_eq_translate_zero
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cubeScale cutoff : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z e : Vec d) :
    section6Response M cubeScale cutoff ω z e =
      section6Response M cubeScale cutoff (translatePotentialSample z ω) 0 e := by
  rw [section6Response_translatePotentialSample, add_zero]

/-- The Section 6 homogenization error is translation covariant. -/
theorem section6HomogenizationError_translatePotentialSample
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z y : Vec d) :
    section6HomogenizationError M s L m (translatePotentialSample z ω) y =
      section6HomogenizationError M s L m ω (z + y) := by
  unfold section6HomogenizationError
  rw [translatePotentialSample_translate]

/-- The error at a translate `z` of `ω` is the error at translate `0` of the
translated sample. -/
theorem section6HomogenizationError_eq_translate_zero
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) :
    section6HomogenizationError M s L m ω z =
      section6HomogenizationError M s L m (translatePotentialSample z ω) 0 := by
  rw [section6HomogenizationError_translatePotentialSample, add_zero]




/-- The anchored partial sums are **not** translation covariant, and this is
the exact defect: translating the sample subtracts the value at the translate.
The anchoring at the origin (`SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor`,
`IsAnchoredC11Limit.anchored : g 0 = 0`) is what breaks covariance.

Consequently `SubdiffusiveProcess.Frozen.Assumptions.aAnchored` is covariant only up to the
random multiplicative factor `exp (anchoredLog ω z)`; it is deliberately not in
the family proved in this module. -/
theorem anchoredPartialSum_translatePotentialSample
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (L : ℕ) (z x : Vec d) :
    SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSum (translatePotentialSample z ω) L x =
      SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSum ω L (x + z) -
        SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSum ω L z := by
  unfold SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [translatePotentialSample_apply, zero_add]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
