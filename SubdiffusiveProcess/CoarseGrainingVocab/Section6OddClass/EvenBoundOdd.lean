module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.DatumPrice

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/OneStepEvenBoundOdd.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepEvenBoundOdd.lean

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass

open MeasureTheory
open Homogenization (Vec vecDot openCubeSet originCube coordFaceReflection)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder


noncomputable section

variable {d : ℕ}

/-! ## 1. The even part is constant along the reflection -/

/-- A slope with vanishing `i`-coordinate does not see the `i`-face
reflection. -/
theorem vecDot_coordFaceReflection_of_apply_eq_zero {g : Vec d} {i : Fin d}
    (hg : g i = 0) (a : ℝ) (y : Vec d) :
    vecDot g (coordFaceReflection a i y) = vecDot g y := by
  classical
  show ∑ j : Fin d, g j * (coordFaceReflection a i y) j = ∑ j : Fin d, g j * y j
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    rw [hg, zero_mul, zero_mul]
  · rw [Homogenization.coordFaceReflection_apply_ne a i j y hj]

/-- An affine function with vanishing `i`-slope is invariant under the `i`-face
reflection. -/
theorem affineEval_coordFaceReflection_of_slope_zero {c : ℝ} {g : Vec d} {i : Fin d}
    (hg : g i = 0) (a : ℝ) (y : Vec d) :
    affineEval c g (coordFaceReflection a i y) = affineEval c g y := by
  rw [affineEval, affineEval, vecDot_coordFaceReflection_of_apply_eq_zero hg]

/-! ## 2. The two halves of the affine minimizer, as functions -/

/-- The **even part** of the affine datum `(c, A)` at the met upper `i`-face, as
a function on `Vec d`. -/
def evenAffinePart (x : Vec d) (m : ℤ) (i : Fin d) (c : ℝ) (A : Vec d) : Vec d → ℝ :=
  affineEval (evenAffineIntercept x m i c A) (evenAffineSlope i A)

/-- The **odd (normal) part** of the affine datum `(c, A)` at the met upper
`i`-face, as a function on `Vec d`. -/
def oddAffinePart (x : Vec d) (m : ℤ) (i : Fin d) (A : Vec d) : Vec d → ℝ :=
  affineEval (oddAffineIntercept x m i A - vecDot (oddAffineSlope i A) x)
    (oddAffineSlope i A)

/-- The odd part is the normal ramp `Aᵢ (yᵢ - a)`. -/
theorem oddAffinePart_apply (x : Vec d) (m : ℤ) (i : Fin d) (A y : Vec d) :
    oddAffinePart x m i A y = A i * (y i - (1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
  rw [oddAffinePart, ← affineLift_eq_affineEval, affineLift_oddAffineDatum]

/-- **The split**, as an identity of functions. -/
theorem affineEval_eq_oddAffinePart_add_evenAffinePart (x : Vec d) (m : ℤ) (i : Fin d)
    (c : ℝ) (A y : Vec d) :
    affineEval (c - vecDot A x) A y
      = oddAffinePart x m i A y + evenAffinePart x m i c A y :=
  affineEval_split x m i c A y

/-- The odd part is odd about the met face. -/
theorem oddAffinePart_coordFaceReflection (x : Vec d) (m : ℤ) (i : Fin d) (A y : Vec d) :
    oddAffinePart x m i A (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y)
      = -oddAffinePart x m i A y := by
  rw [oddAffinePart_apply, oddAffinePart_apply,
    Homogenization.coordFaceReflection_apply_self]
  ring

/-- The even part is even about the met face. -/
theorem evenAffinePart_coordFaceReflection (x : Vec d) (m : ℤ) (i : Fin d) (c : ℝ)
    (A y : Vec d) :
    evenAffinePart x m i c A (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y)
      = evenAffinePart x m i c A y :=
  affineEval_coordFaceReflection_of_slope_zero (evenAffineSlope_apply_self i A) _ y

/-! ## 3. The reflection identity for the affine residual -/

/-- **The reflection identity.**  For a competitor odd about the met face, the
affine residual and its reflection add up to `-2` times the even part — an
exact pointwise identity, with no membership hypothesis. -/
theorem sub_affineEval_add_reflect {x : Vec d} {m : ℤ} {i : Fin d} {V : Vec d → ℝ}
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (c : ℝ) (A : Vec d) (y : Vec d) :
    (V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y)
        - affineEval (c - vecDot A x) A
            (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y))
      + (V y - affineEval (c - vecDot A x) A y)
      = -2 * evenAffinePart x m i c A y := by
  rw [affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A,
    affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A y,
    oddAffinePart_coordFaceReflection, evenAffinePart_coordFaceReflection, hVodd y]
  ring

/-- **The odd summand.**  Subtracting the odd part of the affine minimizer from a
face-odd competitor leaves a face-odd function. -/
theorem faceOdd_sub_oddAffinePart {x : Vec d} {m : ℤ} {i : Fin d} {V : Vec d → ℝ}
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (A : Vec d) (z : Vec d) :
    (fun y => V y - oddAffinePart x m i A y)
        (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)
      = -((fun y => V y - oddAffinePart x m i A y) z) := by
  show V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)
      - oddAffinePart x m i A (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)
    = -(V z - oddAffinePart x m i A z)
  rw [hVodd z, oddAffinePart_coordFaceReflection]
  ring

/-! ## 4. The affine residual on the doubled window -/



theorem normalizedL2On_reflectedWindow_sub_affineEval_le {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m) {i : Fin d}
    (hup : MeetsUpperFace x m (n - 2) i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j)
    {V : Vec d → ℝ}
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2)))) (c : ℝ) (A : Vec d) :
    normalizedL2On (reflectedWindow x m (n - 2))
        (fun y => V y - affineEval (c - vecDot A x) A y)
      ≤ 2 ^ d * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m i c A))
          + normalizedL2On (reflectedWindow x m (n - 2)) (evenAffinePart x m i c A) := by
  set R : Set (Vec d) := reflectedWindow x m (n - 2) with hRdef
  set U : Set (Vec d) := truncatedWindow x m (n - 2) with hUdef
  set e : Vec d → ℝ := evenAffinePart x m i c A with hedef
  set F : Vec d → ℝ := fun y => V y - oddAffinePart x m i A y with hFdef
  set f : Vec d → ℝ := fun y => V y - affineEval (c - vecDot A x) A y with hfdef
  -- the `L²` data
  have hVU : MemLp V 2 (volume.restrict U) :=
    hVR.mono_measure (Measure.restrict_mono (truncatedWindow_subset_reflectedWindow x m (n - 2))
      le_rfl)
  have heR : MemLp e 2 (volume.restrict R) := by
    rw [hedef, evenAffinePart]
    exact memLp_affineEval_reflectedWindow x m (n - 2) _ _
  have heU : MemLp e 2 (volume.restrict U) := by
    rw [hedef, evenAffinePart]
    exact memLp_affineEval_truncatedWindow x m (n - 2) _ _
  have hFR : MemLp F 2 (volume.restrict R) := by
    rw [hFdef, oddAffinePart]
    exact hVR.sub (memLp_affineEval_reflectedWindow x m (n - 2) _ _)
  have hFU : MemLp F 2 (volume.restrict U) := by
    rw [hFdef, oddAffinePart]
    exact hVU.sub (memLp_affineEval_truncatedWindow x m (n - 2) _ _)
  have hfU : MemLp f 2 (volume.restrict U) := by
    rw [hfdef]
    exact hVU.sub (memLp_affineEval_truncatedWindow x m (n - 2) _ _)
  
  have hFodd : oddExtend x m (n - 2) F =ᵐ[volume] F :=
    oddExtend_ae_eq_self_of_faceOdd_upper hup hother (faceOdd_sub_oddAffinePart hVodd A)
  have hFoddR : oddExtend x m (n - 2) F =ᵐ[volume.restrict R] F :=
    MeasureTheory.ae_restrict_of_ae hFodd
  have hoddFR : MemLp (oddExtend x m (n - 2) F) 2 (volume.restrict R) :=
    hFR.ae_eq hFoddR.symm
  have hRpos : 0 < (volume R).toReal :=
    volume_toReal_reflectedWindow_pos x hx (by omega)
  have hUpos : 0 < (volume U).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  have hbridge : normalizedL2On R F ≤ 2 ^ d * normalizedL2On U F := by
    have h := normalizedL2On_oddExtend_le x hmn F hRpos hUpos hoddFR hFU
    rwa [normalizedL2On_congr_ae hFoddR] at h
  -- `F = f + e` on `U`, and `f = F - e` on `R`
  have hFfe : F = fun y => f y + e y := by
    funext y
    show V y - oddAffinePart x m i A y
        = (V y - affineEval (c - vecDot A x) A y) + evenAffinePart x m i c A y
    rw [affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A y]
    ring
  have hfFe : f = fun y => F y + (-e y) := by
    funext y
    show V y - affineEval (c - vecDot A x) A y
        = (V y - oddAffinePart x m i A y) + -evenAffinePart x m i c A y
    rw [affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A y]
    ring
  have hstepU : normalizedL2On U F ≤ normalizedL2On U f + normalizedL2On U e := by
    rw [hFfe]
    exact normalizedL2On_add_le hfU heU
  have hstepR : normalizedL2On R f ≤ normalizedL2On R F + normalizedL2On R e := by
    have hneg : MemLp (fun y => -e y) 2 (volume.restrict R) := heR.neg
    have h := normalizedL2On_add_le (W := R) (f := F) (g := fun y => -e y) hFR hneg
    rw [← hfFe] at h
    refine le_trans h (le_of_eq ?_)
    congr 1
    exact normalizedL2On_neg R e
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hmul : 2 ^ d * normalizedL2On U F
      ≤ 2 ^ d * (normalizedL2On U f + normalizedL2On U e) :=
    mul_le_mul_of_nonneg_left hstepU h2d
  linarith only [hstepR, hbridge, hmul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass
