/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridErrorCarrier
import Homogenization.CoarseGraining.Translation




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

noncomputable section

variable {d : ℕ}

/-- Transposition commutes with translation of a coefficient field. -/
theorem adjointCoeffField_translateCoeffField (w : Vec d) (g : CoeffField d) :
    adjointCoeffField (translateCoeffField w g) =
      translateCoeffField w (adjointCoeffField g) := rfl

/-- The doubled response is covariant under a simultaneous translation of the
domain and coefficient field. -/
theorem setDoubledResponseJ_translateSet (w : Vec d) (V : Set (Vec d))
    (g : CoeffField d) (P Q : BlockVec d) :
    setDoubledResponseJ (translateSet w V) g P Q =
      setDoubledResponseJ V (translateCoeffField w g) P Q := by
  rw [setDoubledResponseJ, setDoubledResponseJ,
    ResponseJ_translateSet_eq_translateCoeffField,
    ResponseJ_translateSet_eq_translateCoeffField,
    adjointCoeffField_translateCoeffField]

variable [NeZero d]

/-- The off-grid one-cube response maximum is the corresponding Chapter 2
quantity in the translated coefficient frame. -/
theorem offGridBlockResponseValueSet_eq_translate (w : Vec d) (R : TriadicCube d)
    (A : Ch02.TriadicCoeffFamily d) (g : CoeffField d)
    (hg : (A.coeffOn R).toCoeffField = translateCoeffField w g) (a0 : Mat d) :
    offGridBlockResponseValueSet w R g a0 =
      Ch02.normalizedBlockResponseValueSet R A a0 := by
  ext value
  rw [offGridBlockResponseValueSet, Ch02.normalizedBlockResponseValueSet]
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    rw [offGridCube, setDoubledResponseJ_translateSet,
      setDoubledResponseJ_openCubeSet R A _ hg]
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    rw [offGridCube, setDoubledResponseJ_translateSet,
      setDoubledResponseJ_openCubeSet R A _ hg]

/-- The supremum form of `offGridBlockResponseValueSet_eq_translate`. -/
theorem offGridBlockResponseMax_eq_translate (w : Vec d) (R : TriadicCube d)
    (A : Ch02.TriadicCoeffFamily d) (g : CoeffField d)
    (hg : (A.coeffOn R).toCoeffField = translateCoeffField w g) (a0 : Mat d) :
    offGridBlockResponseMax w R g a0 = Ch02.normalizedBlockResponseMax R A a0 := by
  rw [offGridBlockResponseMax, Ch02.normalizedBlockResponseMax,
    offGridBlockResponseValueSet_eq_translate w R A g hg]

/-- Translation identifies the off-grid shell maximum with the ordinary
descendant shell maximum. -/
theorem offGridShellMax_eq_translate (w : Vec d) (P : TriadicCube d) (k : ℤ)
    (A : Ch02.TriadicCoeffFamily d) (g : CoeffField d)
    (hg : ∀ Q : TriadicCube d, (A.coeffOn Q).toCoeffField = translateCoeffField w g)
    (a0 : Mat d) :
    offGridShellMax w P k g a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale P k A a0 := by
  rw [offGridShellMax, Ch02.maxDescendantNormalizedBlockResponseAtScale]
  refine congrArg (Ch02.finsetSupReal (descendantsAtScale P k)) ?_
  funext R
  exact offGridBlockResponseMax_eq_translate w R A g (hg R) a0

/-- The full off-grid error is Chapter 2's multiscale cube error in the
translated frame. -/
theorem offGridErrorFunctional_eq_homogenizationErrorOnCube_translate (w : Vec d)
    (P : TriadicCube d) {t : ℝ} (ht : 0 < t) (A : Ch02.TriadicCoeffFamily d)
    (g : CoeffField d)
    (hg : ∀ Q : TriadicCube d, (A.coeffOn Q).toCoeffField = translateCoeffField w g)
    (a0 : Mat d) :
    offGridErrorFunctional w P t g a0 =
      Ch02.HomogenizationErrorOnCube P t .infinity (.finite 2) A a0 := by
  have hshell : ∀ l : ℕ, offGridShellMax w P (P.scale - (l : ℤ)) g a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale P (P.scale - (l : ℤ)) A a0 :=
    fun l => offGridShellMax_eq_translate w P _ A g hg a0
  have hsum : (∑' l : ℕ, Ch02.geometricWeight t 2 l *
      offGridShellMax w P (P.scale - (l : ℤ)) g a0) =
      Ch02.HomogenizationErrorOnCube P t .infinity (.finite 2) A a0 ^ 2 := by
    rw [Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum P ht A a0]
    exact tsum_congr fun l => by rw [hshell l]
  rw [offGridErrorFunctional, hsum]
  exact Real.sqrt_sq
    (homogenizationErrorOnCube_infinity_two_nonneg P A a0 ht)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
