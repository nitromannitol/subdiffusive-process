/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingResponse
import Homogenization.Book.Ch02.Theorems.HomogenizationError.AEEq
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public

/-!
# Local representative invariance below one root cube

The public Chapter 2 invariance API assumes a.e. equality on every triadic
cube.  Off-grid stability only has, and only needs, equality on descendants of
one root.  This file exposes that exact specialization.

-- PROVENANCE: This publicly re-proves the specialization of the private
-- `normalizedBlockResponseMax_eq_of_localAEEq`,
-- `scaleResponseAtScale_infinity_eq_of_descendantAEEq`,
-- `homogenizationErrorOnCube_infinity_eq_of_descendantAEEq`, and
-- `rootPointwiseCoeffFamily_on_descendant_eq_parent` arguments in
-- `Homogenization/Book/Ch03/ABK26/LocalCoarseGraining.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

open Homogenization Homogenization.Book Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-- A one-cube response maximum only reads the representative on that cube. -/
theorem normalizedBlockResponseMax_eq_of_localAEEq
    [NeZero d] {A B : Ch02.TriadicCoeffFamily d} {S : TriadicCube d}
    (hS : Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S)) (a0 : Mat d) :
    Ch02.normalizedBlockResponseMax S A a0 =
      Ch02.normalizedBlockResponseMax S B a0 := by
  unfold Ch02.normalizedBlockResponseMax Ch02.normalizedBlockResponseValueSet
  congr 1
  ext x
  constructor <;> rintro ⟨e, he, rfl⟩ <;>
    refine ⟨e, he, ?_⟩ <;>
    rw [Ch02.doubledResponseJ_eq_ofAEEq hS]

/-- A one-cube upper coarse norm only reads the representative on that cube. -/
theorem coarseBMatrixNorm_eq_of_localAEEq
    {A B : Ch02.TriadicCoeffFamily d} {S : TriadicCube d}
    (hS : Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S)) :
    Ch02.coarseBMatrixNorm S A = Ch02.coarseBMatrixNorm S B := by
  unfold Ch02.coarseBMatrixNorm
  rw [Ch02.bCoarse_eq_ofAEEq hS]

/-- A one-cube inverse dual coarse norm only reads the representative on that
cube. -/
theorem coarseSigmaStarInvMatrixNorm_eq_of_localAEEq
    {A B : Ch02.TriadicCoeffFamily d} {S : TriadicCube d}
    (hS : Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S)) :
    Ch02.coarseSigmaStarInvMatrixNorm S A =
      Ch02.coarseSigmaStarInvMatrixNorm S B := by
  unfold Ch02.coarseSigmaStarInvMatrixNorm
  rw [Ch02.sigmaStarInvCoarse_eq_ofAEEq hS]

/-- Every spatial aggregation at a fixed descendant scale is locally a.e.
invariant. -/
theorem scaleResponseAtScale_eq_of_descendantAEEq
    [NeZero d] {A B : Ch02.TriadicCoeffFamily d} (Q : TriadicCube d) (k : ℤ)
    (h : ∀ S : TriadicCube d, S ∈ descendantsAtScale Q k →
      Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S))
    (p : Ch02.MultiscaleExponent) (a0 : Mat d) :
    Ch02.scaleResponseAtScale Q k p A a0 =
      Ch02.scaleResponseAtScale Q k p B a0 := by
  cases p with
  | finite p =>
      unfold Ch02.scaleResponseAtScale Ch02.finsetAverageReal
      change
        Real.rpow
          (((descendantsAtScale Q k).card : ℝ)⁻¹ *
            ∑ S ∈ descendantsAtScale Q k,
              Real.rpow (Ch02.normalizedBlockResponseMax S A a0) (p / 2)) (1 / p) =
        Real.rpow
          (((descendantsAtScale Q k).card : ℝ)⁻¹ *
            ∑ S ∈ descendantsAtScale Q k,
              Real.rpow (Ch02.normalizedBlockResponseMax S B a0) (p / 2)) (1 / p)
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      rw [normalizedBlockResponseMax_eq_of_localAEEq (h S hS) a0]
  | infinity =>
      unfold Ch02.scaleResponseAtScale
      change
        (Ch02.finsetSupReal (descendantsAtScale Q k)
          (fun S => Ch02.normalizedBlockResponseMax S A a0)) ^ (1 / 2 : ℝ) =
        (Ch02.finsetSupReal (descendantsAtScale Q k)
          (fun S => Ch02.normalizedBlockResponseMax S B a0)) ^ (1 / 2 : ℝ)
      congr 1
      apply Ch02.finsetSupReal_congr
      intro S hS
      exact normalizedBlockResponseMax_eq_of_localAEEq (h S hS) a0

/-- The complete two-exponent homogenization error on `Q` only reads
representatives on descendants of `Q`. -/
theorem homogenizationErrorOnCube_eq_of_descendantAEEq
    [NeZero d] {A B : Ch02.TriadicCoeffFamily d} (Q : TriadicCube d)
    (h : ∀ (k : ℤ) (S : TriadicCube d), S ∈ descendantsAtScale Q k →
      Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S))
    (t : ℝ) (p q : Ch02.MultiscaleExponent) (a0 : Mat d) :
    Ch02.HomogenizationErrorOnCube Q t p q A a0 =
      Ch02.HomogenizationErrorOnCube Q t p q B a0 := by
  unfold Ch02.HomogenizationErrorOnCube Ch02.HomogenizationError
  cases q with
  | finite q =>
      unfold Ch02.HomogenizationErrorFinite
      change
        (∑' j : ℕ, Ch02.geometricWeight t q j *
          (Ch02.scaleResponseAtScale Q (Q.scale - (j : ℤ)) p A a0) ^ q) ^ (1 / q) =
        (∑' j : ℕ, Ch02.geometricWeight t q j *
          (Ch02.scaleResponseAtScale Q (Q.scale - (j : ℤ)) p B a0) ^ q) ^ (1 / q)
      congr 1
      apply tsum_congr
      intro j
      rw [scaleResponseAtScale_eq_of_descendantAEEq Q
        (Q.scale - (j : ℤ)) (fun S hS => h _ S hS) p a0]
  | infinity =>
      unfold Ch02.HomogenizationErrorInfinity
      apply congrArg sSup
      ext x
      constructor <;> rintro ⟨j, rfl⟩ <;>
        refine ⟨j, ?_⟩ <;>
        rw [scaleResponseAtScale_eq_of_descendantAEEq Q
          (Q.scale - (j : ℤ)) (fun S hS => h _ S hS) p a0]

/-- A shell maximum of upper coarse norms is locally a.e. invariant. -/
theorem maxDescendantBMatrixNormAtScale_eq_of_descendantAEEq
    {A B : Ch02.TriadicCoeffFamily d} (Q : TriadicCube d) (k : ℤ)
    (h : ∀ S : TriadicCube d, S ∈ descendantsAtScale Q k →
      Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S)) :
    Ch02.maxDescendantBMatrixNormAtScale Q k A =
      Ch02.maxDescendantBMatrixNormAtScale Q k B := by
  unfold Ch02.maxDescendantBMatrixNormAtScale
  exact Ch02.finsetSupReal_congr _ fun S hS =>
    coarseBMatrixNorm_eq_of_localAEEq (h S hS)

/-- A shell maximum of inverse dual coarse norms is locally a.e. invariant. -/
theorem maxDescendantSigmaStarInvMatrixNormAtScale_eq_of_descendantAEEq
    {A B : Ch02.TriadicCoeffFamily d} (Q : TriadicCube d) (k : ℤ)
    (h : ∀ S : TriadicCube d, S ∈ descendantsAtScale Q k →
      Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S)) :
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k A =
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k B := by
  unfold Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
  exact Ch02.finsetSupReal_congr _ fun S hS =>
    coarseSigmaStarInvMatrixNorm_eq_of_localAEEq (h S hS)

/-- The upper multiscale ellipticity carrier on `Q` only reads descendants of
`Q`. -/
theorem LambdaSq_eq_of_descendantAEEq
    {A B : Ch02.TriadicCoeffFamily d} (Q : TriadicCube d)
    (h : ∀ (k : ℤ) (S : TriadicCube d), S ∈ descendantsAtScale Q k →
      Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S))
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    Ch02.LambdaSq Q s q A = Ch02.LambdaSq Q s q B := by
  cases q with
  | finite q =>
      unfold Ch02.LambdaSq Ch02.LambdaSqFinite
      apply congrArg (fun x : ℝ => Real.rpow x (2 / q))
      apply tsum_congr
      intro j
      rw [maxDescendantBMatrixNormAtScale_eq_of_descendantAEEq Q _
        (fun S hS => h _ S hS)]
  | infinity =>
      unfold Ch02.LambdaSq Ch02.LambdaSqInfinity
      apply congrArg sSup
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        refine ⟨j, ?_⟩
        rw [maxDescendantBMatrixNormAtScale_eq_of_descendantAEEq Q _
          (fun S hS => h _ S hS)]
      · rintro ⟨j, rfl⟩
        refine ⟨j, ?_⟩
        rw [maxDescendantBMatrixNormAtScale_eq_of_descendantAEEq Q _
          (fun S hS => h _ S hS)]

/-- The lower multiscale ellipticity carrier on `Q` only reads descendants of
`Q`. -/
theorem lambdaSq_eq_of_descendantAEEq
    {A B : Ch02.TriadicCoeffFamily d} (Q : TriadicCube d)
    (h : ∀ (k : ℤ) (S : TriadicCube d), S ∈ descendantsAtScale Q k →
      Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S))
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    Ch02.lambdaSq Q s q A = Ch02.lambdaSq Q s q B := by
  cases q with
  | finite q =>
      unfold Ch02.lambdaSq Ch02.lambdaSqFinite
      apply congrArg (fun x : ℝ => Real.rpow x (-(2 / q)))
      apply tsum_congr
      intro j
      rw [maxDescendantSigmaStarInvMatrixNormAtScale_eq_of_descendantAEEq Q _
        (fun S hS => h _ S hS)]
  | infinity =>
      unfold Ch02.lambdaSq Ch02.lambdaSqInfinity
      apply congrArg (fun x : ℝ => x⁻¹)
      apply congrArg sSup
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        refine ⟨j, ?_⟩
        rw [maxDescendantSigmaStarInvMatrixNormAtScale_eq_of_descendantAEEq Q _
          (fun S hS => h _ S hS)]
      · rintro ⟨j, rfl⟩
        refine ⟨j, ?_⟩
        rw [maxDescendantSigmaStarInvMatrixNormAtScale_eq_of_descendantAEEq Q _
          (fun S hS => h _ S hS)]

/-- A family and the canonical pointwise family rooted at `Q` agree a.e. on
every descendant of `Q`. -/
theorem rootPointwiseCoeffFamily_descendant_aeeq_family
    [NeZero d] (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    {S : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale)
    (hS : S ∈ descendantsAtScale Q k) :
    Ch02.CoeffOn.AEEq
      ((Homogenization.Book.Ch03.ABK26.rootPointwiseCoeffFamily Q
        (A.coeffOn Q)).coeffOn S) (A.coeffOn S) := by
  have hroot := Homogenization.Book.Ch03.ABK26.rootPointwiseCoeffFamily_descendant_aeeq
    Q (A.coeffOn Q) hk hS
  have hfamily := A.restrictsTo_descendant hk hS
  exact hroot.trans hfamily.symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
