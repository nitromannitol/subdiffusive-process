module

public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridComposeAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridMatrixCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridLambdaTwo
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.FinitePAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization Homogenization.Book Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The arbitrary-translate `𝒠_{t,∞,2}` stability estimate supplied by the
mirrored off-grid cover, response-subadditivity, packing, and geometric-series
chain.  The exact-representative premise is carrier compatibility: it holds
definitionally for coefficient families built from one ambient field.

This is an honestly named specialization, not the full all-`p,q` source lemma.
-/
theorem mathcalE_stability_infinity_two_of_exact_representative
    {w : Vec d} {P K : TriadicCube d} {g : CoeffField d}
    {lam Lam : ℝ} (A : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {t s : ℝ} (hs0 : 0 < s) (hst : s < t) (ht : t ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    LambdaStabilitySupport.offGridErrorFunctional w P t g a0 ≤
      Real.sqrt (LambdaStabilitySupport.offGridStabilityConst d t s) *
        ((3 : ℝ) ^ (s * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          Ch02.HomogenizationErrorOnCube K s .infinity (.finite 2) A a0) :=
  LambdaStabilitySupport.offGridErrorFunctional_le A a0 hs0 hst ht hg hEll hcontain

/-- The complete arbitrary-translate lower-ellipticity display at `q = 2`.
The translated carrier agrees exactly with `Ch02.lambdaSq⁻¹` at zero
translate; see `offGridLambdaSqInvTwo_zero_eq`. -/
theorem lambdaSq_stability_two_of_exact_representative
    {w : Vec d} {P K : TriadicCube d} {g : CoeffField d}
    {lam Lam : ℝ} (A : Ch02.TriadicCoeffFamily d)
    {t s : ℝ} (hs0 : 0 < s) (hst : s < t) (ht : t ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    LambdaStabilitySupport.offGridLambdaSqInvTwo w P t g ≤
      LambdaStabilitySupport.offGridStabilityConst d t s *
        ((3 : ℝ) ^ (2 * s * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          (Ch02.lambdaSq K s (.finite 2) A)⁻¹) :=
  LambdaStabilitySupport.offGridLambdaSqInvTwo_le A hs0 hst ht hg hEll hcontain

end

end SubdiffusiveProcess.CoarseGrainingVocab
