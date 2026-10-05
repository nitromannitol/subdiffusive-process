module

public import SubdiffusiveProcess.LambdaStability.ScalarTransport

@[expose] public section

/-! Identification and locality of the literal scalar and symmetric matrix quantities. -/
open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.LambdaStability
variable {d : ℕ} [NeZero d]

def primalShell (w : Vec d) (P : TriadicCube d) (k : ℤ) (g : CoeffField d) : ℝ :=
  Ch02.finsetSupReal (descendantsAtScale P k) (fun R => Ch02.matrixNorm
    (Homogenization.aCoarse (sigmaCoarse (translateSet w (openCubeSet R)) g)
      (kappaCoarse (translateSet w (openCubeSet R)) g)))

def primalUpper (w : Vec d) (P : TriadicCube d) (t : ℝ)
    (q : Ch02.MultiscaleExponent) (g : CoeffField d) : ℝ :=
  shellNorm t q (fun l => primalShell w P (P.scale - (l : ℤ)) g)

def responseError (w : Vec d) (P : TriadicCube d) (t : ℝ)
    (g : CoeffField d) (B A : Mat d) : ℝ :=
  Real.sqrt ((1 - (3 : ℝ) ^ (-2 * t)) * ∑' l : ℕ,
    (3 : ℝ) ^ (-2 * t * (l : ℝ)) * probeShell w P (P.scale - (l : ℤ)) g B A)

omit [NeZero d] in
theorem responseError_eq_probeError (w : Vec d) (P : TriadicCube d) (t : ℝ)
    (g : CoeffField d) (B A : Mat d) :
    responseError w P t g B A = probeError w P t g B A := by
  unfold responseError probeError probeEnergy
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro l
  unfold Ch02.geometricWeight Ch02.geometricDiscount
  simp only [Real.rpow_eq_pow]
  rw [show -t * 2 = -2 * t by ring]
  ring

theorem primalUpper_eq_upper (w : Vec d) (P : TriadicCube d) (t : ℝ)
    (q : Ch02.MultiscaleExponent) {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam Set.univ g) (hsym : IsSymmetricCoeffField g) :
    primalUpper w P t q g = upper w P t q g := by
  apply congrArg (shellNorm t q)
  funext l
  unfold primalShell offGridBShellMax offGridBMatrixNorm
  apply Ch02.finsetSupReal_congr
  intro R _
  exact congrArg Ch02.matrixNorm (aCoarse_eq_bCoarse (translatedDomain w R)
    (hEll.mono (translatedDomain w R).measurableSet (Set.subset_univ _)) hsym)

theorem upper_zero_eq (P : TriadicCube d) (t : ℝ) (q : Ch02.MultiscaleExponent)
    (A : Ch02.TriadicCoeffFamily d) (g : CoeffField d) {lam Lam : ℝ}
    (hg : ∀ R : TriadicCube d, (A.coeffOn R).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam Set.univ g) :
    upper 0 P t q g = Ch02.LambdaSq P t q A := by
  have hgw : ∀ R : TriadicCube d, (A.coeffOn R).toCoeffField = translateCoeffField 0 g := by
    intro R
    rw [hg R]
    funext x
    simp only [translateCoeffField, Pi.zero_apply, add_zero]
  have hEllP : IsEllipticFieldOn lam Lam (translateSet 0 (cubeSet P)) g := by
    rw [translateSet_zero]
    exact hEll.mono (measurableSet_cubeSet P) (Set.subset_univ _)
  have hshell : ∀ l : ℕ, offGridBShellMax 0 P (P.scale - (l : ℤ)) g =
      Ch02.maxDescendantBMatrixNormAtScale P (P.scale - (l : ℤ)) A :=
    fun l => offGridBShellMax_eq_translated A 0 P g hgw (by omega) hEllP
  cases q <;> simp only [upper, shellNorm, hshell, Ch02.LambdaSq,
    Ch02.LambdaSqFinite, Ch02.LambdaSqInfinity, Real.rpow_eq_pow]

omit [NeZero d] in
theorem literalShells_eq_of_eqOn (U : Ch02.Domain d) {w : Vec d} {P : TriadicCube d}
    {k : ℤ} (hk : k ≤ P.scale) {g h : CoeffField d} {lam Lam lam' Lam' : ℝ}
    (hg : IsEllipticFieldOn lam Lam (U : Set (Vec d)) g)
    (hh : IsEllipticFieldOn lam' Lam' Set.univ h)
    (heq : Set.EqOn g h (U : Set (Vec d)))
    (hsub : translateSet w (openCubeSet P) ⊆ (U : Set (Vec d))) :
    offGridSigmaStarInvShellMax w P k g = offGridSigmaStarInvShellMax w P k h ∧
    primalShell w P k g = primalShell w P k h ∧
    ∀ B A : Mat d, probeShell w P k g B A = probeShell w P k h B A := by
  have hlocal : ∀ R ∈ descendantsAtScale P k,
      (∀ p q, ResponseJ (translateSet w (openCubeSet R)) p q g =
        ResponseJ (translateSet w (openCubeSet R)) p q h) ∧
      Homogenization.sigmaStarInvCoarse (translateSet w (openCubeSet R)) g =
        Homogenization.sigmaStarInvCoarse (translateSet w (openCubeSet R)) h ∧
      sigmaCoarse (translateSet w (openCubeSet R)) g = sigmaCoarse (translateSet w (openCubeSet R)) h ∧
      kappaCoarse (translateSet w (openCubeSet R)) g = kappaCoarse (translateSet w (openCubeSet R)) h := by
    intro R hR
    have hRU : translateSet w (openCubeSet R) ⊆ (U : Set (Vec d)) := by
      intro z hz
      apply hsub
      exact mem_translateSet_iff_sub_mem.2 (openCubeSet_subset_of_mem_descendantsAtScale hk hR
        (mem_translateSet_iff_sub_mem.1 hz))
    exact carriers_eq_of_eqOn (translatedDomain w R)
      (hg.mono (translatedDomain w R).measurableSet hRU)
      (hh.mono (translatedDomain w R).measurableSet (Set.subset_univ _))
      (heq.mono hRU)
  refine ⟨?_, ?_, ?_⟩
  · unfold offGridSigmaStarInvShellMax offGridSigmaStarInvMatrixNorm
    exact Ch02.finsetSupReal_congr _ (fun R hR => congrArg Ch02.matrixNorm (hlocal R hR).2.1)
  · unfold primalShell
    apply Ch02.finsetSupReal_congr
    intro R hR
    rw [(hlocal R hR).2.2.1, (hlocal R hR).2.2.2]
  · intro B A
    unfold probeShell
    apply Ch02.finsetSupReal_congr
    intro R hR
    unfold probeMax
    simp only [(hlocal R hR).1]

omit [NeZero d] in
theorem literalQuantities_eq_of_eqOn (U : Ch02.Domain d) {w : Vec d} {P : TriadicCube d}
    (t : ℝ) (q : Ch02.MultiscaleExponent) {g h : CoeffField d} {lam Lam lam' Lam' : ℝ}
    (hg : IsEllipticFieldOn lam Lam (U : Set (Vec d)) g)
    (hh : IsEllipticFieldOn lam' Lam' Set.univ h)
    (heq : Set.EqOn g h (U : Set (Vec d)))
    (hsub : translateSet w (openCubeSet P) ⊆ (U : Set (Vec d))) :
    lowerInv w P t q g = lowerInv w P t q h ∧
    primalUpper w P t q g = primalUpper w P t q h ∧
    ∀ B A : Mat d, responseError w P t g B A = responseError w P t h B A := by
  have hshell := fun l : ℕ => literalShells_eq_of_eqOn U (k := P.scale - (l : ℤ))
    (by omega) hg hh heq hsub
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (shellNorm t q) (funext (fun l => (hshell l).1))
  · exact congrArg (shellNorm t q) (funext (fun l => (hshell l).2.1))
  · intro B A
    unfold responseError
    simp only [(hshell _).2.2 B A]

end SubdiffusiveProcess.LambdaStability
