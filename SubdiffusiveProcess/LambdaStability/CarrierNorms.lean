module

public import SubdiffusiveProcess.LambdaStability.WeightedSum
public import SubdiffusiveProcess.LambdaStability.MatrixCaps

@[expose] public section

/-! General exponent translated ellipticity carriers. -/
open Homogenization Homogenization.Book Homogenization.Book.Ch02
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.LambdaStability

/-- The geometric multiscale norm of a nonnegative shell sequence. -/
def shellNorm (t : ℝ) (q : Ch02.MultiscaleExponent) (M : ℕ → ℝ) : ℝ :=
  match q with
  | .finite q => (∑' l : ℕ, Ch02.geometricWeight t q l * M l ^ (q / 2)) ^ (2 / q)
  | .infinity => sSup {y : ℝ | ∃ l : ℕ, y = (3 : ℝ) ^ (-2 * t * (l : ℝ)) * M l}

/-- The factor from the outer weighted sum. -/
def indexFactor (q : Ch02.MultiscaleExponent) (s t : ℝ) : ℝ :=
  match q with
  | .finite q => (t / (t - s)) ^ (2 / q)
  | .infinity => 1

theorem shellNorm_le_of_shell_cap {s t A : ℝ} {q : Ch02.MultiscaleExponent}
    (hs : 0 < s) (hst : s < t) (hq : q.IsAdmissible) (hA : 0 ≤ A)
    (M : ℕ → ℝ) (hM0 : ∀ l, 0 ≤ M l)
    (hM : ∀ l, M l ≤ A * (3 : ℝ) ^ (2 * s * (l : ℝ))) :
    shellNorm t q M ≤ indexFactor q s t * A := by
  cases q with
  | finite q =>
      exact finite_norm_le_of_shell_cap hs hst (lt_of_lt_of_le zero_lt_one hq) hA M hM0 hM
  | infinity =>
      change sSup _ ≤ 1 * A
      rw [one_mul]
      refine csSup_le ⟨_, ⟨0, rfl⟩⟩ ?_
      rintro y ⟨l, rfl⟩
      calc
        (3 : ℝ) ^ (-2 * t * (l : ℝ)) * M l ≤
            (3 : ℝ) ^ (-2 * t * (l : ℝ)) * (A * (3 : ℝ) ^ (2 * s * (l : ℝ))) :=
          mul_le_mul_of_nonneg_left (hM l) (Real.rpow_nonneg (by norm_num) _)
        _ = A * (3 : ℝ) ^ (2 * (s - t) * (l : ℝ)) := by
          rw [show (3 : ℝ) ^ (-2 * t * (l : ℝ)) * (A * (3 : ℝ) ^ (2 * s * (l : ℝ))) =
            A * ((3 : ℝ) ^ (-2 * t * (l : ℝ)) * (3 : ℝ) ^ (2 * s * (l : ℝ))) by ring,
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          congr 2
          ring
        _ ≤ A * 1 := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg l))
        _ = A := mul_one A

variable {d : ℕ} [NeZero d]

def lowerInv (w : Vec d) (P : TriadicCube d) (t : ℝ) (q : Ch02.MultiscaleExponent)
    (g : CoeffField d) : ℝ :=
  shellNorm t q (fun l => offGridSigmaStarInvShellMax w P (P.scale - (l : ℤ)) g)

def upper (w : Vec d) (P : TriadicCube d) (t : ℝ) (q : Ch02.MultiscaleExponent)
    (g : CoeffField d) : ℝ :=
  shellNorm t q (fun l => offGridBShellMax w P (P.scale - (l : ℤ)) g)

theorem lowerInv_zero_eq (P : TriadicCube d) (t : ℝ) (q : Ch02.MultiscaleExponent)
    (ht : 0 < t) (hq : q.IsAdmissible)
    (A : TriadicCoeffFamily d) (g : CoeffField d)
    (hg : ∀ R : TriadicCube d, (A.coeffOn R).toCoeffField = g) :
    lowerInv 0 P t q g = (Ch02.lambdaSq P t q A)⁻¹ := by
  cases q with
  | finite q =>
      simp only [lowerInv, shellNorm, Ch02.lambdaSq, Ch02.lambdaSqFinite,
        offGridSigmaStarInvShellMax_zero_eq P _ A g hg, Real.rpow_eq_pow]
      have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
      have hsum0 : 0 ≤ ∑' l : ℕ, Ch02.geometricWeight t q l *
          (maxDescendantSigmaStarInvMatrixNormAtScale P (P.scale - (l : ℤ)) A) ^ (q / 2) := by
        apply tsum_nonneg
        intro l
        apply mul_nonneg
        · unfold Ch02.geometricWeight
          exact mul_nonneg (Homogenization.geometricDiscount_pos (mul_pos ht hq0)).le
            (Real.rpow_nonneg (by norm_num) _)
        · exact Real.rpow_nonneg
            (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg P (by omega) A) _
      rw [Real.rpow_neg hsum0, inv_inv]
  | infinity =>
      simp only [lowerInv, shellNorm, Ch02.lambdaSq, Ch02.lambdaSqInfinity, inv_inv,
        offGridSigmaStarInvShellMax_zero_eq P _ A g hg, Real.rpow_eq_pow]


end SubdiffusiveProcess.LambdaStability
