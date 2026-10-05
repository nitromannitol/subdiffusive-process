module

public import SubdiffusiveProcess.LambdaStability.Stability
public import SubdiffusiveProcess.CoarseGrainingVocab.SharpCompareJ

@[expose] public section

/-! Stability of all admissible coarse ellipticities and the scalar error norm. -/

open Homogenization hiding Vec Mat TriadicCube
open Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- `max_{z ∈ 3^k ℤ^d ∩ P} |M(x + z + cu_k; g)|` for a matrix-valued coarse quantity `M` of a set and a coefficient field. -/
def aux_l_lambdas_stability_maxNorm {d : ℕ} (x : Vec d) (P : TriadicCube d) (k : ℤ)
    (g : CoeffField d) (M : Set (Vec d) → CoeffField d → Mat d) : ℝ :=
  Ch02.finsetSupReal (Homogenization.descendantsAtScale P k)
    fun R => Ch02.matrixNorm (M (translateSet x (openCubeSet R)) g)

/-- `a_*^{-1}(V; g)` (dual coarse matrix inverse) of a set `V`. -/
def aux_l_lambdas_stability_sigmaStarInv {d : ℕ} (V : Set (Vec d)) (g : CoeffField d) : Mat d :=
  Homogenization.sigmaStarInvCoarse V g

/-- `a(V; g)` (primal coarse matrix) of a set `V`. -/
def aux_l_lambdas_stability_aMat {d : ℕ} (V : Set (Vec d)) (g : CoeffField d) : Mat d :=
  Homogenization.aCoarse (sigmaCoarse V g) (kappaCoarse V g)

/-- `λ_{t,q}^{-1}(x + P; g)`: for `q < ∞`, `((1 - 3^{-tq}) ∑_{l ≥ 0} 3^{-tql} max_z |a_*^{-1}(x+z+cu_{n-l})|^{q/2})^{2/q}`;
for `q = ∞`, `sup_l 3^{-2tl} max_z |a_*^{-1}(x+z+cu_{n-l})|`, where `n = P.scale`. -/
def aux_l_lambdas_stability_lamInv {d : ℕ} (x : Vec d) (P : TriadicCube d) (t : ℝ)
    (q : Ch02.MultiscaleExponent) (g : CoeffField d) : ℝ :=
  match q with
  | .finite q =>
      (∑' l : ℕ, Ch02.geometricWeight t q l *
        (aux_l_lambdas_stability_maxNorm x P (P.scale - (l : ℤ)) g
          aux_l_lambdas_stability_sigmaStarInv) ^ (q / 2)) ^ (2 / q)
  | .infinity =>
      sSup {M : ℝ | ∃ l : ℕ, M = Real.rpow (3 : ℝ) (-2 * t * (l : ℝ)) *
        aux_l_lambdas_stability_maxNorm x P (P.scale - (l : ℤ)) g
          aux_l_lambdas_stability_sigmaStarInv}

/-- `Λ_{t,q}(x + P; g)`, same with `|a(x+z+cu_{n-l})|` and the power `2/q` in place of `-2/q` of `λ`. -/
def aux_l_lambdas_stability_LamUp {d : ℕ} (x : Vec d) (P : TriadicCube d) (t : ℝ)
    (q : Ch02.MultiscaleExponent) (g : CoeffField d) : ℝ :=
  match q with
  | .finite q =>
      (∑' l : ℕ, Ch02.geometricWeight t q l *
        (aux_l_lambdas_stability_maxNorm x P (P.scale - (l : ℤ)) g
          aux_l_lambdas_stability_aMat) ^ (q / 2)) ^ (2 / q)
  | .infinity =>
      sSup {M : ℝ | ∃ l : ℕ, M = Real.rpow (3 : ℝ) (-2 * t * (l : ℝ)) *
        aux_l_lambdas_stability_maxNorm x P (P.scale - (l : ℤ)) g
          aux_l_lambdas_stability_aMat}

/-- `𝓔_{t,∞,2}(x + P; g, a₀)` (`p = ∞`, `q = 2`, `n = P.scale`):
`((1 - 3^{-2t}) ∑_{l ≥ 0} 3^{-2tl} max_z max_{|e|=1} J(x+z+cu_{n-l}, a₀^{-1/2}e, a₀^{1/2}e; g))^{1/2}`. -/
def aux_l_lambdas_stability_err {d : ℕ} (x : Vec d) (P : TriadicCube d) (t : ℝ)
    (g : CoeffField d) (a0 : Mat d) : ℝ :=
  Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * t)) *
    ∑' l : ℕ, Real.rpow (3 : ℝ) (-2 * t * (l : ℝ)) *
      Ch02.finsetSupReal (Homogenization.descendantsAtScale P (P.scale - (l : ℤ)))
        fun R => sSup {y : ℝ | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
          y = ResponseJ (translateSet x (openCubeSet R))
            (Homogenization.matVecMul (matrixInvSqrt a0) e)
            (Homogenization.matVecMul (matrixSqrt a0) e) g})

theorem aux_l_lambdas_stability_lamInv_eq {d : ℕ} [NeZero d]
    (x : Vec d) (P : TriadicCube d) (t : ℝ) (q : Ch02.MultiscaleExponent) (g : CoeffField d) :
    aux_l_lambdas_stability_lamInv x P t q g =
      SubdiffusiveProcess.LambdaStability.lowerInv x P t q g := by
  cases q <;> rfl

theorem aux_l_lambdas_stability_LamUp_eq {d : ℕ} [NeZero d]
    (x : Vec d) (P : TriadicCube d) (t : ℝ) (q : Ch02.MultiscaleExponent) (g : CoeffField d) :
    aux_l_lambdas_stability_LamUp x P t q g =
      SubdiffusiveProcess.LambdaStability.primalUpper x P t q g := by
  cases q <;> rfl

theorem aux_l_lambdas_stability_err_eq {d : ℕ} [NeZero d]
    (x : Vec d) (P : TriadicCube d) (t : ℝ) (g : CoeffField d) (a0 : Mat d) :
    aux_l_lambdas_stability_err x P t g a0 =
      SubdiffusiveProcess.LambdaStability.responseError x P t g
        (matrixInvSqrt a0) (matrixSqrt a0) := by
  rfl

theorem l_lambdas_stability (d : ℕ) [NeZero d] (_hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : Ch02.MultiscaleExponent, q.IsAdmissible →
      ∀ s t : ℝ, 0 < s → s < t → t ≤ 1 / 2 →
      ∀ (g : CoeffField d) (lam Lam : ℝ),
        IsEllipticFieldOn lam Lam (openCubeSet (originCube d 0)) g →
        (∀ y ∈ openCubeSet (originCube d 0), (g y).IsSymm) →
      ∀ x : Vec d,
        translateSet x (openCubeSet (originCube d (-1))) ⊆ openCubeSet (originCube d 0) →
        aux_l_lambdas_stability_lamInv x (originCube d (-1)) t q g ≤
            C / (1 - 2 * s) *
              (match q with
                | .finite q => Real.rpow (t / (t - s)) (2 / q)
                | .infinity => 1) *
              aux_l_lambdas_stability_lamInv 0 (originCube d 0) s q g ∧
        aux_l_lambdas_stability_LamUp x (originCube d (-1)) t q g ≤
            C / (1 - 2 * s) *
              (match q with
                | .finite q => Real.rpow (t / (t - s)) (2 / q)
                | .infinity => 1) *
              aux_l_lambdas_stability_LamUp 0 (originCube d 0) s q g ∧
        ∀ a0 : Mat d, a0.PosDef →
          aux_l_lambdas_stability_err x (originCube d (-1)) t g a0 ≤
            C / Real.sqrt (1 - 2 * s) * Real.sqrt (t / (t - s)) *
              aux_l_lambdas_stability_err 0 (originCube d 0) s g a0 := by
  refine ⟨SubdiffusiveProcess.LambdaStability.stabilityConstant d,
    SubdiffusiveProcess.LambdaStability.stabilityConstant_pos d, ?_⟩
  intro q hq s t hs hst ht g lam Lam hEll hsym x hx
  have hmain := SubdiffusiveProcess.LambdaStability.stability_on_origin hq hs hst ht hEll hsym hx
  simp only [aux_l_lambdas_stability_lamInv_eq, aux_l_lambdas_stability_LamUp_eq,
    aux_l_lambdas_stability_err_eq]
  simp only [SubdiffusiveProcess.LambdaStability.indexFactor] at hmain
  refine ⟨hmain.1, hmain.2.1, ?_⟩
  intro a0 _ha0
  exact hmain.2.2 (matrixInvSqrt a0) (matrixSqrt a0)

end SubdiffusiveProcess.Paper
