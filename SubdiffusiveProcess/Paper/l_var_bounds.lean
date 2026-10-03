module

public import Homogenization.Book.Ch04.RestrictionLaw
public import Homogenization.Book.Ch04.Theorems.Expectations
public import SubdiffusiveProcess.Variance.Assembly
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The operator norm `|A|` of a matrix (Section 1.5 notation of the paper). -/
def aux_l_var_bounds_opNorm {d : ℕ} (A : Mat d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖

/-- `var[M] = 𝔼[|M - 𝔼 M|²]` of a random matrix, as an extended nonnegative number (`𝔼 M` entrywise). -/
def aux_l_var_bounds_var {d : ℕ} (P : Measure (RegCoeffField d)) (M : RegCoeffField d → Mat d) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal
    (aux_l_var_bounds_opNorm (M a - Matrix.of fun i j => ∫ b, M b i j ∂P) ^ 2) ∂P

/-- The coarse-grained matrix `a_*^{-1}(Q)` of the field `a` on the triadic cube `Q`. -/
def aux_l_var_bounds_aStarInv {d : ℕ} (Q : TriadicCube d) (a : RegCoeffField d) : Mat d :=
  (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerRight

/-- Lemma `l.var.bounds` (variance estimate), with symmetry stated modulo spatial null sets.
The actual finite-cutoff law witnesses this premise via the rational-ball symmetry event.

Data of the live statement: a `ℤ^d`-stationary random field `a` (a probability law `P` on the carrier
`RegCoeffField d`, `IsStationaryR P`, i.e. invariant under integer translations) with values in `ℝ^{d×d}_{sym,+}`
(almost every realization is symmetric and locally uniformly elliptic), integers `k < n`, and a positive definite
`β`.  With `cu_n = originCube d n`, the cubes `z + cu_k`, `z ∈ 3^k ℤ^d ∩ cu_n`, are the descendants of `cu_n` at
scale `k`, `avsum` is the arithmetic average over them, `var[M] = 𝔼|M - 𝔼M|²` (operator norm), and the
right-hand side is `2 var[avsum_z a_*^{-1}(z+cu_k)] + 32 𝔼[(avsum_z ∑_i J(z+cu_k, β^{-1} e_i, e_i; a))²]`.
Variances and the last expectation are extended-nonnegative valued, so the inequality carries no integrability
hypothesis (a non-square-integrable `a_*^{-1}(cu_n)` makes both variances infinite). -/
theorem l_var_bounds {d : ℕ} (P : Measure (RegCoeffField d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryR P)
    (hsymm : ∀ᵐ a ∂P, ∀ᵐ x ∂volume, (a.toFun x).IsSymm)
    (hell : Ch04.AELocallyUniformlyEllipticLaw P)
    (n k : ℤ) (hkn : k < n) (β : Mat d) (hβ : β.PosDef) :
    aux_l_var_bounds_var P (fun a => aux_l_var_bounds_aStarInv (originCube d n) a) ≤
      2 * aux_l_var_bounds_var P (fun a =>
        ((descendantsAtScale (originCube d n) k).card : ℝ)⁻¹ •
          ∑ R ∈ descendantsAtScale (originCube d n) k, aux_l_var_bounds_aStarInv R a) +
      32 * ∫⁻ a, ENNReal.ofReal
        ((((descendantsAtScale (originCube d n) k).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtScale (originCube d n) k,
            ∑ i : Fin d, ResponseJ (cubeSet R) (matVecMul β⁻¹ (Pi.single i 1)) (Pi.single i 1) a.toFun) ^ 2)
        ∂P := by
  have _ := hstat
  exact SubdiffusiveProcess.Variance.var_bounds P hsymm hell n k hkn β hβ

end Paper
