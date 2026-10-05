module

public import SubdiffusiveProcess.CoarseGrainingVocab.SharpCompareJ
public import SubdiffusiveProcess.Vocab.PaperHomogenizationError

@[expose] public section

/-!
Definition `d.mathcal.E` (homogenization error `ℰ_{s,p,q}(cu_m, n; a, a₀)`) with a MATRIX reference coefficient `a₀ ∈ ℝ^{d×d}_{sym,+}`
(the `SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError` has only a scalar `alpha`, i.e. `a₀ = alpha • 1`).  `ℰ` is `ℝ≥0∞`-valued, so that the
suprema, the `tsum`, and the powers are total and no junk value `0` can occur for a divergent sum.  Cubes are the triadic cubes `z + cu_l`,
`z ∈ 3^l ℤ^d` (`TriadicCube`, `descendantsAtScale`); the probes are `J(z + cu_l, a₀^{-1/2} e, a₀^{1/2} e; a)` with `a₀^{±1/2}` the symmetric
(inverse) square roots (`CFC.sqrt`).  `aux_d_mathcal_E_eq_paperHomogenizationError` identifies the scalar case with the definition.
-/

open Homogenization hiding Vec Mat TriadicCube
open Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal Matrix.Norms.L2Operator MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- `max_{|e|=1} J(R, a₀^{-1/2} e, a₀^{1/2} e; a)` on one triadic cube `R`. -/
def aux_d_mathcal_E_probeMax {d : ℕ} (R : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d) : ℝ≥0∞ :=
  ⨆ e : {e : Vec d // Homogenization.vecNormSq e = 1},
    ENNReal.ofReal (J (Ch02.cubeDomain R) (a.coeffOn R)
      (Homogenization.matVecMul (matrixInvSqrt a0) e.1)
      (Homogenization.matVecMul (matrixSqrt a0) e.1))

/-- The `p`-aggregation over the cubes of scale `k` inside `Q`:
`(avsum_z (max_e J)^{p/2})^{1/p}` for `p < ∞`, `(max_z max_e J)^{1/2}` for `p = ∞`. -/
def aux_d_mathcal_E_scaleResponse {d : ℕ} (Q : TriadicCube d) (k : ℤ)
    (p : Ch02.MultiscaleExponent) (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d) : ℝ≥0∞ :=
  match p with
  | .finite p =>
      (((Homogenization.descendantsAtScale Q k).card : ℝ≥0∞)⁻¹ *
          ∑ R ∈ Homogenization.descendantsAtScale Q k,
            (aux_d_mathcal_E_probeMax R a a0) ^ (p / 2)) ^ (1 / p)
  | .infinity =>
      (⨆ R : {R : TriadicCube d // R ∈ Homogenization.descendantsAtScale Q k},
        aux_d_mathcal_E_probeMax R a a0) ^ (1 / 2 : ℝ)

/-- **Homogenization error** `ℰ_{s,p,q}(Q, n; a, a₀)` of Definition `d.mathcal.E`, for `s ∈ (0,1]`, `p, q ∈ [1,∞]`, `n ≤ m = Q.scale`,
a coefficient family `a` on the cube `Q`, and a reference matrix `a₀`:
`q < ∞`: `((1 - 3^{-sq}) ∑_{l ≤ n} 3^{-sq(n-l)} (scaleResponse_l)^q)^{1/q}`; `q = ∞`: `sup_{l ≤ n} 3^{-s(n-l)} scaleResponse_l`. -/
def d_mathcal_E {d : ℕ} (Q : TriadicCube d) (n : ℤ) (s : ℝ)
    (p q : Ch02.MultiscaleExponent) (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d) : ℝ≥0∞ :=
  match q with
  | .finite q =>
      (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s q l) *
        (aux_d_mathcal_E_scaleResponse Q (n - (l : ℤ)) p a a0) ^ q) ^ (1 / q)
  | .infinity =>
      ⨆ l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-s * (l : ℝ))) *
        aux_d_mathcal_E_scaleResponse Q (n - (l : ℤ)) p a a0

theorem aux_d_mathcal_E_sqrt_smul_one {d : ℕ} (α : ℝ) (hα : 0 < α) :
    matrixSqrt (α • (1 : Mat d)) = Real.sqrt α • (1 : Mat d) := by
  unfold matrixSqrt
  let a : NNReal := ⟨α, hα.le⟩
  have ha : (a : ℝ) = α := rfl
  clear_value a
  have h : α • (1 : Mat d) = algebraMap NNReal (Mat d) a := by
    simp [Algebra.algebraMap_eq_smul_one, NNReal.smul_def, ha]
  rw [h, CFC.sqrt_algebraMap]
  simp [Algebra.algebraMap_eq_smul_one, NNReal.smul_def, Real.coe_sqrt, ha]

theorem aux_d_mathcal_E_invSqrt_smul_one {d : ℕ} (α : ℝ) (hα : 0 < α) :
    matrixInvSqrt (α • (1 : Mat d)) = (Real.sqrt α)⁻¹ • (1 : Mat d) := by
  have h1 : CFC.sqrt (α • (1 : Mat d)) = Real.sqrt α • (1 : Mat d) :=
    aux_d_mathcal_E_sqrt_smul_one α hα
  unfold matrixInvSqrt
  rw [h1]
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  refine Matrix.inv_eq_right_inv ?_
  simp [smul_smul, hs.ne']

theorem aux_d_mathcal_E_matVecMul_smul_one {d : ℕ} (c : ℝ) (e : Vec d) :
    Homogenization.matVecMul (c • (1 : Mat d)) e = c • e := by
  ext i
  simp [Homogenization.matVecMul, Matrix.smul_apply, Matrix.one_apply,
    Finset.sum_ite_eq]

/-- For a scalar reference `a₀ = alpha • 1` the definition is the `paperHomogenizationError`. -/
theorem aux_d_mathcal_E_eq_paperHomogenizationError {d : ℕ} (Q : TriadicCube d) (n : ℤ) (s : ℝ)
    (p q : Ch02.MultiscaleExponent) (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) (halpha : 0 < alpha) :
    d_mathcal_E Q n s p q a (alpha • (1 : Mat d)) = paperHomogenizationError Q n s p q a alpha := by
  have hprobe : ∀ R : TriadicCube d,
      aux_d_mathcal_E_probeMax R a (alpha • (1 : Mat d)) = paperScalarProbeMax R a alpha := by
    intro R
    simp only [aux_d_mathcal_E_probeMax, paperScalarProbeMax, paperScalarProbe,
      aux_d_mathcal_E_invSqrt_smul_one alpha halpha, aux_d_mathcal_E_sqrt_smul_one alpha halpha,
      aux_d_mathcal_E_matVecMul_smul_one]
  have hscale : ∀ (k : ℤ) (p : Ch02.MultiscaleExponent),
      aux_d_mathcal_E_scaleResponse Q k p a (alpha • (1 : Mat d)) =
        paperScaleResponseAtScale Q k p a alpha := by
    intro k p
    cases p <;> simp only [aux_d_mathcal_E_scaleResponse, paperScaleResponseAtScale,
      paperMaxDescendantProbeAtScale, hprobe]
  cases q <;> simp only [d_mathcal_E, paperHomogenizationError, paperHomogenizationErrorFinite,
    paperHomogenizationErrorInfinity, hscale]

end SubdiffusiveProcess.Paper
