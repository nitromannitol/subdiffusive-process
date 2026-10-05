module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepVariationalClosure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryProjectionSymmetry

@[expose] public section

/-!
# Trace reduction for the stationary one-step projection

The signed-coordinate symmetry of the literal GMC carrier is now proved in
`StationaryProjectionSymmetry`.  This file performs the finite-dimensional
trace algebra  and exposes the sole remaining
analytic input: the trace-one identity for the stationary Helmholtz
projection applied to the centered suffix multiplier.


-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A linear Hilbert-valued map whose covariance on the coordinate vectors is
`c I` has energy `c |p|²` in every direction. -/
theorem norm_sq_linearMap_eq_mul_vecNormSq_of_coordinate_covariance
    {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : Vec d →ₗ[ℝ] H) (c : ℝ)
    (hcov : ∀ i j : Fin d,
      inner ℝ (T (Pi.single i 1)) (T (Pi.single j 1)) =
        if i = j then c else 0)
    (p : Vec d) :
    ‖T p‖ ^ 2 = c * vecNormSq p := by
  have hp : p = ∑ i : Fin d, p i • (Pi.single i 1 : Vec d) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · simp
  calc
    ‖T p‖ ^ 2 = inner ℝ (T p) (T p) :=
      (real_inner_self_eq_norm_sq (T p)).symm
    _ = inner ℝ
        (T (∑ i : Fin d, p i • (Pi.single i 1 : Vec d)))
        (T (∑ i : Fin d, p i • (Pi.single i 1 : Vec d))) := by rw [← hp]
    _ = ∑ i : Fin d, p i * (p i * c) := by
      simp only [map_sum, map_smul, inner_sum, sum_inner,
        real_inner_smul_left, real_inner_smul_right, hcov]
      simp
    _ = c * vecNormSq p := by
      rw [vecNormSq, vecDot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Pairwise orthogonality, equality of the coordinate energies, and their
finite trace determine the covariance matrix completely. -/
theorem norm_sq_linearMap_eq_div_mul_vecNormSq_of_coordinate_symmetry_and_trace
    {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : Vec d →ₗ[ℝ] H) (V : ℝ) (hd : 0 < d)
    (hoff : ∀ i j : Fin d, i ≠ j →
      inner ℝ (T (Pi.single i 1)) (T (Pi.single j 1)) = 0)
    (hdiag : ∀ i j : Fin d,
      ‖T (Pi.single i 1)‖ ^ 2 = ‖T (Pi.single j 1)‖ ^ 2)
    (htrace : ∑ i : Fin d, ‖T (Pi.single i 1)‖ ^ 2 = V)
    (p : Vec d) :
    ‖T p‖ ^ 2 = (V / (d : ℝ)) * vecNormSq p := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hcoordinate : ∀ i : Fin d,
      ‖T (Pi.single i 1)‖ ^ 2 = V / (d : ℝ) := by
    intro i
    have hsum :
        ∑ j : Fin d, ‖T (Pi.single j 1)‖ ^ 2 =
          ∑ _j : Fin d, ‖T (Pi.single i 1)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact hdiag j i
    have hmul : V = (d : ℝ) * ‖T (Pi.single i 1)‖ ^ 2 := by
      calc
        V = ∑ j : Fin d, ‖T (Pi.single j 1)‖ ^ 2 := htrace.symm
        _ = ∑ _j : Fin d, ‖T (Pi.single i 1)‖ ^ 2 := hsum
        _ = (d : ℝ) * ‖T (Pi.single i 1)‖ ^ 2 := by
          simp [nsmul_eq_mul]
    apply (eq_div_iff hdR).2
    rw [hmul]
    ring
  apply norm_sq_linearMap_eq_mul_vecNormSq_of_coordinate_covariance T
    (V / (d : ℝ))
  intro i j
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, real_inner_self_eq_norm_sq]
    exact hcoordinate i
  · rw [ite_eq_right hij]
    exact hoff i j hij

/-- The proved reflection/permutation symmetry reduces the exact one-step
energy formula to the scalar trace identity alone. -/
theorem oneStepProjectedEnergy_eq_suffixVariance_div_dimension_of_trace
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h)
    (htrace : ∑ i : Fin d,
      ‖oneStepPotentialProjection M n h (Pi.single i 1) hh‖ ^ 2 =
        (oneShellCenteredExpTwoMoment M) ^ h - 1) :
    oneStepProjectedEnergy M n h p hh =
      (((oneShellCenteredExpTwoMoment M) ^ h - 1) / (d : ℝ)) *
        vecNormSq p := by
  exact norm_sq_linearMap_eq_div_mul_vecNormSq_of_coordinate_symmetry_and_trace
    (oneStepPotentialProjectionLinear M n h hh)
    ((oneShellCenteredExpTwoMoment M) ^ h - 1)
    (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)
    (fun i j hij => inner_oneStepPotentialProjection_basis_ne_eq_zero
      M n h i j hij hh)
    (fun i j => norm_sq_oneStepPotentialProjection_basis_eq M n h i j hh)
    htrace p

/-- Unit-probe form consumed by the one-step variational estimates. -/
theorem oneStepProjectedEnergy_eq_suffixVariance_div_dimension_of_trace_unit
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (htrace : ∑ i : Fin d,
      ‖oneStepPotentialProjection M n h (Pi.single i 1) hh‖ ^ 2 =
        (oneShellCenteredExpTwoMoment M) ^ h - 1) :
    oneStepProjectedEnergy M n h p hh =
      ((oneShellCenteredExpTwoMoment M) ^ h - 1) / (d : ℝ) := by
  rw [oneStepProjectedEnergy_eq_suffixVariance_div_dimension_of_trace
    M n h p hh htrace, hp, mul_one]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
