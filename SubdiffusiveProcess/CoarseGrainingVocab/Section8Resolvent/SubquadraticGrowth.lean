module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.SubquadraticGrowthShell
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.AnchoredGrowth
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceEstimatesUniqueness

@[expose] public section

/-!
# Almost-sure subquadratic growth of a finite GMC cutoff

For a fixed cutoff only finitely many shells occur.  The growing-ball `(g2)`
envelope therefore bounds its logarithm by a random multiple of the square
root of the dyadic scale.  Absorbing this square root into a fixed linear
dyadic slope gives a pathwise linear spatial majorant, hence the
subquadratic sequence required by whole-space resolvent uniqueness.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open _root_.SubdiffusiveProcess.Model
open _root_.SubdiffusiveProcess.Section8
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The deterministic prefactor obtained by absorbing the finite-shell
`sqrt (n+1)` price into the dyadic exponent `absorbEps`.

-/
def finiteCutoffLinearGrowthConstant
    (M : GMCModel d) (L : ℕ) (C : ℝ) : ℝ :=
  8 * Real.exp
    (((((L : ℝ) + 1) * C * Real.sqrt ((L : ℝ) + 1)) ^ 2 /
        (4 * absorbEps)) + ((L : ℝ) + 1) * |tauSq M.P|)

theorem finiteCutoffLinearGrowthConstant_nonneg
    (M : GMCModel d) (L : ℕ) (C : ℝ) :
    0 ≤ finiteCutoffLinearGrowthConstant M L C := by
  rw [finiteCutoffLinearGrowthConstant]
  positivity

/-- A simultaneous growing-ball shell-value bound implies a global linear
growth bound for the finite cutoff coefficient.

-/
theorem aCutoff_le_linear_of_growingBall_shell_abs_bound
    (M : GMCModel d) (L : ℕ) (omega : PotentialSample d) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ n k : ℕ, ∀ x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
      |omega k x| ≤ C * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) :
    ∀ x : Vec d,
      aCutoff M L omega x ≤
        finiteCutoffLinearGrowthConstant M L C * (1 + ‖x‖) := by
  intro x
  let n : ℕ := dyadicIndex x
  have hnorm : ‖x‖ ≤ (2 : ℝ) ^ n := by
    have h := two_add_norm_le_two_pow_dyadicIndex x
    linarith
  have hxball : x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n) :=
    mem_closedBall_growingBallRadius hnorm
  let E : ℝ := ((L + 1 : ℕ) : ℝ) * C *
    Real.sqrt ((L : ℝ) + 1)
  let D : ℝ := ((L + 1 : ℕ) : ℝ) * |tauSq M.P|
  have hshell : ∀ k ∈ Finset.range (L + 1),
      omega k x - tauSq M.P ≤
        C * Real.sqrt ((n : ℝ) + 1) *
          Real.sqrt ((L : ℝ) + 1) + |tauSq M.P| := by
    intro k hk
    have hkL : k ≤ L := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
    have habs := hC n k x hxball
    have hsqrt : Real.sqrt ((n : ℝ) + (k : ℝ) + 1) ≤
        Real.sqrt ((n : ℝ) + 1) *
          Real.sqrt ((L : ℝ) + 1) := by
      refine (sqrt_natAdd_le_mul n k).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
        (Real.sqrt_nonneg _)
      exact_mod_cast Nat.add_le_add_right hkL 1
    have hvalue : omega k x ≤
        C * Real.sqrt ((n : ℝ) + 1) *
          Real.sqrt ((L : ℝ) + 1) := by
      calc
        omega k x ≤ |omega k x| := le_abs_self _
        _ ≤ C * Real.sqrt ((n : ℝ) + (k : ℝ) + 1) := habs
        _ ≤ C * (Real.sqrt ((n : ℝ) + 1) *
            Real.sqrt ((L : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hsqrt hC0
        _ = C * Real.sqrt ((n : ℝ) + 1) *
            Real.sqrt ((L : ℝ) + 1) := by ring
    linarith [neg_le_abs (tauSq M.P)]
  have hsum :
      ∑ k ∈ Finset.range (L + 1), (omega k x - tauSq M.P) ≤
        E * Real.sqrt ((n : ℝ) + 1) + D := by
    calc
      ∑ k ∈ Finset.range (L + 1), (omega k x - tauSq M.P) ≤
      ∑ _k ∈ Finset.range (L + 1),
            (C * Real.sqrt ((n : ℝ) + 1) *
              Real.sqrt ((L : ℝ) + 1) + |tauSq M.P|) :=
        Finset.sum_le_sum hshell
      _ = E * Real.sqrt ((n : ℝ) + 1) + D := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        dsimp [E, D]
        push_cast
        ring
  have hT0 : 0 ≤ (n : ℝ) + 1 := by positivity
  have habsorb := mul_sqrt_le_absorb (E := E) hT0
  have hlog :
      ∑ k ∈ Finset.range (L + 1), (omega k x - tauSq M.P) ≤
        absorbEps * ((n : ℝ) + 1) +
          (E ^ 2 / (4 * absorbEps) + D) := by
    linarith
  have hslope : 0 ≤ absorbEps := absorbEps_pos.le
  have hslopeLe : absorbEps ≤ 3 * Real.log 2 / 4 := by
    rw [absorbEps]
    have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    linarith
  have hdyadic := exp_mul_dyadic_le hslope hslopeLe x
  have hbase : (1 : ℝ) ≤ 1 + ‖x‖ := by
    linarith [norm_nonneg x]
  have hrpow : (1 + ‖x‖) ^ anchoredKappa ≤ 1 + ‖x‖ := by
    have hkappa : anchoredKappa ≤ (1 : ℝ) := anchoredKappa_mem.2.le
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase hkappa
  rw [aCutoff]
  calc
    Real.exp (∑ k ∈ Finset.range (L + 1), (omega k x - tauSq M.P)) ≤
        Real.exp (absorbEps * ((n : ℝ) + 1) +
          (E ^ 2 / (4 * absorbEps) + D)) := Real.exp_le_exp.mpr hlog
    _ = Real.exp (E ^ 2 / (4 * absorbEps) + D) *
        Real.exp (absorbEps * ((n : ℝ) + 1)) := by
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp (E ^ 2 / (4 * absorbEps) + D) *
        (8 * (1 + ‖x‖) ^ anchoredKappa) :=
      mul_le_mul_of_nonneg_left hdyadic (Real.exp_pos _).le
    _ ≤ Real.exp (E ^ 2 / (4 * absorbEps) + D) *
        (8 * (1 + ‖x‖)) := by
      gcongr
    _ = finiteCutoffLinearGrowthConstant M L C * (1 + ‖x‖) := by
      rw [finiteCutoffLinearGrowthConstant]
      dsimp [E, D]
      push_cast
      ring

/-- Almost surely a finite-cutoff coefficient has a global linear spatial
majorant.

-/
theorem ae_exists_aCutoff_linear_growth (M : GMCModel d) (L : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : Vec d, aCutoff M L omega x ≤ K * (1 + ‖x‖) := by
  refine (ae_exists_forall_growingBall_shell_abs_bound M).mono ?_
  rintro omega ⟨C, hC0, hC⟩
  exact ⟨finiteCutoffLinearGrowthConstant M L C,
    finiteCutoffLinearGrowthConstant_nonneg M L C,
    aCutoff_le_linear_of_growingBall_shell_abs_bound M L omega hC0 hC⟩

/-- A linear sequence is subquadratic in the exact normalization used by the
whole-space resolvent uniqueness argument.

-/
theorem tendsto_linear_majorant_subquadratic (K B : ℝ) :
    Tendsto (fun m : ℕ ↦
      (((m : ℝ) + 1) ^ 2)⁻¹ * (K * B * ((m : ℝ) + 1)))
      atTop (nhds 0) := by
  have htop : Tendsto (fun m : ℕ ↦ (m : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun m : ℕ ↦ ((m : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hconst : Tendsto (fun _m : ℕ ↦ K * B) atTop (nhds (K * B)) :=
    tendsto_const_nhds
  have hmul := hconst.mul hinv
  convert hmul using 1
  · funext m
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · simp

/-- Almost surely, the finite cutoff supplies exactly the subquadratic ball
majorant required by
`finiteCutoffWholeSpaceSolution_ae_eq_of_subquadratic_bound`.

-/
theorem ae_exists_aCutoff_subquadratic_majorant
    (M : GMCModel d) (L : ℕ) (x0 : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∃ A : ℕ → ℝ,
      (∀ m : ℕ, ∀ x ∈ Metric.ball x0 (3 * ((m : ℝ) + 1)),
        aCutoff M L omega x ≤ A m) ∧
      Tendsto (fun m : ℕ ↦ (((m : ℝ) + 1) ^ 2)⁻¹ * A m)
        atTop (nhds 0) := by
  refine (ae_exists_aCutoff_linear_growth M L).mono ?_
  rintro omega ⟨K, hK0, hK⟩
  let B : ℝ := 4 + ‖x0‖
  let A : ℕ → ℝ := fun m ↦ K * B * ((m : ℝ) + 1)
  refine ⟨A, ?_, ?_⟩
  · intro m x hx
    have hdist : dist x x0 ≤ 3 * ((m : ℝ) + 1) :=
      (Metric.mem_ball.mp hx).le
    have hnorm : ‖x‖ ≤ ‖x0‖ + 3 * ((m : ℝ) + 1) :=
      norm_le_norm_add_const_of_dist_le hdist
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hlinear : 1 + ‖x‖ ≤ B * ((m : ℝ) + 1) := by
      dsimp [B]
      nlinarith [norm_nonneg x0]
    simpa only [A, mul_assoc] using
      (hK x).trans (mul_le_mul_of_nonneg_left hlinear hK0)
  · exact tendsto_linear_majorant_subquadratic K B

/-- Almost-sure uniqueness of finite-cutoff whole-space massive solutions,
obtained by feeding the subquadratic majorant into the pathwise uniqueness
theorem.

-/
theorem ae_finiteCutoffWholeSpaceSolution_unique
    (M : GMCModel d) (L : ℕ) {t : ℝ} (ht : 0 < t)
    {f : Vec d → ℝ} (hf : MemLp f 2 volume) (x0 : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ∀ u v : WholeSpaceDivergenceResolventSolution (aCutoff M L omega) t f,
        u.toFun =ᵐ[volume] v.toFun ∧ u.grad =ᵐ[volume] v.grad := by
  refine (ae_exists_aCutoff_subquadratic_majorant M L x0).mono ?_
  rintro omega ⟨A, hA, hAlim⟩ u v
  exact finiteCutoffWholeSpaceSolution_ae_eq_of_subquadratic_bound
    M L omega ht hf hA hAlim u v

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
