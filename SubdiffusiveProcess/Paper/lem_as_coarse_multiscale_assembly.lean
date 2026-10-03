module

public import SubdiffusiveProcess.Paper.in_J
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
public import Mathlib.Tactic

@[expose] public section

/-!
# Multiscale assembly for pathwise coarse ellipticity

The discounted coarse quantities are controlled by cell-matrix bounds in the
retained, deep, and subwavelength regimes.
-/

open scoped BigOperators ENNReal NNReal
open Homogenization.Book.Ch02
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-! ## A. Cell-matrix majorants bound the Ch02 multiscale ellipticities -/

theorem aux_lem_as_coarse_ms_weight_nonneg {s q : ℝ} (hsq : 0 ≤ s * q) (n : ℕ) :
    0 ≤ geometricWeight s q n := by
  unfold geometricWeight geometricDiscount
  refine mul_nonneg ?_ (Real.rpow_nonneg (by norm_num) _)
  have h : Real.rpow (3 : ℝ) (-s * q) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  linarith

theorem aux_lem_as_coarse_ms_maxB_le {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) (B : ℕ → ℝ)
    (hB : ∀ n : ℕ, ∀ R ∈ Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ)),
      coarseBMatrixNorm R a ≤ B n) (n : ℕ) :
    maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤ B n :=
  finsetSupReal_le _ (Homogenization.descendantsAtScale_nonempty Q
    (sub_le_self _ (by exact_mod_cast Nat.zero_le n))) (hB n)

theorem aux_lem_as_coarse_ms_maxS_le {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) (B : ℕ → ℝ)
    (hB : ∀ n : ℕ, ∀ R ∈ Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ)),
      coarseSigmaStarInvMatrixNorm R a ≤ B n) (n : ℕ) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤ B n :=
  finsetSupReal_le _ (Homogenization.descendantsAtScale_nonempty Q
    (sub_le_self _ (by exact_mod_cast Nat.zero_le n))) (hB n)

/-- `q = 1`: the squared sum of square roots is bounded by the sum of the matrices
(paper: "weighted Cauchy--Schwarz bounds the squared sum of square-root matrices by this sum
of matrices"), then by the cell majorant. -/
theorem aux_lem_as_coarse_ms_Lambda_one_le {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) (B : ℕ → ℝ)
    (hB : ∀ n : ℕ, ∀ R ∈ Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ)),
      coarseBMatrixNorm R a ≤ B n)
    (hsum : Summable fun n : ℕ => geometricWeight s 1 n * B n) :
    LambdaSq Q s (.finite 1) a ≤ ∑' n : ℕ, geometricWeight s 1 n * B n := by
  refine (LambdaSq_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale Q a hs).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_)
    (summable_geometricWeight_one_mul_maxDescendantBMatrixNormAtScale Q a hs) hsum
  exact mul_le_mul_of_nonneg_left (aux_lem_as_coarse_ms_maxB_le Q a B hB n)
    (aux_lem_as_coarse_ms_weight_nonneg (by linarith) n)

theorem aux_lem_as_coarse_ms_lambda_one_inv_le {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) (B : ℕ → ℝ)
    (hB : ∀ n : ℕ, ∀ R ∈ Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ)),
      coarseSigmaStarInvMatrixNorm R a ≤ B n)
    (hsum : Summable fun n : ℕ => geometricWeight s 1 n * B n) :
    (lambdaSq Q s (.finite 1) a)⁻¹ ≤ ∑' n : ℕ, geometricWeight s 1 n * B n := by
  refine (lambdaSq_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
    Q a hs).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_)
    (summable_geometricWeight_one_mul_maxDescendantSigmaStarInvMatrixNormAtScale Q a hs) hsum
  exact mul_le_mul_of_nonneg_left (aux_lem_as_coarse_ms_maxS_le Q a B hB n)
    (aux_lem_as_coarse_ms_weight_nonneg (by linarith) n)

/-- `q = 2`: the definition is already the discounted sum of the matrices. -/
theorem aux_lem_as_coarse_ms_Lambda_two_eq {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) (s : ℝ) :
    LambdaSq Q s (.finite 2) a =
      ∑' n : ℕ, geometricWeight s 2 n *
        maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
  simp only [LambdaSq, LambdaSqFinite]
  norm_num

theorem aux_lem_as_coarse_ms_lambda_two_inv_eq {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) (s : ℝ) :
    (lambdaSq Q s (.finite 2) a)⁻¹ =
      ∑' n : ℕ, geometricWeight s 2 n *
        maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
  simp only [lambdaSq, lambdaSqFinite]
  norm_num
  rw [Real.rpow_neg_one, inv_inv]

theorem aux_lem_as_coarse_ms_Lambda_two_le {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) (B : ℕ → ℝ)
    (hB : ∀ n : ℕ, ∀ R ∈ Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ)),
      coarseBMatrixNorm R a ≤ B n)
    (hsum : Summable fun n : ℕ => geometricWeight s 2 n * B n) :
    LambdaSq Q s (.finite 2) a ≤ ∑' n : ℕ, geometricWeight s 2 n * B n := by
  rw [aux_lem_as_coarse_ms_Lambda_two_eq]
  have hle : ∀ n : ℕ, geometricWeight s 2 n *
      maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤ geometricWeight s 2 n * B n :=
    fun n => mul_le_mul_of_nonneg_left (aux_lem_as_coarse_ms_maxB_le Q a B hB n)
      (aux_lem_as_coarse_ms_weight_nonneg (by linarith) n)
  have hnn : ∀ n : ℕ, 0 ≤ geometricWeight s 2 n *
      maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    fun n => mul_nonneg (aux_lem_as_coarse_ms_weight_nonneg (by linarith) n)
      (maxDescendantBMatrixNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnn hle hsum) hsum

theorem aux_lem_as_coarse_ms_lambda_two_inv_le {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) (B : ℕ → ℝ)
    (hB : ∀ n : ℕ, ∀ R ∈ Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ)),
      coarseSigmaStarInvMatrixNorm R a ≤ B n)
    (hsum : Summable fun n : ℕ => geometricWeight s 2 n * B n) :
    (lambdaSq Q s (.finite 2) a)⁻¹ ≤ ∑' n : ℕ, geometricWeight s 2 n * B n := by
  rw [aux_lem_as_coarse_ms_lambda_two_inv_eq]
  have hle : ∀ n : ℕ, geometricWeight s 2 n *
      maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤
        geometricWeight s 2 n * B n :=
    fun n => mul_le_mul_of_nonneg_left (aux_lem_as_coarse_ms_maxS_le Q a B hB n)
      (aux_lem_as_coarse_ms_weight_nonneg (by linarith) n)
  have hnn : ∀ n : ℕ, 0 ≤ geometricWeight s 2 n *
      maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    fun n => mul_nonneg (aux_lem_as_coarse_ms_weight_nonneg (by linarith) n)
      (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnn hle hsum) hsum

/-! ## B. Three-regime geometric summation -/

/-- Tail of a geometric series past a real threshold `x ≥ 0`. -/
theorem aux_lem_as_coarse_ms_tail_geom {r x : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hx : 0 ≤ x) :
    Summable (fun n : ℕ => if x < (n : ℝ) then r ^ n else 0) ∧
      ∑' n : ℕ, (if x < (n : ℝ) then r ^ n else 0) ≤ r ^ x / (1 - r) := by
  set m : ℕ := ⌊x⌋₊ + 1 with hm
  have hxm : x < (m : ℝ) := by rw [hm]; push_cast; exact Nat.lt_floor_add_one x
  have hgeo : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0.le hr1
  have hnn : ∀ n : ℕ, 0 ≤ (if x < (n : ℝ) then r ^ n else 0) := fun n => by
    split_ifs <;> positivity
  have hle1 : ∀ n : ℕ, (if x < (n : ℝ) then r ^ n else 0) ≤ (if m ≤ n then r ^ n else 0) := by
    intro n
    by_cases h1 : x < (n : ℝ)
    · have h2 : m ≤ n := by
        have : ⌊x⌋₊ < n := (Nat.floor_lt hx).2 h1
        omega
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1]
      split_ifs <;> positivity
  have hind_nn : ∀ n : ℕ, 0 ≤ (if m ≤ n then r ^ n else 0) := fun n => by
    split_ifs <;> positivity
  have hind_le : ∀ n : ℕ, (if m ≤ n then r ^ n else 0) ≤ r ^ n := fun n => by
    split_ifs
    · exact le_rfl
    · positivity
  have hsum_ind : Summable (fun n : ℕ => if m ≤ n then r ^ n else 0) :=
    Summable.of_nonneg_of_le hind_nn hind_le hgeo
  have htsum_ind : ∑' n : ℕ, (if m ≤ n then r ^ n else 0) = r ^ m / (1 - r) := by
    rw [← hsum_ind.sum_add_tsum_nat_add m]
    have h0 : ∑ i ∈ Finset.range m, (if m ≤ i then r ^ i else 0) = 0 :=
      Finset.sum_eq_zero (fun i hi => if_neg (by simp at hi; omega))
    have h1 : (fun i : ℕ => if m ≤ i + m then r ^ (i + m) else 0) =
        fun i : ℕ => r ^ m * r ^ i :=
      funext fun i => by rw [if_pos (by omega), pow_add, mul_comm]
    rw [h0, zero_add, h1, tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1, div_eq_mul_inv]
  refine ⟨Summable.of_nonneg_of_le hnn hle1 hsum_ind, ?_⟩
  calc ∑' n : ℕ, (if x < (n : ℝ) then r ^ n else 0)
      ≤ ∑' n : ℕ, (if m ≤ n then r ^ n else 0) :=
        Summable.tsum_le_tsum hle1 (Summable.of_nonneg_of_le hnn hle1 hsum_ind) hsum_ind
    _ = r ^ m / (1 - r) := htsum_ind
    _ ≤ r ^ x / (1 - r) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hxm.le

/-- The discounted weight against a power profile is a geometric term. -/
theorem aux_lem_as_coarse_ms_weight_mul_rpow (s q rho : ℝ) (n : ℕ) :
    geometricWeight s q n * (3 : ℝ) ^ (rho * (n : ℝ)) =
      geometricDiscount s q * ((3 : ℝ) ^ (-(s * q - rho))) ^ n := by
  unfold geometricWeight
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3), mul_assoc]
  congr 1
  change (3 : ℝ) ^ (-s * q * (n : ℝ)) * (3 : ℝ) ^ (rho * (n : ℝ)) = _
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

theorem aux_lem_as_coarse_ms_weight_eq_pow (s q : ℝ) (n : ℕ) :
    geometricWeight s q n = geometricDiscount s q * ((3 : ℝ) ^ (-(s * q))) ^ n := by
  have h := aux_lem_as_coarse_ms_weight_mul_rpow s q 0 n
  simpa using h

/-- **Three-regime summation** (paper lines 4539--4553).  Retained cells `n ≤ θN` are bounded
by `K 3^{ρn}`, deep cells `θN < n ≤ N` by `K' 3^{ρn}`, and cells below the last wavelength
`n > N` by a constant `S`.  The discounted series is then at most
`c/(1-3^{-(sq-ρ)}) (K + K' 3^{-(sq-ρ)θN}) + 3^{-sqN} S`. -/
theorem aux_lem_as_coarse_ms_three_regime {s q rho theta : ℝ} (hs : 0 < s) (hq : 1 ≤ q)
    (hrho : rho < s * q) (htheta : 0 ≤ theta) (N : ℕ) {K K' S : ℝ}
    (hK : 0 ≤ K) (hK' : 0 ≤ K') (hS : 0 ≤ S) (B : ℕ → ℝ) (hB0 : ∀ n, 0 ≤ B n)
    (hshallow : ∀ n : ℕ, (n : ℝ) ≤ theta * N → B n ≤ K * (3 : ℝ) ^ (rho * (n : ℝ)))
    (hdeep : ∀ n : ℕ, theta * N < (n : ℝ) → n ≤ N → B n ≤ K' * (3 : ℝ) ^ (rho * (n : ℝ)))
    (hsub : ∀ n : ℕ, N < n → B n ≤ S) :
    Summable (fun n : ℕ => geometricWeight s q n * B n) ∧
      ∑' n : ℕ, geometricWeight s q n * B n ≤
        geometricDiscount s q / (1 - (3 : ℝ) ^ (-(s * q - rho))) *
            (K + K' * (3 : ℝ) ^ (-(s * q - rho) * (theta * N))) +
          (3 : ℝ) ^ (-(s * q) * N) * S := by
  set c : ℝ := geometricDiscount s q with hc
  set r : ℝ := (3 : ℝ) ^ (-(s * q - rho)) with hr
  set u : ℝ := (3 : ℝ) ^ (-(s * q)) with hu
  have hsq : 0 < s * q := mul_pos hs (by linarith)
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hu0 : 0 < u := Real.rpow_pos_of_pos (by norm_num) _
  have hu1 : u < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc_eq : c = 1 - u := by
    rw [hc, hu]; unfold geometricDiscount; congr 1; change (3 : ℝ) ^ (-s * q) = _; ring_nf
  have hc0 : 0 ≤ c := by rw [hc_eq]; linarith
  have hθN : 0 ≤ theta * (N : ℝ) := mul_nonneg htheta (Nat.cast_nonneg N)
  obtain ⟨hs2, ht2⟩ := aux_lem_as_coarse_ms_tail_geom hr0 hr1 hθN
  obtain ⟨hs3, ht3⟩ := aux_lem_as_coarse_ms_tail_geom hu0 hu1 (Nat.cast_nonneg N)
  have hs1 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0.le hr1
  let G : ℕ → ℝ := fun n =>
    c * (K * r ^ n) + c * (K' * (if theta * N < (n : ℝ) then r ^ n else 0)) +
      c * (S * (if (N : ℝ) < (n : ℝ) then u ^ n else 0))
  have hGs1 : Summable (fun n : ℕ => c * (K * r ^ n)) := (hs1.mul_left K).mul_left c
  have hGs2 : Summable (fun n : ℕ => c * (K' * (if theta * N < (n : ℝ) then r ^ n else 0))) :=
    (hs2.mul_left K').mul_left c
  have hGs3 : Summable (fun n : ℕ => c * (S * (if (N : ℝ) < (n : ℝ) then u ^ n else 0))) :=
    (hs3.mul_left S).mul_left c
  have hGsum : Summable G := (hGs1.add hGs2).add hGs3
  have hwn : ∀ n : ℕ, 0 ≤ geometricWeight s q n :=
    fun n => aux_lem_as_coarse_ms_weight_nonneg hsq.le n
  have hind2 : ∀ n : ℕ, 0 ≤ (if theta * N < (n : ℝ) then r ^ n else 0) := fun n => by
    split_ifs <;> positivity
  have hind3 : ∀ n : ℕ, 0 ≤ (if (N : ℝ) < (n : ℝ) then u ^ n else 0) := fun n => by
    split_ifs <;> positivity
  have hG1 : ∀ n : ℕ, 0 ≤ c * (K * r ^ n) := fun n => by positivity
  have hG2 : ∀ n : ℕ, 0 ≤ c * (K' * (if theta * N < (n : ℝ) then r ^ n else 0)) :=
    fun n => mul_nonneg hc0 (mul_nonneg hK' (hind2 n))
  have hG3 : ∀ n : ℕ, 0 ≤ c * (S * (if (N : ℝ) < (n : ℝ) then u ^ n else 0)) :=
    fun n => mul_nonneg hc0 (mul_nonneg hS (hind3 n))
  have hterm : ∀ n : ℕ, geometricWeight s q n * B n ≤ G n := by
    intro n
    by_cases hsh : (n : ℝ) ≤ theta * N
    · have h := mul_le_mul_of_nonneg_left (hshallow n hsh) (hwn n)
      have heq : geometricWeight s q n * (K * (3 : ℝ) ^ (rho * (n : ℝ))) = c * (K * r ^ n) := by
        rw [mul_left_comm, aux_lem_as_coarse_ms_weight_mul_rpow]; ring
      rw [heq] at h
      have := hG2 n; have := hG3 n
      change _ ≤ c * (K * r ^ n) + _ + _
      linarith
    · push_neg at hsh
      by_cases hdp : n ≤ N
      · have h := mul_le_mul_of_nonneg_left (hdeep n hsh hdp) (hwn n)
        have heq : geometricWeight s q n * (K' * (3 : ℝ) ^ (rho * (n : ℝ))) =
            c * (K' * (if theta * N < (n : ℝ) then r ^ n else 0)) := by
          rw [if_pos hsh, mul_left_comm, aux_lem_as_coarse_ms_weight_mul_rpow]; ring
        rw [heq] at h
        have := hG1 n; have := hG3 n
        change _ ≤ _ + c * (K' * (if theta * N < (n : ℝ) then r ^ n else 0)) + _
        linarith
      · push_neg at hdp
        have h := mul_le_mul_of_nonneg_left (hsub n hdp) (hwn n)
        have hNn : (N : ℝ) < (n : ℝ) := by exact_mod_cast hdp
        have heq : geometricWeight s q n * S =
            c * (S * (if (N : ℝ) < (n : ℝ) then u ^ n else 0)) := by
          rw [if_pos hNn, aux_lem_as_coarse_ms_weight_eq_pow]; ring
        rw [heq] at h
        have := hG1 n; have := hG2 n
        change _ ≤ _ + _ + c * (S * (if (N : ℝ) < (n : ℝ) then u ^ n else 0))
        linarith
  have hnn : ∀ n : ℕ, 0 ≤ geometricWeight s q n * B n := fun n => mul_nonneg (hwn n) (hB0 n)
  have hsumWB : Summable (fun n : ℕ => geometricWeight s q n * B n) :=
    Summable.of_nonneg_of_le hnn hterm hGsum
  refine ⟨hsumWB, ?_⟩
  have htG : ∑' n : ℕ, G n =
      c * (K * ∑' n : ℕ, r ^ n) +
        c * (K' * ∑' n : ℕ, (if theta * N < (n : ℝ) then r ^ n else 0)) +
        c * (S * ∑' n : ℕ, (if (N : ℝ) < (n : ℝ) then u ^ n else 0)) := by
    change ∑' n : ℕ, (c * (K * r ^ n) + c * (K' * (if theta * N < (n : ℝ) then r ^ n else 0)) +
      c * (S * (if (N : ℝ) < (n : ℝ) then u ^ n else 0))) = _
    rw [Summable.tsum_add (hGs1.add hGs2) hGs3, Summable.tsum_add hGs1 hGs2,
      tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
  have hgeo : ∑' n : ℕ, r ^ n = 1 / (1 - r) := by
    rw [tsum_geometric_of_lt_one hr0.le hr1, one_div]
  have hrθ : r ^ (theta * (N : ℝ)) = (3 : ℝ) ^ (-(s * q - rho) * (theta * N)) := by
    rw [hr, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have huN : u ^ ((N : ℕ) : ℝ) = (3 : ℝ) ^ (-(s * q) * N) := by
    rw [hu, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have h1r : 0 < 1 - r := by linarith
  have h1u : 0 < 1 - u := by linarith
  calc ∑' n : ℕ, geometricWeight s q n * B n
      ≤ ∑' n : ℕ, G n := Summable.tsum_le_tsum hterm hsumWB hGsum
    _ = c * (K * ∑' n : ℕ, r ^ n) +
        c * (K' * ∑' n : ℕ, (if theta * N < (n : ℝ) then r ^ n else 0)) +
        c * (S * ∑' n : ℕ, (if (N : ℝ) < (n : ℝ) then u ^ n else 0)) := htG
    _ ≤ c * (K * (1 / (1 - r))) + c * (K' * (r ^ (theta * (N : ℝ)) / (1 - r))) +
        c * (S * (u ^ ((N : ℕ) : ℝ) / (1 - u))) := by
        rw [hgeo]
        gcongr
    _ = c / (1 - r) * (K + K' * (3 : ℝ) ^ (-(s * q - rho) * (theta * N))) +
        (3 : ℝ) ^ (-(s * q) * N) * S := by
        rw [← hrθ, ← huN, hc_eq]
        field_simp

/-! ## C. The `in_J` interface for the root cube -/

/-- The depth-`n` descendants of the unit root, in the chart of the root itself. -/
abbrev aux_lem_as_coarse_ms_desc (d : ℕ) (n : ℕ) : Finset (Homogenization.TriadicCube d) :=
  Homogenization.descendantsAtScale (Homogenization.originCube d 0)
    ((Homogenization.originCube d 0).scale - (n : ℤ))

/-- **Interface.**  A per-depth majorant `B` of both cell matrices of the root chart bounds
`Jc.Lam` and `Jc.lam⁻¹` of the root, for `q ∈ {1,2}`. -/
theorem aux_lem_as_coarse_ms_root_le {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (B : ℕ → ℝ)
    (hB : ∀ n : ℕ, ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
      coarseBMatrixNorm R (Jc.chart z r hr a z r) ≤ B n ∧
        coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr a z r) ≤ B n)
    (qe : ℝ≥0∞) (hqe : qe = 1 ∨ qe = 2)
    (hsum : Summable fun n : ℕ => geometricWeight s qe.toReal n * B n) :
    Jc.Lam z r hr a z r s qe ≤ ∑' n : ℕ, geometricWeight s qe.toReal n * B n ∧
      (Jc.lam z r hr a z r s qe)⁻¹ ≤ ∑' n : ℕ, geometricWeight s qe.toReal n * B n := by
  haveI : NeZero d := ⟨by omega⟩
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := subset_rfl
  have hBb := fun n R hR => (hB n R hR).1
  have hBs := fun n R hR => (hB n R hR).2
  rcases hqe with rfl | rfl
  · rw [Jc.Lam_eq z r hr a z r hr hsub s hs 1 le_rfl,
      Jc.lam_eq z r hr a z r hr hsub s hs 1 le_rfl]
    simp only [ENNReal.one_ne_top, if_false, ENNReal.toReal_one] at hsum ⊢
    exact ⟨aux_lem_as_coarse_ms_Lambda_one_le _ _ hs.1 B hBb hsum,
      aux_lem_as_coarse_ms_lambda_one_inv_le _ _ hs.1 B hBs hsum⟩
  · rw [Jc.Lam_eq z r hr a z r hr hsub s hs 2 (by norm_num),
      Jc.lam_eq z r hr a z r hr hsub s hs 2 (by norm_num)]
    have h2 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h2' : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    simp only [h2, if_false, h2'] at hsum ⊢
    exact ⟨aux_lem_as_coarse_ms_Lambda_two_le _ _ hs.1 B hBb hsum,
      aux_lem_as_coarse_ms_lambda_two_inv_le _ _ hs.1 B hBs hsum⟩

/-- `q ∈ {1,2}` read as a real exponent. -/
theorem aux_lem_as_coarse_ms_qe_real {qe : ℝ≥0∞} (hqe : qe = 1 ∨ qe = 2) :
    1 ≤ qe.toReal ∧ qe.toReal ≤ 2 := by
  rcases hqe with rfl | rfl <;> norm_num

/-! ## D. Root bound at one cutoff from the three regimes -/

/-- **Root bound at a fixed cutoff.**  Cell-matrix bounds in the three depth regimes give
`Λ_{s,q} + λ_{s,q}⁻¹` of the root, `q ∈ {1,2}`. -/
theorem aux_lem_as_coarse_ms_root_three_regime {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (rho theta : ℝ) (hrhos : rho < s)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1) (N : ℕ) {K K' S : ℝ}
    (hK : 0 ≤ K) (hK' : 0 ≤ K') (hS : 0 ≤ S)
    (hshallow : ∀ n : ℕ, (n : ℝ) ≤ theta * N → ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
      coarseBMatrixNorm R (Jc.chart z r hr a z r) ≤ K * (3 : ℝ) ^ (rho * (n : ℝ)) ∧
        coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr a z r) ≤
          K * (3 : ℝ) ^ (rho * (n : ℝ)))
    (hdeep : ∀ n : ℕ, theta * N < (n : ℝ) → n ≤ N → ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
      coarseBMatrixNorm R (Jc.chart z r hr a z r) ≤ K' * (3 : ℝ) ^ (rho * (n : ℝ)) ∧
        coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr a z r) ≤
          K' * (3 : ℝ) ^ (rho * (n : ℝ)))
    (hsub : ∀ n : ℕ, N < n → ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
      coarseBMatrixNorm R (Jc.chart z r hr a z r) ≤ S ∧
        coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr a z r) ≤ S)
    (qe : ℝ≥0∞) (hqe : qe = 1 ∨ qe = 2) :
    Jc.Lam z r hr a z r s qe + (Jc.lam z r hr a z r s qe)⁻¹ ≤
      2 * (geometricDiscount s qe.toReal / (1 - (3 : ℝ) ^ (-(s * qe.toReal - rho))) *
          (K + K' * (3 : ℝ) ^ (-(s * qe.toReal - rho) * (theta * N))) +
        (3 : ℝ) ^ (-(s * qe.toReal) * N) * S) := by
  obtain ⟨hq1, _⟩ := aux_lem_as_coarse_ms_qe_real hqe
  have hrho' : rho < s * qe.toReal := by nlinarith [hs.1]
  let B : ℕ → ℝ := fun n =>
    if (n : ℝ) ≤ theta * N then K * (3 : ℝ) ^ (rho * (n : ℝ))
    else if n ≤ N then K' * (3 : ℝ) ^ (rho * (n : ℝ)) else S
  have hB0 : ∀ n, 0 ≤ B n := fun n => by
    simp only [B]; split_ifs <;> positivity
  have hBsh : ∀ n : ℕ, (n : ℝ) ≤ theta * N → B n ≤ K * (3 : ℝ) ^ (rho * (n : ℝ)) :=
    fun n h => by simp only [B, if_pos h, le_refl]
  have hBdp : ∀ n : ℕ, theta * N < (n : ℝ) → n ≤ N → B n ≤ K' * (3 : ℝ) ^ (rho * (n : ℝ)) :=
    fun n h h' => by simp only [B, if_neg (not_le.2 h), if_pos h', le_refl]
  have hθN : theta * (N : ℝ) ≤ N :=
    mul_le_of_le_one_left (Nat.cast_nonneg N) htheta1
  have hBsb : ∀ n : ℕ, N < n → B n ≤ S := by
    intro n h
    have h1 : ¬ (n : ℝ) ≤ theta * N := by
      have : (N : ℝ) < n := by exact_mod_cast h
      linarith
    have h2 : ¬ n ≤ N := by omega
    simp only [B, if_neg h1, if_neg h2, le_refl]
  have hBcell : ∀ n : ℕ, ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
      coarseBMatrixNorm R (Jc.chart z r hr a z r) ≤ B n ∧
        coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr a z r) ≤ B n := by
    intro n R hR
    by_cases h1 : (n : ℝ) ≤ theta * N
    · simp only [B, if_pos h1]; exact hshallow n h1 R hR
    · by_cases h2 : n ≤ N
      · simp only [B, if_neg h1, if_pos h2]; exact hdeep n (not_le.1 h1) h2 R hR
      · simp only [B, if_neg h1, if_neg h2]; exact hsub n (by omega) R hR
  obtain ⟨hsum, htsum⟩ := aux_lem_as_coarse_ms_three_regime (q := qe.toReal) hs.1 hq1 hrho'
    htheta N hK hK' hS B hB0 hBsh hBdp hBsb
  obtain ⟨hL, hl⟩ := aux_lem_as_coarse_ms_root_le hd Jc z r hr a s hs B hBcell qe hqe hsum
  linarith

/-! ## E. Uniform-in-cutoff pathwise assembly -/

/-- The `N`-independent constant of the three regimes, uniformly in `q ∈ {1,2}`. -/
theorem aux_lem_as_coarse_ms_regime_const_le {s rho theta xi : ℝ} (hs : 0 < s)
    (hrhos : rho < s) (htheta : 0 ≤ theta) (hxi : xi ≤ (s - rho) * theta)
    {q : ℝ} (hq1 : 1 ≤ q) (N : ℕ) {K Kd S Ksub : ℝ} (hK : 0 ≤ K) (hKd0 : 0 ≤ Kd) (hS : 0 ≤ S)
    (hKd : Kd ≤ (3 : ℝ) ^ (xi * (N : ℝ)))
    (hSN : (3 : ℝ) ^ (-(s * (N : ℝ))) * S ≤ Ksub) :
    2 * (geometricDiscount s q / (1 - (3 : ℝ) ^ (-(s * q - rho))) *
          (K + Kd * (3 : ℝ) ^ (-(s * q - rho) * (theta * N))) +
        (3 : ℝ) ^ (-(s * q) * N) * S) ≤
      2 * ((K + 1) / (1 - (3 : ℝ) ^ (-(s - rho))) + Ksub) := by
  have hsq : s ≤ s * q := le_mul_of_one_le_right hs.le hq1
  have hr1 : (3 : ℝ) ^ (-(s - rho)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hrq : (3 : ℝ) ^ (-(s * q - rho)) ≤ (3 : ℝ) ^ (-(s - rho)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hc0 : 0 ≤ geometricDiscount s q := by
    unfold geometricDiscount
    have : Real.rpow (3 : ℝ) (-s * q) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
    linarith
  have hc1 : geometricDiscount s q ≤ 1 := by
    unfold geometricDiscount
    have : 0 < Real.rpow (3 : ℝ) (-s * q) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  have hfrac : geometricDiscount s q / (1 - (3 : ℝ) ^ (-(s * q - rho))) ≤
      1 / (1 - (3 : ℝ) ^ (-(s - rho))) := by
    apply div_le_div₀ zero_le_one hc1 (by linarith) (by linarith)
  have hdeep : Kd * (3 : ℝ) ^ (-(s * q - rho) * (theta * N)) ≤ 1 := by
    calc Kd * (3 : ℝ) ^ (-(s * q - rho) * (theta * N))
        ≤ (3 : ℝ) ^ (xi * (N : ℝ)) * (3 : ℝ) ^ (-(s * q - rho) * (theta * N)) :=
          mul_le_mul_of_nonneg_right hKd (by positivity)
      _ = (3 : ℝ) ^ (xi * (N : ℝ) + -(s * q - rho) * (theta * N)) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ ≤ (3 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          have h1 : xi * (N : ℝ) ≤ (s - rho) * theta * N := mul_le_mul_of_nonneg_right hxi hN
          have h2 : (s - rho) * theta * N ≤ (s * q - rho) * (theta * N) := by
            have : (s - rho) ≤ (s * q - rho) := by linarith
            have hθN : 0 ≤ theta * (N : ℝ) := mul_nonneg htheta hN
            nlinarith
          linarith
      _ = 1 := Real.rpow_zero 3
  have hsub : (3 : ℝ) ^ (-(s * q) * N) * S ≤ Ksub := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hS) hSN
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hinner : K + Kd * (3 : ℝ) ^ (-(s * q - rho) * (theta * N)) ≤ K + 1 := by linarith
  have hinner0 : 0 ≤ K + Kd * (3 : ℝ) ^ (-(s * q - rho) * (theta * N)) := by positivity
  have hmain : geometricDiscount s q / (1 - (3 : ℝ) ^ (-(s * q - rho))) *
        (K + Kd * (3 : ℝ) ^ (-(s * q - rho) * (theta * N))) ≤
      (K + 1) / (1 - (3 : ℝ) ^ (-(s - rho))) := by
    calc _ ≤ 1 / (1 - (3 : ℝ) ^ (-(s - rho))) * (K + 1) :=
          mul_le_mul hfrac hinner hinner0 (by
            have : 0 < 1 - (3 : ℝ) ^ (-(s - rho)) := by linarith
            positivity)
      _ = (K + 1) / (1 - (3 : ℝ) ^ (-(s - rho))) := by ring
  linarith

/-- **Pathwise assembly, uniform in the cutoff** (paper lines 4530--4557).  At one sample:
retained cell matrices bounded by `K 3^{ρk}` (shallow), deep cell matrices by `K_N 3^{ρk}` with
`K_N ≤ 3^{ξN}` and `ξ ≤ (s-ρ)θ`, and sub-wavelength cell matrices by `S_N` with
`3^{-sN} S_N ≤ K_sub`, all for `N ≥ N₀`, give one finite constant bounding
`Λ_{s,q} + λ_{s,q}⁻¹` of the root for **all** `N` and `q ∈ {1,2}`.  The finitely many omitted
cutoffs are absorbed because `Jc.Lam`, `Jc.lam⁻¹` are real numbers. -/
theorem lem_as_coarse_multiscale_assembly {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (coef : ℕ → PositiveCoefficient (centeredCube z r hr))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (rho theta xi : ℝ) (hrhos : rho < s)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1) (hxi : xi ≤ (s - rho) * theta)
    (N0 : ℕ) (K Ksub : ℝ) (Kdeep S : ℕ → ℝ)
    (hK : 0 ≤ K) (hKd : ∀ N, 0 ≤ Kdeep N) (hS : ∀ N, 0 ≤ S N)
    (hKdN : ∀ N, N0 ≤ N → Kdeep N ≤ (3 : ℝ) ^ (xi * (N : ℝ)))
    (hSN : ∀ N, N0 ≤ N → (3 : ℝ) ^ (-(s * (N : ℝ))) * S N ≤ Ksub)
    (hshallow : ∀ N, N0 ≤ N → ∀ n : ℕ, (n : ℝ) ≤ theta * N →
      ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
        coarseBMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤ K * (3 : ℝ) ^ (rho * (n : ℝ)) ∧
          coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤
            K * (3 : ℝ) ^ (rho * (n : ℝ)))
    (hdeep : ∀ N, N0 ≤ N → ∀ n : ℕ, theta * N < (n : ℝ) → n ≤ N →
      ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
        coarseBMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤
            Kdeep N * (3 : ℝ) ^ (rho * (n : ℝ)) ∧
          coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤
            Kdeep N * (3 : ℝ) ^ (rho * (n : ℝ)))
    (hsub : ∀ N, N0 ≤ N → ∀ n : ℕ, N < n → ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
      coarseBMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤ S N ∧
        coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤ S N) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ qe : ℝ≥0∞, (qe = 1 ∨ qe = 2) →
      Jc.Lam z r hr (coef N) z r s qe + (Jc.lam z r hr (coef N) z r s qe)⁻¹ ≤ C := by
  let v : ℕ → ℝ≥0∞ → ℝ := fun N qe =>
    Jc.Lam z r hr (coef N) z r s qe + (Jc.lam z r hr (coef N) z r s qe)⁻¹
  let Cbig : ℝ := 2 * ((K + 1) / (1 - (3 : ℝ) ^ (-(s - rho))) + Ksub)
  let C0 : ℝ := ∑ N ∈ Finset.range N0, (|v N 1| + |v N 2|)
  have hKsub : 0 ≤ Ksub :=
    le_trans (mul_nonneg (by positivity) (hS N0)) (hSN N0 le_rfl)
  have hr1 : (3 : ℝ) ^ (-(s - rho)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hCbig : 0 ≤ Cbig := by
    have : 0 < 1 - (3 : ℝ) ^ (-(s - rho)) := by linarith
    positivity
  have hC0 : 0 ≤ C0 := Finset.sum_nonneg fun N _ => by positivity
  refine ⟨Cbig + C0 + 1, by linarith, ?_⟩
  intro N qe hqe
  change v N qe ≤ _
  rcases lt_or_ge N N0 with hN | hN
  · have hmem : N ∈ Finset.range N0 := Finset.mem_range.2 hN
    have hle : |v N 1| + |v N 2| ≤ C0 :=
      Finset.single_le_sum (f := fun N => |v N 1| + |v N 2|)
        (fun N _ => by positivity) hmem
    have hvq : v N qe ≤ |v N 1| + |v N 2| := by
      rcases hqe with rfl | rfl
      · linarith [le_abs_self (v N 1), abs_nonneg (v N 2)]
      · linarith [le_abs_self (v N 2), abs_nonneg (v N 1)]
    linarith
  · obtain ⟨hq1, _⟩ := aux_lem_as_coarse_ms_qe_real hqe
    have h1 := aux_lem_as_coarse_ms_root_three_regime hd Jc z r hr (coef N) s hs rho theta
      hrhos htheta htheta1 N hK (hKd N) (hS N) (hshallow N hN) (hdeep N hN) (hsub N hN) qe hqe
    have h2 := aux_lem_as_coarse_ms_regime_const_le hs.1 hrhos htheta hxi hq1 N hK (hKd N)
      (hS N) (hKdN N hN) (hSN N hN)
    change v N qe ≤ _ at h1
    linarith

end Paper

