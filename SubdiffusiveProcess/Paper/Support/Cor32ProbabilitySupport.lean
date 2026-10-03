module

public import SubdiffusiveProcess.Lane3.ScalarAndAffine
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.lem_branch
public import SubdiffusiveProcess.Paper.lem_witness
public import SubdiffusiveProcess.Paper.order_of_parameters
public import SubdiffusiveProcess.Paper.prop_allchain
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.prop_conc
public import SubdiffusiveProcess.Paper.thm_C0
public import SubdiffusiveProcess.Paper.optimal_endpoints
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Lane3.Forms
public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Lane3.DirichletForm
public import SubdiffusiveProcess.Lane3.ResamplingV2
public import SubdiffusiveProcess.Lane3.UpperDensity
public import SubdiffusiveProcess.Lane3.BandFiltration
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import SubdiffusiveProcess.Probability.ResponseCompactness
public import SubdiffusiveProcess.Variational.QuadraticSaving
public import SubdiffusiveProcess.Compactness.OperatorLimits
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic
public import Mathlib.Data.Set.Card

@[expose] public section







-- so ExtraGood is MeasurableSet on a non-complete space); see HEADER_DIFF_cor_32.md.

-- `2 ≤ p` scoping was unprovable (prop_allchain's witness/union-bound machinery needs a genuine

-- branching entropy `H1*d*log 3`, not just `p ≥ 2`). Replaced by `hpRate`, an `hpRate`-style

-- exactly for `prop_allchain`'s witness rate `A = 2*log2+1+(24/theta')*(b*+log c+log2+1)` with
-- `theta' := theta/2`, `c := card Child = 3^(H1*d)`, `b* := 1`; see HEADER_DIFF_cor_32.md and
-- DEV_cor_32.md for the derivation.
set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Several frozen hypotheses (hd, hH1, hJoint, hsymAE, hsymAF, hAE, hAF, ...) are not needed by
-- the part of the proof that is complete; silence the resulting unused-variable noise rather than


open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

namespace Paper
noncomputable section



lemma aux_cor_32_abs_quadratic_form_le {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    |x ⬝ᵥ M.mulVec x| ≤ (∑ i : Fin d, ∑ j : Fin d, |M i j|) * (x ⬝ᵥ x) := by
  have h_sum_eq : x ⬝ᵥ M.mulVec x = ∑ i : Fin d, ∑ j : Fin d, x i * M i j * x j := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [h_sum_eq]
  have hxx : ∀ i : Fin d, (x i) ^ 2 ≤ x ⬝ᵥ x := by
    intro i
    have h := Finset.single_le_sum (f := fun k => x k * x k)
      (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ i)
    rw [pow_two, dotProduct]
    exact h
  have h_term : ∀ i j : Fin d, |x i * M i j * x j| ≤ |M i j| * (x ⬝ᵥ x) := by
    intro i j
    have hij : |x i| * |x j| ≤ x ⬝ᵥ x := by
      nlinarith [hxx i, hxx j, sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    calc
      |x i * M i j * x j| = |M i j| * (|x i| * |x j|) := by
        rw [abs_mul, abs_mul]; ring
      _ ≤ |M i j| * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_left hij (abs_nonneg _)
  calc
    |∑ i : Fin d, ∑ j : Fin d, x i * M i j * x j| ≤
        ∑ i : Fin d, |∑ j : Fin d, x i * M i j * x j| :=
      Finset.abs_sum_le_sum_abs (fun i => ∑ j : Fin d, x i * M i j * x j) Finset.univ
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |x i * M i j * x j| :=
      Finset.sum_le_sum fun i _ =>
        Finset.abs_sum_le_sum_abs (fun j => x i * M i j * x j) Finset.univ
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |M i j| * (x ⬝ᵥ x) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_term i j
    _ = (∑ i : Fin d, ∑ j : Fin d, |M i j|) * (x ⬝ᵥ x) := by
      simp_rw [← Finset.sum_mul]

theorem aux_cor_32_notand_card_union_le {ι : Type*} [Fintype ι] (P Q : ι → Prop) :
    Nat.card {j : ι // ¬ (P j ∧ Q j)} ≤
      Nat.card {j : ι // ¬ P j} + Nat.card {j : ι // ¬ Q j} := by
  classical
    have h_set_eq : {j | ¬ (P j ∧ Q j)} = {j | ¬ P j} ∪ {j | ¬ Q j} := by
      ext j; simp [Set.mem_setOf_eq, Set.mem_union, imp_iff_not_or]
    calc
      Nat.card {j : ι // ¬ (P j ∧ Q j)} = Nat.card ↥({j | ¬ (P j ∧ Q j)}) := rfl
      _ = Nat.card ↥({j | ¬ P j} ∪ {j | ¬ Q j}) := by rw [h_set_eq]
      _ ≤ Nat.card ↥{j | ¬ P j} + Nat.card ↥{j | ¬ Q j} := Set.card_union_le _ _
      _ = Nat.card {j : ι // ¬ P j} + Nat.card {j : ι // ¬ Q j} := rfl

/-- Real-valued cast of `aux_cor_32_notand_card_union_le` (paper cor-32, lines 3491-3498). -/
theorem aux_cor_32_card_union_real {ι : Type*} [Fintype ι] (P Q : ι → Prop) :
    (Nat.card {j : ι // ¬ (P j ∧ Q j)} : ℝ) ≤
      (Nat.card {j : ι // ¬ P j} : ℝ) + (Nat.card {j : ι // ¬ Q j} : ℝ) := by
  exact_mod_cast aux_cor_32_notand_card_union_le P Q

/-- Pointwise combination step: given the base-event bad-count bound and the extra-test
bad-count bound at the same level and branch prefix (paper cor-32, lines 3491-3498), the bad
count for their conjunction obeys the summed `theta`-density, summed-allowance bound. -/
theorem aux_cor_32_card_and_le {d : ℕ} (H1 : ℕ) {Ω : Type*}
    (Good1 Good2 : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω)
    (omega : Ω) (J : ℕ) (pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1))
    (theta1 theta2 c1 c2 : ℝ)
    (h1 : (Nat.card {j : Fin J // ¬ omega ∈ Good1 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
          theta1 * (J : ℝ) + c1)
    (h2 : (Nat.card {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
          theta2 * (J : ℝ) + c2) :
    (Nat.card {j : Fin J // ¬ (omega ∈ Good1 (j.val + 1)
        (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩) ∧
      omega ∈ Good2 (j.val + 1)
        (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
      (theta1 + theta2) * (J : ℝ) + (c1 + c2) := by
  set P' := fun (j : Fin J) => omega ∈ Good1 (j.val + 1)
    (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩) with hP'
  set Q' := fun (j : Fin J) => omega ∈ Good2 (j.val + 1)
    (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩) with hQ'
  have h_union := aux_cor_32_card_union_real P' Q'
  have h_sum : (Nat.card {j : Fin J // ¬ P' j} : ℝ) + (Nat.card {j : Fin J // ¬ Q' j} : ℝ) ≤
      (theta1 * (J : ℝ) + c1) + (theta2 * (J : ℝ) + c2) := by
    have hP'_card : (Nat.card {j : Fin J // ¬ P' j} : ℝ) ≤ theta1 * (J : ℝ) + c1 := by
      simpa [hP'] using h1
    have hQ'_card : (Nat.card {j : Fin J // ¬ Q' j} : ℝ) ≤ theta2 * (J : ℝ) + c2 := by
      simpa [hQ'] using h2
    exact add_le_add hP'_card hQ'_card
  have h_goal : (Nat.card {j : Fin J // ¬ (P' j ∧ Q' j)} : ℝ) ≤
      (theta1 + theta2) * (J : ℝ) + (c1 + c2) := by
    linarith [h_union, h_sum]
  simpa [hP', hQ'] using h_goal

/-- Assembly: given a `theta1`-density bound for `Good1` and a `theta2`-density bound for
`Good2`, produce the single measurable, nonnegative allowance `Bnew` and the combined
`(theta1+theta2)`-density bound for their conjunction (paper cor-32, lines 3491-3498). -/
theorem aux_cor_32_extragood_bound_of_base_and_extra
    {d : ℕ} (H1 : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Good1 Good2 : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω)
    (theta1 theta2 : ℝ)
    (Bbase Bextra : Ω → ℝ)
    (hBbaseMeas : Measurable Bbase) (hBbaseNonneg : ∀ omega, 0 ≤ Bbase omega)
    (hBextraMeas : Measurable Bextra) (hBextraNonneg : ∀ omega, 0 ≤ Bextra omega)
    (hBase : ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
      ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
        (Nat.card {j : Fin J // ¬ omega ∈ Good1 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
          theta1 * (J : ℝ) + Bbase omega)
    (hExtra : ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
      ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
        (Nat.card {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
          theta2 * (J : ℝ) + Bextra omega) :
    ∃ Bnew : Ω → ℝ, Measurable Bnew ∧ (∀ omega, 0 ≤ Bnew omega) ∧
      ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
        ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
          (Nat.card {j : Fin J // ¬ (omega ∈ Good1 (j.val + 1)
              (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩) ∧
            omega ∈ Good2 (j.val + 1)
              (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
            (theta1 + theta2) * (J : ℝ) + Bnew omega := by
  refine ⟨fun omega => Bbase omega + Bextra omega, hBbaseMeas.add hBextraMeas,
    fun omega => add_nonneg (hBbaseNonneg omega) (hBextraNonneg omega), ?_⟩
  filter_upwards [hBase, hExtra] with omega hB hE J hJ pi
  have h_card := aux_cor_32_card_and_le H1 Good1 Good2 omega J pi theta1 theta2
    (Bbase omega) (Bextra omega) (hB J hJ pi) (hE J hJ pi)
  simpa using h_card

/-- Consumer: specializing the general assembly lemma to an equal `theta/2` split on both
sides — exactly the split `cor_32`'s `hBaseChain` already uses for the base event — turns any
matching `theta/2`-density extra-test bound into the full `theta`-density `Bnew` bound
`hBound` needs (paper cor-32, lines 3491-3498). -/
theorem aux_cor_32_hBound_of_base_and_extra
    {d : ℕ} (H1 : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Good1 Good2 : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω)
    (theta : ℝ)
    (Bbase Bextra : Ω → ℝ)
    (hBbaseMeas : Measurable Bbase) (hBbaseNonneg : ∀ omega, 0 ≤ Bbase omega)
    (hBextraMeas : Measurable Bextra) (hBextraNonneg : ∀ omega, 0 ≤ Bextra omega)
    (hBase : ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
      ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
        (Nat.card {j : Fin J // ¬ omega ∈ Good1 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
          (theta / 2) * (J : ℝ) + Bbase omega)
    (hExtra : ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
      ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
        (Nat.card {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
          (theta / 2) * (J : ℝ) + Bextra omega) :
    ∃ Bnew : Ω → ℝ, Measurable Bnew ∧ (∀ omega, 0 ≤ Bnew omega) ∧
      ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
        ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
          (Nat.card {j : Fin J // ¬ (omega ∈ Good1 (j.val + 1)
              (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩) ∧
            omega ∈ Good2 (j.val + 1)
              (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
            theta * (J : ℝ) + Bnew omega := by
  obtain ⟨Bnew, hMeas, hNonneg, hBound⟩ :=
    aux_cor_32_extragood_bound_of_base_and_extra H1 P Good1 Good2 (theta / 2) (theta / 2)
      Bbase Bextra hBbaseMeas hBbaseNonneg hBextraMeas hBextraNonneg hBase hExtra
  refine ⟨Bnew, hMeas, hNonneg, ?_⟩
  filter_upwards [hBound] with omega h J hJ pi
  have heq : (theta / 2 + theta / 2) * (J : ℝ) = theta * (J : ℝ) := by ring
  have h' := h J hJ pi
  rw [heq] at h'
  exact h'

/-- Entrywise formula for `Bk n w omega i j` in terms of the entries of `AE`, `AF` and the
constant `ck n w` (paper cor-32, eq:mfd-31 definition of `B_k`). Purely algebraic (`Matrix.sub_apply`,
`Matrix.smul_apply`); used to transport entrywise measurability of `AE`, `AF` to `Bk`. -/
theorem aux_cor_32_bk_entry_eq {d : ℕ} (AEm AFm : Matrix (Fin d) (Fin d) ℝ) (ckv : ℝ) (i j : Fin d) :
    ((Matrix.trace AEm)⁻¹ • (AFm - ckv • AEm)) i j =
      (Matrix.trace AEm)⁻¹ * (AFm i j - ckv * AEm i j) := by
  simp [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, mul_sub]



theorem aux_cor_32_extragood_measurable {d : ℕ} {H1 : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (AE AF : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω →
      Matrix (Fin d) (Fin d) ℝ)
    (hAEmeas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (i j : Fin d),
      Measurable (fun omega : Ω => AE n w omega i j))
    (hAFmeas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (i j : Fin d),
      Measurable (fun omega : Ω => AF n w omega i j))
    (ck : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℝ)
    (BaseGood : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω)
    (hBaseMeas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      MeasurableSet (BaseGood n w))
    (thresh : ℝ)
    (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) :
    MeasurableSet {omega : Ω | omega ∈ BaseGood n w ∧
      (∑ i : Fin d, ∑ j : Fin d,
        |((Matrix.trace (AE n w omega))⁻¹ •
            (AF n w omega - ck n w • AE n w omega)) i j|) ≤ thresh} := by
  have hBk_meas : ∀ i j : Fin d,
      Measurable (fun omega : Ω =>
        ((Matrix.trace (AE n w omega))⁻¹ •
            (AF n w omega - ck n w • AE n w omega)) i j) := by
    intro i j
    have heq : (fun omega : Ω =>
        ((Matrix.trace (AE n w omega))⁻¹ •
            (AF n w omega - ck n w • AE n w omega)) i j) =
        (fun omega : Ω =>
          (Matrix.trace (AE n w omega))⁻¹ *
            (AF n w omega i j - ck n w * AE n w omega i j)) := by
      funext omega
      exact aux_cor_32_bk_entry_eq (AE n w omega) (AF n w omega) (ck n w) i j
    rw [heq]
    have htrace_meas : Measurable (fun omega : Ω => Matrix.trace (AE n w omega)) := by
      have : (fun omega : Ω => Matrix.trace (AE n w omega)) =
          fun omega : Ω => ∑ i : Fin d, AE n w omega i i := by
        funext omega; rfl
      rw [this]
      exact Finset.measurable_sum Finset.univ (fun i _ => hAEmeas n w i i)
    exact (htrace_meas.inv).mul
      ((hAFmeas n w i j).sub (measurable_const.mul (hAEmeas n w i j)))
  have hsum_meas : Measurable (fun omega : Ω =>
      ∑ i : Fin d, ∑ j : Fin d,
        |((Matrix.trace (AE n w omega))⁻¹ •
            (AF n w omega - ck n w • AE n w omega)) i j|) :=
    Finset.measurable_sum Finset.univ fun i _ =>
      Finset.measurable_sum Finset.univ fun j _ => (hBk_meas i j).abs
  exact (hBaseMeas n w).inter (measurableSet_le hsum_meas measurable_const)

/-- The `Bk`-based test statistic alone (no `BaseGood` intersection), same entrywise-measurable
argument as `aux_cor_32_extragood_measurable`'s internal `hsum_meas`, factored out for reuse by
the extra-test all-chain construction (`aux_cor_32_extra_chain`). -/
theorem aux_cor_32_test_measurable {d : ℕ} {H1 : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (AE AF : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω →
      Matrix (Fin d) (Fin d) ℝ)
    (hAEmeas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (i j : Fin d),
      Measurable (fun omega : Ω => AE n w omega i j))
    (hAFmeas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (i j : Fin d),
      Measurable (fun omega : Ω => AF n w omega i j))
    (ck : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℝ)
    (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) :
    Measurable (fun omega : Ω =>
      ∑ i : Fin d, ∑ j : Fin d,
        |((Matrix.trace (AE n w omega))⁻¹ •
            (AF n w omega - ck n w • AE n w omega)) i j|) := by
  have hBk_meas : ∀ i j : Fin d,
      Measurable (fun omega : Ω =>
        ((Matrix.trace (AE n w omega))⁻¹ •
            (AF n w omega - ck n w • AE n w omega)) i j) := by
    intro i j
    have heq : (fun omega : Ω =>
        ((Matrix.trace (AE n w omega))⁻¹ •
            (AF n w omega - ck n w • AE n w omega)) i j) =
        (fun omega : Ω =>
          (Matrix.trace (AE n w omega))⁻¹ *
            (AF n w omega i j - ck n w * AE n w omega i j)) := by
      funext omega
      exact aux_cor_32_bk_entry_eq (AE n w omega) (AF n w omega) (ck n w) i j
    rw [heq]
    have htrace_meas : Measurable (fun omega : Ω => Matrix.trace (AE n w omega)) := by
      have : (fun omega : Ω => Matrix.trace (AE n w omega)) =
          fun omega : Ω => ∑ i : Fin d, AE n w omega i i := by
        funext omega; rfl
      rw [this]
      exact Finset.measurable_sum Finset.univ (fun i _ => hAEmeas n w i i)
    exact (htrace_meas.inv).mul
      ((hAFmeas n w i j).sub (measurable_const.mul (hAEmeas n w i j)))
  exact Finset.measurable_sum Finset.univ fun i _ =>
    Finset.measurable_sum Finset.univ fun j _ => (hBk_meas i j).abs

theorem aux_iIndepFun_precomp
    {Om Om' ι X : Type*} [MeasurableSpace Om] [MeasurableSpace Om'] [MeasurableSpace X]
    (P : Measure Om) (Q : Measure Om') (Y : Om → Om') (hY : Measurable Y)
    (hmap : Measure.map Y P = Q)
    (g : ι → Om' → X) (hg_meas : ∀ i, Measurable (g i))
    (hindep : ProbabilityTheory.iIndepFun g Q) :
    ProbabilityTheory.iIndepFun (fun i => g i ∘ Y) P := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff] at hindep ⊢
  intro s F hF
  have hex : ∀ i ∈ s, ∃ t : Set X, MeasurableSet t ∧ (g i ∘ Y) ⁻¹' t = F i := by
    intro i hi
    exact MeasurableSpace.measurableSet_comap.mp (hF i hi)
  let t : ι → Set X := fun i => if hi : i ∈ s then Classical.choose (hex i hi) else ∅
  have ht : ∀ i ∈ s, MeasurableSet (t i) ∧ (g i ∘ Y) ⁻¹' (t i) = F i := by
    intro i hi
    simp only [t, dif_pos hi]
    exact Classical.choose_spec (hex i hi)
  have hFeq : ∀ i ∈ s, F i = Y ⁻¹' (g i ⁻¹' t i) := by
    intro i hi
    rw [← (ht i hi).2]
    rfl
  have hInter : (⋂ i ∈ s, F i) = Y ⁻¹' (⋂ i ∈ s, g i ⁻¹' t i) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h i hi
      have h2 := h i hi
      rw [hFeq i hi] at h2
      simpa using h2
    · intro h i hi
      rw [hFeq i hi]
      simpa using h i hi
  have hmeasInter : MeasurableSet (⋂ i ∈ s, g i ⁻¹' t i) :=
    MeasurableSet.biInter s.countable_toSet (fun i hi => (hg_meas i) ((ht i hi).1))
  have hPF : P (⋂ i ∈ s, F i) = Q (⋂ i ∈ s, g i ⁻¹' t i) := by
    rw [hInter, ← hmap, Measure.map_apply hY hmeasInter]
  have hprodF : ∀ i ∈ s, P (F i) = Q (g i ⁻¹' t i) := by
    intro i hi
    rw [hFeq i hi, ← hmap, Measure.map_apply hY (hg_meas i (ht i hi).1)]
  have hkey : Q (⋂ i ∈ s, g i ⁻¹' t i) = ∏ i ∈ s, Q (g i ⁻¹' t i) :=
    hindep s (fun i hi => MeasurableSpace.measurableSet_comap.mpr ⟨t i, (ht i hi).1, rfl⟩)
  rw [hPF, hkey]
  exact Finset.prod_congr rfl (fun i hi => (hprodF i hi).symm)

theorem aux_cor_32_field_layers_iIndepFun
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (field : Ω → BilateralField d) (hfield_meas : Measurable field)
    (hfield_map : Measure.map field P = (chaosSampleLaw model).toMeasure) :
    ProbabilityTheory.iIndepFun (fun (j:ℤ) (omega:Ω) => field omega j) P := by
  have hg_indep : ProbabilityTheory.iIndepFun (fun (j:ℤ) (bf:BilateralField d) => bf j)
      (chaosSampleLaw model).toMeasure := by
    change ProbabilityTheory.iIndepFun (fun j (omega : ℤ → C(SpatialCoordinates d, ℝ)) => omega j)
      (Measure.infinitePi (fun j : ℤ =>
        (SubdiffusiveProcess.scaledLayerLaw d (SubdiffusiveProcess.chaosRootFieldLaw model) j :
          Measure C(SpatialCoordinates d, ℝ))))
    exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
  exact aux_iIndepFun_precomp P (chaosSampleLaw model).toMeasure field hfield_meas hfield_map
    (fun j bf => bf j) (fun j => measurable_pi_apply j) hg_indep




theorem aux_cor_32_node_cover
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (p A q r K Cbound lam0 : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (hCbound : 0 ≤ Cbound) (hlam0 : 0 < lam0)
    (hKdef : K = lam0 * (1 - r) / 2)
    (hbudget : ∀ k : ℕ,
      2 * ((2 * (Cbound / q * q ^ k) / (K * r ^ k)) ^ p) ≤ Real.exp (-(A * ((k : ℝ) + 1))))
    (Band : ℕ → MeasurableSpace Ω) (hBand_mono : Monotone Band)
    (T : Ω → ℝ) (Tb : ℕ → Ω → ℝ)
    (hTb_meas : ∀ H, StronglyMeasurable[Band H] (Tb H))
    (hTb_ae : ∀ H, AEStronglyMeasurable (Tb H) P)
    (hT_ae : AEStronglyMeasurable T P)
    (hnT : eLpNorm T (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cbound)
    (herr : ∀ H, eLpNorm (fun om => T om - Tb H om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cbound * q ^ H))
    (Sigma : Set Ω) (hlimit : ∀ ω ∈ Sigma, Tendsto (fun H => Tb H ω) atTop (𝓝 (T ω))) :
    ∃ W : ℕ+ → Set Ω,
      (∀ h : ℕ+, MeasurableSet[Band h] (W h)) ∧
      (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-(A * (h : ℝ))))) ∧
      Sigma ∩ {ω | lam0 ≤ T ω} ⊆ ⋃ h : ℕ+, W h := by
  have hK : 0 < K := by
    rw [hKdef]; exact div_pos (mul_pos hlam0 (by linarith)) (by norm_num)
  let E : ℕ → Set Ω := fun k => {om | K * r ^ k ≤ |aux_increment (fun H => Tb H om) k|}
  have hYmeas : ∀ k : ℕ,
      StronglyMeasurable[Band k] (fun om => aux_increment (fun H => Tb H om) k) := by
    intro k
    cases k with
    | zero => simpa [aux_increment] using hTb_meas 0
    | succ k =>
        have h1 : StronglyMeasurable[Band (k+1)] (Tb (k+1)) := hTb_meas (k+1)
        have h2 : StronglyMeasurable[Band (k+1)] (Tb k) :=
          (hTb_meas k).mono (hBand_mono (Nat.le_succ k))
        simpa only [aux_increment, Pi.sub_apply] using! h1.sub h2
  have hEmeas : ∀ k : ℕ, MeasurableSet[Band k] (E k) := by
    intro k
    letI : MeasurableSpace Ω := Band k
    exact measurableSet_le measurable_const (hYmeas k).measurable.abs
  have hEprob : ∀ k : ℕ, P (E k) ≤ ENNReal.ofReal (Real.exp (-(A * ((k : ℝ) + 1)))) := by
    intro k
    have hthresh : 0 < K * r ^ k := mul_pos hK (pow_pos hr k)
    have htail := aux_increment_tail P p Cbound q hp hCbound hq hq1
      T Tb hT_ae hTb_ae hnT herr k (K * r ^ k) hthresh
    exact htail.trans (ENNReal.ofReal_le_ofReal (hbudget k))
  have hcover : Sigma ∩ {ω | lam0 ≤ T ω} ⊆ ⋃ k : ℕ, E k := by
    intro om hom
    obtain ⟨k, hk⟩ := aux_increment_witness (fun H => Tb H om) (T om) lam0 r hlam0 hr.le
      (hlimit om hom.1) hom.2
    exact Set.mem_iUnion.mpr ⟨k, by simpa [E, hKdef] using hk⟩
  let w : ℕ → ℕ+ := fun k => ⟨k + 1, Nat.succ_pos k⟩
  have hw : Function.Injective w := by
    intro j k hjk
    have : j + 1 = k + 1 := congrArg (fun h : ℕ+ => (h : ℕ)) hjk
    omega
  have hEmeas' : ∀ k : ℕ, MeasurableSet[Band (w k)] (E k) := by
    intro k
    have hle : Band k ≤ Band (w k) := hBand_mono (by simp [w])
    exact hle (E k) (hEmeas k)
  have hEprob' : ∀ k : ℕ, P (E k) ≤ ENNReal.ofReal (Real.exp (-(A * ((w k : ℕ) : ℝ)))) := by
    intro k
    have : ((w k : ℕ) : ℝ) = (k : ℝ) + 1 := by simp [w]
    rw [this]
    exact hEprob k
  obtain ⟨W, hWmeas, hWprob, hWcover⟩ :=
    aux_reindex_cover P (fun h : ℕ+ => Band (h : ℕ))
      (fun h => ENNReal.ofReal (Real.exp (-(A * (h : ℝ)))))
      (Sigma ∩ {ω | lam0 ≤ T ω}) w hw E hEmeas' hEprob' hcover
  exact ⟨W, hWmeas, hWprob, hWcover⟩



-- Reproduces prop_allchain's own `hrate` computation (lines ~104-156 of

-- c := 3^(H1*d) (matching Fintype.card (OddGridIndex d (subdivisionHalfWidth H1))^K's log).
theorem aux_cor_32_A_beats_log_card
    (H1 d : ℕ) (theta A : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hAeq : A = 2 * Real.log 2 + 1 + (48 / theta) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) :
    1 + ((H1 * d : ℕ) : ℝ) * Real.log 3 ≤
      A * (theta / 2) / 24 + Real.log (1 - Real.exp (-A / 2)) := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hHd_nonneg : (0:ℝ) ≤ ((H1 * d : ℕ) : ℝ) := by positivity
  have hlog3nonneg : 0 ≤ Real.log (3:ℝ) := Real.log_nonneg (by norm_num)
  have hK : (0:ℝ) < 1 + ((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 1 := by positivity
  have hApos : 0 < A := by
    have h48 : 0 < (48:ℝ)/theta := div_pos (by norm_num) htheta0
    nlinarith [hHd_nonneg, hlog3nonneg, hlog2]
  have hAterm : A * (theta / 2) / 24 =
      (2 * Real.log 2 + 1) * (theta / 2) / 24 +
        (1 + ((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 1) := by
    have hθ2 : theta / 2 ≠ 0 := by positivity
    rw [hAeq]
    field_simp
    ring
  have hAhalf : -A / 2 ≤ -Real.log 2 := by
    have h48 : 0 < (48:ℝ)/theta := div_pos (by norm_num) htheta0
    nlinarith [hHd_nonneg, hlog3nonneg]
  have hexphalf : Real.exp (-A / 2) ≤ (1 / 2 : ℝ) := by
    calc
      Real.exp (-A / 2) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr hAhalf
      _ = (1 / 2 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
  have hlograte : -Real.log 2 ≤ Real.log (1 - Real.exp (-A / 2)) := by
    have hsub : (1 / 2 : ℝ) ≤ 1 - Real.exp (-A / 2) := by linarith
    have hlog := Real.log_le_log (by norm_num : (0:ℝ) < 1 / 2) hsub
    have heq : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  rw [hAterm]
  nlinarith [hlograte]



theorem aux_cor_32_rate_and_delta0
    (H1 d : ℕ) (theta eps c0 p Cp aexp : ℝ)
    (htheta : 0 < theta) (htheta1 : theta < 1) (heps : 0 < eps) (hc0 : 0 < c0)
    (hp : 0 < p) (hCp : 0 < Cp) (haexp : 0 < aexp)
    (hpRate : 2 * (2 * Real.log 2 + 1 + (48 / theta) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3) :
    ∃ A q r K delta0 : ℝ,
      0 < A ∧ q = (3 : ℝ) ^ (-aexp) ∧ 0 < q ∧ q < 1 ∧ 0 < r ∧ r < 1 ∧
      K = eps * c0 * (1 - r) / 2 ∧ 0 < K ∧ 0 < delta0 ∧
      (∀ eta : ℝ, 0 < eta → eta ≤ delta0 → ∀ k : ℕ,
        2 * ((2 * (Cp * eta / q * q ^ k) / (K * r ^ k)) ^ p) ≤
          Real.exp (-(A * ((k : ℝ) + 1)))) ∧
      (1 + ((H1 * d : ℕ) : ℝ) * Real.log 3 ≤
        A * (theta / 2) / 24 + Real.log (1 - Real.exp (-A / 2))) := by
  set A : ℝ := 2 * Real.log 2 + 1 + (48 / theta) *
      (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2) with hAdef
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hHd_nonneg : (0:ℝ) ≤ ((H1 * d : ℕ) : ℝ) := by positivity
  have hApos : 0 < A := by
    rw [hAdef]
    have h48 : 0 < (48:ℝ) / theta := div_pos (by norm_num) htheta
    have hinner : 0 < ((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2 := by positivity
    nlinarith
  have hgap : A < aexp * p * Real.log 3 := by
    have h2A : A < 2 * A := by linarith
    nlinarith [hpRate]
  obtain ⟨q, r, hqeq, hq, hq1, hr, hr1, hrate⟩ :=
    aux_geometric_rate aexp A p haexp hp hgap
  set K : ℝ := eps * c0 * (1 - r) / 2 with hKdef
  have hK : 0 < K := by
    rw [hKdef]
    exact div_pos (mul_pos (mul_pos heps hc0) (by linarith)) (by norm_num)
  obtain ⟨eta0, heta0pos, hbudget⟩ :=
    aux_geometric_budget 1 p A Cp q r K hp hCp hq hr hK hrate
  refine ⟨A, q, r, K, eta0, hApos, hqeq, hq, hq1, hr, hr1, hKdef, hK, heta0pos, ?_, ?_⟩
  · intro eta heta hetale k
    have := hbudget eta heta hetale k
    simpa using this
  · exact aux_cor_32_A_beats_log_card H1 d theta A htheta htheta1 hAdef



-- Measurability transport: cor_32's own `Band` window (symmetric radius, centred at -(H1*n))
-- is a sub-sigma-algebra of `branch_many_bad_nodes`/`union_bound_finitely_many_bad_branches`'s
-- own asymmetric window `Icc(n_i - h, n_i + 2h)` via `g(-j)`, for `n_i := H1*n` and any `h ≥ radius`.
theorem aux_cor_32_band_le_branch_window
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (g : ℤ → Ω → X) (nidx radius bound : ℤ) (hradius : radius ≤ bound) :
    (⨆ (j : ℤ) (_ : |j + nidx| ≤ radius), MeasurableSpace.comap (g j) ‹MeasurableSpace X›) ≤
      ⨆ (j : ℤ) (_ : j ∈ Finset.Icc (nidx - bound) (nidx + 2 * bound)),
        MeasurableSpace.comap (g (-j)) ‹MeasurableSpace X› := by
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  have hmem : (-j) ∈ Finset.Icc (nidx - bound) (nidx + 2 * bound) := by
    simp only [Finset.mem_Icc]
    rw [abs_le] at hj
    omega
  have heq : MeasurableSpace.comap (g j) ‹MeasurableSpace X› =
      MeasurableSpace.comap (g (-(-j))) ‹MeasurableSpace X› := by
    rw [neg_neg]
  rw [heq]
  exact le_iSup₂ (f := fun j (_ : j ∈ Finset.Icc (nidx - bound) (nidx + 2 * bound)) =>
    MeasurableSpace.comap (g (-j)) ‹MeasurableSpace X›) (-j) hmem



theorem aux_geometric_rpow_tsum_ne_top_base
    (C q p : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) (hp : 0 < p) :
    (∑' n : ℕ, ENNReal.ofReal (C * q ^ n) ^ p) ≠ ∞ := by
  have hqp1 : (q ^ p : ℝ) < 1 := Real.rpow_lt_one hq0 hq1 hp
  have hs : Summable (fun n : ℕ => C ^ p * (q ^ p) ^ n) :=
    (summable_geometric_of_lt_one (Real.rpow_nonneg hq0 p) hqp1).mul_left (C ^ p)
  have heq : ∀ n : ℕ, ENNReal.ofReal (C * q ^ n) ^ p = ENNReal.ofReal (C ^ p * (q ^ p) ^ n) := by
    intro n
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC (pow_nonneg hq0 n)) hp.le,
      Real.mul_rpow hC (pow_nonneg hq0 n), ← Real.rpow_natCast (q ^ p), ← Real.rpow_natCast q,
      ← Real.rpow_mul hq0, ← Real.rpow_mul hq0, mul_comm (p : ℝ) (n : ℝ)]
  rw [tsum_congr heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (Real.rpow_nonneg hC p) (pow_nonneg (Real.rpow_nonneg hq0 p) n)) hs]
  exact ENNReal.ofReal_ne_top

theorem aux_ae_tendsto_zero_of_geometric_base
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p q C : ℝ) (hp : 0 < p) (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (herr : ∀ n, eLpNorm (f n) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (C * q ^ n)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (0 : ℝ)) := by
  have hsum_le : (∑' n : ℕ, eLpNorm (f n) (ENNReal.ofReal p) P ^ p) ≤
      ∑' n : ℕ, ENNReal.ofReal (C * q ^ n) ^ p :=
    ENNReal.tsum_le_tsum (fun n => ENNReal.rpow_le_rpow (herr n) hp.le)
  have hsum : (∑' n : ℕ, eLpNorm (f n) (ENNReal.ofReal p) P ^ p) ≠ ∞ :=
    ne_top_of_le_ne_top (aux_geometric_rpow_tsum_ne_top_base C q p hC hq0 hq1 hp) hsum_le
  exact aux_ae_tendsto_zero_of_eLpNorm_rpow_tsum P p hp f hf hsum


theorem aux_cor_32_budget_scale (p Cp q K0 A r t : ℝ) (hq : q ≠ 0) (hK0 : K0 ≠ 0) (hr : r ≠ 0)
    (ht : t ≠ 0)
    (hbudget0 : ∀ k : ℕ, 2 * ((2 * (Cp / q * q ^ k) / (K0 * r ^ k)) ^ p) ≤
      Real.exp (-(A * ((k : ℝ) + 1)))) :
    ∀ k : ℕ, 2 * ((2 * ((Cp * t) / q * q ^ k) / ((K0 * t) * r ^ k)) ^ p) ≤
      Real.exp (-(A * ((k : ℝ) + 1))) := by
  intro k
  have heq : (2 * ((Cp * t) / q * q ^ k) / ((K0 * t) * r ^ k)) =
      (2 * (Cp / q * q ^ k) / (K0 * r ^ k)) := by
    have hrk : r ^ k ≠ 0 := pow_ne_zero k hr
    field_simp
  rw [heq]
  exact hbudget0 k


end
end Paper
