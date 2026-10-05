module

public import SubdiffusiveProcess.Section10.ClassicalBrownianFDD

@[expose] public section

/-! Finite increment determination on the actual compact-open continuous path carrier. -/
open MeasureTheory MarkovProcess
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The vector of successive increments along a finite ordered time family. -/
def pathIncrements {d n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (w : FiniteRealPath d) : Fin n → Fin d → ℝ :=
  fun j => w (t j.succ) - w (t j.castSucc)

theorem measurable_pathIncrements {d n : ℕ} (t : Fin (n + 1) → ℝ≥0) :
    Measurable (pathIncrements (d := d) t) := by
  apply Measurable.of_eval
  intro j
  exact (ContinuousEvalConst.continuous_eval_const (t j.succ)).measurable.sub
    (ContinuousEvalConst.continuous_eval_const (t j.castSucc)).measurable

/-- Expand a continuous real functional into coefficients on the finite coordinates. -/
theorem finite_dual_coordinates {d n : ℕ}
    (L : StrongDual ℝ (Fin n → Fin d → ℝ)) (v : Fin n → Fin d → ℝ) :
    L v = ∑ j : Fin n, ∑ i : Fin d,
      L (Pi.single j (Pi.single i 1)) * v j i := by
  classical
  rw [← L.sum_comp_single]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← (L.comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => Fin d → ℝ) j)).sum_comp_single]
  apply Finset.sum_congr rfl
  intro i hi
  change L (Pi.single j (Pi.single i (v j i))) =
    L (Pi.single j (Pi.single i 1)) * v j i
  have hs : Pi.single j (Pi.single i (v j i)) =
      v j i • (Pi.single j (Pi.single i (1 : ℝ)) : Fin n → Fin d → ℝ) := by
    ext k l
    by_cases hk : k = j <;> by_cases hl : l = i <;>
      simp [smul_eq_mul, hk, hl]
  rw [hs, map_smul]
  exact mul_comm _ _

/-- Prefix reconstruction of a finite sequence from its successive differences. -/
theorem sum_prefix_increments {n : ℕ} {E : Type*} [AddCommGroup E]
    (f : Fin (n + 1) → E) (k : Fin (n + 1)) :
    (∑ j : Fin n, if j.val < k.val then f j.succ - f j.castSucc else 0) =
      f k - f 0 := by
  classical
  induction k using Fin.induction with
  | zero => simp
  | succ i ih =>
    have hs : ∀ j : Fin n,
        (if j.val < i.succ.val then f j.succ - f j.castSucc else 0) =
          (if j.val < i.castSucc.val then f j.succ - f j.castSucc else 0) +
            (if j = i then f i.succ - f i.castSucc else 0) := by
      intro j
      simp only [Fin.val_succ, Fin.val_castSucc]
      by_cases hji : j = i
      · subst j
        simp
      · by_cases hlt : j.val < i.val
        · simp only [ite_eq_left (Nat.lt_succ_of_lt hlt), ite_eq_left hlt, ite_eq_right hji, add_zero]
        · have hnot : ¬ j.val < i.val + 1 := by
            have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
            omega
          simp only [ite_eq_right hlt, ite_eq_right hnot, ite_eq_right hji, add_zero]
    simp_rw [hs]
    rw [Finset.sum_add_distrib, ih, Fintype.sum_ite_eq']
    abel

/-- Inserting time zero before a monotone nonnegative time sequence preserves order. -/
theorem monotone_cons_zero {n : ℕ} (u : Fin n → ℝ≥0) (hu : Monotone u) :
    Monotone (Fin.cons 0 u) := by
  intro i j hij
  cases i using Fin.cases with
  | zero => simpa only [Fin.cons_zero] using! (bot_le : 0 ≤ Fin.cons (α := fun _ => ℝ≥0) 0 u j)
  | succ i =>
    cases j using Fin.cases with
    | zero => have : i.succ.val ≤ (0 : Fin (n + 1)).val := hij; simp at this
    | succ j => exact hu (by simpa only [Fin.succ_le_succ_iff] using hij)

/-- Ordered increment laws determine finite path laws when both paths start at zero.
The time list may contain repetitions, including time zero. -/
theorem finite_path_measure_eq_of_increment_map_eq
    {d : ℕ} (Q R : Measure (FiniteRealPath d))
    [IsFiniteMeasure Q] [IsFiniteMeasure R]
    (hQ0 : ∀ᵐ w ∂Q, w 0 = 0) (hR0 : ∀ᵐ w ∂ R, w 0 = 0)
    (hinc : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      Q.map (pathIncrements t) = R.map (pathIncrements t)) : Q = R := by
  classical
  apply finiteRealPath_measure_eq_of_fdd_charFunDual
  intro I
  let e : Fin I.card ≃o I := I.orderIsoOfFin rfl
  let u : Fin I.card → ℝ≥0 := fun j => (e j : ℝ≥0)
  let t : Fin (I.card + 1) → ℝ≥0 := Fin.cons 0 u
  have ht : Monotone t := monotone_cons_zero u
    (fun i j hij => e.monotone hij)
  let reconstruct : (Fin I.card → Fin d → ℝ) → I → Fin d → ℝ :=
    fun v s => ∑ j : Fin I.card, if j.val ≤ (e.symm s).val then v j else 0
  have hm : Measurable reconstruct := by
    apply Continuous.measurable
    apply continuous_pi
    intro s
    apply continuous_finsetSum
    intro j hj
    by_cases h : j.val ≤ (e.symm s).val
    · simp only [ite_eq_left h]
      exact continuous_apply j
    · simp only [ite_eq_right h]
      exact continuous_const
  have key : ∀ (P : Measure (FiniteRealPath d)), (∀ᵐ w ∂P, w 0 = 0) →
      P.map (ContinuousPath.finiteEvaluation (fun s : I => (s : ℝ≥0))) =
        (P.map (pathIncrements t)).map reconstruct := by
    intro P hP
    rw [Measure.map_map hm (measurable_pathIncrements t)]
    apply Measure.map_congr
    filter_upwards [hP] with w hw
    funext s
    change w (s : ℝ≥0) =
      ∑ j : Fin I.card, if j.val ≤ (e.symm s).val then
        w (t j.succ) - w (t j.castSucc) else 0
    symm
    calc
      _ = w (t (e.symm s).succ) - w (t 0) := by
        simpa only [Fin.val_succ, Nat.lt_succ_iff] using
          sum_prefix_increments (fun j => w (t j)) (e.symm s).succ
      _ = w (s : ℝ≥0) := by
        simp only [t, Fin.cons_succ, Fin.cons_zero, u, e.apply_symm_apply, hw, sub_zero]
  rw [key Q hQ0, key R hR0, hinc I.card t ht]

/-- Equality of ordered increment characteristic functions determines centered path laws. -/
theorem finite_path_measure_eq_of_increment_charFun
    {d : ℕ} (Q R : Measure (FiniteRealPath d))
    [IsFiniteMeasure Q] [IsFiniteMeasure R]
    (hQ0 : ∀ᵐ w ∂Q, w 0 = 0) (hR0 : ∀ᵐ w ∂ R, w 0 = 0)
    (hinc : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      ∀ xi : Fin n → Fin d → ℝ,
        (∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
            ((xi j i * pathIncrements t w j i : ℝ) : ℂ)) ∂Q) =
          ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
            ((xi j i * pathIncrements t w j i : ℝ) : ℂ)) ∂ R) : Q = R := by
  apply finite_path_measure_eq_of_increment_map_eq Q R hQ0 hR0
  intro n t ht
  apply Measure.ext_of_charFunDual
  funext L
  have key : ∀ P : Measure (FiniteRealPath d),
      charFunDual (P.map (pathIncrements t)) L =
        ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
          ((L (Pi.single j (Pi.single i 1)) * pathIncrements t w j i : ℝ) : ℂ)) ∂P := by
    intro P
    rw [charFunDual_apply, integral_map (measurable_pathIncrements t).aemeasurable
      (by fun_prop)]
    apply integral_congr_ae
    filter_upwards with w
    rw [finite_dual_coordinates]
    simp only [Complex.ofReal_sum, mul_comm Complex.I]
  rw [key Q, key R]
  exact hinc n t ht _

end SubdiffusiveProcess.Section10
