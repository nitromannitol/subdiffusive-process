module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess

/-- The unrestricted weighted sum over optional positive-radius witnesses at finitely many anchors. -/
theorem tsum_optional_witness_weights (J : ℕ) (A : ℝ) (hA : 0 < A) :
    (∑' w : Fin J → Option ℕ+,
      ∏ i : Fin J, (w i).elim (1 : ℝ≥0∞)
        (fun h => ENNReal.ofReal (Real.exp (-A * (h : ℝ) / 2)))) =
      ENNReal.ofReal (((1 - Real.exp (-A / 2))⁻¹) ^ J) := by
  let f : Option ℕ+ → ℝ≥0∞ := fun o =>
    o.elim (1 : ℝ≥0∞)
      (fun h => ENNReal.ofReal (Real.exp (-A * (h : ℝ) / 2)))
  have hopt (g : Option ℕ+ → ℝ≥0∞) :
      (∑' o, g o) = g none + ∑' p : ℕ+, g (some p) := by
    let eo := Equiv.optionEquivSumPUnit ℕ+
    let es := Equiv.sumEquivSigmaBool ℕ+ PUnit
    calc
      (∑' o, g o) = ∑' s : ℕ+ ⊕ PUnit, g (eo.symm s) :=
        (eo.symm.tsum_eq g).symm
      _ = ∑' z : (b : Bool) × bif b then PUnit else ℕ+,
          g (eo.symm (es.symm z)) := by
        exact (es.symm.tsum_eq (fun s => g (eo.symm s))).symm
      _ = g none + ∑' p : ℕ+, g (some p) := by
        change (∑' z : (b : Bool) × bif b then PUnit else ℕ+,
          (fun b x => g (eo.symm (es.symm ⟨b, x⟩))) z.1 z.2) = _
        have hs := ENNReal.tsum_sigma
          (fun b x => g (eo.symm (es.symm ⟨b, x⟩)))
        rw [hs]
        simp [eo, es, Equiv.sumEquivSigmaBool, Equiv.optionEquivSumPUnit,
          tsum_fintype]
        rfl
  have hneg : -A / 2 < 0 := by linarith
  have hexp : Real.exp (-A / 2) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hneg
  have hq : ENNReal.ofReal (Real.exp (-A / 2)) < 1 :=
    ENNReal.ofReal_lt_one.mpr hexp
  have hcoord : (∑' o, f o) =
      (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ := by
    rw [hopt]
    have hpnat : (∑' p : ℕ+, f (some p)) =
        ∑' n : ℕ, ENNReal.ofReal (Real.exp (-A * ((n + 1 : ℕ) : ℝ) / 2)) := by
      rw [← (Equiv.pnatEquivNat.symm.tsum_eq (fun n : ℕ+ => f (some n)))]
      simp [f, Equiv.pnatEquivNat]
    rw [hpnat]
    rw [show (∑' n : ℕ, ENNReal.ofReal (Real.exp (-A * ((n + 1 : ℕ) : ℝ) / 2))) =
        ∑' n : ℕ, (ENNReal.ofReal (Real.exp (-A / 2))) ^ (n + 1) by
      apply tsum_congr
      intro n
      rw [← ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [← Real.exp_nat_mul]
      ring_nf]
    rw [ENNReal.tsum_geometric_add_one]
    have hsub : 1 - ENNReal.ofReal (Real.exp (-A / 2)) ≠ 0 :=
      ne_of_gt (tsub_pos_iff_lt.mpr hq)
    have hmul :
        (1 - ENNReal.ofReal (Real.exp (-A / 2))) *
            (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ = 1 := by
      exact ENNReal.mul_inv_cancel
        hsub (by simp)
    simp only [f, Option.elim_none]
    calc
      1 + ENNReal.ofReal (Real.exp (-A / 2)) *
          (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ =
          (1 - ENNReal.ofReal (Real.exp (-A / 2))) *
              (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ +
            ENNReal.ofReal (Real.exp (-A / 2)) *
              (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ := by
            rw [hmul]
      _ = (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ := by
        rw [← add_mul, tsub_add_cancel_of_le hq.le, one_mul]
  have hfactor : ∀ n : ℕ,
      (∑' w : Fin n → Option ℕ+, ∏ i : Fin n, f (w i)) =
        (∑' o : Option ℕ+, f o) ^ n := by
    intro n
    induction n with
    | zero =>
        simp [tsum_fintype]
    | succ n ih =>
        let ec := Fin.consEquiv (fun _ : Fin (n + 1) => Option ℕ+)
        calc
          (∑' w : Fin (n + 1) → Option ℕ+, ∏ i : Fin (n + 1), f (w i)) =
              ∑' p : Option ℕ+ × (Fin n → Option ℕ+),
                ∏ i : Fin (n + 1), f ((ec p) i) := by
            exact (ec.tsum_eq (fun w => ∏ i : Fin (n + 1), f (w i))).symm
          _ = ∑' b : Option ℕ+, ∑' v : Fin n → Option ℕ+,
                f b * ∏ i : Fin n, f (v i) := by
            change (∑' p : Option ℕ+ × (Fin n → Option ℕ+),
              (fun b v => ∏ i : Fin (n + 1), f ((ec (b, v)) i)) p.1 p.2) = _
            calc
              (∑' p : Option ℕ+ × (Fin n → Option ℕ+),
                (fun b v => ∏ i : Fin (n + 1), f ((ec (b, v)) i)) p.1 p.2) =
                  ∑' b : Option ℕ+, ∑' v : Fin n → Option ℕ+,
                    ∏ i : Fin (n + 1), f ((ec (b, v)) i) := by
                      simpa using (ENNReal.tsum_prod
                        (f := fun b v => ∏ i : Fin (n + 1), f ((ec (b, v)) i)))
              _ = ∑' b : Option ℕ+, ∑' v : Fin n → Option ℕ+,
                    f b * ∏ i : Fin n, f (v i) := by
                apply tsum_congr
                intro b
                apply tsum_congr
                intro v
                simp [ec, Fin.prod_univ_succ]
          _ = (∑' b : Option ℕ+, f b) *
                (∑' v : Fin n → Option ℕ+, ∏ i : Fin n, f (v i)) := by
            simp_rw [ENNReal.tsum_mul_left]
            rw [ENNReal.tsum_mul_right]
          _ = (∑' o : Option ℕ+, f o) ^ (n + 1) := by
            rw [ih, pow_succ, mul_comm]
  change (∑' w : Fin J → Option ℕ+, ∏ i : Fin J, f (w i)) = _
  rw [hfactor J, hcoord]
  have hbase : ENNReal.ofReal ((1 - Real.exp (-A / 2))⁻¹) =
      (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (sub_pos.mpr hexp)]
    rw [ENNReal.ofReal_sub (1 : ℝ) (le_of_lt (Real.exp_pos _))]
    simp
  rw [← hbase, ← ENNReal.ofReal_pow
    (le_of_lt (inv_pos.mpr (sub_pos.mpr hexp)))]

end SubdiffusiveProcess
