module

public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Paper.in_responses

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal BigOperators
/-! Adjacent physical reference scalars are compared using their exact signed prefixes and annealed ordering. -/
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A signed integer prefix gains exactly one term at each nonnegative endpoint. -/
theorem aux_goodext_adjacent_reference_signed_increment (f : ℤ → ℝ) (k : ℕ) :
    (if 0 ≤ (k : ℤ) then ∑ j ∈ Finset.Ico (0 : ℤ) k, f j
      else -∑ j ∈ Finset.Ico (k : ℤ) 0, f j) =
      (if 0 ≤ (k : ℤ) - 1 then ∑ j ∈ Finset.Ico (0 : ℤ) ((k : ℤ) - 1), f j
        else -∑ j ∈ Finset.Ico ((k : ℤ) - 1) 0, f j) + f ((k : ℤ) - 1) := by
  cases k with
  | zero =>
    have hint : Finset.Ico (-1 : ℤ) 0 = {-1} := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    norm_num [hint]
  | succ k =>
    have hk : (0 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - 1 := by omega
    rw [ite_eq_left (show (0 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) by omega), ite_eq_left hk]
    have hsum := Finset.sum_Ico_add_eq_sum_Ico_add_one hk f
    have hend : (((k + 1 : ℕ) : ℤ) - 1) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
    rw [hend] at hsum
    exact hsum.symm

/-- Adjacent same-center references differ by at most the intervening layer and annealed normalization. -/
theorem goodext_adjacent_reference
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (xi : BilateralField d) (N k : ℕ) (hk : k ≤ N) (z : SpatialCoordinates d) :
    aux_in_deterministic_onestep_sref M H xi N (k : ℤ) z ≤
      aux_in_deterministic_onestep_sref M H xi N ((k : ℤ) - 1) z *
        Real.exp (_root_.SubdiffusiveProcess.Model.tauSq M.P + |xi (-((k : ℤ) - 1)) z|) := by
  let tau : ℝ := _root_.SubdiffusiveProcess.Model.tauSq M.P
  let kap : ℕ → ℝ := fun j => Real.exp (((j : ℝ) + 1) * tau) * ahom M j
  let ret : ℤ → ℝ := fun l => if 0 ≤ l then
    ∑ j ∈ Finset.Ico (0 : ℤ) l, xi (-j) z else -∑ j ∈ Finset.Ico l (0 : ℤ), xi (-j) z
  have hkap (j : ℕ) : 0 < kap j := mul_pos (Real.exp_pos _) (ahom_pos M j)
  have hkapstep (j : ℕ) : kap j ≤ Real.exp tau * kap (j + 1) := by
    have horder := (Rm.ahom_ordering j (j + 1) (by omega)).2
    have hcast : (((j + 1 : ℕ) : ℝ) - (j : ℝ)) = 1 := by push_cast; ring
    rw [hcast, mul_one] at horder
    calc
      kap j ≤ Real.exp (((j : ℝ) + 1) * tau) * (Real.exp (2 * tau) * ahom M (j + 1)) :=
        mul_le_mul_of_nonneg_left horder (Real.exp_pos _).le
      _ = Real.exp tau * kap (j + 1) := by
        dsimp only [kap]
        rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring
  have hret : ret (k : ℤ) = ret ((k : ℤ) - 1) + xi (-((k : ℤ) - 1)) z :=
    aux_goodext_adjacent_reference_signed_increment (fun j => xi (-j) z) k
  have hidx : ((N : ℤ) - ((k : ℤ) - 1)).toNat = ((N : ℤ) - k).toNat + 1 := by omega
  change kap ((N : ℤ) - k).toNat / kap N * Real.exp (H xi z + ret (k : ℤ)) ≤
    kap ((N : ℤ) - ((k : ℤ) - 1)).toNat / kap N *
      Real.exp (H xi z + ret ((k : ℤ) - 1)) * Real.exp (tau + |xi (-((k : ℤ) - 1)) z|)
  rw [hidx, hret]
  have hE : Real.exp (H xi z + (ret ((k : ℤ) - 1) + xi (-((k : ℤ) - 1)) z)) ≤
      Real.exp (H xi z + ret ((k : ℤ) - 1)) * Real.exp |xi (-((k : ℤ) - 1)) z| := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [le_abs_self (xi (-((k : ℤ) - 1)) z)])
  calc
    _ ≤ (Real.exp tau * kap (((N : ℤ) - k).toNat + 1)) / kap N *
        (Real.exp (H xi z + ret ((k : ℤ) - 1)) * Real.exp |xi (-((k : ℤ) - 1)) z|) :=
      mul_le_mul (div_le_div_of_nonneg_right (hkapstep _) (hkap N).le) hE
        (Real.exp_pos _).le
        (div_nonneg (mul_pos (Real.exp_pos _) (hkap _)).le (hkap N).le)
    _ = _ := by simp only [Real.exp_add]; ring

end SubdiffusiveProcess.Paper
