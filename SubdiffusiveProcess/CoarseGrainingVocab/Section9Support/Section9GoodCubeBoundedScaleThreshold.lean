module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTailThreshold
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
@[expose] public section

/-! A fixed upper bound on the cutoff permits an arbitrarily small dimensionless logarithmic Lipschitz threshold, chosen before the model. -/

set_option autoImplicit false
open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

private def entropyCoef (d : ℕ) (r : ℤ) : ℝ :=
  ((3 * Real.log (((shellCoverShifts d r).card : ℕ) : ℝ)) ^ (2 : ℝ)⁻¹) *
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)

private lemma sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h2 : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h47 : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
    have e6 : (Real.sqrt x + Real.sqrt y) ^ 2
        = Real.sqrt x ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) + Real.sqrt y ^ 2 := by
      ring
    rw [e6, Real.sq_sqrt hx, Real.sq_sqrt hy]
    linarith
  have h3 := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y))] at h3
  exact h3

private lemma pow_mono3 : ∀ m l : ℕ, m ≤ l → (3:ℝ) ^ m ≤ (3:ℝ) ^ l := by
  intro m l hml
  revert hml
  induction l with
  | zero =>
    intro h
    have hm : m = 0 := Nat.le_zero.mp h
    subst hm
    simp
  | succ l ih =>
    intro h
    rcases Nat.lt_or_ge m (l + 1) with h1 | h1
    · refine le_trans (ih (Nat.le_of_lt_succ h1)) ?_
      rw [pow_succ]
      linarith [pow_pos (show (0:ℝ) < 3 by norm_num) l]
    · rw [Nat.le_antisymm h1 h]

private lemma sum_le_card_mul {f : ℕ → ℝ} {w : ℝ} :
    ∀ (m : ℕ), 0 ≤ w → (∀ k ∈ Finset.range m, f k ≤ w) →
      ∑ k ∈ Finset.range m, f k ≤ (m : ℝ) * w := by
  intro m _ h
  calc ∑ k ∈ Finset.range m, f k ≤ ∑ _k ∈ Finset.range m, w :=
      Finset.sum_le_sum h
    _ = (m : ℝ) * w := by simp

theorem exists_goodCube_boundedScale_logLipschitz_threshold
    (d J : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 / 2 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
        ∀ n : ℕ, n ≤ J → logLipschitzThreshold M n * (3 : ℝ)^n ≤ eps := by
  have hne : eps ≠ 0 := ne_of_gt heps
  set B : ℝ := 1 + ∑ i ∈ Finset.range (J + 2), |entropyCoef d (((i : ℕ) : ℤ) + 1)| with hB
  have hBpos : 0 < B := by
    rw [hB]
    have h34 : 0 ≤ ∑ i ∈ Finset.range (J + 2), |entropyCoef d (((i : ℕ) : ℤ) + 1)| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  set C : ℝ := ((J + 1 : ℕ) : ℝ) * (3:ℝ)^J * B with hC
  have hJ1 : (0:ℝ) < ((J + 1 : ℕ) : ℝ) := by
    have h43 : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
    have hJ0 : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg (J : ℕ)
    rw [h43]
    linarith
  have hCpos : 0 < C := by
    rw [hC]
    exact mul_pos (mul_pos hJ1 (pow_pos (by norm_num) J)) hBpos
  have h3J : 0 ≤ (3:ℝ)^J := by positivity
  set T : ℝ := 1 + 2 * C / eps with hT
  have hTpos : 0 < T := by
    have h44 : 0 ≤ 2 * C / eps := div_nonneg (by linarith) heps.le
    linarith
  have h2C : (2:ℝ) * C ≤ eps * T := by
    rw [hT]
    have e : eps * (1 + 2 * C / eps) = eps + 2 * C := by
      field_simp
    rw [e]
    linarith
  have hX : (2:ℝ) * (C * T⁻¹) ≤ eps := by
    have h39 := mul_le_mul_of_nonneg_right h2C (inv_nonneg.mpr hTpos.le)
    have e4 : eps * T * T⁻¹ = eps := mul_inv_cancel_right₀ hTpos.ne' eps
    rw [e4] at h39
    have e5 : (2:ℝ) * (C * T⁻¹) = (2:ℝ) * C * T⁻¹ := by ring
    rw [e5]
    exact h39
  have hD : 0 < 2 * (C * Real.sqrt (J:ℝ)) + 1 := by
    have hCs : 0 ≤ C * Real.sqrt (J:ℝ) := mul_nonneg hCpos.le (Real.sqrt_nonneg _)
    linarith
  set delta0 : ℝ := min (1 / 2) (min (eps / (2 * (C * Real.sqrt (J:ℝ)) + 1)) (Real.exp (-T)))
    with hdelta0
  have hd0pos : 0 < delta0 := by
    rw [hdelta0]
    exact lt_min (by norm_num) (lt_min (div_pos heps hD) (Real.exp_pos _))
  have hd0half : delta0 ≤ 1 / 2 := by
    rw [hdelta0]
    exact min_le_left _ _
  set w : ℝ := T⁻¹ + delta0 * Real.sqrt (J:ℝ) with hw
  have w_nn : 0 ≤ w := by
    have h45 : 0 ≤ T⁻¹ := inv_nonneg.mpr hTpos.le
    have h46 : 0 ≤ delta0 * Real.sqrt (J:ℝ) := mul_nonneg hd0pos.le (Real.sqrt_nonneg _)
    linarith [hw]
  have hY : (2:ℝ) * (C * Real.sqrt (J:ℝ) * delta0) ≤ eps := by
    have hδle : delta0 ≤ eps / (2 * (C * Real.sqrt (J:ℝ)) + 1) := by
      rw [hdelta0]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h40 := mul_le_mul_of_nonneg_right hδle (le_of_lt hD)
    rw [div_mul_cancel₀ _ hD.ne'] at h40
    have h41 : (2:ℝ) * (C * Real.sqrt (J:ℝ) * delta0) + delta0
        = delta0 * (2 * (C * Real.sqrt (J:ℝ)) + 1) := by ring
    linarith [h40, h41, hd0pos.le]
  have hsp : C * w ≤ eps := by
    have h42 : C * w = C * T⁻¹ + C * Real.sqrt (J:ℝ) * delta0 := by
      rw [hw]; ring
    rw [h42]
    linarith [hX, hY]
  refine ⟨delta0, hd0pos, hd0half, ?_⟩
  intro M hM n hn
  have hδ1 : 0 < M.delta := M.shellPrefix.delta_pos
  have hδ4 : M.delta ≤ Real.exp (-T) := by
    refine le_trans hM ?_
    rw [hdelta0]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hlogδ : Real.log M.delta ≤ -T := by
    have h26 := Real.log_le_log hδ1 hδ4
    rwa [Real.log_exp] at h26
  have hneglog : T ≤ -Real.log M.delta := by linarith
  have hδtail : M.delta * tailIndex M ≤ T⁻¹ := by
    have h27 : M.delta * tailIndex M = (-Real.log M.delta)⁻¹ := by
      unfold tailIndex
      field_simp
    rw [h27]
    exact inv_anti₀ hTpos hneglog
  have htailnn : 0 ≤ tailIndex M := by
    unfold tailIndex
    have h28 : 0 < M.delta * (-Real.log M.delta) := mul_pos hδ1 (by linarith)
    exact le_of_lt (inv_pos.mpr h28)
  have h3n : 0 < (3:ℝ)^n := pow_pos (by norm_num) n
  have hcast : ((n + 1 : ℕ) : ℝ) ≤ ((J + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
  have hperk : ∀ k ∈ Finset.range (n + 1),
      |((3:ℝ)^k)⁻¹ * (coverEntropyScale M (shellCoverDepth n k) * shellDeviation M n k) * (3:ℝ)^n|
        ≤ (3:ℝ)^J * B * w := by
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hApos : 0 < ((3:ℝ)^k)⁻¹ := inv_pos.mpr (pow_pos (by norm_num) k)
    have hA1 : ((3:ℝ)^k)⁻¹ ≤ 1 := by
      have h29 := pow_mono3 0 k (Nat.zero_le k)
      rw [pow_zero] at h29
      have h30 : (0:ℝ) < (1:ℝ) := by norm_num
      have h31 := inv_anti₀ h30 h29
      rw [inv_one] at h31
      exact h31
    have hSnn : 0 ≤ shellDeviation M n k := by
      unfold shellDeviation
      exact Real.sqrt_nonneg _
    have hnkJ : ((n - k : ℕ) : ℝ) ≤ (J : ℝ) := Nat.cast_le.mpr (by omega)
    have h35 : shellCoverDepth n k = ((n - k : ℕ) : ℤ) + 1 := rfl
    have hmem : (n - k : ℕ) ∈ Finset.range (J + 2) := Finset.mem_range.mpr (by omega)
    have hCB' : |entropyCoef d (((n - k : ℕ) : ℤ) + 1)| ≤ B := by
      rw [hB]
      have h37 := Finset.single_le_sum
        (fun i (_ : i ∈ Finset.range (J + 2)) => abs_nonneg (entropyCoef d ((i : ℤ) + 1))) hmem
      linarith
    have hCB : |entropyCoef d (shellCoverDepth n k)| ≤ B := by rw [h35]; exact hCB'
    have hce : coverEntropyScale M (shellCoverDepth n k)
        = entropyCoef d (shellCoverDepth n k) * M.delta := by
      unfold coverEntropyScale entropyCoef; ring
    have hsqrtle : Real.sqrt (tailIndex M ^ 2 + ((n - k : ℕ) : ℝ))
        ≤ tailIndex M + Real.sqrt ((n - k : ℕ) : ℝ) := by
      have h36 := sqrt_add_le (tailIndex M ^ 2) ((n - k : ℕ) : ℝ) (sq_nonneg (tailIndex M))
        (Nat.cast_nonneg (n - k : ℕ))
      rw [Real.sqrt_sq htailnn] at h36
      exact h36
    have hδS : M.delta * shellDeviation M n k ≤ w := by
      rw [hw]
      show M.delta * Real.sqrt (tailIndex M ^ 2 + ((n - k : ℕ) : ℝ)) ≤ T⁻¹ + delta0 * Real.sqrt (J:ℝ)
      refine le_trans (mul_le_mul_of_nonneg_left hsqrtle hδ1.le) ?_
      rw [mul_add]
      exact add_le_add hδtail (mul_le_mul hM (Real.sqrt_le_sqrt hnkJ) (Real.sqrt_nonneg _) hd0pos.le)
    have habs : |((3:ℝ)^k)⁻¹ * (coverEntropyScale M (shellCoverDepth n k) * shellDeviation M n k) * (3:ℝ)^n|
        = ((3:ℝ)^k)⁻¹ * (|entropyCoef d (shellCoverDepth n k)| * M.delta * shellDeviation M n k) * (3:ℝ)^n := by
      simp only [abs_mul, hce, abs_of_pos hApos, abs_of_pos hδ1, abs_of_nonneg hSnn, abs_of_pos h3n]
    rw [habs]
    have hA1' : ((3:ℝ)^k)⁻¹ * |entropyCoef d (shellCoverDepth n k)| ≤ B := by
      have h31 := mul_le_mul hA1 hCB (abs_nonneg _) zero_le_one
      rw [one_mul] at h31
      exact h31
    have e : ((3:ℝ)^k)⁻¹ * (|entropyCoef d (shellCoverDepth n k)| * M.delta * shellDeviation M n k)
        = (((3:ℝ)^k)⁻¹ * |entropyCoef d (shellCoverDepth n k)|) * (M.delta * shellDeviation M n k) := by
      ring
    rw [e]
    calc (((3:ℝ)^k)⁻¹ * |entropyCoef d (shellCoverDepth n k)|) * (M.delta * shellDeviation M n k) * (3:ℝ)^n
        ≤ B * w * (3:ℝ)^n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hA1' hδS (mul_nonneg hδ1.le hSnn) hBpos.le) h3n.le
      _ = (3:ℝ)^n * (B * w) := by ring
      _ ≤ (3:ℝ)^J * (B * w) :=
          mul_le_mul_of_nonneg_right (pow_mono3 n J hn)
            (mul_nonneg hBpos.le w_nn)
      _ = (3:ℝ)^J * B * w := by ring
  have hsum : logLipschitzThreshold M n * (3:ℝ)^n ≤ ((n + 1 : ℕ) : ℝ) * ((3:ℝ)^J * B * w) := by
    unfold logLipschitzThreshold
    rw [Finset.sum_mul]
    exact le_trans (Finset.sum_le_sum fun k _ => le_abs_self _)
      (sum_le_card_mul (n + 1) (mul_nonneg (mul_nonneg h3J hBpos.le) w_nn)
        (fun k hk => hperk k hk))
  calc logLipschitzThreshold M n * (3:ℝ)^n
      ≤ ((n + 1 : ℕ) : ℝ) * ((3:ℝ)^J * B * w) := hsum
    _ ≤ ((J + 1 : ℕ) : ℝ) * ((3:ℝ)^J * B * w) :=
        mul_le_mul_of_nonneg_right hcast (mul_nonneg (mul_nonneg h3J hBpos.le) w_nn)
    _ = C * w := by rw [hC]; ring
    _ ≤ eps := hsp

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
