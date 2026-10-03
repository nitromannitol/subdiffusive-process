module

public import SubdiffusiveProcess.Lane3.Forms
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic

@[expose] public section




open Finset Filter Topology

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

theorem ramp_nonneg (a b x : ℝ) : 0 ≤ ramp a b x := by
  unfold ramp
  aesop

theorem ramp_le_one (a b x : ℝ) : ramp a b x ≤ 1 := by
  unfold ramp
  aesop

theorem ramp_eq_one_of_le {a b x : ℝ} (hab : a < b) (hx : b ≤ x) : ramp a b x = 1 := by
  unfold ramp
  have hb : 0 < b - a := by linarith
  have hdiv : 1 ≤ (x - a) / (b - a) := by
    rw [one_le_div hb]
    linarith
  have hmax : 1 ≤ max 0 ((x - a) / (b - a)) := le_trans hdiv (le_max_right _ _)
  exact min_eq_left hmax

theorem ramp_eq_zero_of_le {a b x : ℝ} (hab : a < b) (hx : x ≤ a) : ramp a b x = 0 := by
  have hba : 0 ≤ b - a := by linarith
  have hnum : x - a ≤ 0 := by linarith
  have hdiv : (x - a) / (b - a) ≤ 0 :=
    div_nonpos_iff.mpr (Or.inr ⟨hnum, hba⟩)
  unfold ramp
  rw [max_eq_left hdiv, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem abs_ramp_sub_ramp_le {a b x y : ℝ} (hab : a < b) :
    |ramp a b x - ramp a b y| ≤ |x - y| / (b - a) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hmin : |min 1 (max 0 ((x - a) / (b - a))) - min 1 (max 0 ((y - a) / (b - a)))|
      ≤ |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))| := by
    have h := abs_min_sub_min_le_max (1:ℝ) (max 0 ((x - a) / (b - a))) 1
      (max 0 ((y - a) / (b - a)))
    have heq : max |(1:ℝ) - 1| |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))|
        = |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))| := by
      simp
    rwa [heq] at h
  have hmax : |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))|
      ≤ |(x - a) / (b - a) - (y - a) / (b - a)| := by
    have h := abs_max_sub_max_le_max (0:ℝ) ((x - a) / (b - a)) 0 ((y - a) / (b - a))
    have heq : max |(0:ℝ) - 0| |(x - a) / (b - a) - (y - a) / (b - a)|
        = |(x - a) / (b - a) - (y - a) / (b - a)| := by
      simp
    rwa [heq] at h
  have huv : (x - a) / (b - a) - (y - a) / (b - a) = (x - y) / (b - a) := by
    rw [← sub_div]; ring
  have habs : |(x - a) / (b - a) - (y - a) / (b - a)| = |x - y| / (b - a) := by
    rw [huv, abs_div, abs_of_pos hba]
  calc |ramp a b x - ramp a b y|
      = |min 1 (max 0 ((x - a) / (b - a))) - min 1 (max 0 ((y - a) / (b - a)))| := rfl
    _ ≤ |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))| := hmin
    _ ≤ |(x - a) / (b - a) - (y - a) / (b - a)| := hmax
    _ = |x - y| / (b - a) := habs

theorem sq_add_le_two_add (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

theorem tsum_exp_neg_mul_nat {b : ℝ} (hb : 0 < b) :
    (∑' n : ℕ, Real.exp (-b * (n : ℝ))) = (1 - Real.exp (-b))⁻¹ := by
  have hr0 : 0 ≤ Real.exp (-b) := Real.exp_nonneg (-b)
  have hr1 : Real.exp (-b) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h : (∑' n : ℕ, Real.exp (-b * (n : ℝ))) =
      ∑' n : ℕ, (Real.exp (-b)) ^ n := by
    apply tsum_congr
    intro n
    rw [mul_comm (-b) (n : ℝ)]
    exact Real.exp_nat_mul (-b) n
  rw [h]
  exact tsum_geometric_of_lt_one hr0 hr1

theorem tsum_exp_neg_shift {b : ℝ} (hb : 0 < b) (m : ℝ) :
    (∑' n : ℕ, Real.exp (-b * (m + (n : ℝ)))) =
      Real.exp (-b * m) * (1 - Real.exp (-b))⁻¹ := by
  have hpos : 0 ≤ Real.exp (-b) := le_of_lt (Real.exp_pos (-b))
  have hlt : Real.exp (-b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : (∑' n : ℕ, Real.exp (-b) ^ n) = (1 - Real.exp (-b))⁻¹ :=
    tsum_geometric_of_lt_one hpos hlt
  have hterm : ∀ n : ℕ,
      Real.exp (-b * (m + (n : ℝ))) = Real.exp (-b * m) * Real.exp (-b) ^ n := by
    intro n
    rw [show -b * (m + (n : ℝ)) = -b * m + (n : ℝ) * (-b) by ring]
    rw [Real.exp_add, Real.exp_nat_mul (-b) n]
  calc
    (∑' n : ℕ, Real.exp (-b * (m + (n : ℝ))))
        = ∑' n : ℕ, Real.exp (-b * m) * Real.exp (-b) ^ n := by
          apply tsum_congr
          intro n
          exact hterm n
    _ = Real.exp (-b * m) * ∑' n : ℕ, Real.exp (-b) ^ n := by
          rw [tsum_mul_left]
    _ = Real.exp (-b * m) * (1 - Real.exp (-b))⁻¹ := by
          rw [hgeom]

theorem abs_sqrt_sub_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  have key : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v →
      Real.sqrt v - Real.sqrt u ≤ Real.sqrt (v - u) := by
    intro u v hu huv
    have hvu : 0 ≤ v - u := sub_nonneg.mpr huv
    have hsum : 0 ≤ Real.sqrt u + Real.sqrt (v - u) :=
      add_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg (v - u))
    have h1 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
    have h2 : Real.sqrt (v - u) ^ 2 = v - u := Real.sq_sqrt hvu
    have h3 : 0 ≤ Real.sqrt u * Real.sqrt (v - u) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hle : Real.sqrt v ≤ Real.sqrt u + Real.sqrt (v - u) := by
      have h : v ≤ (Real.sqrt u + Real.sqrt (v - u)) ^ 2 := by
        nlinarith [h1, h2, h3]
      have := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_sq hsum] at this
    linarith
  rcases le_total x y with hxy | hyx
  · have h := key hx hxy
    have e1 : |Real.sqrt x - Real.sqrt y| = Real.sqrt y - Real.sqrt x := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.sqrt_le_sqrt hxy))]; ring
    have e2 : |x - y| = y - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
    rw [e1, e2]
    exact h
  · have h := key hy hyx
    have e1 : |Real.sqrt x - Real.sqrt y| = Real.sqrt x - Real.sqrt y := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt hyx))]
    have e2 : |x - y| = x - y := by
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    rw [e1, e2]
    exact h

theorem min_le_sqrt_mul {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    min A B ≤ Real.sqrt (A * B) := by
  have hm : 0 ≤ min A B := le_min hA hB
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hsq : (min A B) ^ 2 ≤ (Real.sqrt (A * B)) ^ 2 := by
    rw [Real.sq_sqrt hAB]
    calc (min A B) ^ 2 = min A B * min A B := pow_two _
      _ ≤ A * B := mul_le_mul (min_le_left A B) (min_le_right A B) hm hA
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg hm, abs_of_nonneg (Real.sqrt_nonneg _)] at h

theorem efron_stein_square_sum_le {n : ℕ} (Del mx : ℝ) (hDel : 0 ≤ Del)
    (nu ze : Fin n → ℝ) (hnu : ∀ i, 0 ≤ nu i) (hze : ∀ i, 0 ≤ ze i)
    (hmx : ∀ i, nu i ≤ mx) :
    (∑ i : Fin n, (Del * nu i + Real.sqrt (nu i * ze i)) ^ 2) ≤
      2 * Del ^ 2 * mx * (∑ i : Fin n, nu i) + 2 * mx * (∑ i : Fin n, ze i) := by
  have hterm : ∀ i : Fin n,
      (Del * nu i + Real.sqrt (nu i * ze i)) ^ 2 ≤
        2 * Del ^ 2 * mx * nu i + 2 * mx * ze i := by
    intro i
    have hnu_i : 0 ≤ nu i := hnu i
    have hze_i : 0 ≤ ze i := hze i
    have hsq : (Real.sqrt (nu i * ze i)) ^ 2 = nu i * ze i :=
      Real.sq_sqrt (mul_nonneg hnu_i hze_i)
    have hnu_le : nu i * nu i ≤ mx * nu i :=
      mul_le_mul_of_nonneg_right (hmx i) hnu_i
    have ha : (Del * nu i) ^ 2 ≤ Del ^ 2 * (mx * nu i) := by
      have h := mul_le_mul_of_nonneg_left hnu_le (sq_nonneg Del)
      nlinarith [h]
    have hb : (Real.sqrt (nu i * ze i)) ^ 2 ≤ mx * ze i := by
      rw [hsq]
      exact mul_le_mul_of_nonneg_right (hmx i) hze_i
    have h1 := two_mul_le_add_sq (Del * nu i) (Real.sqrt (nu i * ze i))
    nlinarith [h1, ha, hb]
  calc ∑ i : Fin n, (Del * nu i + Real.sqrt (nu i * ze i)) ^ 2
      ≤ ∑ i : Fin n, (2 * Del ^ 2 * mx * nu i + 2 * mx * ze i) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = 2 * Del ^ 2 * mx * (∑ i : Fin n, nu i) + 2 * mx * (∑ i : Fin n, ze i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]


/-- The dyadic split of Lemma `mfd:lem-witness`, paper lines 2894-2900: if the
prefix sum exceeds `λ k`, either its first band approximant exceeds `λ k / 2`
or one dyadic increment exceeds its allotment, because the allotments sum to
`λ k / 4`. -/
theorem exceedance_dyadic_split
    (lam k : ℝ) (hlam : 0 < lam) (hk : 0 < k) (Sfun : ℕ → ℝ) (S : ℝ)
    (hlim : Tendsto Sfun atTop (𝓝 S)) (hS : lam * k < S) :
    lam * k / 2 < Sfun 0 ∨
      ∃ l : ℕ, 1 ≤ l ∧
        lam * k / (2 : ℝ) ^ (l + 2) < Sfun l - Sfun (l - 1) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, hinc⟩ := hcon
  have hlk : 0 < lam * k := mul_pos hlam hk
  have key : ∀ n : ℕ, Sfun n ≤ lam * k / 2 + lam * k / 4 * (1 - (1 / 2 : ℝ) ^ n) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ m ih =>
        have h := hinc (m + 1) (by omega)
        have hm : m + 1 - 1 = m := by omega
        rw [hm] at h
        have h2 : (0 : ℝ) < 2 ^ m := by positivity
        have hpow : (2 : ℝ) ^ (m + 1 + 2) = 8 * 2 ^ m := by ring
        rw [hpow] at h
        have hsucc : (1 / 2 : ℝ) ^ (m + 1) = (1 / 2 : ℝ) ^ m * (1 / 2) := pow_succ _ _
        have hhalf : (1 / 2 : ℝ) ^ m = ((2 : ℝ) ^ m)⁻¹ := by
          rw [div_pow, one_pow, one_div]
        have heq : lam * k / 4 * (1 - (1 / 2 : ℝ) ^ m) + lam * k / (8 * 2 ^ m)
            = lam * k / 4 * (1 - (1 / 2 : ℝ) ^ (m + 1)) := by
          rw [hsucc, hhalf]
          field_simp
          ring
        linarith
  have hbound : ∀ n : ℕ, Sfun n ≤ lam * k / 2 + lam * k / 4 := by
    intro n
    have hkey := key n
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
    nlinarith
  have hSle : S ≤ lam * k / 2 + lam * k / 4 := le_of_tendsto' hlim hbound
  linarith

end Lane3
end SubdiffusiveProcess
