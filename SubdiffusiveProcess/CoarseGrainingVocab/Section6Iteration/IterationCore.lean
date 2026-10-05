module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.DiscreteGronwall




@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

open Finset

noncomputable section

/-! ### The explicit constants -/

/-- The reabsorption factor of the excess-sum reabsorption bound: `h κ^h`.  The source prints
`3^{(d+2)h}` that value is too small for `d ≥ 3`, so `κ` is kept as a
parameter. -/
def iterM (h : ℕ) (κ : ℝ) : ℝ := (h : ℝ) * κ ^ h

/-- The good-run constant, as recomputed in `IterationGoodRun.lean`. -/
def goodConst (h : ℕ) (κ Cstab : ℝ) : ℝ :=
  5 / 2 * iterM h κ + 6 + 5 * Cstab * (7 / 2 * iterM h κ + 7)

/-- The exponential rate of the good-run bound: `exp(goodRate · ∑ ε)`. -/
def goodRate (Cstab : ℝ) : ℝ := 5 * Cstab + 2

/-- The one-scale crossing constant. -/
def badConst (κ Cstab : ℝ) : ℝ := κ + Cstab * (1 + κ)

theorem iterM_nonneg (h : ℕ) {κ : ℝ} (hκ : 1 ≤ κ) : 0 ≤ iterM h κ :=
  mul_nonneg (Nat.cast_nonneg h) (pow_nonneg (le_trans zero_le_one hκ) h)

theorem one_le_goodConst (h : ℕ) {κ Cstab : ℝ} (hκ : 1 ≤ κ) (hC : 0 ≤ Cstab) :
    1 ≤ goodConst h κ Cstab := by
  have hM : 0 ≤ iterM h κ := iterM_nonneg h hκ
  have h1 : 0 ≤ 5 * Cstab * (7 / 2 * iterM h κ + 7) := by positivity
  have h2 : 0 ≤ 5 / 2 * iterM h κ := by positivity
  rw [goodConst]
  linarith only [h1, h2]

theorem goodRate_nonneg {Cstab : ℝ} (hC : 0 ≤ Cstab) : 0 ≤ goodRate Cstab := by
  rw [goodRate]
  linarith only [hC]

theorem one_le_badConst {κ Cstab : ℝ} (hκ : 1 ≤ κ) (hC : 0 ≤ Cstab) :
    1 ≤ badConst κ Cstab := by
  have h1 : 0 ≤ Cstab * (1 + κ) := by
    have : (0 : ℝ) ≤ 1 + κ := by linarith only [hκ]
    exact mul_nonneg hC this
  rw [badConst]
  linarith only [hκ, h1]

/-! ### One-scale comparability -/

section BadCrossing

variable {E p : ℤ → ℝ} {κ Cstab : ℝ}

/-- **One-scale crossing**: `E_{k−1} + p_{k−1} ≤ badConst (E_k + p_k)`.  The source
reads this off the gradient stability estimate "and the definition of excess"; here it is
read off the abstract `hmono`/`hstab`. -/
theorem badCrossing (hE : ∀ k, 0 ≤ E k) (hκ : 1 ≤ κ) (hC : 0 ≤ Cstab)
    (hmono : ∀ k, E k ≤ κ * E (k + 1)) (hp : ∀ k, 0 ≤ p k)
    (hstab : ∀ k, |p k - p (k - 1)| ≤ Cstab * (E k + E (k - 1))) (k : ℤ) :
    E (k - 1) + p (k - 1) ≤ badConst κ Cstab * (E k + p k) := by
  have hmk : E (k - 1) ≤ κ * E k := by
    have h := hmono (k - 1)
    rwa [sub_add_cancel] at h
  have hsk : |p k - p (k - 1)| ≤ Cstab * (E k + E (k - 1)) := hstab k
  have hpk : p (k - 1) - p k ≤ Cstab * (E k + E (k - 1)) := by
    have h1 : p (k - 1) - p k = -(p k - p (k - 1)) := by ring
    have h2 : -(p k - p (k - 1)) ≤ |p k - p (k - 1)| := neg_le_abs _
    linarith only [h1, h2, hsk]
  have hCmk : Cstab * (E k + E (k - 1)) ≤ Cstab * (E k + κ * E k) :=
    mul_le_mul_of_nonneg_left (by linarith only [hmk]) hC
  have hEk : 0 ≤ E k := hE k
  have hpk0 : 0 ≤ p k := hp k
  have hexp : badConst κ Cstab * (E k + p k)
      = κ * E k + Cstab * (E k + κ * E k) + (badConst κ Cstab - 1) * p k + p k := by
    rw [badConst]; ring
  have hslack : 0 ≤ (badConst κ Cstab - 1) * p k :=
    mul_nonneg (by linarith only [one_le_badConst hκ hC]) hpk0
  rw [hexp]
  linarith only [hmk, hpk, hCmk, hslack]

end BadCrossing

/-! ### Reindexing helpers -/

/-- Reflection reindex: a `range` sum of a reflected function is an `Icc` sum. -/
theorem refl_sum (F : ℤ → ℝ) (c : ℤ) (l : ℕ) :
    ∑ t ∈ range l, F (c - t) = ∑ k ∈ Icc (c - l + 1) c, F k := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [Finset.sum_range_succ, ih]
      have hset : Icc (c - (l + 1 : ℕ) + 1) c = insert (c - l) (Icc (c - l + 1) c) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        push_cast
        omega
      rw [hset, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      ring

/-- Shift reindex: `∑_{[a+h,b]} f(j−h) = ∑_{[a,b−h]} f`. -/
theorem sum_Icc_shift (f : ℤ → ℝ) (a b h : ℤ) :
    ∑ j ∈ Icc (a + h) b, f (j - h) = ∑ k ∈ Icc a (b - h), f k := by
  rw [show Icc (a + h) b = (Icc a (b - h)).map (addRightEmbedding h) by
    rw [Finset.map_add_right_Icc]; ring_nf]
  rw [Finset.sum_map]
  simp [addRightEmbedding]

/-! ### The reabsorption of the excess sum -/

section Reabsorption

variable {E p ε δ : ℤ → ℝ} {θ κ : ℝ} {h : ℕ}

/-- Iterated quasi-monotonicity: `E c ≤ κ^t E (c + t)`. -/
theorem excessIterMono (hκ0 : 0 ≤ κ) (hmono : ∀ k, E k ≤ κ * E (k + 1)) :
    ∀ (t : ℕ) (c : ℤ), E c ≤ κ ^ t * E (c + t) := by
  intro t
  induction t with
  | zero => intro c; simp
  | succ t ih =>
      intro c
      have h1 : E c ≤ κ ^ t * E (c + t) := ih c
      have h2 : E (c + t) ≤ κ * E (c + t + 1) := hmono (c + t)
      have h3 : κ ^ t * E (c + t) ≤ κ ^ t * (κ * E (c + t + 1)) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hκ0 t)
      have hidx : c + ((t + 1 : ℕ) : ℤ) = c + (t : ℤ) + 1 := by push_cast; ring
      have h4 : κ ^ t * (κ * E (c + t + 1)) = κ ^ (t + 1) * E (c + ((t + 1 : ℕ) : ℤ)) := by
        rw [hidx]
        ring
      calc E c ≤ κ ^ t * E (c + t) := h1
        _ ≤ κ ^ t * (κ * E (c + t + 1)) := h3
        _ = κ ^ (t + 1) * E (c + ((t + 1 : ℕ) : ℤ)) := h4

/-- The top `h` terms of the excess sum are controlled by `E_b`: this is where the
factor `iterM h κ = h κ^h` (the source's `3^{(d+2)h}`) comes from. -/
theorem topHBound (hκ : 1 ≤ κ) (hE : ∀ k, 0 ≤ E k)
    (hmono : ∀ k, E k ≤ κ * E (k + 1)) (b : ℤ) :
    ∑ k ∈ Icc (b - h + 1) b, E k ≤ iterM h κ * E b := by
  have hκ0 : (0 : ℝ) ≤ κ := le_trans zero_le_one hκ
  have hterm : ∀ k ∈ Icc (b - (h : ℤ) + 1) b, E k ≤ κ ^ h * E b := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    set t : ℕ := (b - k).toNat with htdef
    have hbt : b = k + (t : ℤ) := by rw [htdef]; omega
    have hEk : E k ≤ κ ^ t * E b := by
      have hmt := excessIterMono hκ0 hmono t k
      rwa [← hbt] at hmt
    have htle : t ≤ h := by rw [htdef]; omega
    have hpow : κ ^ t ≤ κ ^ h := pow_le_pow_right₀ hκ htle
    calc E k ≤ κ ^ t * E b := hEk
      _ ≤ κ ^ h * E b := mul_le_mul_of_nonneg_right hpow (hE b)
  have hcard : (((Icc (b - (h : ℤ) + 1) b).card : ℕ) : ℝ) = (h : ℝ) := by
    rw [Int.card_Icc, show b + 1 - (b - (h : ℤ) + 1) = (h : ℤ) by ring, Int.toNat_natCast]
  calc ∑ k ∈ Icc (b - (h : ℤ) + 1) b, E k
      ≤ ∑ _k ∈ Icc (b - (h : ℤ) + 1) b, κ ^ h * E b := Finset.sum_le_sum hterm
    _ = (((Icc (b - (h : ℤ) + 1) b).card : ℕ) : ℝ) * (κ ^ h * E b) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = iterM h κ * E b := by rw [hcard, iterM]; ring

/-- **Reabsorption of the excess sum**.

On a run of scales `[a,b]` carrying the `h`-gap decay recurrence, the excess sum
from any `i ∈ [a,b]` to `b` is controlled by `E_b` alone, up to the error sums,
with **no dependence on `b − i`**.  The numerical gate `θ^h < 3/5` is what makes
the reabsorption possible; the error sum starts at `i + h`, which is the honest
range at which summing the recurrence produces error terms. -/
theorem reabsorbSum (hθpos : 0 < θ) (hθh : θ ^ h < 3 / 5) (hE : ∀ k, 0 ≤ E k)
    (hε : ∀ k, 0 ≤ ε k) (hp : ∀ k, 0 ≤ p k) (hδ : ∀ k, 0 ≤ δ k) (hκ : 1 ≤ κ)
    (hmono : ∀ k, E k ≤ κ * E (k + 1)) {a b : ℤ}
    (hdecay : ∀ j, a ≤ j → j ≤ b → E (j - h) ≤ θ ^ h * E j + ε j * p j + δ j) :
    ∑ k ∈ Icc a b, E k
      ≤ 5 / 2 * (iterM h κ * E b + ∑ k ∈ Icc (a + (h : ℤ)) b, (ε k * p k + δ k)) := by
  have hθh0 : 0 ≤ θ ^ h := le_of_lt (pow_pos hθpos h)
  have htop : ∑ k ∈ Icc (b - (h : ℤ) + 1) b, E k ≤ iterM h κ * E b :=
    topHBound hκ hE hmono b
  set U : ℝ := ∑ k ∈ Icc a b, E k with hUdef
  set T : ℝ := ∑ k ∈ Icc (a + (h : ℤ)) b, (ε k * p k + δ k) with hTdef
  have hU0 : 0 ≤ U := by rw [hUdef]; exact Finset.sum_nonneg fun k _ => hE k
  have hT0 : 0 ≤ T :=
    Finset.sum_nonneg fun k _ => add_nonneg (mul_nonneg (hε k) (hp k)) (hδ k)
  have htop0 : 0 ≤ iterM h κ * E b := mul_nonneg (iterM_nonneg h hκ) (hE b)
  by_cases hlong : a + (h : ℤ) ≤ b
  · have hdecsum : ∑ j ∈ Icc (a + (h : ℤ)) b, E (j - (h : ℤ))
        ≤ θ ^ h * (∑ j ∈ Icc (a + (h : ℤ)) b, E j) + T := by
      have hle : ∀ j ∈ Icc (a + (h : ℤ)) b,
          E (j - (h : ℤ)) ≤ θ ^ h * E j + (ε j * p j + δ j) := by
        intro j hj
        simp only [Finset.mem_Icc] at hj
        have hd := hdecay j (by omega) hj.2
        linarith only [hd]
      calc ∑ j ∈ Icc (a + (h : ℤ)) b, E (j - (h : ℤ))
          ≤ ∑ j ∈ Icc (a + (h : ℤ)) b, (θ ^ h * E j + (ε j * p j + δ j)) :=
            Finset.sum_le_sum hle
        _ = θ ^ h * (∑ j ∈ Icc (a + (h : ℤ)) b, E j) + T := by
            rw [hTdef, Finset.sum_add_distrib, Finset.mul_sum]
    have hLo : ∑ j ∈ Icc (a + (h : ℤ)) b, E (j - (h : ℤ))
        = ∑ k ∈ Icc a (b - (h : ℤ)), E k := sum_Icc_shift E a b (h : ℤ)
    have hUsplit : U = (∑ k ∈ Icc a (b - (h : ℤ)), E k)
        + ∑ k ∈ Icc (b - (h : ℤ) + 1) b, E k := by
      rw [hUdef]
      have hunion : Icc a b = Icc a (b - (h : ℤ)) ∪ Icc (b - (h : ℤ) + 1) b := by
        ext x
        simp only [Finset.mem_union, Finset.mem_Icc]
        omega
      have hdisj : Disjoint (Icc a (b - (h : ℤ))) (Icc (b - (h : ℤ) + 1) b) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_Icc] at hx hx'
        omega
      rw [hunion, Finset.sum_union hdisj]
    have hsubE : ∑ j ∈ Icc (a + (h : ℤ)) b, E j ≤ U := by
      rw [hUdef]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hE k
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    rw [hLo] at hdecsum
    have hkey : U ≤ θ ^ h * U + T + iterM h κ * E b := by
      have h1 : (∑ k ∈ Icc a (b - (h : ℤ)), E k) ≤ θ ^ h * U + T := by
        have hmul := mul_le_mul_of_nonneg_left hsubE hθh0
        linarith only [hdecsum, hmul]
      linarith only [hUsplit, h1, htop]
    have hprod : 2 / 5 * U ≤ (1 - θ ^ h) * U :=
      mul_le_mul_of_nonneg_right (by linarith only [hθh]) hU0
    linarith only [hkey, hprod]
  · push Not at hlong
    have hUsub : U ≤ iterM h κ * E b := by
      rw [hUdef]
      calc ∑ k ∈ Icc a b, E k ≤ ∑ k ∈ Icc (b - (h : ℤ) + 1) b, E k := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hE k
            intro x hx
            simp only [Finset.mem_Icc] at hx ⊢
            omega
        _ ≤ iterM h κ * E b := htop
    linarith only [hUsub, hT0, htop0]

end Reabsorption

/-! ### The telescoped slope stability -/

section SlopeTelescope

variable {E p : ℤ → ℝ} {Cstab : ℝ}

/-- **Telescoped gradient stability estimate** (summed): the slope difference across a run
is controlled by twice `Cstab` times the excess sum.  The factor `2` is the
honest accounting: each `E_k` occurs in at most two of the telescoped pairs. -/
theorem slopeTelescope (hC : 0 ≤ Cstab) (hE : ∀ k, 0 ≤ E k)
    (hstab : ∀ k, |p k - p (k - 1)| ≤ Cstab * (E k + E (k - 1))) (b : ℤ) (l : ℕ) :
    |p (b - l) - p b| ≤ 2 * Cstab * ∑ k ∈ Icc (b - l) b, E k := by
  have hsum : ∑ t ∈ range l, (p (b - ((t : ℤ) + 1)) - p (b - (t : ℤ)))
      = p (b - (l : ℤ)) - p b := by
    have hns := Finset.sum_range_sub (fun t : ℕ => p (b - (t : ℤ))) l
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero] at hns
    exact hns
  have hstep : ∀ t ∈ range l,
      |p (b - ((t : ℤ) + 1)) - p (b - (t : ℤ))|
        ≤ Cstab * (E (b - (t : ℤ)) + E (b - (t : ℤ) - 1)) := by
    intro t _
    have hk := hstab (b - (t : ℤ))
    have hcast : b - ((t : ℤ) + 1) = b - (t : ℤ) - 1 := by ring
    calc |p (b - ((t : ℤ) + 1)) - p (b - (t : ℤ))|
        = |p (b - (t : ℤ)) - p (b - (t : ℤ) - 1)| := by rw [abs_sub_comm, hcast]
      _ ≤ Cstab * (E (b - (t : ℤ)) + E (b - (t : ℤ) - 1)) := hk
  have hAbs : |p (b - (l : ℤ)) - p b|
      ≤ ∑ t ∈ range l, Cstab * (E (b - (t : ℤ)) + E (b - (t : ℤ) - 1)) := by
    rw [← hsum]
    calc |∑ t ∈ range l, (p (b - ((t : ℤ) + 1)) - p (b - (t : ℤ)))|
        ≤ ∑ t ∈ range l, |p (b - ((t : ℤ) + 1)) - p (b - (t : ℤ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ range l, Cstab * (E (b - (t : ℤ)) + E (b - (t : ℤ) - 1)) :=
          Finset.sum_le_sum hstep
  have hsplit : ∑ t ∈ range l, Cstab * (E (b - (t : ℤ)) + E (b - (t : ℤ) - 1))
      = Cstab * ((∑ t ∈ range l, E (b - (t : ℤ)))
        + ∑ t ∈ range l, E (b - (t : ℤ) - 1)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hR1 : ∑ t ∈ range l, E (b - (t : ℤ)) ≤ ∑ k ∈ Icc (b - (l : ℤ)) b, E k := by
    rw [refl_sum E b l]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hE k
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hR2 : ∑ t ∈ range l, E (b - (t : ℤ) - 1) ≤ ∑ k ∈ Icc (b - (l : ℤ)) b, E k := by
    have hcong : ∑ t ∈ range l, E (b - (t : ℤ) - 1)
        = ∑ t ∈ range l, E ((b - 1) - (t : ℤ)) := by
      refine Finset.sum_congr rfl fun t _ => ?_
      congr 1
      ring
    rw [hcong, refl_sum E (b - 1) l]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hE k
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  calc |p (b - (l : ℤ)) - p b|
      ≤ Cstab * ((∑ t ∈ range l, E (b - (t : ℤ)))
          + ∑ t ∈ range l, E (b - (t : ℤ) - 1)) := by rw [← hsplit]; exact hAbs
    _ ≤ Cstab * (2 * ∑ k ∈ Icc (b - (l : ℤ)) b, E k) :=
        mul_le_mul_of_nonneg_left (by linarith only [hR1, hR2]) hC
    _ = 2 * Cstab * ∑ k ∈ Icc (b - (l : ℤ)) b, E k := by ring

end SlopeTelescope

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
