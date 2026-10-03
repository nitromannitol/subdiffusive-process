module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingFailure

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The scale weight `3^{3j/2}` of a cell; a good vertex has weight `0`. -/
def cellTau : CrossCell d → ℝ
  | Sum.inl p => (3 : ℝ) ^ ((3 : ℝ) * p.1 / 2)
  | Sum.inr _ => 0

theorem cellTau_nonneg (c : CrossCell d) : 0 ≤ cellTau c := by
  cases c with
  | inl p => exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  | inr v => exact le_rfl

/-- The exponential half of a cell's weight. -/
def crossGain (dim : ℕ) (cprob q : ℝ) : CrossCell d → ℝ≥0∞ := fun c =>
  ENNReal.ofReal (Real.exp (-(cprob / 2 / 2 ^ dim) * q * cellTau c))

theorem crossGain_inr (dim : ℕ) (cprob q : ℝ) (v : Lattice d) :
    crossGain (d := d) dim cprob q (Sum.inr v) = 1 := by
  simp [crossGain, cellTau]

/-- **The weight splits into gain times the halved-rate weight.** -/
theorem cellWeight_eq_gain_mul (dim Cdep : ℕ) (Cprob cprob q : ℝ) (c : CrossCell d) :
    cellWeight dim Cdep Cprob cprob q c =
      crossGain dim cprob q c * cellWeight dim Cdep Cprob (cprob / 2) q c := by
  cases c with
  | inr v => simp [cellWeight, crossGain, cellTau]
  | inl p =>
      obtain ⟨j, a⟩ := p
      set K : ℝ := (((2 * (Cdep * 3 ^ j) + 1) ^ dim : ℕ) : ℝ) * max 1 Cprob with hK
      set t : ℝ := (3 : ℝ) ^ ((3 : ℝ) * j / 2) with ht
      have hKpos : 0 ≤ K := by
        have : (0 : ℝ) ≤ (((2 * (Cdep * 3 ^ j) + 1) ^ dim : ℕ) : ℝ) := Nat.cast_nonneg _
        have h1 : (0 : ℝ) ≤ max 1 Cprob := le_trans zero_le_one (le_max_left _ _)
        exact mul_nonneg this h1
      show ENNReal.ofReal (K * Real.exp (-(cprob / 2 ^ dim) * q * t)) =
        ENNReal.ofReal (Real.exp (-(cprob / 2 / 2 ^ dim) * q * t)) *
          ENNReal.ofReal (K * Real.exp (-(cprob / 2 / 2 ^ dim) * q * t))
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      have hexp : Real.exp (-(cprob / 2 / 2 ^ dim) * q * t) *
          (K * Real.exp (-(cprob / 2 / 2 ^ dim) * q * t)) =
          K * Real.exp (-(cprob / 2 / 2 ^ dim) * q * t +
            -(cprob / 2 / 2 ^ dim) * q * t) := by
        rw [Real.exp_add]; ring
      rw [hexp]
      congr 2
      have h2 : ((2 : ℝ) ^ dim) ≠ 0 := by positivity
      field_simp
      ring

/-- The product of the gains along a chain is the exponential of the total
scale weight. -/
theorem prod_map_crossGain (dim : ℕ) (cprob q : ℝ) (L : List (CrossCell d)) :
    (L.map (crossGain dim cprob q)).prod =
      ENNReal.ofReal (Real.exp (-(cprob / 2 / 2 ^ dim) * q *
        (L.map cellTau).sum)) := by
  induction L with
  | nil => simp
  | cons c L ih =>
      rw [List.map_cons, List.prod_cons, ih, crossGain,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      simp only [List.map_cons, List.sum_cons]
      ring

/-- The weight product splits. -/
theorem prod_map_cellWeight_eq (dim Cdep : ℕ) (Cprob cprob q : ℝ)
    (L : List (CrossCell d)) :
    (L.map (cellWeight dim Cdep Cprob cprob q)).prod =
      (L.map (crossGain dim cprob q)).prod *
        (L.map (cellWeight dim Cdep Cprob (cprob / 2) q)).prod := by
  induction L with
  | nil => simp
  | cons c L ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons,
        List.map_cons, List.prod_cons, cellWeight_eq_gain_mul]
      ring

/-! ## The coverage lower bound on the total scale weight -/

theorem cellRadius_le_tau (Cbox Cdep : ℕ) (c : CrossCell d) :
    ((cellRadius Cbox Cdep c : ℕ) : ℝ) ≤ ((Cbox + Cdep : ℕ) : ℝ) * cellTau c := by
  cases c with
  | inr v => simp [cellRadius, cellTau]
  | inl p =>
      obtain ⟨j, a⟩ := p
      show (((Cbox + Cdep) * 3 ^ j : ℕ) : ℝ) ≤
        ((Cbox + Cdep : ℕ) : ℝ) * (3 : ℝ) ^ ((3 : ℝ) * j / 2)
      have hpow : ((3 : ℝ) ^ j) ≤ (3 : ℝ) ^ ((3 : ℝ) * j / 2) := by
        rw [show ((3 : ℝ) ^ j) = (3 : ℝ) ^ ((j : ℝ)) from (Real.rpow_natCast 3 j).symm]
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      push_cast
      have hnn : (0 : ℝ) ≤ ((Cbox : ℝ) + (Cdep : ℝ)) := by positivity
      nlinarith

theorem one_le_tau_of_isLeft {c : CrossCell d} (h : c.isLeft = true) :
    (1 : ℝ) ≤ cellTau c := by
  cases c with
  | inr v => simp at h
  | inl p =>
      show (1 : ℝ) ≤ (3 : ℝ) ^ ((3 : ℝ) * p.1 / 2)
      refine Real.one_le_rpow (by norm_num) ?_
      have : (0 : ℝ) ≤ (p.1 : ℝ) := Nat.cast_nonneg _
      linarith

theorem sum_cellRadius_le (Cbox Cdep : ℕ) (L : List (CrossCell d)) :
    (((L.map (cellRadius Cbox Cdep)).sum : ℕ) : ℝ) ≤
      ((Cbox + Cdep : ℕ) : ℝ) * (L.map cellTau).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Nat.cast_add]
      have h1 := cellRadius_le_tau Cbox Cdep c
      have hnn : (0 : ℝ) ≤ ((Cbox + Cdep : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [h1, ih]

theorem length_le_sum_cellTau (L : List (CrossCell d)) :
    (L.length : ℝ) ≤ (L.map cellTau).sum + (goodCellCount L : ℝ) := by
  induction L with
  | nil => simp [goodCellCount]
  | cons c L ih =>
      rw [goodCellCount_cons]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      by_cases h : c.isRight = true
      · have htau : cellTau c = 0 := by
          cases c with
          | inl p => simp at h
          | inr v => rfl
        rw [if_pos h, htau]
        push_cast
        linarith
      · have hleft : c.isLeft = true := by
          cases c with
          | inl p => rfl
          | inr v => simp at h
        have htau : (1 : ℝ) ≤ cellTau c := one_le_tau_of_isLeft hleft
        rw [if_neg h]
        push_cast
        linarith

/-- **The certificate's total scale weight is linear in `l`.** -/
theorem le_sum_cellTau {Cbox Cdep J : ℕ} {z : Lattice d} {l gb : ℕ}
    {L : List (CrossCell d)} (hL : CrossChain Cbox Cdep J z l L)
    (hgb : goodCellCount L ≤ gb) :
    (l : ℝ) ≤ (6 * ((Cbox + Cdep : ℕ) : ℝ) + 3 * (J : ℝ)) * (L.map cellTau).sum +
      3 * (J : ℝ) * (gb : ℝ) := by
  have hcov := crossChain_le_radius_sum hL
  have hcovR : (l : ℝ) ≤ 6 * (((L.map (cellRadius Cbox Cdep)).sum : ℕ) : ℝ) +
      3 * ((J : ℝ) * (L.length : ℝ)) := by
    have hc := (Nat.cast_le (α := ℝ)).mpr hcov
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc
    linarith
  have hrad := sum_cellRadius_le Cbox Cdep L
  have hlen := length_le_sum_cellTau L
  have hgbR : ((goodCellCount L : ℕ) : ℝ) ≤ (gb : ℝ) := by exact_mod_cast hgb
  have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
  have hsum : (0 : ℝ) ≤ (L.map cellTau).sum := by
    refine List.sum_nonneg ?_
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
    exact cellTau_nonneg c
  nlinarith [hcovR, hrad, hlen, hgbR]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
