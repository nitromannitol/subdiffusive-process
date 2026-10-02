import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalBandTail




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ}

/-- The separation constant of a band, in units of `3 ^ j`. -/
def bandBase (Cbox Cdep : ℕ) : ℕ := 6 * (1 + Cbox + Cdep) + 1

theorem one_le_bandBase (Cbox Cdep : ℕ) : 1 ≤ bandBase Cbox Cdep := by
  rw [bandBase]; omega

/-- The band separation, in units of `3 ^ j`. -/
theorem bandSep_succ_le (Cbox Cdep j : ℕ) :
    bandSep Cbox Cdep j + 1 ≤ bandBase Cbox Cdep * 3 ^ j := by
  have h1 : (1 : ℕ) ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
  have hsep : bandSep Cbox Cdep j = 6 * (1 + Cbox + Cdep) * 3 ^ j := by
    rw [bandSep, pow_succ]
    ring
  rw [hsep, bandBase, add_mul, one_mul]
  omega

/-- `a < (a / b + 1) * b` for a positive divisor. -/
private theorem lt_div_add_one_mul (a b : ℕ) (hb : 0 < b) : a < (a / b + 1) * b :=
  (Nat.div_lt_iff_lt_mul hb).mp (Nat.lt_succ_self _)

/-- The number of bands run at scale `L`. -/
def bandDepth (d Cbox Cdep L : ℕ) : ℕ :=
  Nat.log 3 (L / bandBase Cbox Cdep) / (d + 2)

/-- The number of separated roots the union bound uses in band `j`. -/
def bandMult (d Cbox Cdep L j : ℕ) : ℕ :=
  L / (3 ^ (j * (d + 1)) * (bandSep Cbox Cdep j + 1))

/-- The denominator of `bandMult` is at most `bandBase · 3 ^ (j (d+2))`. -/
theorem bandDen_le (Cbox Cdep j : ℕ) :
    3 ^ (j * (d + 1)) * (bandSep Cbox Cdep j + 1) ≤ bandBase Cbox Cdep * 3 ^ (j * (d + 2)) := by
  have hstep : 3 ^ (j * (d + 1)) * (bandBase Cbox Cdep * 3 ^ j)
      = bandBase Cbox Cdep * 3 ^ (j * (d + 2)) := by
    have hexp : j * (d + 2) = j * (d + 1) + j := by ring
    rw [hexp, pow_add]
    ring
  calc 3 ^ (j * (d + 1)) * (bandSep Cbox Cdep j + 1)
      ≤ 3 ^ (j * (d + 1)) * (bandBase Cbox Cdep * 3 ^ j) :=
        Nat.mul_le_mul_left _ (bandSep_succ_le Cbox Cdep j)
    _ = bandBase Cbox Cdep * 3 ^ (j * (d + 2)) := hstep

/-- **Every band up to the depth fits inside `L`.** -/
theorem bandBase_mul_pow_le {Cbox Cdep L j : ℕ} (hL : bandBase Cbox Cdep ≤ L)
    (hj : j ≤ bandDepth d Cbox Cdep L) :
    bandBase Cbox Cdep * 3 ^ (j * (d + 2)) ≤ L := by
  have hbpos : 0 < bandBase Cbox Cdep := one_le_bandBase Cbox Cdep
  have hdiv : L / bandBase Cbox Cdep ≠ 0 := by
    have := (Nat.one_le_div_iff hbpos).mpr hL
    omega
  have hlog : 3 ^ Nat.log 3 (L / bandBase Cbox Cdep) ≤ L / bandBase Cbox Cdep :=
    Nat.pow_log_le_self 3 hdiv
  have hexp : j * (d + 2) ≤ Nat.log 3 (L / bandBase Cbox Cdep) := by
    have h1 : bandDepth d Cbox Cdep L * (d + 2) ≤ Nat.log 3 (L / bandBase Cbox Cdep) :=
      Nat.div_mul_le_self _ _
    have h2 : j * (d + 2) ≤ bandDepth d Cbox Cdep L * (d + 2) :=
      Nat.mul_le_mul_right _ hj
    omega
  have hpow : 3 ^ (j * (d + 2)) ≤ L / bandBase Cbox Cdep :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hexp) hlog
  calc bandBase Cbox Cdep * 3 ^ (j * (d + 2))
      ≤ bandBase Cbox Cdep * (L / bandBase Cbox Cdep) := Nat.mul_le_mul_left _ hpow
    _ = L / bandBase Cbox Cdep * bandBase Cbox Cdep := by ring
    _ ≤ L := Nat.div_mul_le_self _ _

/-- **The depth is as large as it can be.**  Consequently `3 ^ (bandDepth) ≍ L ^ (1/(d+2))`. -/
theorem lt_bandBase_mul_pow (d Cbox Cdep L : ℕ) :
    L < bandBase Cbox Cdep * 3 ^ (d + 2) * (3 ^ bandDepth d Cbox Cdep L) ^ (d + 2) := by
  have hbpos : 0 < bandBase Cbox Cdep := one_le_bandBase Cbox Cdep
  have hone : (1 : ℕ) ≤ (3 ^ bandDepth d Cbox Cdep L) ^ (d + 2) :=
    Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by norm_num))
  by_cases hL : L < bandBase Cbox Cdep
  · have h3 : (1 : ℕ) ≤ 3 ^ (d + 2) := Nat.one_le_pow _ _ (by norm_num)
    calc L < bandBase Cbox Cdep := hL
      _ = bandBase Cbox Cdep * 1 * 1 := by ring
      _ ≤ bandBase Cbox Cdep * 3 ^ (d + 2) * (3 ^ bandDepth d Cbox Cdep L) ^ (d + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) hone
  · push_neg at hL
    set t : ℕ := Nat.log 3 (L / bandBase Cbox Cdep) with ht
    set J : ℕ := bandDepth d Cbox Cdep L with hJ
    have hdiv : L / bandBase Cbox Cdep ≠ 0 := by
      have := (Nat.one_le_div_iff hbpos).mpr hL
      omega
    have hlt : L / bandBase Cbox Cdep < 3 ^ (t + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have hL' : L < (L / bandBase Cbox Cdep + 1) * bandBase Cbox Cdep :=
      lt_div_add_one_mul L _ hbpos
    have hstep : L < 3 ^ (t + 1) * bandBase Cbox Cdep := by
      have : (L / bandBase Cbox Cdep + 1) * bandBase Cbox Cdep ≤
          3 ^ (t + 1) * bandBase Cbox Cdep :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hr : t < J * (d + 2) + (d + 2) := by
      have h := lt_div_add_one_mul t (d + 2) (by omega)
      have hrw : (t / (d + 2) + 1) * (d + 2) = t / (d + 2) * (d + 2) + (d + 2) := by ring
      rw [hrw] at h
      have hJt : J = t / (d + 2) := by rw [hJ, bandDepth, ← ht]
      rw [hJt]
      exact h
    have hpow : 3 ^ (t + 1) ≤ 3 ^ (J * (d + 2)) * 3 ^ (d + 2) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfinal : 3 ^ (t + 1) * bandBase Cbox Cdep ≤
        bandBase Cbox Cdep * 3 ^ (d + 2) * (3 ^ J) ^ (d + 2) := by
      have hrw : (3 : ℕ) ^ (J * (d + 2)) = (3 ^ J) ^ (d + 2) := by rw [← pow_mul]
      calc 3 ^ (t + 1) * bandBase Cbox Cdep
          ≤ (3 ^ (J * (d + 2)) * 3 ^ (d + 2)) * bandBase Cbox Cdep :=
            Nat.mul_le_mul_right _ hpow
        _ = bandBase Cbox Cdep * 3 ^ (d + 2) * (3 ^ J) ^ (d + 2) := by rw [hrw]; ring
    omega

/-! ## The band multiplicities -/

theorem bandDen_pos (Cbox Cdep j : ℕ) :
    0 < 3 ^ (j * (d + 1)) * (bandSep Cbox Cdep j + 1) := by
  have : (1 : ℕ) ≤ 3 ^ (j * (d + 1)) := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 0 < bandSep Cbox Cdep j + 1 := by omega
  exact Nat.mul_pos (by omega) h2

/-- Every band up to the depth carries at least one separated root. -/
theorem one_le_bandMult {Cbox Cdep L j : ℕ} (hL : bandBase Cbox Cdep ≤ L)
    (hj : j ≤ bandDepth d Cbox Cdep L) : 1 ≤ bandMult d Cbox Cdep L j := by
  refine (Nat.one_le_div_iff (bandDen_pos Cbox Cdep j)).mpr ?_
  exact le_trans (bandDen_le Cbox Cdep j) (bandBase_mul_pow_le hL hj)

/-- The selected roots fit inside the band count. -/
theorem bandMult_mul_le (d Cbox Cdep L j : ℕ) :
    bandMult d Cbox Cdep L j * (bandSep Cbox Cdep j + 1) ≤ L / 3 ^ (j * (d + 1)) := by
  rw [bandMult, ← Nat.div_div_eq_div_mul]
  exact Nat.div_mul_le_self _ _

/-- The multiplicity is within a factor `2` of `L / (bandBase · 3 ^ (j (d+2)))`. -/
theorem lt_two_mul_bandMult {Cbox Cdep L j : ℕ} (hL : bandBase Cbox Cdep ≤ L)
    (hj : j ≤ bandDepth d Cbox Cdep L) :
    L < 2 * bandMult d Cbox Cdep L j * (bandBase Cbox Cdep * 3 ^ (j * (d + 2))) := by
  have hm1 : 1 ≤ bandMult d Cbox Cdep L j := one_le_bandMult hL hj
  have hup : L < (bandMult d Cbox Cdep L j + 1) *
      (3 ^ (j * (d + 1)) * (bandSep Cbox Cdep j + 1)) := by
    rw [bandMult]
    exact lt_div_add_one_mul L _ (bandDen_pos Cbox Cdep j)
  have h1 : (bandMult d Cbox Cdep L j + 1) *
      (3 ^ (j * (d + 1)) * (bandSep Cbox Cdep j + 1)) ≤
      2 * bandMult d Cbox Cdep L j * (bandBase Cbox Cdep * 3 ^ (j * (d + 2))) :=
    Nat.mul_le_mul (by omega) (bandDen_le Cbox Cdep j)
  omega

/-- **Every band produces the same gain `3 ^ J`, up to a factor `2`.** -/
theorem three_pow_bandDepth_lt {Cbox Cdep L j : ℕ} (hL : bandBase Cbox Cdep ≤ L)
    (hj : j ≤ bandDepth d Cbox Cdep L) :
    3 ^ bandDepth d Cbox Cdep L < 2 * bandMult d Cbox Cdep L j * 3 ^ j := by
  set J : ℕ := bandDepth d Cbox Cdep L with hJ
  set m : ℕ := bandMult d Cbox Cdep L j with hm
  have hbpos : 0 < bandBase Cbox Cdep := one_le_bandBase Cbox Cdep
  have hm1 : 1 ≤ m := one_le_bandMult hL hj
  have hlow : bandBase Cbox Cdep * 3 ^ (J * (d + 2)) ≤ L := bandBase_mul_pow_le hL le_rfl
  have hup2 : L < 2 * m * (bandBase Cbox Cdep * 3 ^ (j * (d + 2))) := by
    rw [hm]
    exact lt_two_mul_bandMult hL hj
  -- cancel `bandBase`
  have hcancel : 3 ^ (J * (d + 2)) < 2 * m * 3 ^ (j * (d + 2)) := by
    refine Nat.lt_of_mul_lt_mul_left (a := bandBase Cbox Cdep) ?_
    calc bandBase Cbox Cdep * 3 ^ (J * (d + 2)) ≤ L := hlow
      _ < 2 * m * (bandBase Cbox Cdep * 3 ^ (j * (d + 2))) := hup2
      _ = bandBase Cbox Cdep * (2 * m * 3 ^ (j * (d + 2))) := by ring
  -- cancel `3 ^ (J (d+1))`
  have hsplitJ : (3 : ℕ) ^ (J * (d + 2)) = 3 ^ (J * (d + 1)) * 3 ^ J := by
    have hexp : J * (d + 2) = J * (d + 1) + J := by ring
    rw [hexp, pow_add]
  have hsplitj : (3 : ℕ) ^ (j * (d + 2)) = 3 ^ (j * (d + 1)) * 3 ^ j := by
    have hexp : j * (d + 2) = j * (d + 1) + j := by ring
    rw [hexp, pow_add]
  have hmono : (3 : ℕ) ^ (j * (d + 1)) ≤ 3 ^ (J * (d + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hj)
  have hfin : 3 ^ (J * (d + 1)) * 3 ^ J < 3 ^ (J * (d + 1)) * (2 * m * 3 ^ j) := by
    calc 3 ^ (J * (d + 1)) * 3 ^ J = 3 ^ (J * (d + 2)) := hsplitJ.symm
      _ < 2 * m * 3 ^ (j * (d + 2)) := hcancel
      _ = 2 * m * (3 ^ (j * (d + 1)) * 3 ^ j) := by rw [hsplitj]
      _ ≤ 2 * m * (3 ^ (J * (d + 1)) * 3 ^ j) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmono)
      _ = 3 ^ (J * (d + 1)) * (2 * m * 3 ^ j) := by ring
  have := Nat.lt_of_mul_lt_mul_left hfin
  omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
