module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalRenormalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory ProbabilityTheory Finset
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The pair count -/

/-- The pairs of sub-box centres that the level-`k` dependence range separates. -/
def separatedPairs (R : ℕ) (S : Finset (Lattice d)) : Finset (Lattice d × Lattice d) :=
  (S ×ˢ S).filter fun yz => R < latticeDist yz.1 yz.2

/-- The entropy of the two-seed decomposition: at most `(#S) ^ 2` pairs. -/
theorem card_separatedPairs_le (R : ℕ) (S : Finset (Lattice d)) :
    (separatedPairs R S).card ≤ S.card ^ 2 := by
  calc (separatedPairs R S).card ≤ (S ×ˢ S).card := Finset.card_filter_le _ _
    _ = S.card * S.card := Finset.card_product _ _
    _ = S.card ^ 2 := (sq _).symm

/-- Members of `separatedPairs` are separated, by construction. -/
theorem separated_of_mem_separatedPairs {R : ℕ} {S : Finset (Lattice d)}
    {yz : Lattice d × Lattice d} (h : yz ∈ separatedPairs R S) :
    R < latticeDist yz.1 yz.2 := (Finset.mem_filter.mp h).2

/-! ## The two-seed step -/

/-- Two events of a finite-range field at separated sites are independent. -/
theorem measure_inter_event_eq_mul_of_finiteRange
    {E : Lattice d → Set Ω} {R : ℕ} {y w : Lattice d}
    (hindep : FiniteRangeIndependentEvents μ R E) (hsep : R < latticeDist y w) :
    μ (E y ∩ E w) = μ (E y) * μ (E w) := by
  have hsep' : ∀ u ∈ ({y} : Set (Lattice d)), ∀ v ∈ ({w} : Set (Lattice d)),
      R < latticeDist u v := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst hu; subst hv
    exact hsep
  exact (Indep_iff _ _ μ).mp (hindep _ _ hsep') _ _
    (measurableSet_event_of_mem (Set.mem_singleton y))
    (measurableSet_event_of_mem (Set.mem_singleton w))

/-- **The two-seed union bound.**  An event forced to contain either two
separated level-`k` failures or a long closed crossing costs one factor `p ^ 2`
per separated pair, plus the crossing. -/
theorem measure_le_card_mul_sq_add_of_twoSeedDecomposition [IsProbabilityMeasure μ]
    {Bk : Lattice d → Set Ω} {Cross A : Set Ω} {R : ℕ} {S : Finset (Lattice d)}
    {p : ℝ≥0∞}
    (hindep : FiniteRangeIndependentEvents μ R Bk)
    (hp : ∀ y, μ (Bk y) ≤ p)
    (hdec : A ⊆ (⋃ yz ∈ separatedPairs R S, Bk yz.1 ∩ Bk yz.2) ∪ Cross) :
    μ A ≤ (separatedPairs R S).card * p ^ 2 + μ Cross := by
  refine (measure_mono hdec).trans ((measure_union_le _ _).trans ?_)
  refine add_le_add ?_ le_rfl
  calc μ (⋃ yz ∈ separatedPairs R S, Bk yz.1 ∩ Bk yz.2)
      ≤ ∑ yz ∈ separatedPairs R S, μ (Bk yz.1 ∩ Bk yz.2) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _yz ∈ separatedPairs R S, p ^ 2 := by
        refine Finset.sum_le_sum fun yz hyz => ?_
        rw [measure_inter_event_eq_mul_of_finiteRange hindep
          (separated_of_mem_separatedPairs hyz), sq]
        exact mul_le_mul' (hp _) (hp _)
    _ = (separatedPairs R S).card * p ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]



theorem measure_le_ofReal_twoSeedStep [IsProbabilityMeasure μ]
    {Bk : Lattice d → Set Ω} {Cross A : Set Ω} {R : ℕ} {S : Finset (Lattice d)}
    {pk ek gk : ℝ} (hpk : 0 ≤ pk) (hek : 0 ≤ ek) (hgk : 0 ≤ gk)
    (hindep : FiniteRangeIndependentEvents μ R Bk)
    (hp : ∀ y, μ (Bk y) ≤ ENNReal.ofReal pk)
    (hcross : μ Cross ≤ ENNReal.ofReal gk)
    (hcard : ((separatedPairs R S).card : ℝ) ≤ Real.exp ek)
    (hdec : A ⊆ (⋃ yz ∈ separatedPairs R S, Bk yz.1 ∩ Bk yz.2) ∪ Cross) :
    μ A ≤ ENNReal.ofReal (Real.exp ek * (pk ^ 2 + gk)) := by
  have hone : (1 : ℝ) ≤ Real.exp ek := by
    have := Real.add_one_le_exp ek
    linarith
  have hmain := measure_le_card_mul_sq_add_of_twoSeedDecomposition hindep hp hdec
  refine hmain.trans ?_
  rw [← ENNReal.ofReal_pow hpk]
  have hstep :
      ((separatedPairs R S).card : ℝ≥0∞) * ENNReal.ofReal (pk ^ 2) + μ Cross ≤
        ENNReal.ofReal (Real.exp ek * pk ^ 2) + ENNReal.ofReal (Real.exp ek * gk) := by
    refine add_le_add ?_ (hcross.trans (ENNReal.ofReal_le_ofReal ?_))
    · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hcard (by positivity))
    · nlinarith
  refine hstep.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  ring_nf

/-! ## The `√2` schedule -/

/-- The scale schedule `L_k = exp (√2 ^ k)` forced by the printed exponent
`(log L) ^ 2`. -/
def sqrtTwoScale (k : ℕ) : ℝ := Real.exp (Real.sqrt 2 ^ k)



def sqrtTwoRatio (k : ℕ) : ℝ := Real.exp ((Real.sqrt 2 - 1) * Real.sqrt 2 ^ k)

theorem sqrtTwoScale_pos (k : ℕ) : 0 < sqrtTwoScale k := Real.exp_pos _

theorem sqrtTwoRatio_pos (k : ℕ) : 0 < sqrtTwoRatio k := Real.exp_pos _

/-- The schedule step `L_{k+1} = L_k * l_k`. -/
theorem sqrtTwoScale_succ (k : ℕ) :
    sqrtTwoScale (k + 1) = sqrtTwoScale k * sqrtTwoRatio k := by
  rw [sqrtTwoScale, sqrtTwoScale, sqrtTwoRatio, ← Real.exp_add, pow_succ]
  congr 1
  ring

/-- `log l_k = (√2 − 1) log L_k`: the ratio is the pinned power of the scale. -/
theorem log_sqrtTwoRatio (k : ℕ) :
    Real.log (sqrtTwoRatio k) = (Real.sqrt 2 - 1) * Real.log (sqrtTwoScale k) := by
  rw [sqrtTwoRatio, sqrtTwoScale, Real.log_exp, Real.log_exp]

/-- The level entropy `e_k = log (C l_k ^ (2 d))` of the printed recursion. -/
def sqrtTwoScheduleEntropy (Centropy : ℝ) (d k : ℕ) : ℝ :=
  Real.log Centropy + 2 * d * ((Real.sqrt 2 - 1) * Real.sqrt 2 ^ k)

/-- The entropy is literally the printed `log (C l_k ^ (2 d))`. -/
theorem sqrtTwoScheduleEntropy_eq_log {Centropy : ℝ} (hC : 0 < Centropy) (d k : ℕ) :
    sqrtTwoScheduleEntropy Centropy d k =
      Real.log (Centropy * sqrtTwoRatio k ^ (2 * d)) := by
  rw [Real.log_mul hC.ne' (pow_pos (sqrtTwoRatio_pos k) _).ne', Real.log_pow,
    sqrtTwoRatio, Real.log_exp,
    sqrtTwoScheduleEntropy]
  push_cast
  ring

theorem sqrtTwoScheduleEntropy_nonneg {Centropy : ℝ} (hC : 1 ≤ Centropy) (d k : ℕ) :
    0 ≤ sqrtTwoScheduleEntropy Centropy d k := by
  have hlog : 0 ≤ Real.log Centropy := Real.log_nonneg hC
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hpow : (0 : ℝ) ≤ Real.sqrt 2 ^ k := by positivity
  have : 0 ≤ 2 * (d : ℝ) * ((Real.sqrt 2 - 1) * Real.sqrt 2 ^ k) := by
    have : 0 ≤ (Real.sqrt 2 - 1) * Real.sqrt 2 ^ k := by nlinarith
    positivity
  simp only [sqrtTwoScheduleEntropy]
  linarith

/-! ## The closed-form entropy budget -/

theorem one_sub_sqrtTwo_div_two_inv : (1 - Real.sqrt 2 / 2)⁻¹ = 2 + Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hmul : (1 - Real.sqrt 2 / 2) * (2 + Real.sqrt 2) = 1 := by nlinarith [h2]
  exact inv_eq_of_mul_eq_one_right hmul

theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- `∑_{i<k} (√2 / 2) ^ i ≤ 2 + √2`. -/
theorem geom_sum_sqrtTwo_div_two_le (k : ℕ) :
    ∑ i ∈ Finset.range k, (Real.sqrt 2 / 2) ^ i ≤ 2 + Real.sqrt 2 := by
  set r : ℝ := Real.sqrt 2 / 2 with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hrdef]; linarith [sqrt_two_lt_two]
  calc ∑ i ∈ Finset.range k, r ^ i ≤ ∑' i, r ^ i :=
      (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun i _ => by positivity)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
    _ = 2 + Real.sqrt 2 := one_sub_sqrtTwo_div_two_inv

/-- `∑_{i<k} 2⁻¹ ^ i ≤ 2`. -/
theorem geom_sum_half_le (k : ℕ) : ∑ i ∈ Finset.range k, ((2 : ℝ)⁻¹) ^ i ≤ 2 := by
  have hr0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
  have hr1 : (2 : ℝ)⁻¹ < 1 := by norm_num
  calc ∑ i ∈ Finset.range k, ((2 : ℝ)⁻¹) ^ i ≤ ∑' i, ((2 : ℝ)⁻¹) ^ i :=
      (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun i _ => by positivity)
    _ = (1 - (2 : ℝ)⁻¹)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
    _ = 2 := by norm_num

/-- **The closed-form entropy budget of the `√2` schedule.**

`∑_i (e_i + log 2) 2^{-i} ≤ 2 (log C + log 2) + 2 √2 d`, because
`(√2 − 1)(2 + √2) = √2`.  Together with `hS : S ≤ a = c q` this is the explicit
`q₀(d) = (2 log (2 C) + 2 √2 d) / c`. -/
theorem sqrtTwoScheduleEntropy_sum_le {Centropy : ℝ} (hC : 1 ≤ Centropy) (d k : ℕ) :
    ∑ i ∈ Finset.range k,
        (sqrtTwoScheduleEntropy Centropy d i + Real.log 2) * ((2 : ℝ)⁻¹) ^ i ≤
      2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * d := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hlogC : 0 ≤ Real.log Centropy := Real.log_nonneg hC
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsplit : ∀ i : ℕ,
      (sqrtTwoScheduleEntropy Centropy d i + Real.log 2) * ((2 : ℝ)⁻¹) ^ i =
        (Real.log Centropy + Real.log 2) * (((2 : ℝ)⁻¹) ^ i) +
          (2 * (d : ℝ) * (Real.sqrt 2 - 1)) * ((Real.sqrt 2 / 2) ^ i) := by
    intro i
    have hp : (Real.sqrt 2 / 2) ^ i = Real.sqrt 2 ^ i * ((2 : ℝ)⁻¹) ^ i := by
      rw [← mul_pow, div_eq_mul_inv]
    rw [sqrtTwoScheduleEntropy, hp]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hA : (Real.log Centropy + Real.log 2) * ∑ i ∈ Finset.range k, ((2 : ℝ)⁻¹) ^ i ≤
      (Real.log Centropy + Real.log 2) * 2 :=
    mul_le_mul_of_nonneg_left (geom_sum_half_le k) (by linarith)
  have hcoef : (0 : ℝ) ≤ 2 * (d : ℝ) * (Real.sqrt 2 - 1) := by
    have : (0 : ℝ) ≤ Real.sqrt 2 - 1 := by linarith
    positivity
  have hB : (2 * (d : ℝ) * (Real.sqrt 2 - 1)) *
        ∑ i ∈ Finset.range k, (Real.sqrt 2 / 2) ^ i ≤
      (2 * (d : ℝ) * (Real.sqrt 2 - 1)) * (2 + Real.sqrt 2) :=
    mul_le_mul_of_nonneg_left (geom_sum_sqrtTwo_div_two_le k) hcoef
  have hid : (2 * (d : ℝ) * (Real.sqrt 2 - 1)) * (2 + Real.sqrt 2) =
      2 * Real.sqrt 2 * d := by nlinarith [h2]
  linarith [hid ▸ hB]

/-! ## The crossing scale clears the induction threshold -/

/-- `(k + 1) log 2 ≤ (3/2) √2 ^ k`: the crossing exponent `L_k ^ (3/2)` dominates
the `2 · 2 ^ k` the two-seed induction needs. -/
theorem succ_mul_log_two_le_three_halves_sqrtTwo_pow (k : ℕ) :
    ((k : ℝ) + 1) * Real.log 2 ≤ 3 / 2 * Real.sqrt 2 ^ k := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (1.41 : ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hL : Real.log 2 ≤ 0.694 :=
    le_of_lt (lt_of_lt_of_le Real.log_two_lt_d9 (by norm_num))
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  induction k with
  | zero => simpa using by linarith
  | succ k ih =>
    have hpow : (0 : ℝ) < Real.sqrt 2 ^ k := by positivity
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · rw [pow_one]
        push_cast
        linarith
      · rw [show (1 : ℕ) + 1 = 2 from rfl, hsq]
        push_cast
        linarith
    · have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hmul : Real.sqrt 2 * (((k : ℝ) + 1) * Real.log 2) ≤
          Real.sqrt 2 * (3 / 2 * Real.sqrt 2 ^ k) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      rw [pow_succ]
      push_cast
      nlinarith

/-- `2 · 2 ^ k ≤ L_k ^ (3/2) = exp ((3/2) √2 ^ k)`. -/
theorem two_mul_two_pow_le_exp_three_halves (k : ℕ) :
    2 * 2 ^ k ≤ Real.exp (3 / 2 * Real.sqrt 2 ^ k) := by
  have hval : Real.exp (((k : ℕ) + 1 : ℕ) * Real.log 2) = 2 * 2 ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    ring
  calc (2 : ℝ) * 2 ^ k = Real.exp (((k : ℕ) + 1 : ℕ) * Real.log 2) := hval.symm
    _ ≤ Real.exp (3 / 2 * Real.sqrt 2 ^ k) := by
        refine Real.exp_le_exp.mpr ?_
        have := succ_mul_log_two_le_three_halves_sqrtTwo_pow k
        push_cast
        linarith

/-! ## The induction, re-run on the `√2` schedule -/

/-- **The `q`-uniform rate on the `√2` schedule.**

Feeding the printed one-step recursion into
`le_exp_neg_half_of_entropyReserve_recursion` with the closed-form budget
`S = 2 (log C + log 2) + 2 √2 d` gives `p_k ≤ exp (-(a / 2) 2 ^ k)` with
`a = c q`, uniformly for all `a ≥ S`: the rate is linear in `q` and the constant
is dimensional. -/
theorem le_exp_neg_half_of_sqrtTwo_renormalization
    {p g : ℕ → ℝ} {a Centropy : ℝ} {d : ℕ} (ha : 0 < a) (hC : 1 ≤ Centropy)
    (hq0 : 2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * d ≤ a)
    (hpnn : ∀ k, 0 ≤ p k)
    (hp0 : p 0 ≤ Real.exp (-a))
    (hrec : ∀ k, p (k + 1) ≤
      Real.exp (sqrtTwoScheduleEntropy Centropy d k) * (p k ^ 2 + Real.exp (-(a * g k))))
    (hg : ∀ k, 2 * 2 ^ k ≤ g k) :
    ∀ k, p k ≤ Real.exp (-(a / 2 * 2 ^ k)) := by
  refine le_exp_neg_half_of_entropyReserve_recursion ha
    (fun i => sqrtTwoScheduleEntropy_nonneg hC d i) hpnn
    (fun k => sqrtTwoScheduleEntropy_sum_le hC d k) hq0 ?_ hrec hg
  simpa [entropyReserveWeight] using hp0

/-- **The printed bound, at every intermediate scale.**  With the crossing scale
`g_k = L_k ^ (3/2)` the induction closes, and the level bound converts to
`exp (-(a / 4) (log L) ^ 2)` at every `L ≥ e` — the manuscript's
`C exp (-c q (log L) ^ 2)` with `C = 1` and the constant `c / 4` explicit. -/
theorem exp_neg_log_sq_of_sqrtTwo_renormalization
    {p : ℕ → ℝ} {a Centropy : ℝ} {d : ℕ} (ha : 0 < a) (hC : 1 ≤ Centropy)
    (hq0 : 2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * d ≤ a)
    (hpnn : ∀ k, 0 ≤ p k)
    (hp0 : p 0 ≤ Real.exp (-a))
    (hrec : ∀ k, p (k + 1) ≤
      Real.exp (sqrtTwoScheduleEntropy Centropy d k) *
        (p k ^ 2 + Real.exp (-(a * Real.exp (3 / 2 * Real.sqrt 2 ^ k)))))
    {L : ℝ} (hL : Real.exp 1 ≤ L) :
    ∃ k : ℕ, sqrtTwoScale k ≤ L ∧ p k ≤ Real.exp (-(a / 4 * Real.log L ^ 2)) := by
  have hlevel := le_exp_neg_half_of_sqrtTwo_renormalization ha hC hq0 hpnn hp0 hrec
    (fun k => two_mul_two_pow_le_exp_three_halves k)
  obtain ⟨k, hle, hbound⟩ :=
    exists_level_exp_neg_log_sq (b := a / 2) (by linarith) hL
  refine ⟨k, hle, (hlevel k).trans (hbound.trans (le_of_eq ?_))⟩
  congr 1
  ring

/-- **The packaged provider form.**  A dominating sequence `p` for the level
probabilities, satisfying the printed one-step recursion on the `√2` schedule,
transfers the `q`-uniform rate to every level-`k` unfavourable event. -/
theorem measure_le_exp_neg_of_sqrtTwo_renormalization
    {B : ℕ → Lattice d → Set Ω} {p g : ℕ → ℝ} {a Centropy : ℝ} {dim : ℕ}
    (ha : 0 < a) (hC : 1 ≤ Centropy)
    (hq0 : 2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * dim ≤ a)
    (hpnn : ∀ k, 0 ≤ p k)
    (hdom : ∀ k x, μ (B k x) ≤ ENNReal.ofReal (p k))
    (hp0 : p 0 ≤ Real.exp (-a))
    (hrec : ∀ k, p (k + 1) ≤
      Real.exp (sqrtTwoScheduleEntropy Centropy dim k) *
        (p k ^ 2 + Real.exp (-(a * g k))))
    (hg : ∀ k, 2 * 2 ^ k ≤ g k) (k : ℕ) (x : Lattice d) :
    μ (B k x) ≤ ENNReal.ofReal (Real.exp (-(a / 2 * 2 ^ k))) :=
  (hdom k x).trans (ENNReal.ofReal_le_ofReal
    (le_exp_neg_half_of_sqrtTwo_renormalization ha hC hq0 hpnn hp0 hrec hg k))


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
