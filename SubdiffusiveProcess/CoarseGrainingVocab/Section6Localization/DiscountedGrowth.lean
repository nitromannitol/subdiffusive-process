module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatioEvent

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open Homogenization Homogenization.Book
open scoped BigOperators

noncomputable section

variable {d : ℕ}

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have hexp : Real.exp 1 < (3 : ℝ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have hlog := Real.log_lt_log (Real.exp_pos 1) hexp
  simpa only [Real.log_exp] using hlog.le

private theorem exp_le_three_rpow_of_nonneg_of_le {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.exp x ≤ (3 : ℝ) ^ y := by
  have hy : 0 ≤ y := hx.trans hxy
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  apply Real.exp_le_exp.mpr
  calc
    x ≤ y := hxy
    _ = 1 * y := (one_mul y).symm
    _ ≤ Real.log 3 * y := mul_le_mul_of_nonneg_right one_le_log_three hy

/-- The deterministic `rho_(m,n)` half of the discounted exponential-growth
display.  The hypotheses and exponent are the manuscript's literal
`64 delta^2 <= s` and `s(m-n)/16`. -/
theorem exp_abs_normalizerLogError_le_three_rpow
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m n : ℕ} (hnm : n ≤ m)
    {s : ℝ} (hs : 64 * M.delta ^ 2 ≤ s) :
    Real.exp |normalizerLogError M m n| ≤
      (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 16) := by
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have htauFour : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ 4 * M.delta ^ 2 := by
    calc
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤
          (Real.log 2 / 2) * M.delta ^ 2 := tauSq_le_delta_sq M
      _ ≤ 4 * M.delta ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg M.delta)
  have hgap : 0 ≤ (((m - n : ℕ) : ℝ)) := by positivity
  have hrho := abs_normalizerLogError_le_of_le M hnm
  have hbudget :
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ) ≤
        (s * ((m - n : ℕ) : ℝ)) / 16 := by
    have htauGap := mul_le_mul_of_nonneg_right htauFour hgap
    have hsGap := mul_le_mul_of_nonneg_right hs hgap
    nlinarith
  exact exp_le_three_rpow_of_nonneg_of_le (abs_nonneg _)
    (hrho.trans hbudget)

private theorem translatedCube_subset_goodFieldTwoCube
    {m n : ℕ} (hnm : n ≤ m) {z : Vec d} (hz : z ∈ cube d m) :
    translatedCube d (n : ℤ) z ⊆
      cube d ((m + 1 + (m - n) : ℕ) : ℤ) := by
  rintro x ⟨y, hy, rfl⟩
  rw [cube, mem_openCubeSet_originCube_iff] at hz hy ⊢
  intro i
  have hzi := hz i
  have hyi := hy i
  simp only [zpow_natCast] at hzi hyi
  change (-(1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1 + (m - n)) < z i + y i) ∧
    (z i + y i < (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1 + (m - n)))
  have hpow_nm : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hnm
  have hpow_large : (3 : ℝ) ^ (m + 1) ≤
      (3 : ℝ) ^ (m + 1 + (m - n)) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
  have hmpos : 0 < (3 : ℝ) ^ m := by positivity
  have htarget : (3 : ℝ) ^ m <
      (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1 + (m - n)) := by
    have hsucc : (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := by
      rw [pow_succ]
      ring
    rw [hsucc] at hpow_large
    nlinarith
  constructor <;> nlinarith

private theorem exp_abs_shellBlock_le_goodFieldTwo_finiteProduct
    {m n : ℕ} (hnm : n ≤ m)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    Real.exp |shellBlock m n omega x| ≤
      ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
        Real.exp |omega i x| := by
  unfold shellBlock
  calc
    Real.exp |∑ i ∈ Finset.Icc (n + 1) m, omega i x| ≤
        Real.exp (∑ i ∈ Finset.Icc (n + 1) m, |omega i x|) :=
      Real.exp_le_exp.mpr (Finset.abs_sum_le_sum_abs _ _)
    _ = ∏ i ∈ Finset.Icc (n + 1) m, Real.exp |omega i x| := by
      rw [Real.exp_sum]
    _ ≤ ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
        Real.exp |omega i x| := by
      let u := Finset.Icc (n + 1) m
      let v := Finset.Icc (m - (m - n)) (m + (m - n))
      have huv : u ⊆ v := by
        intro i hi
        simp only [u, v, Finset.mem_Icc] at hi ⊢
        omega
      have hleft : 0 ≤ ∏ i ∈ u, Real.exp |omega i x| := by positivity
      have hrest : 1 ≤ ∏ i ∈ v \ u, Real.exp |omega i x| := by
        induction v \ u using Finset.induction_on with
        | empty => simp
        | @insert a w haw ih =>
            rw [Finset.prod_insert haw]
            exact one_le_mul_of_one_le_of_one_le
              (Real.one_le_exp (abs_nonneg _)) ih
      change (∏ i ∈ u, Real.exp |omega i x|) ≤
        ∏ i ∈ v, Real.exp |omega i x|
      calc
        (∏ i ∈ u, Real.exp |omega i x|) =
            1 * ∏ i ∈ u, Real.exp |omega i x| := by rw [one_mul]
        _ ≤ (∏ i ∈ v \ u, Real.exp |omega i x|) *
            ∏ i ∈ u, Real.exp |omega i x| :=
          mul_le_mul_of_nonneg_right hrest hleft
        _ = ∏ i ∈ v, Real.exp |omega i x| := Finset.prod_sdiff huv

private theorem one_le_goodFieldTwo_tail
    (m q : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x y : Vec d) :
    1 ≤ ∏' i : ℕ, if m + q ≤ i then
      Real.exp (4 * |omega i x - omega i y|) else 1 := by
  let f : ℕ → ℝ := fun i => if m + q ≤ i then
    Real.exp (4 * |omega i x - omega i y|) else 1
  have hf : ∀ i, 1 ≤ f i := by
    intro i
    dsimp [f]
    split
    · exact Real.one_le_exp (by positivity)
    · exact le_rfl
  by_cases hmult : Multipliable f
  · apply le_hasProd_of_le_prod hmult.hasProd
    intro u
    induction u using Finset.induction_on with
    | empty => simp
    | @insert a w haw ih =>
        rw [Finset.prod_insert haw]
        exact one_le_mul_of_one_le_of_one_le (hf a) ih
  · rw [tprod_eq_one_of_not_multipliable hmult]

/-- Pointwise shell-block growth read from `GoodFieldTwo`, with the exact
boundedness guard needed to eliminate the junk value of the real `sSup` in
`supNormOn`. -/
theorem exp_abs_shellBlock_le_of_goodFieldTwo
    {m n : ℕ} (hnm : n ≤ m) {s : ℝ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {z : Vec d}
    (hz : z ∈ cube d m) (hgood : GoodFieldTwo m 0 s omega)
    (hBdd : BddAbove {a : ℝ | ∃ x ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i x|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1|}) :
    ∀ x ∈ translatedCube d (n : ℤ) z,
      Real.exp |shellBlock m n omega x| ≤
        6 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8) := by
  intro x hx
  have hxlarge : x ∈ cube d ((m + 1 + (m - n) : ℕ) : ℤ) :=
    translatedCube_subset_goodFieldTwoCube hnm hz hx
  have hxlarge' : x ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0 := by
    exact ⟨x, hxlarge, by simp⟩
  let finitePart : ℝ :=
    ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)), Real.exp |omega i x|
  let tailPart : ℝ :=
    ∏' i : ℕ, if m + (m - n) ≤ i then
      Real.exp (4 * |omega i x - omega i 0|) else 1
  have hfinitePos : 0 < finitePart := by
    dsimp [finitePart]
    positivity
  have htailOne : 1 ≤ tailPart := by
    exact one_le_goodFieldTwo_tail m (m - n) omega x 0
  have hcontrolPos : 0 < finitePart + tailPart := by linarith
  have hpoint : finitePart + tailPart ≤
      supNormOn (translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0)
        (fun x =>
          (∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
              Real.exp |omega i x|) +
            ∏' i : ℕ, if m + (m - n) ≤ i then
              Real.exp (4 * |omega i x - omega i 0|) else 1) := by
    unfold supNormOn
    have hle := le_csSup hBdd
      (show |finitePart + tailPart| ∈ {a : ℝ | ∃ y ∈
          translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
            a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
                Real.exp |omega i y|) +
              ∏' i : ℕ, if m + (m - n) ≤ i then
                Real.exp (4 * |omega i y - omega i 0|) else 1|} by
        refine ⟨x, hxlarge', ?_⟩
        rfl)
    rwa [abs_of_pos hcontrolPos] at hle
  have hevent := hgood (m - n)
  have hfinite :
      Real.exp |shellBlock m n omega x| ≤ finitePart := by
    exact exp_abs_shellBlock_le_goodFieldTwo_finiteProduct hnm omega x
  exact hfinite.trans ((le_add_of_nonneg_right (zero_le_one.trans htailOne)).trans
    (hpoint.trans hevent))

/-- Supremum-norm form of the discounted shell-block growth estimate. -/
theorem exp_supNormOn_shellBlock_le_of_goodFieldTwo
    {m n : ℕ} (hnm : n ≤ m) {s : ℝ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {z : Vec d}
    (hz : z ∈ cube d m) (hgood : GoodFieldTwo m 0 s omega)
    (hBdd : BddAbove {a : ℝ | ∃ x ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i x|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1|}) :
    Real.exp (supNormOn (translatedCube d (n : ℤ) z)
      (shellBlock m n omega)) ≤
        6 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8) := by
  let B : ℝ := 6 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hpoint := exp_abs_shellBlock_le_of_goodFieldTwo
    hnm omega hz hgood hBdd
  have habs : ∀ x ∈ translatedCube d (n : ℤ) z,
      |shellBlock m n omega x| ≤ Real.log B := by
    intro x hx
    rw [← Real.log_exp |shellBlock m n omega x|]
    exact Real.log_le_log (Real.exp_pos _) (hpoint x hx)
  have hsup : supNormOn (translatedCube d (n : ℤ) z)
      (shellBlock m n omega) ≤ Real.log B := by
    unfold supNormOn
    apply csSup_le
    · have hzero : (0 : Vec d) ∈ cube d (n : ℤ) := by
        rw [cube, mem_openCubeSet_originCube_iff]
        intro i
        have hp : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
        constructor <;> simp only [Pi.zero_apply] <;> nlinarith
      exact ⟨|shellBlock m n omega z|, z,
        ⟨0, hzero, by simp⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact habs x hx
  calc
    Real.exp (supNormOn (translatedCube d (n : ℤ) z)
        (shellBlock m n omega)) ≤ Real.exp (Real.log B) :=
      Real.exp_le_exp.mpr hsup
    _ = B := Real.exp_log hBpos
    _ = 6 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8) := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
