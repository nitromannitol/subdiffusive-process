import Homogenization.Probability.IndependentSums.GammaSigma.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# A graded `Γ₂` envelope with a `√(k+1)` threshold

Rows `I k` of finitely many observables, each with a common `Γ₂` scale `a k`,
are dominated simultaneously by one almost surely finite random constant at the
deterministic price `√(k+1) · a k`.

Two points distinguish this from the `Γ₁`/linear device
`Algsuperdiff/Section3/Provider/CoarseEllipticity/JointGridDepthMaximum.lean`
(`gradedFiniteEnvelope`), which is the shape template followed here.

* The threshold is `λ √(k+1) · a k`, not `(growth + 2)(k+1) · a k`.  With a
  Gaussian tail `exp (-t²)` the row entropy `exp (growth (k+1))` is already
  paid by `t = λ √(k+1)` as soon as `λ² ≥ growth + 2`, because the exponent
  becomes `(k+1)(growth - λ² t²)`.  The linear device would deliver a factor
  `k+1`, i.e. `log (2 + ‖x‖)` downstream instead of `√(log (2 + ‖x‖))`.
* The per-row estimate is the *raw* union bound
  `measureReal_biUnion_upperTailEvent_le`: `card · exp (-t^σ)`, with the card
  left standing.  The packaged finite-supremum lemma
  `isBigOWith_gammaSigma_finset_sup'` instead converts `card` into a scale
  `(3 log card)^{1/σ}`, which stops decaying once the graded index enters the
  threshold, so it cannot drive a graded Borel–Cantelli.

The conclusion is almost sure, as it must be under marginal tail hypotheses
only; no pointwise statement is asserted.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open MeasureTheory
open Homogenization Homogenization.IndependentSums
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] {mu : Measure Ω}

/-! ## The raw union bound

This is the estimate `isBigOWith_gammaSigma_finset_sup'` is built from, before
it repackages `card` as a scale factor `(3 log card)^{1/σ}`. -/

/-- Union bound for a finite family of one-sided `Γ_σ` tails at a common
scale, with the cardinality left as an explicit factor. -/
theorem measureReal_biUnion_upperTailEvent_le [IsFiniteMeasure mu]
    (s : Finset ι) {X : ι → Ω → ℝ} {A sigma t : ℝ} (ht : 1 ≤ t)
    (hX : ∀ i ∈ s, IsBigOWith mu (gammaSigma sigma) (X i) A) :
    mu.real (⋃ i ∈ s, upperTailEvent (X i) (A * t)) ≤
      (s.card : ℝ) * Real.exp (-(t ^ sigma)) := by
  refine (measureReal_biUnion_finset_le (μ := mu) s
    (fun i => upperTailEvent (X i) (A * t))).trans ?_
  refine (Finset.sum_le_sum fun i hi =>
    (isBigOWith_gammaSigma_iff.mp (hX i hi)) ht).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Elementary exponential sums -/

private theorem exp_neg_le_half {s : ℝ} (hs : 1 ≤ s) :
    Real.exp (-s) ≤ 1 / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp s :=
    (by linarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ Real.exp 1).trans
      (Real.exp_le_exp.2 hs)
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos s)]
  linarith

private theorem summable_exp_neg_two_mul_succ {s : ℝ} (hs : 1 ≤ s) :
    Summable fun k : ℕ => Real.exp (-(2 * ((k : ℝ) + 1) * s)) := by
  have hq0 : 0 ≤ Real.exp (-(2 * s)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(2 * s)) < 1 := by
    have hneg : -(2 * s) < 0 := by linarith
    simpa only [Real.exp_zero] using Real.exp_lt_exp.2 hneg
  have hgeom : Summable fun k : ℕ => Real.exp (-(2 * s)) ^ (k + 1) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_right _).congr
      fun k => (pow_succ _ k).symm
  refine hgeom.congr fun k => ?_
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem tsum_exp_neg_two_mul_succ_le {s : ℝ} (hs : 1 ≤ s) :
    ∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * s)) ≤ Real.exp (-s) := by
  set u : ℝ := Real.exp (-s) with hu_def
  set q : ℝ := Real.exp (-(2 * s)) with hq_def
  have hu0 : 0 < u := Real.exp_pos _
  have hu_half : u ≤ 1 / 2 := exp_neg_le_half hs
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    have hneg : -(2 * s) < 0 := by linarith
    simpa only [hq_def, Real.exp_zero] using Real.exp_lt_exp.2 hneg
  have hq_eq : q = u ^ 2 := by
    rw [hq_def, hu_def, show -(2 * s) = -s + -s by ring, Real.exp_add]
    ring
  have hsum : ∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * s)) = (1 - q)⁻¹ * q := by
    have hterm : ∀ k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * s)) = q ^ (k + 1) := by
      intro k
      rw [hq_def, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [tsum_congr hterm, tsum_congr (fun k : ℕ => pow_succ q k), tsum_mul_right,
      tsum_geometric_of_lt_one hq0 hq1]
  have hq_half : q ≤ 1 / 2 := by
    rw [hq_eq]
    nlinarith
  have hden : 0 < 1 - q := by linarith
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hden]
    linarith
  rw [hsum]
  calc
    (1 - q)⁻¹ * q ≤ 2 * q := mul_le_mul_of_nonneg_right hinv hq0
    _ = 2 * u ^ 2 := by rw [hq_eq]
    _ ≤ u := by nlinarith

private theorem summable_exp_neg_sq_succ :
    Summable fun n : ℕ => Real.exp (-(((n : ℝ) + 1) ^ 2)) := by
  have hgeom : Summable fun n : ℕ => Real.exp (-((n : ℝ) + 1)) := by
    have hq0 : (0 : ℝ) ≤ Real.exp (-1) := (Real.exp_pos _).le
    have hq1 : Real.exp (-1 : ℝ) < 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.2 (by norm_num : (-1 : ℝ) < 0)
    refine ((summable_geometric_of_lt_one hq0 hq1).mul_right (Real.exp (-1))).congr
      fun n => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeom
  refine Real.exp_le_exp.2 ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-! ## The graded threshold -/

/-- The `Γ₂` graded normalization of row `k`: the row scale times `λ √(k+1)`. -/
def sqrtGradedScale (lam : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  lam * Real.sqrt ((k : ℝ) + 1) * a k

private theorem one_le_sqrt_succ (k : ℕ) : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) + 1 by linarith)
  nlinarith [Real.sqrt_nonneg ((k : ℝ) + 1)]

theorem sqrtGradedScale_pos {lam : ℝ} {a : ℕ → ℝ} (hlam : 0 < lam)
    (ha : ∀ k, 0 < a k) (k : ℕ) : 0 < sqrtGradedScale lam a k := by
  have hs : (0 : ℝ) < Real.sqrt ((k : ℝ) + 1) :=
    lt_of_lt_of_le zero_lt_one (one_le_sqrt_succ k)
  exact mul_pos (mul_pos hlam hs) (ha k)

/-- The bad event in row `k` at threshold `t`. -/
def sqrtGradedRowEvent (I : ℕ → Finset ι) (X : ℕ → ι → Ω → ℝ) (a : ℕ → ℝ)
    (lam t : ℝ) (k : ℕ) : Set Ω :=
  ⋃ i ∈ I k, upperTailEvent (X k i) (sqrtGradedScale lam a k * t)

/-- The bad event in any row at threshold `t`. -/
def sqrtGradedAllRowsEvent (I : ℕ → Finset ι) (X : ℕ → ι → Ω → ℝ) (a : ℕ → ℝ)
    (lam t : ℝ) : Set Ω :=
  ⋃ k : ℕ, sqrtGradedRowEvent I X a lam t k

/-! ## The row and column estimates -/

private theorem rpow_two_eq_sq (u : ℝ) : u ^ (2 : ℝ) = u ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- One row: the raw union bound already beats the row entropy, with the
Gaussian threshold `λ √(k+1) t`. -/
theorem measureReal_sqrtGradedRowEvent_le [IsFiniteMeasure mu]
    (I : ℕ → Finset ι) (X : ℕ → ι → Ω → ℝ) (a : ℕ → ℝ)
    {growth lam t : ℝ} (hgrowth : 0 ≤ growth) (hlam : 1 ≤ lam)
    (hlam2 : growth + 2 ≤ lam ^ 2) (ht : 1 ≤ t)
    (hcard : ∀ k, ((I k).card : ℝ) ≤ Real.exp (growth * ((k : ℝ) + 1)))
    (hX : ∀ k, ∀ i ∈ I k, IsBigOWith mu (gammaSigma 2) (X k i) (a k)) (k : ℕ) :
    mu.real (sqrtGradedRowEvent I X a lam t k) ≤
      Real.exp (-(2 * ((k : ℝ) + 1) * t ^ 2)) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := one_le_sqrt_succ k
  have hs2 : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 :=
    Real.sq_sqrt (by linarith)
  have ht2 : (1 : ℝ) ≤ t ^ 2 := by nlinarith
  set u : ℝ := lam * Real.sqrt ((k : ℝ) + 1) * t with hu_def
  have hprod : (1 : ℝ) ≤ lam * Real.sqrt ((k : ℝ) + 1) := by
    simpa using mul_le_mul hlam hs1 zero_le_one (by linarith : (0 : ℝ) ≤ lam)
  have hu1 : 1 ≤ u := by
    rw [hu_def]
    simpa using mul_le_mul hprod ht zero_le_one (by linarith : (0 : ℝ) ≤
      lam * Real.sqrt ((k : ℝ) + 1))
  have hthr : sqrtGradedScale lam a k * t = a k * u := by
    rw [sqrtGradedScale, hu_def]; ring
  have hupow : u ^ (2 : ℝ) = lam ^ 2 * ((k : ℝ) + 1) * t ^ 2 := by
    rw [rpow_two_eq_sq, hu_def, mul_pow, mul_pow, hs2]
  have hraw := measureReal_biUnion_upperTailEvent_le (mu := mu) (I k)
    (X := X k) (A := a k) (sigma := 2) (t := u) hu1 (hX k)
  have hexp : Real.exp (growth * ((k : ℝ) + 1) - u ^ (2 : ℝ)) ≤
      Real.exp (-(2 * ((k : ℝ) + 1) * t ^ 2)) := by
    refine Real.exp_le_exp.2 ?_
    rw [hupow]
    have h1 : growth ≤ growth * t ^ 2 := by nlinarith
    have h2 : (growth + 2) * t ^ 2 ≤ lam ^ 2 * t ^ 2 := by nlinarith
    have h4 : growth - lam ^ 2 * t ^ 2 + 2 * t ^ 2 ≤ 0 := by nlinarith
    have h5 : ((k : ℝ) + 1) * (growth - lam ^ 2 * t ^ 2 + 2 * t ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) h4
    nlinarith [h5]
  calc
    mu.real (sqrtGradedRowEvent I X a lam t k) ≤
        ((I k).card : ℝ) * Real.exp (-(u ^ (2 : ℝ))) := by
      rw [sqrtGradedRowEvent, hthr]
      exact hraw
    _ ≤ Real.exp (growth * ((k : ℝ) + 1)) * Real.exp (-(u ^ (2 : ℝ))) :=
      mul_le_mul_of_nonneg_right (hcard k) (Real.exp_pos _).le
    _ = Real.exp (growth * ((k : ℝ) + 1) - u ^ (2 : ℝ)) := by
      rw [← Real.exp_add, sub_eq_add_neg]
    _ ≤ Real.exp (-(2 * ((k : ℝ) + 1) * t ^ 2)) := hexp

/-- All rows at once: the depth entropy is paid by the same Gaussian
threshold. -/
theorem measureReal_sqrtGradedAllRowsEvent_le [IsFiniteMeasure mu]
    (I : ℕ → Finset ι) (X : ℕ → ι → Ω → ℝ) (a : ℕ → ℝ)
    {growth lam t : ℝ} (hgrowth : 0 ≤ growth) (hlam : 1 ≤ lam)
    (hlam2 : growth + 2 ≤ lam ^ 2) (ht : 1 ≤ t)
    (hcard : ∀ k, ((I k).card : ℝ) ≤ Real.exp (growth * ((k : ℝ) + 1)))
    (hX : ∀ k, ∀ i ∈ I k, IsBigOWith mu (gammaSigma 2) (X k i) (a k)) :
    mu.real (sqrtGradedAllRowsEvent I X a lam t) ≤ Real.exp (-(t ^ 2)) := by
  have ht2 : (1 : ℝ) ≤ t ^ 2 := by nlinarith
  have hrow := measureReal_sqrtGradedRowEvent_le (mu := mu) I X a hgrowth hlam
    hlam2 ht hcard hX
  have hsummable := summable_exp_neg_two_mul_succ ht2
  have hmeasure : mu (sqrtGradedAllRowsEvent I X a lam t) ≤
      ENNReal.ofReal (∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * t ^ 2))) := by
    rw [sqrtGradedAllRowsEvent,
      ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) hsummable]
    refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k => ?_)
    rw [← ENNReal.ofReal_toReal (measure_ne_top mu
      (sqrtGradedRowEvent I X a lam t k))]
    exact ENNReal.ofReal_le_ofReal (hrow k)
  calc
    mu.real (sqrtGradedAllRowsEvent I X a lam t) ≤
        (ENNReal.ofReal
          (∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * t ^ 2)))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
    _ = ∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) * t ^ 2)) :=
      ENNReal.toReal_ofReal (tsum_nonneg fun k => (Real.exp_pos _).le)
    _ ≤ Real.exp (-(t ^ 2)) := tsum_exp_neg_two_mul_succ_le ht2

/-! ## The almost sure envelope -/

/-- The Borel–Cantelli step.  Almost surely some integer threshold is never
exceeded, in any row. -/
theorem ae_exists_notMem_sqrtGradedAllRowsEvent [IsFiniteMeasure mu]
    (I : ℕ → Finset ι) (X : ℕ → ι → Ω → ℝ) (a : ℕ → ℝ)
    {growth lam : ℝ} (hgrowth : 0 ≤ growth) (hlam : 1 ≤ lam)
    (hlam2 : growth + 2 ≤ lam ^ 2)
    (hcard : ∀ k, ((I k).card : ℝ) ≤ Real.exp (growth * ((k : ℝ) + 1)))
    (hX : ∀ k, ∀ i ∈ I k, IsBigOWith mu (gammaSigma 2) (X k i) (a k)) :
    ∀ᵐ omega ∂mu, ∃ n : ℕ,
      omega ∉ sqrtGradedAllRowsEvent I X a lam ((n : ℝ) + 1) := by
  set E : ℕ → Set Ω := fun n =>
    sqrtGradedAllRowsEvent I X a lam ((n : ℝ) + 1) with hE_def
  have hn1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := by
    intro n
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hEbound : ∀ n : ℕ,
      mu (E n) ≤ ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) ^ 2))) := by
    intro n
    have hreal := measureReal_sqrtGradedAllRowsEvent_le (mu := mu) I X a hgrowth
      hlam hlam2 (hn1 n) hcard hX
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top mu (E n))
      (Real.exp_pos _).le).2 hreal
  have htsum : (∑' n : ℕ, mu (E n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le)
      summable_exp_neg_sq_succ]
    exact ENNReal.ofReal_ne_top
  refine (MeasureTheory.ae_finite_setOf_mem (μ := mu) (s := E) htsum).mono ?_
  intro omega hfin
  by_contra hall
  push_neg at hall
  have huniv : {n : ℕ | omega ∈ E n} = Set.univ :=
    Set.eq_univ_of_forall fun n => hall n
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

/-- **The graded `Γ₂` envelope.**  Almost surely one finite random constant
dominates every entry of every row at the price `√(k+1) · a k`.

This is the `Γ₂` counterpart of `gradedFiniteEnvelope_spec`: the `Γ₁` device
would give the price `(k+1) · a k`. -/
theorem ae_exists_forall_le_sqrt_mul_of_isBigOWith_gammaTwo [IsFiniteMeasure mu]
    (I : ℕ → Finset ι) (X : ℕ → ι → Ω → ℝ) (a : ℕ → ℝ)
    {growth lam : ℝ} (hgrowth : 0 ≤ growth) (hlam : 1 ≤ lam)
    (hlam2 : growth + 2 ≤ lam ^ 2)
    (hcard : ∀ k, ((I k).card : ℝ) ≤ Real.exp (growth * ((k : ℝ) + 1)))
    (hX : ∀ k, ∀ i ∈ I k, IsBigOWith mu (gammaSigma 2) (X k i) (a k)) :
    ∀ᵐ omega ∂mu, ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ i ∈ I k,
      X k i omega ≤ C * (Real.sqrt ((k : ℝ) + 1) * a k) := by
  refine (ae_exists_notMem_sqrtGradedAllRowsEvent (mu := mu) I X a hgrowth hlam
    hlam2 hcard hX).mono ?_
  intro omega ⟨n, hn⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  refine ⟨lam * ((n : ℝ) + 1), by nlinarith, fun k i hi => ?_⟩
  have hnot : omega ∉ upperTailEvent (X k i)
      (sqrtGradedScale lam a k * ((n : ℝ) + 1)) := by
    intro hmem
    exact hn (Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hmem⟩⟩⟩)
  rw [mem_upperTailEvent, not_lt] at hnot
  refine hnot.trans_eq ?_
  rw [sqrtGradedScale]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
