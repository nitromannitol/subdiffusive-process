module

public import SubdiffusiveProcess.FractionalEmbedding.DyadicAlgebra
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.FractionalEmbedding
variable {α : Type*} [MeasurableSpace α]

/-- Real upper-level masses; on a finite measure space these retain the full mass. -/
def levelMass (μ : Measure α) (f : α → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  (μ {x | levelScale t k < f x}).toReal

/-- The bounded dyadic truncation moment, with its nonnegative integral retained. -/
def truncatedMoment (μ : Measure α) (f : α → ℝ) (t q : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((min (f x) (levelScale t (N + 1))) ^ q) ∂μ

theorem levelMass_nonneg (μ : Measure α) (f : α → ℝ) (t : ℝ) (k : ℕ) :
    0 ≤ levelMass μ f t k := by
  exact ENNReal.toReal_nonneg

theorem levelMass_step (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    levelMass μ f t (k + 1) ≤ levelMass μ f t k := by
  unfold levelMass
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono
  intro x hx
  change levelScale t (k + 1) < f x at hx
  change levelScale t k < f x
  rw [levelScale_succ] at hx
  have hp := levelScale_pos ht k
  linarith

theorem levelMass_le_univ (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (t : ℝ) (k : ℕ) : levelMass μ f t k ≤ (μ Set.univ).toReal := by
  unfold levelMass
  exact ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _))

/-- Markov's bound written in real squared moments. -/
theorem squared_tail_bound (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    (hf : Measurable f) {t : ℝ} (ht : 0 < t)
    (hfinite : (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ) < ⊤) :
    t ^ 2 * (μ {x | t < f x}).toReal ≤
      (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ).toReal := by
  have hset : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hf
  have hle : ENNReal.ofReal (t ^ 2) * μ {x | t < f x} ≤
      ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
    calc
      _ = ∫⁻ x, {x | t < f x}.indicator (fun _ => ENNReal.ofReal (t ^ 2)) x ∂μ :=
        (lintegral_indicator_const hset _).symm
      _ ≤ _ := by
        apply lintegral_mono
        intro x
        by_cases hx : t < f x
        · rw [Set.indicator_of_mem (show x ∈ {x | t < f x} from hx)]
          exact ENNReal.ofReal_le_ofReal (by nlinarith)
        · rw [Set.indicator_of_notMem (show x ∉ {x | t < f x} from hx)]
          exact bot_le
  have h := ENNReal.toReal_mono hfinite.ne hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg t)] at h

theorem truncatedMoment_lt_top (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) {t q : ℝ} (ht : 0 < t) (hq : 0 < q)
    (hf0 : ∀ x, 0 ≤ f x) (N : ℕ) : truncatedMoment μ f t q N < ⊤ := by
  unfold truncatedMoment
  have hle : (∫⁻ x, ENNReal.ofReal ((min (f x) (levelScale t (N + 1))) ^ q) ∂μ) ≤
      ENNReal.ofReal ((levelScale t (N + 1)) ^ q) * μ Set.univ := by
    rw [← lintegral_const]
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (le_min (hf0 x) (levelScale_pos ht _).le)
      (min_le_right _ _) hq.le
  exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ))

/-- Integrating the finite dyadic pointwise bound. -/
theorem truncatedMoment_le_levels (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) {t q : ℝ} (ht : 0 < t) (hq : 0 < q)
    (hf0 : ∀ x, 0 ≤ f x) (N : ℕ) :
    (truncatedMoment μ f t q N).toReal ≤ t ^ q * (μ Set.univ).toReal +
      ∑ k ∈ Finset.range (N + 1), (levelScale t (k + 1)) ^ q * levelMass μ f t k := by
  classical
  let F : ℕ → α → ℝ≥0∞ := fun k x =>
    if levelScale t k < f x then ENNReal.ofReal ((levelScale t (k + 1)) ^ q) else 0
  have hF (k : ℕ) : Measurable (F k) :=
    Measurable.ite (measurableSet_lt measurable_const hf) measurable_const measurable_const
  have hFn (k : ℕ) : ∫⁻ x, F k x ∂μ =
      ENNReal.ofReal ((levelScale t (k + 1)) ^ q) * μ {x | levelScale t k < f x} := by
    have hset : MeasurableSet {x | levelScale t k < f x} := measurableSet_lt measurable_const hf
    simpa only [F, Set.indicator, Set.mem_setOf_eq] using lintegral_indicator_const hset
      (ENNReal.ofReal ((levelScale t (k + 1)) ^ q))
  have htq : 0 ≤ t ^ q := Real.rpow_nonneg ht.le _
  have hw (k : ℕ) : 0 ≤ (levelScale t (k + 1)) ^ q := Real.rpow_nonneg (levelScale_pos ht _).le _
  have hpoint (x : α) :
      ENNReal.ofReal ((min (f x) (levelScale t (N + 1))) ^ q) ≤
        ENNReal.ofReal (t ^ q) + ∑ k ∈ Finset.range (N + 1), F k x := by
    have hn (k : ℕ) : 0 ≤
        (if levelScale t k < f x then (levelScale t (k + 1)) ^ q else 0) := by
      split_ifs
      · exact hw k
      · exact le_rfl
    have h := ENNReal.ofReal_le_ofReal (truncated_rpow_le_dyadic t (f x) q ht (hf0 x) hq.le N)
    rw [ENNReal.ofReal_add htq (Finset.sum_nonneg fun k _ => hn k),
      ENNReal.ofReal_sum_of_nonneg (fun k _ => hn k)] at h
    convert h using 1
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [F]
    split_ifs <;> simp only [ENNReal.ofReal_zero]
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (N + 1),
      (levelScale t (k + 1)) ^ q * levelMass μ f t k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (levelMass_nonneg μ f t k)
  have hR : ENNReal.ofReal (t ^ q * (μ Set.univ).toReal +
        ∑ k ∈ Finset.range (N + 1), (levelScale t (k + 1)) ^ q * levelMass μ f t k) =
      ENNReal.ofReal (t ^ q) * μ Set.univ +
        ∑ k ∈ Finset.range (N + 1),
          ENNReal.ofReal ((levelScale t (k + 1)) ^ q) * μ {x | levelScale t k < f x} := by
    rw [ENNReal.ofReal_add (mul_nonneg htq ENNReal.toReal_nonneg) hsum0,
      ENNReal.ofReal_mul htq, ENNReal.ofReal_toReal (measure_ne_top μ Set.univ),
      ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hw k) (levelMass_nonneg μ f t k))]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [ENNReal.ofReal_mul (hw k)]
    exact congrArg (ENNReal.ofReal ((levelScale t (k + 1)) ^ q) * ·)
      (ENNReal.ofReal_toReal (measure_ne_top μ _))
  have hle : truncatedMoment μ f t q N ≤ ENNReal.ofReal
      (t ^ q * (μ Set.univ).toReal + ∑ k ∈ Finset.range (N + 1),
        (levelScale t (k + 1)) ^ q * levelMass μ f t k) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (t ^ q) + ∑ k ∈ Finset.range (N + 1), F k x ∂μ :=
        lintegral_mono hpoint
      _ = ENNReal.ofReal (t ^ q) * μ Set.univ + ∑ k ∈ Finset.range (N + 1), ∫⁻ x, F k x ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_finset_sum _ (fun k _ => hF k)]
      _ = _ := by simp_rw [hFn]; exact hR.symm
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (add_nonneg (mul_nonneg htq ENNReal.toReal_nonneg) hsum0)] at h

/-- The dyadic cutoffs eventually dominate any real amplitude. -/
theorem levelScale_unbounded {t : ℝ} (ht : 0 < t) (a : ℝ) :
    ∃ N : ℕ, a ≤ levelScale t (N + 1) := by
  have hlinear : ∀ n : ℕ, (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨N, hN⟩ := exists_nat_gt (a / t)
  refine ⟨N, ?_⟩
  have ha : a < (N : ℝ) * t := (div_lt_iff₀ ht).mp hN
  have hp : (N : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
    have h := hlinear (N + 1)
    push_cast at h
    linarith
  have h := mul_le_mul_of_nonneg_left hp ht.le
  unfold levelScale
  linarith

/-- Uniform moment estimates on the bounded truncations pass to the full moment. -/
theorem fullMoment_from_truncations (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {t q β B : ℝ} (ht : 0 < t) (hq : 0 < q) (hβ : 0 < β) (hB : 0 ≤ B)
    (hbound : ∀ N, (truncatedMoment μ f t q N).toReal ^ β ≤ B) :
    (∫⁻ x, ENNReal.ofReal ((f x) ^ q) ∂μ) < ⊤ ∧
      (∫⁻ x, ENNReal.ofReal ((f x) ^ q) ∂μ).toReal ^ β ≤ B := by
  let F : ℕ → α → ℝ≥0∞ := fun N x =>
    ENNReal.ofReal ((min (f x) (levelScale t (N + 1))) ^ q)
  have hF (N : ℕ) : Measurable (F N) :=
    ((hf.min measurable_const).pow_const q).ennreal_ofReal
  have hmono : Monotone F := by
    intro N M hNM x
    dsimp only [F]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (le_min (hf0 x) (levelScale_pos ht _).le) _ hq.le
    apply min_le_min_left
    unfold levelScale
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) ht.le
  have hsup (x : α) : (⨆ N, F N x) = ENNReal.ofReal ((f x) ^ q) := by
    apply le_antisymm
    · refine iSup_le fun N => ENNReal.ofReal_le_ofReal ?_
      exact Real.rpow_le_rpow (le_min (hf0 x) (levelScale_pos ht _).le)
        (min_le_left _ _) hq.le
    · obtain ⟨N, hN⟩ := levelScale_unbounded ht (f x)
      apply le_iSup_of_le N
      dsimp only [F]
      rw [min_eq_left hN]
  have hraw : (∫⁻ x, ENNReal.ofReal ((f x) ^ q) ∂μ) =
      ⨆ N, truncatedMoment μ f t q N := by
    simp only [truncatedMoment]
    rw [← lintegral_iSup hF hmono]
    apply lintegral_congr
    intro x
    exact (hsup x).symm
  have hNbound (N : ℕ) : (truncatedMoment μ f t q N) ^ β ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal (truncatedMoment_lt_top μ f ht hq hf0 N).ne,
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hβ.le]
    exact ENNReal.ofReal_le_ofReal (hbound N)
  have hpow : (∫⁻ x, ENNReal.ofReal ((f x) ^ q) ∂μ) ^ β ≤ ENNReal.ofReal B := by
    rw [hraw]
    have hmap : (⨆ N, truncatedMoment μ f t q N) ^ β =
        ⨆ N, (truncatedMoment μ f t q N) ^ β :=
      (ENNReal.orderIsoRpow β hβ).map_iSup _
    rw [hmap]
    exact iSup_le hNbound
  refine ⟨(ENNReal.rpow_lt_top_iff_of_pos hβ).mp (hpow.trans_lt ENNReal.ofReal_lt_top), ?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpow
  rwa [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hB] at h

end SubdiffusiveProcess.FractionalEmbedding
