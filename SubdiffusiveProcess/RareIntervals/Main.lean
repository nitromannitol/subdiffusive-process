module

public import SubdiffusiveProcess.RareIntervals.Prob
public import SubdiffusiveProcess.RareIntervals.Arith

@[expose] public section

/-!
# The rare-interval lemma for an abstract scheme

`measure_bad_le`: the number of `k ∈ [a, a+N-1]` for which some `E_{k,j}` occurs is `≥ θ N` with probability at most
`2 N e^{-λ N} + 2^{3N} e^{-λ θ N / 6}` (long intervals `j ≥ N` + greedy retention and entropy `2^{3N}`).
`rare_intervals_scheme` absorbs the two terms into `e^{-λ θ N / 24}` once `λ θ ≥ 100`.
-/

namespace SubdiffusiveProcess.RareIntervals

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

open Classical in
theorem measure_bad_le (S : Scheme) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℤ → MeasurableSpace Ω} (hind : iIndep m μ) (hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω))
    (E : ℤ → ℕ → Set Ω)
    (hE : ∀ k j, MeasurableSet[⨆ i ∈ Finset.Icc (S.lo k j) (S.hi k j), m i] (E k j))
    (lam : ℝ) (hP : ∀ k j, μ (E k j) ≤ ENNReal.ofReal (Real.exp (-(lam * ((j : ℝ) + 1)))))
    (hlam : 1 ≤ lam) (θ : ℝ) (a : ℤ) (N : ℕ) :
    μ {ω | θ * N ≤ ((Finset.Icc a (a + (N : ℤ) - 1)).filter (fun k => ∃ j : ℕ, ω ∈ E k j)).card} ≤
      ENNReal.ofReal (2 * N * Real.exp (-(lam * N))) +
        2 ^ (3 * N) * ENNReal.ofReal (Real.exp (-(lam * (θ * N / 6)))) := by
  set I : Finset ℤ := Finset.Icc a (a + (N : ℤ) - 1) with hI
  let wt : Finset (ℤ × ℕ) → ℤ := fun F => ∑ x ∈ F, (S.hi x.1 x.2 - S.lo x.1 x.2 + 1)
  let P : Finset (ℤ × ℕ) → Prop := fun F => θ * N / 3 ≤ (wt F : ℝ)
  set 𝓕 : Finset (Finset (ℤ × ℕ)) :=
    (I ×ˢ Finset.range N).powerset.filter (fun F => SepFam S F ∧ P F) with h𝓕
  have hsubset : {ω | θ * N ≤ (I.filter (fun k => ∃ j : ℕ, ω ∈ E k j)).card} ⊆
      (⋃ k ∈ I, ⋃ i : ℕ, E k (N + i)) ∪ ⋃ F ∈ 𝓕, ⋂ x ∈ F, E x.1 x.2 := by
    intro ω hω
    by_cases hlong : ω ∈ ⋃ k ∈ I, ⋃ i : ℕ, E k (N + i)
    · exact Or.inl hlong
    right
    set B : Finset ℤ := I.filter (fun k => ∃ j : ℕ, ω ∈ E k j) with hB
    have hωB : θ * N ≤ B.card := hω
    let jf : ℤ → ℕ := fun k => if h : ∃ j : ℕ, ω ∈ E k j then Classical.choose h else 0
    have hjf : ∀ k ∈ B, ω ∈ E k (jf k) := by
      intro k hk
      have h := (Finset.mem_filter.mp hk).2
      simp only [jf, dite_eq_left h]
      exact Classical.choose_spec h
    have hjfN : ∀ k ∈ B, jf k < N := by
      intro k hk
      by_contra hge
      push Not at hge
      apply hlong
      simp only [Set.mem_iUnion]
      refine ⟨k, (Finset.mem_filter.mp hk).1, jf k - N, ?_⟩
      have : N + (jf k - N) = jf k := by omega
      rw [this]
      exact hjf k hk
    obtain ⟨T, hTB, hTsep, hTcard⟩ := exists_separated_subfamily (fun k => S.lo k (jf k))
      (fun k => S.hi k (jf k)) (fun k => ⟨S.lo_le k (jf k), S.le_hi k (jf k)⟩) B
    set F : Finset (ℤ × ℕ) := T.image (fun t => (t, jf t)) with hF
    have hinjF : Function.Injective (fun t : ℤ => (t, jf t)) := fun s t h => (Prod.ext_iff.mp h).1
    have hFsub : F ⊆ I ×ˢ Finset.range N := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      have htB := hTB ht
      exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp htB).1, Finset.mem_range.mpr (hjfN t htB)⟩
    have hFsep : SepFam S F := by
      intro x hx y hy hxy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      have hst : s ≠ t := fun h => hxy (by rw [h])
      exact hTsep s hs t ht hst
    have hwt : wt F = ∑ t ∈ T, (S.hi t (jf t) - S.lo t (jf t) + 1) := by
      simp only [wt, hF]
      rw [Finset.sum_image (fun s _ t _ h => hinjF h)]
    have hP : P F := by
      show θ * N / 3 ≤ (wt F : ℝ)
      rw [hwt]
      have h1 : (B.card : ℝ) ≤ 3 * ((∑ t ∈ T, (S.hi t (jf t) - S.lo t (jf t) + 1) : ℤ) : ℝ) := by
        exact_mod_cast hTcard
      linarith
    refine Set.mem_iUnion₂.mpr ⟨F, ?_, ?_⟩
    · rw [h𝓕, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hFsub, hFsep, hP⟩
    · simp only [Set.mem_iInter]
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact hjf t (hTB ht)
  have hlong := measure_long_le E lam hlam hP a N
  have hcfg : ∀ F ∈ 𝓕, μ (⋂ x ∈ F, E x.1 x.2) ≤
      ENNReal.ofReal (Real.exp (-(lam * (θ * N / 6)))) := by
    intro F hF
    obtain ⟨hFsep, hFP⟩ := (Finset.mem_filter.mp hF).2
    refine (measure_config_le S hind hm E hE lam hP F hFsep).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hlen : ((wt F : ℤ) : ℝ) ≤ 2 * ∑ x ∈ F, ((x.2 : ℝ) + 1) := by
      have : wt F ≤ ∑ x ∈ F, (2 * ((x.2 : ℤ) + 1)) :=
        Finset.sum_le_sum (fun x _ => S.len_le x.1 x.2)
      have h2 : (((∑ x ∈ F, (2 * ((x.2 : ℤ) + 1))) : ℤ) : ℝ) = 2 * ∑ x ∈ F, ((x.2 : ℝ) + 1) := by
        push_cast
        rw [Finset.mul_sum]
      rw [← h2]
      exact_mod_cast this
    have hP' : θ * N / 3 ≤ (wt F : ℝ) := hFP
    have : θ * N / 6 ≤ ∑ x ∈ F, ((x.2 : ℝ) + 1) := by linarith
    nlinarith
  calc _ ≤ μ ((⋃ k ∈ I, ⋃ i : ℕ, E k (N + i)) ∪ ⋃ F ∈ 𝓕, ⋂ x ∈ F, E x.1 x.2) := measure_mono hsubset
    _ ≤ μ (⋃ k ∈ I, ⋃ i : ℕ, E k (N + i)) + μ (⋃ F ∈ 𝓕, ⋂ x ∈ F, E x.1 x.2) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * N * Real.exp (-(lam * N))) +
          ∑ F ∈ 𝓕, μ (⋂ x ∈ F, E x.1 x.2) := by
        gcongr
        exact measure_biUnion_finset_le _ _
    _ ≤ ENNReal.ofReal (2 * N * Real.exp (-(lam * N))) +
          ∑ F ∈ 𝓕, ENNReal.ofReal (Real.exp (-(lam * (θ * N / 6)))) := by
        gcongr with F hF
        exact hcfg F hF
    _ = ENNReal.ofReal (2 * N * Real.exp (-(lam * N))) +
          (𝓕.card : ENNReal) * ENNReal.ofReal (Real.exp (-(lam * (θ * N / 6)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        have := card_sepFam_le S a N P
        have h2 : 𝓕.card ≤ 2 ^ (3 * N) := this
        exact_mod_cast h2

/-- **Selection of rare intervals, abstract scheme version.** -/
theorem rare_intervals_scheme (S : Scheme) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℤ → MeasurableSpace Ω} (hind : iIndep m μ) (hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω))
    (E : ℤ → ℕ → Set Ω)
    (hE : ∀ k j, MeasurableSet[⨆ i ∈ Finset.Icc (S.lo k j) (S.hi k j), m i] (E k j))
    (lam : ℝ) (hP : ∀ k j, μ (E k j) ≤ ENNReal.ofReal (Real.exp (-(lam * ((j : ℝ) + 1)))))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 100 ≤ lam * θ) (a : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    open Classical in
    μ {ω | θ * N ≤ ((Finset.Icc a (a + (N : ℤ) - 1)).filter (fun k => ∃ j : ℕ, ω ∈ E k j)).card} ≤
      ENNReal.ofReal (Real.exp (-((1 / 24) * lam * θ * N))) := by
  have hlam : 1 ≤ lam := by nlinarith
  refine (measure_bad_le S hind hm E hE lam hP hlam θ a N).trans ?_
  have harith := rare_arith lam θ N hN hθ0 hθ1 hC
  have h1 : (2 : ENNReal) ^ (3 * N) = ENNReal.ofReal ((2 : ℝ) ^ (3 * N)) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [h1, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have : -((1 / 24) * lam * θ * N) = -(lam * θ * N / 24) := by ring
  rw [this]
  exact harith

end SubdiffusiveProcess.RareIntervals
