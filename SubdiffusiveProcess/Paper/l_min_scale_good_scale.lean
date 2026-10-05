module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.GoodStoppingClause
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GoodStoppingDepthTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GoodStopping
public import SubdiffusiveProcess.Section6.DensityOfGoodScales

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Paper

/-- Measurable form of the stopping witness of
`Section6CutoffRegularity.exists_stopping_witness_ogammaLE_of_le`: the same
construction (depth replaced by its measurable envelope), remembering that the
produced index is itself measurable. -/
private theorem aux_l_min_scale_good_scale_witness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (J : Ω → ℤ) (hJ : ∀ ω, J ω ∈ Set.Icc (-1 : ℤ) m)
    {K r A : ℝ} (hK : 1 ≤ K) (hr : 0 < r)
    (hA : depthGammaOneScaleSharp K r ≤ A)
    (htail : ∀ q : ℕ, 0 < q →
      μ.real {ω | q < ((m : ℤ) - J ω).toNat} ≤ K * Real.exp (-(r * (q : ℝ)))) :
    ∃ X : Ω → ℤ, Measurable X ∧ (∀ ω, X ω ∈ Set.Icc (-1 : ℤ) m) ∧
      (∀ ω, X ω ≤ J ω) ∧
      SubdiffusiveProcess.OGammaLE μ 1 A (fun ω => max ((((m : ℤ) - X ω).toNat : ℝ) - 1) 0) := by
  set D : Ω → ℕ := envelopedDepth μ m J with hDdef
  have hDmeas : Measurable D := measurable_envelopedDepth μ m J
  have hdepth : (fun ω => max ((((m : ℤ) -
      ((m : ℤ) - (D ω : ℤ))).toNat : ℝ) - 1) 0) = depthObservable D := by
    funext ω
    have hsimp : (m : ℤ) - ((m : ℤ) - (D ω : ℤ)) = (D ω : ℤ) := by ring
    rw [hsimp, Int.toNat_natCast]
    rfl
  have hXmeas : Measurable (fun ω => (m : ℤ) - (D ω : ℤ)) :=
    measurable_const.sub
      ((measurable_from_top : Measurable (fun n : ℕ => (n : ℤ))).comp hDmeas)
  refine ⟨fun ω => (m : ℤ) - (D ω : ℤ), hXmeas, ?_, ?_, ?_⟩
  · intro ω
    show (m : ℤ) - (D ω : ℤ) ∈ Set.Icc (-1 : ℤ) (m : ℤ)
    have hle : D ω ≤ m + 1 := envelopedDepth_le_succ μ m J ω
    have hcast : (D ω : ℤ) ≤ (m : ℤ) + 1 := by exact_mod_cast hle
    have hnonneg : (0 : ℤ) ≤ (D ω : ℤ) := Int.natCast_nonneg _
    exact Set.mem_Icc.2 ⟨by omega, by omega⟩
  · intro ω
    show (m : ℤ) - (D ω : ℤ) ≤ J ω
    have hdom : stoppingDepth m J ω ≤ D ω := stoppingDepth_le_envelopedDepth hJ ω
    have hcast : (stoppingDepth m J ω : ℤ) ≤ (D ω : ℤ) := by exact_mod_cast hdom
    rw [cast_stoppingDepth hJ ω] at hcast
    omega
  · rw [hdepth]
    have hsharp := ogammaLE_one_depthObservable_sharp (μ := μ) hDmeas hK hr (by
      intro q hq
      exact (measureReal_envelopedDepth_tail_le m J q).trans (htail q hq))
    exact ogammaLE_mono_scale zero_lt_one (depthGammaOneScaleSharp_pos hK hr) hA
      (measurable_depthObservable hDmeas) hsharp

/-- The parameter arithmetic of the tail-to-`O_{Γ_1}` step, over plain reals. -/
private theorem aux_l_min_scale_good_scale_arith
    {C0 B s eps lam DD : ℝ}
    (hC0 : 0 < C0) (hB : 0 < B) (hs : 0 < s) (heps : 0 < eps)
    (hlam : 0 < lam) (hDD : 0 < DD)
    (hkey : C0 * (16 * (1 + Real.log 2) + 4 * B + 2) *
        ((s ^ 6)⁻¹ * (eps⁻¹ ^ 2 * DD)) ≤ lam) :
    C0 * ((s ^ 6)⁻¹ * (eps⁻¹ ^ 2 * DD)) ≤ lam / 2 ∧
    B ≤ (s ^ 6 * eps ^ 2 * (lam / 2) / (C0 * DD)) / 2 ∧
    4 * ((1 + Real.log 2) /
        ((s ^ 6 * eps ^ 2 * (lam / 2) / (C0 * DD)) / 2)) =
      16 * (1 + Real.log 2) * C0 * ((s ^ 6)⁻¹ * (eps⁻¹ ^ 2 * DD)) * lam⁻¹ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs6 : (0 : ℝ) < s ^ 6 := pow_pos hs 6
  have heps2 : (0 : ℝ) < eps ^ 2 := pow_pos heps 2
  have hepsinv : (0 : ℝ) < eps⁻¹ ^ 2 := pow_pos (inv_pos.mpr heps) 2
  set P : ℝ := (s ^ 6)⁻¹ * (eps⁻¹ ^ 2 * DD) with hPdef
  have hP : 0 < P := by
    rw [hPdef]
    exact mul_pos (inv_pos.mpr hs6) (mul_pos hepsinv hDD)
  have hPid : P * (s ^ 6 * eps ^ 2) = DD := by
    rw [hPdef]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hP, hC0, hB, hlog2, hkey]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2),
      le_div_iff₀ (mul_pos hC0 hDD)]
    have hscaled := mul_le_mul_of_nonneg_right hkey
      (mul_pos hs6 heps2).le
    rw [mul_assoc, hPid] at hscaled
    have hcoeff : C0 * (4 * B) ≤ C0 * (16 * (1 + Real.log 2) + 4 * B + 2) := by
      nlinarith [hC0, hlog2]
    have hexpand : C0 * (4 * B) * DD ≤
        C0 * (16 * (1 + Real.log 2) + 4 * B + 2) * DD :=
      mul_le_mul_of_nonneg_right hcoeff hDD.le
    nlinarith [hexpand, hscaled]
  · rw [hPdef]
    field_simp
    ring

/-- `O_{Γ_1}` control of `X` is the same as control of its positive part. -/
private theorem aux_l_min_scale_good_scale_ogamma_congr
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : ℝ)
    {f g : Ω → ℝ} (h : ∀ ω, max (f ω) 0 = max (g ω) 0)
    (hf : SubdiffusiveProcess.OGammaLE μ 1 A f) : SubdiffusiveProcess.OGammaLE μ 1 A g := by
  have hfun : (fun ω => Real.exp ((A⁻¹ * max (g ω) 0) ^ (1 : ℝ))) =
      fun ω => Real.exp ((A⁻¹ * max (f ω) 0) ^ (1 : ℝ)) := by
    funext ω
    rw [h ω]
  unfold SubdiffusiveProcess.OGammaLE at hf ⊢
  rw [hfun]
  exact hf

/-- **Lemma `l.min.scale.good.scale`** :
there is a random index `N(λ,ε,s,m) ∈ {-1,…,m}` with `0 ≤ m - N ≤ 1 + O_{Γ_1}(·)`,
such that every `n ≤ N` has, at every triadic centre `z ∈ 3^n ℤ^d ∩ 𝒞_m`, more
than `(1-λ)(m-n)` good scales `j ∈ [n,m]` (equivalently fewer than
`1 + λ(m-n)` bad ones). -/
theorem l_min_scale_good_scale (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ lambda epsilon s : ℝ,
      lambda ∈ Set.Ioc (0 : ℝ) 1 → epsilon ∈ Set.Ioc (0 : ℝ) 1 →
      s ∈ Set.Ioc (0 : ℝ) 1 →
      C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 * |Real.log M.delta| ≤ lambda →
      ∀ m : ℕ, ∃ N : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℤ,
        Measurable N ∧
        (∀ ω, N ω ∈ Set.Icc (-1 : ℤ) m) ∧
        SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
          (C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ * M.delta ^ 2 *
            |Real.log M.delta|)
          (fun ω => (m : ℝ) - (N ω : ℝ) - 1) ∧
        ∀ ω, ∀ n : ℕ, (n : ℤ) ≤ N ω →
          (∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
            (1 - lambda) * ((m : ℝ) - (n : ℝ)) <
              ∑ j ∈ Finset.Icc n m,
                if ω ∈ goodEvent M none j z epsilon s then (1 : ℝ) else 0) ∧
          (∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
            ∑ j ∈ Finset.Icc n m,
                (1 - if ω ∈ goodEvent M none j z epsilon s then (1 : ℝ) else 0) <
              1 + lambda * ((m : ℝ) - (n : ℝ))) := by
  have hDensity : Section6Stopping.DensityOfGoodScalesInput d :=
    _root_.SubdiffusiveProcess.Section6.density_of_good_scales d
  obtain ⟨C0, hC0, hStoppingTail⟩ :=
    Section6Stopping.measure_goodStoppingDepth_tail_le_sum_exp hDensity
  have hB : 0 < entropyBudget d := entropyBudget_pos d
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C0 * (16 * (1 + Real.log 2) + 4 * entropyBudget d + 2), by positivity, ?_⟩
  set C : ℝ := C0 * (16 * (1 + Real.log 2) + 4 * entropyBudget d + 2) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  intro M lambda epsilon s hlambda hepsilon hs hlam2 m
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨he0, he1⟩ := hepsilon
  obtain ⟨hl0, hl1⟩ := hlambda
  have hd0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hdhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hlogneg : Real.log M.delta < 0 :=
    Real.log_neg hd0 (hdhalf.trans_lt (by norm_num))
  have hlogpos : 0 < |Real.log M.delta| := abs_pos.mpr hlogneg.ne
  set DD : ℝ := M.delta ^ 2 * |Real.log M.delta| with hDDdef
  have hDD : 0 < DD := by
    rw [hDDdef]
    exact mul_pos (pow_pos hd0 2) hlogpos
  have hz6 : s ^ (-6 : ℤ) = (s ^ (6 : ℕ))⁻¹ := by
    rw [show (-6 : ℤ) = -(6 : ℕ) by norm_num, zpow_neg, zpow_natCast]
  have hz8 : s ^ (-8 : ℤ) = (s ^ (8 : ℕ))⁻¹ := by
    rw [show (-8 : ℤ) = -(8 : ℕ) by norm_num, zpow_neg, zpow_natCast]
  have hs68 : (s ^ (6 : ℕ))⁻¹ ≤ (s ^ (8 : ℕ))⁻¹ := by
    have h68 : s ^ (8 : ℕ) ≤ s ^ (6 : ℕ) :=
      pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
    simpa [one_div] using one_div_le_one_div_of_le (pow_pos hs0 8) h68
  have hPpos : (0 : ℝ) < (s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD) :=
    mul_pos (inv_pos.mpr (pow_pos hs0 6))
      (mul_pos (pow_pos (inv_pos.mpr he0) 2) hDD)
  have hkey : C * ((s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) ≤ lambda := by
    refine le_trans ?_ hlam2
    have hmono : C * ((s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) ≤
        C * ((s ^ (8 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hs68 (by positivity)) hCpos.le
    refine hmono.trans_eq ?_
    rw [hz8, hDDdef]; ring
  obtain ⟨harith1, harith2, harith3⟩ :=
    aux_l_min_scale_good_scale_arith (C0 := C0) (B := entropyBudget d) (s := s)
      (eps := epsilon) (lam := lambda) (DD := DD) hC0 hB hs0 he0 hl0 hDD
      (by rw [hCdef] at hkey; exact hkey)
  have hsmall : C0 * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
      |Real.log M.delta| ≤ lambda / 2 := by
    refine le_trans (le_of_eq ?_) harith1
    rw [hz6, hDDdef]; ring
  set rate : ℝ := s ^ 6 * epsilon ^ 2 * (lambda / 2) /
    (C0 * M.delta ^ 2 * |Real.log M.delta|) with hratedef
  have hratepos : 0 < rate := by
    rw [hratedef]
    refine div_pos (mul_pos (mul_pos (pow_pos hs0 6) (pow_pos he0 2))
      (by linarith)) ?_
    exact mul_pos (mul_pos hC0 (pow_pos hd0 2)) hlogpos
  have hrateDD : rate = s ^ 6 * epsilon ^ 2 * (lambda / 2) / (C0 * DD) := by
    rw [hratedef, hDDdef]
    ring
  have hentropy : entropyBudget d ≤ rate / 2 := by rw [hrateDD]; exact harith2
  -- the literal first-failure index of the paper, and its depth tail
  set Jstop : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℤ :=
    fun omega => (goodStoppingIndex M none lambda epsilon s m omega : ℤ)
    with hJstopdef
  have hJ : ∀ omega, Jstop omega ∈ Set.Icc (-1 : ℤ) (m : ℤ) := fun omega =>
    (goodStoppingIndex M none lambda epsilon s m omega).property
  have htail : ∀ q : ℕ, 0 < q →
      M.P.toMeasure.real {omega | q < ((m : ℤ) - Jstop omega).toNat} ≤
        2 * Real.exp (-(rate / 2 * (q : ℝ))) := by
    intro q _hq
    have hset : {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d |
          q < ((m : ℤ) - Jstop omega).toNat} =
        {omega | q < Section6Stopping.goodStoppingDepth M lambda epsilon s m omega} :=
      rfl
    by_cases hqm : q ≤ m
    · have hE := hStoppingTail M s lambda epsilon ⟨hs0, hs1⟩ ⟨hl0, hl1⟩
        ⟨he0, he1⟩ hsmall q m
      have hfin : ∀ n ∈ Finset.range (m - q + 1),
          ((3 ^ (d * (m - n)) : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1))) ≠ ⊤ :=
        fun n _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          ENNReal.ofReal_ne_top
      have hsum_ne_top :
          (∑ n ∈ Finset.range (m - q + 1),
            ((3 ^ (d * (m - n)) : ℕ) : ℝ≥0∞) *
              ENNReal.ofReal (Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1))))
            ≠ ⊤ := ENNReal.sum_ne_top.2 hfin
      have hreal := ENNReal.toReal_mono hsum_ne_top hE
      rw [ENNReal.toReal_sum hfin] at hreal
      have hterms : ∀ n ∈ Finset.range (m - q + 1),
          (((3 ^ (d * (m - n)) : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1)))).toReal =
            ((3 ^ (d * (m - n)) : ℕ) : ℝ) *
              Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1)) := by
        intro n _
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
          ENNReal.toReal_ofReal (Real.exp_pos _).le]
      rw [Finset.sum_congr rfl hterms] at hreal
      rw [hset]
      exact hreal.trans (sum_entropy_exp_le hqm hratepos hentropy)
    · have hempty : {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d |
          q < ((m : ℤ) - Jstop omega).toNat} = ∅ := by
        ext omega
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_lt]
        have h := (hJ omega).1
        omega
      rw [hempty, measureReal_empty]
      positivity
  have hscale : depthGammaOneScaleSharp 2 (rate / 2) ≤
      C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ * M.delta ^ 2 *
        |Real.log M.delta| := by
    have hsharp : depthGammaOneScaleSharp 2 (rate / 2) =
        16 * (1 + Real.log 2) * C0 *
          ((s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) * lambda⁻¹ := by
      rw [depthGammaOneScaleSharp, depthTailScaleSharp, hrateDD]
      simpa using harith3
    rw [hsharp]
    have hlinv : (0 : ℝ) < lambda⁻¹ := inv_pos.mpr hl0
    have h16 : 16 * (1 + Real.log 2) * C0 ≤ C := by
      rw [hCdef]; nlinarith [hC0.le, hB.le, hlog2.le]
    have hstep : 16 * (1 + Real.log 2) * C0 *
        ((s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) ≤
        C * ((s ^ (8 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) := by
      refine (mul_le_mul_of_nonneg_right h16 hPpos.le).trans ?_
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hs68 (by positivity)) hCpos.le
    calc 16 * (1 + Real.log 2) * C0 *
          ((s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) * lambda⁻¹
        ≤ C * ((s ^ (8 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) * lambda⁻¹ :=
          mul_le_mul_of_nonneg_right hstep hlinv.le
      _ = C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ * M.delta ^ 2 *
            |Real.log M.delta| := by rw [hz8, hDDdef]; ring
  obtain ⟨X, hXmeas, hrange, hdom, hog⟩ :=
    aux_l_min_scale_good_scale_witness (μ := M.P.toMeasure) m Jstop hJ
      (by norm_num : (1 : ℝ) ≤ 2) (by positivity : (0 : ℝ) < rate / 2)
      hscale htail
  refine ⟨X, hXmeas, hrange, ?_, ?_⟩
  · refine aux_l_min_scale_good_scale_ogamma_congr M.P.toMeasure _ ?_ hog
    intro ω
    have h0 : 0 ≤ (m : ℤ) - X ω := by have := (hrange ω).2; omega
    have hcast : (((m : ℤ) - X ω).toNat : ℝ) = (m : ℝ) - (X ω : ℝ) := by
      have h := Int.toNat_of_nonneg h0
      have h' : ((((m : ℤ) - X ω).toNat : ℕ) : ℝ) = (((m : ℤ) - X ω : ℤ) : ℝ) := by
        exact_mod_cast h
      rw [h']
      push_cast
      ring
    simp only [hcast]
    rw [max_assoc, max_self]
  · intro ω n hn
    have hbad : ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
        ∑ j ∈ Finset.Icc n m,
            (1 - if ω ∈ goodEvent M none j z epsilon s then (1 : ℝ) else 0) <
          1 + lambda * ((m : ℝ) - (n : ℝ)) := by
      intro z hzgrid hzmem
      exact Section6Stopping.badScaleCount_lt_of_le_goodStoppingIndex
        M none lambda epsilon s m n ω (hn.trans (hdom ω)) z hzgrid hzmem
    refine ⟨?_, hbad⟩
    intro z hzgrid hzmem
    have hlt := hbad z hzgrid hzmem
    have hnm : n ≤ m := by
      have := (hrange ω).2
      omega
    have hcount : ((Finset.Icc n m).card : ℝ) = (m : ℝ) - (n : ℝ) + 1 := by
      rw [Nat.card_Icc, Nat.cast_sub (by omega : n ≤ m + 1), Nat.cast_add]
      norm_num
      ring
    have hsplit : ∑ j ∈ Finset.Icc n m,
        (1 - if ω ∈ goodEvent M none j z epsilon s then (1 : ℝ) else 0) =
        ((m : ℝ) - (n : ℝ) + 1) -
          ∑ j ∈ Finset.Icc n m,
            if ω ∈ goodEvent M none j z epsilon s then (1 : ℝ) else 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcount, mul_one]
    rw [hsplit] at hlt
    linarith

end SubdiffusiveProcess.Paper
