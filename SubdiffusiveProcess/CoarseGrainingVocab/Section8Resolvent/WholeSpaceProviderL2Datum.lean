import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderL2Existence




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped BigOperators CompactlySupported

noncomputable section

variable {d : ℕ} {a : Vec d → ℝ}



theorem exists_wholeSpaceSolution_of_memLp
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) {t : ℝ} (ht : 0 < t)
    (hsolve : ∀ g : C_c(Vec d, ℝ),
      ∃ u : WholeSpaceDivergenceResolventSolution a t g,
        (∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, g x ^ 2 ∂volume) ∧
        (∫ x, a x * vecNormSq (u.grad x) ∂volume ≤
          2⁻¹ * t⁻¹ * ∫ x, g x ^ 2 ∂volume))
    (huniq : ∀ g : Vec d → ℝ, MemLp g 2 volume →
      ∀ u v : WholeSpaceDivergenceResolventSolution a t g,
        u.toFun =ᵐ[volume] v.toFun ∧ u.grad =ᵐ[volume] v.grad)
    {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    ∃ u : WholeSpaceDivergenceResolventSolution a t f,
      (∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
      (∫ x, a x * vecNormSq (u.grad x) ∂volume ≤
        2⁻¹ * t⁻¹ * ∫ x, f x ^ 2 ∂volume) := by
  classical
  have hnonneg : ∀ x, 0 ≤ a x := fun x ↦ (hpos x).le
  obtain ⟨fc, hfc⟩ := exists_compactSupport_l2_approx hf
  choose U hUL2 hUen using hsolve
  have hmemfc : ∀ n, MemLp ((fc n : Vec d → ℝ)) 2 volume := fun n ↦
    (fc n).continuous.memLp_of_hasCompactSupport (fc n).hasCompactSupport
  have hunMem : ∀ n, MemLp ((U (fc n)).toFun) 2 volume := fun n ↦
    (U (fc n)).memL2_toFun
  have hGnMem : ∀ n (i : Fin d),
      MemLp (fun x ↦ Real.sqrt (a x) * (U (fc n)).grad x i) 2 volume :=
    fun n i ↦ memLp_sqrt_mul_grad hcont hnonneg (U (fc n)) i
  -- The solution map is a contraction in both norms.
  have hdiff : ∀ n m : ℕ,
      (∫ x, ((U (fc n)).toFun x - (U (fc m)).toFun x) ^ 2 ∂volume ≤
        ∫ x, (fc n x - fc m x) ^ 2 ∂volume) ∧
      (∀ i : Fin d, ∫ x, (Real.sqrt (a x) * (U (fc n)).grad x i -
          Real.sqrt (a x) * (U (fc m)).grad x i) ^ 2 ∂volume ≤
        2⁻¹ * t⁻¹ * ∫ x, (fc n x - fc m x) ^ 2 ∂volume) := by
    intro n m
    set w := WholeSpaceDivergenceResolventSolution.sub hcont hpos
      (hmemfc n) (hmemfc m) (U (fc n)) (U (fc m)) with hw_def
    obtain ⟨hval, hgrad⟩ := huniq (fun x ↦ fc n x - fc m x)
      ((hmemfc n).sub (hmemfc m)) w (U (fc n - fc m))
    have hL2 : ∫ x, ((U (fc n)).toFun x - (U (fc m)).toFun x) ^ 2 ∂volume ≤
        ∫ x, (fc n x - fc m x) ^ 2 ∂volume := by
      have hEq : ∫ x, ((U (fc n)).toFun x - (U (fc m)).toFun x) ^ 2 ∂volume =
          ∫ x, (U (fc n - fc m)).toFun x ^ 2 ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards [hval] with x hx
        show (w.toFun x) ^ 2 = _
        rw [hx]
      rw [hEq]
      exact hUL2 (fc n - fc m)
    have hEn : ∫ x, a x * vecNormSq (w.grad x) ∂volume ≤
        2⁻¹ * t⁻¹ * ∫ x, (fc n x - fc m x) ^ 2 ∂volume := by
      have hEq : ∫ x, a x * vecNormSq (w.grad x) ∂volume =
          ∫ x, a x * vecNormSq ((U (fc n - fc m)).grad x) ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards [hgrad] with x hx
        rw [hx]
      rw [hEq]
      exact hUen (fc n - fc m)
    refine ⟨hL2, fun i ↦ ?_⟩
    have hptle : ∀ x, (Real.sqrt (a x) * (U (fc n)).grad x i -
        Real.sqrt (a x) * (U (fc m)).grad x i) ^ 2 ≤
        a x * vecNormSq (w.grad x) := by
      intro x
      have h1 : (Real.sqrt (a x) * (U (fc n)).grad x i -
          Real.sqrt (a x) * (U (fc m)).grad x i) ^ 2 =
          a x * ((U (fc n)).grad x i - (U (fc m)).grad x i) ^ 2 := by
        rw [← mul_sub, mul_pow, Real.sq_sqrt (hnonneg x)]
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ (hnonneg x)
      have h2 : vecNormSq (w.grad x) =
          ∑ j, ((U (fc n)).grad x j - (U (fc m)).grad x j) *
            ((U (fc n)).grad x j - (U (fc m)).grad x j) := rfl
      rw [h2, sq]
      exact Finset.single_le_sum
        (f := fun j ↦ ((U (fc n)).grad x j - (U (fc m)).grad x j) *
          ((U (fc n)).grad x j - (U (fc m)).grad x j))
        (fun j _ ↦ mul_self_nonneg _) (Finset.mem_univ i)
    refine le_trans (integral_mono ?_ w.integrable_energy hptle) hEn
    exact ((hGnMem n i).sub (hGnMem m i)).integrable_sq
  -- Cauchy for the data.
  have hdataCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      ∫ x, (fc n x - fc m x) ^ 2 ∂volume ≤ ε := by
    intro ε hε
    have hev : ∀ᶠ n in atTop, ∫ x, (f x - fc n x) ^ 2 ∂volume < ε / 4 :=
      hfc.eventually_lt_const (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn m hm ↦ ?_⟩
    have hbase := integral_sq_sub_le_two_mul_add (hmemfc n) (hmemfc m) hf
    have hsym : ∫ x, (fc n x - f x) ^ 2 ∂volume =
        ∫ x, (f x - fc n x) ^ 2 ∂volume := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      ring
    rw [hsym] at hbase
    have h1 := hN n hn
    have h2 := hN m hm
    linarith
  -- The two limits.
  obtain ⟨V, hVmem, hconvU⟩ := exists_l2_limit_of_cauchy hunMem (by
    intro ε hε
    obtain ⟨N, hN⟩ := hdataCauchy ε hε
    exact ⟨N, fun n hn m hm ↦ ((hdiff n m).1).trans (hN n hn m hm)⟩)
  have hgradLimits : ∀ i : Fin d, ∃ H : Vec d → ℝ, MemLp H 2 volume ∧
      Tendsto (fun n ↦ ∫ x,
        (Real.sqrt (a x) * (U (fc n)).grad x i - H x) ^ 2 ∂volume)
        atTop (𝓝 0) := by
    intro i
    refine exists_l2_limit_of_cauchy (fun n ↦ hGnMem n i) ?_
    intro ε hε
    have hscale : 0 < 2 * t * ε := by positivity
    obtain ⟨N, hN⟩ := hdataCauchy (2 * t * ε) hscale
    refine ⟨N, fun n hn m hm ↦ ?_⟩
    refine ((hdiff n m).2 i).trans ?_
    have hbound := hN n hn m hm
    have hcoef : (0 : ℝ) < 2⁻¹ * t⁻¹ := by positivity
    have hstep : 2⁻¹ * t⁻¹ * ∫ x, (fc n x - fc m x) ^ 2 ∂volume ≤
        2⁻¹ * t⁻¹ * (2 * t * ε) :=
      mul_le_mul_of_nonneg_left hbound hcoef.le
    refine hstep.trans (le_of_eq ?_)
    field_simp
  choose Gl hGlmem hconvG using hgradLimits
  -- Datum convergence with the sign the assembly expects.
  have hconvF : Tendsto (fun n ↦ ∫ x, (fc n x - f x) ^ 2 ∂volume)
      atTop (𝓝 0) := by
    have hsym : ∀ n, ∫ x, (fc n x - f x) ^ 2 ∂volume =
        ∫ x, (f x - fc n x) ^ 2 ∂volume := by
      intro n
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      ring
    simpa only [hsym] using hfc
  -- Assemble the limit carrier.
  obtain ⟨u, huV, huG⟩ :=
    exists_wholeSpaceSolution_of_l2_limits (a := a) (t := t) hcont hpos
      (fn := fun n ↦ (fc n : Vec d → ℝ))
      (un := fun n ↦ (U (fc n)).toFun)
      (Gn := fun n ↦ (U (fc n)).grad)
      hmemfc hunMem hGnMem hf hVmem hGlmem
      (fun n W hW i ↦
        hasWeakPartialDerivOn_of_wholeSpaceSolution (U (fc n)) hW i)
      (fun n W hW φ ↦ massive_identity_of_wholeSpaceSolution (U (fc n)) hW φ)
      hconvF hconvU hconvG
  refine ⟨u, ?_, ?_⟩
  · rw [huV]
    have hlimU : Tendsto (fun n ↦ ∫ x, (U (fc n)).toFun x ^ 2 ∂volume) atTop
        (𝓝 (∫ x, V x ^ 2 ∂volume)) :=
      tendsto_integral_sq_of_l2_tendsto hunMem hVmem hconvU
    have hlimF : Tendsto (fun n ↦ ∫ x, (fc n : Vec d → ℝ) x ^ 2 ∂volume) atTop
        (𝓝 (∫ x, f x ^ 2 ∂volume)) :=
      tendsto_integral_sq_of_l2_tendsto hmemfc hf hconvF
    exact le_of_tendsto_of_tendsto' hlimU hlimF fun n ↦ hUL2 (fc n)
  · have hsum : ∫ x, a x * vecNormSq (u.grad x) ∂volume =
        ∑ i, ∫ x, Gl i x ^ 2 ∂volume := by
      have hEq := integral_weighted_energy_eq_sum (a := a) hnonneg
        (g := u.grad)
        (fun i ↦ (memLp_sqrt_mul_grad hcont hnonneg u i).integrable_sq)
      rw [hEq]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      simp only [huG x i]
    have hsumN : ∀ n, ∫ x, a x * vecNormSq ((U (fc n)).grad x) ∂volume =
        ∑ i, ∫ x, (Real.sqrt (a x) * (U (fc n)).grad x i) ^ 2 ∂volume :=
      fun n ↦ integral_weighted_energy_eq_sum (a := a) hnonneg
        (fun i ↦ (hGnMem n i).integrable_sq)
    have hlimEn : Tendsto
        (fun n ↦ ∫ x, a x * vecNormSq ((U (fc n)).grad x) ∂volume) atTop
        (𝓝 (∑ i, ∫ x, Gl i x ^ 2 ∂volume)) := by
      simp only [hsumN]
      refine tendsto_finset_sum Finset.univ fun i _ ↦ ?_
      exact tendsto_integral_sq_of_l2_tendsto (fun n ↦ hGnMem n i)
        (hGlmem i) (hconvG i)
    have hlimF : Tendsto
        (fun n ↦ 2⁻¹ * t⁻¹ * ∫ x, (fc n : Vec d → ℝ) x ^ 2 ∂volume) atTop
        (𝓝 (2⁻¹ * t⁻¹ * ∫ x, f x ^ 2 ∂volume)) :=
      (tendsto_integral_sq_of_l2_tendsto hmemfc hf hconvF).const_mul _
    rw [hsum]
    exact le_of_tendsto_of_tendsto' hlimEn hlimF fun n ↦ hUen (fc n)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
