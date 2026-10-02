import SubdiffusiveProcess.Probability.OpNormAdditiveTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section
namespace Paper

/-- **Pathwise operator-norm convergence.** A sequence of symmetric bounded operators on a Hilbert
space whose unit-ball images lie in one compact set, and whose quadratic tests converge on a
dense set closed under addition, converges in operator norm. This is the existing
in-probability criterion applied on a one-point probability space. -/
theorem conv_represented_opNorm_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (G : ℕ → E →L[ℝ] E)
    (hsym : ∀ N (x y : E), ⟪G N x, y⟫_ℝ = ⟪x, G N y⟫_ℝ)
    (C : Set E) (hC : IsCompact C) (hCG : ∀ N (x : E), ‖x‖ ≤ 1 → G N x ∈ C)
    (D : Set E) (hDdense : Dense D) (hDadd : ∀ a ∈ D, ∀ b ∈ D, a + b ∈ D)
    (hquad : ∀ h ∈ D, ∃ q : ℝ, Tendsto (fun N => ⟪h, G N h⟫_ℝ) atTop (𝓝 q)) :
    ∃ L : E →L[ℝ] E, Tendsto G atTop (𝓝 L) := by
  classical
  let P : Measure Unit := Measure.dirac ()
  haveI : IsProbabilityMeasure P := inferInstance
  have hmain := SubdiffusiveProcess.Probability.opNorm_cauchy_in_probability_of_additive_dense_tests
    P (fun N _ => G N) (fun N _ x y => hsym N x y) (fun _ _ => 0)
    (fun rho hrho => ⟨0, fun N => by simp [P]⟩)
    (fun Mb => ⟨C, hC, fun N _ _ x hx => hCG N x hx⟩) D hDdense hDadd ?_
  · have hcs : CauchySeq G := by
      rw [Metric.cauchySeq_iff']
      intro eps heps
      obtain ⟨N0, hN0⟩ := hmain eps heps (1 / 2) (by norm_num)
      refine ⟨N0, fun N hN => ?_⟩
      by_contra hlt
      have hle : eps ≤ ‖G N - G N0‖ := by
        rw [not_lt, dist_eq_norm] at hlt
        exact hlt
      have h1 := hN0 N N0 hN le_rfl
      have hmem : (() : Unit) ∈ {ω : Unit | eps ≤ ‖G N - G N0‖} := hle
      have h2 : (1 : ENNReal) ≤ P {ω : Unit | eps ≤ ‖G N - G N0‖} := by
        have : P {ω : Unit | eps ≤ ‖G N - G N0‖} = 1 := by
          have hset : {ω : Unit | eps ≤ ‖G N - G N0‖} = Set.univ := by
            ext ω; cases ω; exact ⟨fun _ => trivial, fun _ => hle⟩
          rw [hset, measure_univ]
        rw [this]
      have h3 : (1 : ENNReal) ≤ ENNReal.ofReal (1 / 2) := h2.trans h1
      have h4 : ENNReal.ofReal (1 / 2 : ℝ) < 1 := by
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
      exact absurd h3 (not_le.2 h4)
    exact cauchySeq_tendsto_of_complete hcs
  · intro h hh eps heps rho hrho
    obtain ⟨q, hq⟩ := hquad h hh
    obtain ⟨N0, hN0⟩ := Metric.cauchySeq_iff'.1 hq.cauchySeq (eps / 2) (by positivity)
    refine ⟨N0, fun N N' hN hN' => ?_⟩
    have hsub : {ω : Unit | eps ≤ |⟪h, G N h⟫_ℝ - ⟪h, G N' h⟫_ℝ|} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have h1 := hN0 N hN
      have h2 := hN0 N' hN'
      rw [Real.dist_eq] at h1 h2
      rw [abs_lt] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    rw [hsub, measure_empty]
    exact zero_le _

end Paper
