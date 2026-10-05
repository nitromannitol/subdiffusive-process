module

public import SubdiffusiveProcess.Probability.OpNormCauchyInProbability

@[expose] public section

/-!
# Dense additive test families for convergence of random operators

The quadratic tests need only be closed under addition. Passing to differences of tests
recovers the addition-and-subtraction hypothesis of the existing compact-operator criterion.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace SubdiffusiveProcess.Probability

/-- Operator-norm Cauchy convergence in probability from quadratic tests on a dense set
closed under addition. No closure under subtraction is required. -/
theorem opNorm_cauchy_in_probability_of_additive_dense_tests
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (G : ℕ → Ω → E →L[ℝ] E)
    (hsym : ∀ N ω (x y : E), ⟪G N ω x, y⟫_ℝ = ⟪x, G N ω y⟫_ℝ)
    (Kc : ℕ → Ω → ℝ)
    (htight : ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
      P {ω | Mb < Kc N ω} ≤ ENNReal.ofReal rho)
    (hcomp : ∀ Mb : ℝ, ∃ C : Set E, IsCompact C ∧
      ∀ N ω, Kc N ω ≤ Mb → ∀ x : E, ‖x‖ ≤ 1 → G N ω x ∈ C)
    (D : Set E) (hDdense : Dense D)
    (hDadd : ∀ a ∈ D, ∀ b ∈ D, a + b ∈ D)
    (hquad : ∀ h ∈ D, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ,
      ∀ N N', N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|} ≤ ENNReal.ofReal rho) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ,
      ∀ N N', N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ ‖G N ω - G N' ω‖} ≤ ENNReal.ofReal rho := by
  classical
  let Ddiff : Set E := {x | ∃ a ∈ D, ∃ b ∈ D, x = a - b}
  obtain ⟨b₀, hb₀⟩ := hDdense.nonempty
  have hdense : Dense Ddiff := hDdense.mono fun a ha =>
    ⟨a + b₀, hDadd a ha b₀ hb₀, b₀, hb₀, by abel⟩
  have hclosed : ∀ a ∈ Ddiff, ∀ b ∈ Ddiff, a + b ∈ Ddiff ∧ a - b ∈ Ddiff := by
    rintro x ⟨a, ha, b, hb, rfl⟩ y ⟨c, hc, d, hd, rfl⟩
    constructor
    · exact ⟨a + c, hDadd a ha c hc, b + d, hDadd b hb d hd, by abel⟩
    · exact ⟨a + d, hDadd a ha d hd, b + c, hDadd b hb c hc, by abel⟩
  apply opNorm_cauchy_in_probability_of_uniformly_compact
    P G hsym Kc htight hcomp Ddiff hdense hclosed
  rintro x ⟨a, ha, b, hb, rfl⟩ eps heps rho hrho
  let H : Finset E := {a, b, a + b}
  have hHD : ∀ h ∈ H, h ∈ D := by
    intro h hh
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hDadd a ha b hb
  obtain ⟨N0, hN0⟩ := aux_finite_quad_cauchy P G D hquad H hHD
    (eps := eps / 8) (by positivity) hrho
  refine ⟨N0, fun N N' hN hN' => ?_⟩
  refine (measure_mono ?_).trans (hN0 N N' hN hN')
  intro ω hω
  by_contra hbad
  have hsmall : ∀ h ∈ H,
      |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ| < eps / 8 := by
    intro h hh
    exact lt_of_not_ge fun hlarge => hbad ⟨h, hh, hlarge⟩
  have ha' := abs_lt.mp (hsmall a (by simp [H]))
  have hb' := abs_lt.mp (hsmall b (by simp [H]))
  have hab' := abs_lt.mp (hsmall (a + b) (by simp [H]))
  have hidentity (A : E →L[ℝ] E) :
      ⟪a - b, A (a - b)⟫_ℝ =
        2 * ⟪a, A a⟫_ℝ + 2 * ⟪b, A b⟫_ℝ - ⟪a + b, A (a + b)⟫_ℝ := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right]
    ring
  have hlt : |⟪a - b, G N ω (a - b)⟫_ℝ - ⟪a - b, G N' ω (a - b)⟫_ℝ| < eps := by
    rw [hidentity, hidentity, abs_lt]
    constructor <;> linarith
  exact (not_lt_of_ge hω) hlt

end SubdiffusiveProcess.Probability
