module

public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set
noncomputable section
namespace SubdiffusiveProcess.Probability

/-- Uniform convergence in probability follows when every deterministic
subsequence has a further subsequence converging to the specified limit. -/
theorem uniform_probability_limit_of_subsequence
    {Ω X : Type*} [MeasurableSpace Ω] (P : Measure Ω) (K : Set X)
    (F : ℕ → Ω → X → ℝ) (R : Ω → X → ℝ)
    (h : ∀ psi : ℕ → ℕ, StrictMono psi → ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
        P {omega | ∃ x ∈ K, eps ≤ |F (psi (phi N)) omega x - R omega x|} ≤
          ENNReal.ofReal rho) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      P {omega | ∃ x ∈ K, eps ≤ |F N omega x - R omega x|} ≤ ENNReal.ofReal rho := by
  intro eps heps rho hrho
  by_contra hn
  have hfreq : ∃ᶠ N in atTop,
      ¬ P {omega | ∃ x ∈ K, eps ≤ |F N omega x - R omega x|} ≤ ENNReal.ofReal rho := by
    rw [frequently_atTop]
    intro N0
    by_contra hh
    apply hn
    refine ⟨N0, fun N hN => ?_⟩
    by_contra hbad
    exact hh ⟨N, hN, hbad⟩
  obtain ⟨psi, hpsi, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨phi, -, hphi⟩ := h psi hpsi
  obtain ⟨N0, hN0⟩ := hphi eps heps rho hrho
  exact hbad (phi N0) (hN0 N0 le_rfl)

end SubdiffusiveProcess.Probability
