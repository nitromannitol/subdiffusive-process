import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalLevelEnergy

/-! Positive-level testing with the pure killed Sobolev bound. The original
coefficient energy and weighted source are retained, without the mass term
in the Section 9 Sobolev vocabulary. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal
namespace SubdiffusiveProcess.Section10

/-- All native zero-trace functions satisfy the pure weighted Sobolev estimate. -/
def TorsionSobolevBound {d : ℕ} (A b : Vec d → ℝ) (U : Set (Vec d))
    (p Ksob : ℝ) : Prop :=
  ∀ v : H10Function U, lpSq b U p v.toFun ≤
    ENNReal.ofReal (Ksob * energy A U v.toH1Function)

/-- The actual weak equation supplies every positive-level energy inequality. -/
theorem torsion_positive_level_bound {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {A b : Vec d → ℝ}
    (hb : CoefficientOn U b) {p Ksob : ℝ} (hKsob : 0 ≤ Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob)
    {f : Vec d → ℝ} (u : H10Function U)
    (hu : IsMassiveWeakSolutionOn A b 0 U u.toH1Function f) :
    ∀ h : ℝ, 0 ≤ h →
      (eLpNorm (fun x => max (u.toFun x - h) 0) (ENNReal.ofReal p)
        ((weightedMeasure b).restrict U)) ^ 2 ≤
      ENNReal.ofReal Ksob * ∫⁻ x, ENNReal.ofReal (|f x| * max (u.toFun x - h) 0)
        ∂(weightedMeasure b).restrict U := by
  intro h hh
  obtain ⟨v, hvf, hvg⟩ := exists_h10_positivePart hU u hh
  have hv0 (x : Vec d) : 0 ≤ v.toFun x := by rw [hvf x]; exact le_max_right _ _
  have hid : energy A U v.toH1Function =
      ∫ x, f x * v.toFun x ∂(weightedMeasure b).restrict U := by
    rw [integral_weightedMeasure_restrict_eq hU.isOpen.measurableSet b _ hb]
    have ht := hu v
    rw [positivePart_energy_eq hvg] at ht
    simpa only [zero_mul, zero_add, mul_assoc] using ht
  have henergy : ENNReal.ofReal (energy A U v.toH1Function) ≤
      ∫⁻ x, ENNReal.ofReal (|f x| * v.toFun x) ∂(weightedMeasure b).restrict U := by
    calc
      _ ≤ ‖∫ x, f x * v.toFun x ∂(weightedMeasure b).restrict U‖ₑ := by
        rw [hid, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖f x * v.toFun x‖ₑ ∂(weightedMeasure b).restrict U :=
        enorm_integral_le_lintegral_enorm _
      _ = _ := by
        apply lintegral_congr
        intro x
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 x)]
  have hs := hSob v
  rw [ENNReal.ofReal_mul hKsob] at hs
  have hp := hs.trans (mul_le_mul_right henergy (ENNReal.ofReal Ksob))
  have hvfun : v.toFun = fun x => max (u.toFun x - h) 0 := funext hvf
  change (eLpNorm v.toFun (ENNReal.ofReal p) ((weightedMeasure b).restrict U)) ^ 2 ≤ _ at hp
  simpa only [hvfun] using hp

end SubdiffusiveProcess.Section10
