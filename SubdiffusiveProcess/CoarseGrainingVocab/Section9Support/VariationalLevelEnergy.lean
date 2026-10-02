import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.InteriorGreenGain
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationLevelEnergy

/-!
# Positive-level Sobolev estimates for the variational Green inverse

The actual zero-mass weak equation is tested with its positive level
truncations. Sobolev and Dirichlet Poincaré supply the quantitative
constant; the qualitative coefficient bounds do not appear in it.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Every nonnegative-level truncation of the Green solution satisfies
the pure Sobolev level estimate, with no high-integrability assumption
on the solution and no diffusion law. -/
theorem variational_green_positive_level_bound {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {c rho : Vec d → ℝ}
    (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {p A F : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hSob : SobolevAssumption c rho U p A F)
    (hPoi : PoincareAssumption c rho U A F)
    {f : Vec d → ℝ} (u : H10Function U)
    (hu : IsMassiveWeakSolutionOn c rho 0 U u.toH1Function f) :
    ∀ k : ℝ, 0 ≤ k →
      (eLpNorm (fun x => max (u.toH1Function.toFun x - k) 0) (ENNReal.ofReal p)
        ((weightedMeasure rho).restrict U)) ^ 2 ≤
      ENNReal.ofReal (A * (A + 1) * F * ((weightedMeasure rho U).toReal) ^ (-(1 - 2 / p))) *
        ∫⁻ x, ENNReal.ofReal (|f x| * max (u.toH1Function.toFun x - k) 0)
          ∂(weightedMeasure rho).restrict U := by
  intro k hk
  obtain ⟨v, hvf, hvg⟩ := exists_h10_positivePart hU u hk
  have hv0 (x : Vec d) : 0 ≤ v.toH1Function.toFun x := by rw [hvf x]; exact le_max_right _ _
  have hc0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ c x := by
    obtain ⟨_, lo, hi, hlo, hb⟩ := hc
    exact hb.mono fun _ hx => hlo.le.trans hx.1
  have hid : energy c U v.toH1Function =
      ∫ x, f x * v.toH1Function.toFun x ∂(weightedMeasure rho).restrict U := by
    rw [integral_weightedMeasure_restrict_eq hU.isOpen.measurableSet rho _ hr]
    have ht := hu v
    rw [positivePart_energy_eq hvg] at ht
    simpa only [zero_mul, zero_add, mul_assoc] using ht
  have henergy : ENNReal.ofReal (energy c U v.toH1Function) ≤
      ∫⁻ x, ENNReal.ofReal (|f x| * v.toH1Function.toFun x) ∂(weightedMeasure rho).restrict U := by
    calc
      _ ≤ ‖∫ x, f x * v.toH1Function.toFun x ∂(weightedMeasure rho).restrict U‖ₑ := by
        rw [hid, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖f x * v.toH1Function.toFun x‖ₑ ∂(weightedMeasure rho).restrict U :=
        enorm_integral_le_lintegral_enorm _
      _ = _ := by
        apply lintegral_congr
        intro x
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 x)]
  have hs := sobolev_energy_bound_of_sobolevAssumption_poincareAssumption hA hF hc0 hSob hPoi v
  have hp := hs.trans (mul_le_mul' le_rfl henergy)
  have hvfun : v.toH1Function.toFun = fun x => max (u.toH1Function.toFun x - k) 0 := funext hvf
  change (eLpNorm v.toH1Function.toFun (ENNReal.ofReal p) ((weightedMeasure rho).restrict U)) ^ 2 ≤ _ at hp
  rw [hvfun] at hp
  exact hp

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
