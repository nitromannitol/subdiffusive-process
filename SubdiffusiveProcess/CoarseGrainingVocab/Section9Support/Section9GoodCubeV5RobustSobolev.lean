import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5RobustMass

/-!
# Step S of the robust good-cube event: the Sobolev field

`ledger/proofplans/l.weighted.good.cube.events.robust-event.md` §5 Step S.  The plan's
derivation has three ingredients; the two that are pure perturbation algebra are proved here,
reusing C2 from `Section9GoodCubeV5RobustMass.lean`.

* `weightedMeasure_restrict_mul_le_smul` — C2 restated as a comparison of **measures**, which is
  the form `eLpNorm` consumes.
* `lpSq_mul_le` — hence the `p`-seminorm against the multiplied weighted measure pays only the
  scalar factor `u^{1/p}`, squared, by `eLpNorm_mono_measure` followed by
  `eLpNorm_smul_measure_of_ne_zero`.
* `energy_mul_ge` — a pointwise lower bound on the multiplier is a scalar lower bound on the
  Dirichlet energy.  One honest side condition the plan's pointwise argument hides: `energy` is a
  **Bochner** integral, so its monotonicity needs both integrands integrable on the cube; those
  are carried as hypotheses rather than assumed away.

With these, the plan's exponent bookkeeping is the identity
`2/p + (1 - 2/p) - 1 = 0`: the `lpSq` factor contributes `(k(1+ε))^{2/p}`, the negative power of
the weighted measure contributes `(k(1+ε))^{1-2/p}`, and the energy contributes `(k(1-ε))⁻¹`, so
the transferred constant is `CC · (1+ε)/(1-ε)`, independent of `p` **and** of the multiplier's
scale `k`.  Assembling that into `GoodCubeSobolevDisplay` is the remaining step; it needs the
antitonicity of `x ↦ x^{-(1-2/p)}` on `ℝ≥0∞` with its zero and infinity edge cases.
-/

set_option autoImplicit false
open Homogenization hiding Vec
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-- **C2 as a comparison of measures.**  On the window, the multiplied weighted measure is
dominated by the scalar multiple of the original one.  This is the form the `L^p` seminorm
consumes. -/
theorem weightedMeasure_restrict_mul_le_smul {S U : Set (Vec d)} (hU : MeasurableSet U)
    (hUS : U ⊆ S)
    {a theta : Vec d → ℝ} {u : ℝ} (hu : 0 ≤ u) (ha : ∀ x ∈ S, 0 ≤ a x)
    (hupper : ∀ x ∈ S, theta x ≤ u) :
    (weightedMeasure (fun x => a x * theta x)).restrict U ≤
      ENNReal.ofReal u • (weightedMeasure a).restrict U := by
  refine Measure.le_iff.mpr fun E hE => ?_
  rw [Measure.restrict_apply hE, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hE]
  exact weightedMeasure_mul_le (hE.inter hU) (fun _ hx => hUS hx.2) hu ha hupper

/-- **Step S, the `L^p` half.**  The `p`-seminorm against the multiplied weighted measure pays
only the scalar factor `u^{1/p}`, squared. -/
theorem lpSq_mul_le {S U : Set (Vec d)} (hU : MeasurableSet U) (hUS : U ⊆ S)
    {a theta : Vec d → ℝ} {u p : ℝ} (hu : 0 < u)
    (ha : ∀ x ∈ S, 0 ≤ a x) (hupper : ∀ x ∈ S, theta x ≤ u) (f : Vec d → ℝ) :
    lpSq (fun x => a x * theta x) U p f ≤
      (ENNReal.ofReal u ^ (1 / ENNReal.ofReal p).toReal) ^ (2 : ℕ) * lpSq a U p f := by
  have hune : ENNReal.ofReal u ≠ 0 := by
    simpa using hu
  have hmono : eLpNorm f (ENNReal.ofReal p)
        ((weightedMeasure (fun x => a x * theta x)).restrict U) ≤
      eLpNorm f (ENNReal.ofReal p) (ENNReal.ofReal u • (weightedMeasure a).restrict U) :=
    eLpNorm_mono_measure f
      (weightedMeasure_restrict_mul_le_smul hU hUS hu.le ha hupper)
  rw [eLpNorm_smul_measure_of_ne_zero hune] at hmono
  unfold lpSq
  calc (eLpNorm f (ENNReal.ofReal p)
        ((weightedMeasure (fun x => a x * theta x)).restrict U)) ^ (2 : ℕ)
      ≤ (ENNReal.ofReal u ^ (1 / ENNReal.ofReal p).toReal •
          eLpNorm f (ENNReal.ofReal p) ((weightedMeasure a).restrict U)) ^ (2 : ℕ) :=
        pow_le_pow_left' hmono 2
    _ = (ENNReal.ofReal u ^ (1 / ENNReal.ofReal p).toReal) ^ (2 : ℕ) *
          (eLpNorm f (ENNReal.ofReal p) ((weightedMeasure a).restrict U)) ^ (2 : ℕ) := by
        rw [smul_eq_mul, mul_pow]

/-- The Dirichlet integrand is nonnegative. -/
theorem vecDot_self_nonneg (v : Vec d) : 0 ≤ vecDot v v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- **Step S, the energy half.**  A pointwise lower bound on the multiplier is a scalar lower
bound on the Dirichlet energy.  The Bochner integral needs both integrands integrable; that is
the only side condition the plan's pointwise argument hides. -/
theorem energy_mul_ge {S U : Set (Vec d)} (hU : MeasurableSet U) (hUS : U ⊆ S)
    {a theta : Vec d → ℝ} {l : ℝ}
    (ha : ∀ x ∈ S, 0 ≤ a x) (hlower : ∀ x ∈ S, l ≤ theta x)
    (f : H1Function U)
    (hint1 : IntegrableOn (fun x => a x * vecDot (f.grad x) (f.grad x)) U)
    (hint2 : IntegrableOn (fun x => a x * theta x * vecDot (f.grad x) (f.grad x)) U) :
    l * energy a U f ≤ energy (fun x => a x * theta x) U f := by
  unfold energy
  rw [← integral_const_mul]
  refine integral_mono_ae (hint1.const_mul l) hint2 ?_
  filter_upwards [ae_restrict_mem hU] with x hx
  have hxS := hUS hx
  have hg := vecDot_self_nonneg (f.grad x)
  have hprod : 0 ≤ (theta x - l) * (a x * vecDot (f.grad x) (f.grad x)) :=
    mul_nonneg (by linarith [hlower x hxS]) (mul_nonneg (ha x hxS) hg)
  nlinarith [hprod]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
