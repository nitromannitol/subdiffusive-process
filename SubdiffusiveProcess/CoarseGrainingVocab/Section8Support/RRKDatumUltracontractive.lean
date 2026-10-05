module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumUltracontractive

/-! ## Cauchy–Schwarz on a finite measure -/

/-- On a finite measure the `L¹` seminorm is at most the square root of the mass
times the `L²` seminorm. -/
theorem eLpNorm_one_le_of_two {X : Type*} [MeasurableSpace X] {nu : Measure X}
    {f : X → ℝ} (hf : AEStronglyMeasurable f nu) :
    eLpNorm f 1 nu ≤ eLpNorm f 2 nu * (nu Set.univ) ^ ((2 : ℝ)⁻¹) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := nu) (f := f)
    (p := 1) (q := 2) one_le_two hf
  have hexp : (1 : ℝ) / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = (2 : ℝ)⁻¹ := by
    norm_num
  rwa [hexp] at h


/-- Dividing by a mass and multiplying by its square root is dividing by the
square root. -/
theorem div_mul_mul_sqrt (a b : ℝ) {M r : ℝ} (hr : 0 < r) (hM : r * r = M) :
    a / M * b * r = a / r * b := by
  rw [← hM]
  field_simp

/-! ## The `L² → L^∞` bound for a fixed resolvent power -/

section Diffusion

variable {d : ℕ} {c rho : Vec d → ℝ} {law : ProbabilityTheory.Kernel (Vec d) (Path d)}

/-- **The `L^∞` half of (RRK) for the killed forms.**  A fixed power of
the killed resolvent maps `L²(μ)` to `L^∞(μ)`, with the constant of
`LocalResolventIterationUltra.iterate_eLpNorm_le` divided by the *square root*
of the weighted mass instead of the mass.

`(killedResolvent law U s)^[k+1]` is `(I + sH)^{-(k+1)}` for the killed form on
`U`: the third clause of `LocalDiffusion` identifies `killedResolvent law U s f`
with the massive weak solution of mass `s⁻¹` and datum `s⁻¹ f`. -/
theorem iterate_eLpNorm_two_le
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hm0 : (weightedMeasure rho) U ≠ 0) (hmtop : (weightedMeasure rho) U ≠ ∞)
    {p0 A F s : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hF : 0 < F) (hs : 0 < s)
    (hSob : SobolevAssumption c rho U p0 A F)
    (k : ℕ) (hk : qExp p0 ≤ rExp p0 ^ k) {f : Vec d → ℝ}
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) :
    eLpNorm ((killedResolvent law U s)^[k + 1] f) ∞ ((weightedMeasure rho).restrict U) ≤
      ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
          Real.sqrt (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) *
        eLpNorm f 2 ((weightedMeasure rho).restrict U) := by
  have hmuniv : ((weightedMeasure rho).restrict U) Set.univ = (weightedMeasure rho) U :=
    Measure.restrict_apply_univ _
  have hfinite : IsFiniteMeasure ((weightedMeasure rho).restrict U) :=
    ⟨by rw [hmuniv]; exact lt_of_le_of_ne le_top hmtop⟩
  have hmass : 0 < (((weightedMeasure rho) U)).toReal := ENNReal.toReal_pos hm0 hmtop
  have hf1 : MemLp f 1 ((weightedMeasure rho).restrict U) := hf.mono_exponent one_le_two
  have hstep := iterate_eLpNorm_le hD hU hm0 hmtop hp0 hA hF hs hSob k hk hf1
  refine hstep.trans ?_
  have hone := eLpNorm_one_le_of_two (nu := (weightedMeasure rho).restrict U) hf.aestronglyMeasurable
  rw [hmuniv] at hone
  have hsqrt : ((weightedMeasure rho) U) ^ ((2 : ℝ)⁻¹)
      = ENNReal.ofReal (Real.sqrt (((weightedMeasure rho) U).toReal)) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_pos hmass, ENNReal.ofReal_toReal hmtop]
    norm_num
  rw [hsqrt] at hone
  calc
    ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
          (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) *
        eLpNorm f 1 ((weightedMeasure rho).restrict U)
        ≤ ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
            (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) *
          (eLpNorm f 2 ((weightedMeasure rho).restrict U) *
            ENNReal.ofReal (Real.sqrt (((weightedMeasure rho) U).toReal))) := by
          gcongr
    _ = ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
          Real.sqrt (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) *
        eLpNorm f 2 ((weightedMeasure rho).restrict U) := by
          have hsq : Real.sqrt (((weightedMeasure rho) U).toReal) *
              Real.sqrt (((weightedMeasure rho) U).toReal)
              = ((weightedMeasure rho) U).toReal := Real.mul_self_sqrt hmass.le
          have hspos : 0 < Real.sqrt (((weightedMeasure rho) U).toReal) := Real.sqrt_pos.mpr hmass
          have hkey : ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
                (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹) *
                Real.sqrt (((weightedMeasure rho) U).toReal)
              = ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
                Real.sqrt (((weightedMeasure rho) U).toReal) *
                (1 + F / s) ^ ((1 - 2 / p0)⁻¹) :=
            div_mul_mul_sqrt _ _ hspos hsq
          have hnn : 0 ≤ ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
              (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹) := by
            have h1 : (0 : ℝ) ≤ A ^ ((1 - 2 / p0)⁻¹) :=
              Real.rpow_nonneg (by linarith) _
            have h2 : (0 : ℝ) ≤ (1 + F / s) ^ ((1 - 2 / p0)⁻¹) :=
              Real.rpow_nonneg (by positivity) _
            have h3 : (0 : ℝ) ≤ ultraConstant p0 := (ultraConstant_pos p0).le
            positivity
          rw [mul_comm (eLpNorm f 2 ((weightedMeasure rho).restrict U)), ← mul_assoc,
            ← ENNReal.ofReal_mul hnn, hkey]


/-- **(RRK) with the `C^α(K)` norm replaced by the sup norm.**  For the
killed forms there is a resolvent power `N`, depending only on the
Sobolev exponent `p0`, and a finite constant with

    ‖(I + sH)^{-N} f‖_{L^∞(μ)} ≤ C ‖f‖_{L²(μ)}.

This is the half of the resolvent regularity-kernel hypothesis
 that the Stampacchia/Sobolev chain of
`LocalResolventIterationUltra` already carries.  The other half — the Hölder
modulus on a compact `K ⋐ U` — is *not* supplied here and is not supplied here. -/
theorem exists_rrk_sup_bound
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hm0 : (weightedMeasure rho) U ≠ 0) (hmtop : (weightedMeasure rho) U ≠ ∞)
    {p0 A F s : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hF : 0 < F) (hs : 0 < s)
    (hSob : SobolevAssumption c rho U p0 A F) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∃ C : ℝ, 0 < C ∧ ∀ f : Vec d → ℝ,
      MemLp f 2 ((weightedMeasure rho).restrict U) →
        eLpNorm ((killedResolvent law U s)^[N0] f) ∞ ((weightedMeasure rho).restrict U) ≤
          ENNReal.ofReal C * eLpNorm f 2 ((weightedMeasure rho).restrict U) := by
  obtain ⟨N0, hN0, k, hNk, hk⟩ := exists_iterate_eLpNorm_le p0 hp0
  have hmass : 0 < (((weightedMeasure rho) U)).toReal := ENNReal.toReal_pos hm0 hmtop
  refine ⟨N0, hN0, ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
      Real.sqrt (((weightedMeasure rho) U).toReal) * (1 + F / s) ^ ((1 - 2 / p0)⁻¹), ?_, ?_⟩
  · have h1 : (0 : ℝ) < A ^ ((1 - 2 / p0)⁻¹) := Real.rpow_pos_of_pos (by linarith) _
    have h2 : (0 : ℝ) < (1 + F / s) ^ ((1 - 2 / p0)⁻¹) :=
      Real.rpow_pos_of_pos (by positivity) _
    have h3 : (0 : ℝ) < ultraConstant p0 := ultraConstant_pos p0
    have h4 : (0 : ℝ) < Real.sqrt (((weightedMeasure rho) U).toReal) :=
      Real.sqrt_pos.mpr hmass
    positivity
  · intro f hf
    rw [hNk]
    exact iterate_eLpNorm_two_le hD hU hm0 hmtop hp0 hA hF hs hSob k hk hf

end Diffusion

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumUltracontractive
