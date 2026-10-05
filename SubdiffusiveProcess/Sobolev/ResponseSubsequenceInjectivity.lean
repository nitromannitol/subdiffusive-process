module

public import SubdiffusiveProcess.Sobolev.ResponseInjectivity

@[expose] public section

/-! Injectivity of an inverse limit from approximants along further subsequences.
The subsequence may depend on the datum and accuracy. Construction and bounded
energy of those approximants remain explicit hypotheses. -/

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace SubdiffusiveProcess

/-- Arbitrarily accurate bounded-energy approximants along further subsequences make an inverse limit injective. -/
theorem injective_limit_of_volumeResponse_subsequence_approximations
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : ℕ → PositiveCoefficient Ω)
    (G : DomainL2 Ω →L[ℝ] DomainL2 Ω) (D : Set (DomainL2 Ω))
    (hD : Dense D)
    (hresponse : ∀ f : DomainL2 Ω,
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (𝓝 (inner ℝ f (G f))))
    (happrox : ∀ φ ∈ D, ∀ ε : ℝ, 0 < ε →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧ ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm S (a (seq n)) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε)) :
    Function.Injective G := by
  intro f g hfg
  let x : DomainL2 Ω := f - g
  have hGx : G x = 0 := by
    simp only [x, map_sub, hfg, sub_self]
  have hresponse_zero : Tendsto (fun n => inverseResponse S (a n)
      ((sobolevVolumeLoad x).comp S.space.subtypeL)) atTop (𝓝 0) := by
    simpa only [hGx, inner_zero_right] using hresponse x
  have hxD : ∀ φ ∈ D, inner ℝ x φ = 0 := by
    intro φ hφ
    by_contra hpair_ne
    have hpair_pos : 0 < |inner ℝ x φ| := abs_pos.mpr hpair_ne
    let ε : ℝ := |inner ℝ x φ| / (2 * (‖x‖ + 1))
    have hε : 0 < ε := by
      dsimp only [ε]
      positivity
    obtain ⟨seq, hseq, w, C, henergy, hclose⟩ := happrox φ hφ ε hε
    have hC : 0 ≤ C := by
      exact (responseForm_nonneg S (a (seq 0)) (w 0)).trans (henergy 0)
    have hsquare : ∀ n : ℕ,
        (((sobolevVolumeLoad x).comp S.space.subtypeL) (w n)) ^ 2 ≤
          inverseResponse S (a (seq n)) ((sobolevVolumeLoad x).comp S.space.subtypeL) * C := by
      intro n
      exact (sq_load_le_inverseResponse_mul_responseForm S (a (seq n))
        ((sobolevVolumeLoad x).comp S.space.subtypeL) (w n)).trans
          (mul_le_mul_of_nonneg_left (henergy n) (inverseResponse_nonneg S (a (seq n)) _))
    have hsqrt : Tendsto (fun n => Real.sqrt
        (inverseResponse S (a (seq n)) ((sobolevVolumeLoad x).comp S.space.subtypeL) * C))
        atTop (𝓝 0) := by
      have hmul := (hresponse_zero.comp hseq.tendsto_atTop).mul_const C
      have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hmul
      simpa only [Function.comp_def, zero_mul, Real.sqrt_zero] using hs
    have hload_abs : Tendsto (fun n =>
        |((sobolevVolumeLoad x).comp S.space.subtypeL) (w n)|) atTop (𝓝 0) := by
      apply squeeze_zero'
      · exact Eventually.of_forall fun n => abs_nonneg _
      · exact Eventually.of_forall fun n => Real.abs_le_sqrt (hsquare n)
      · exact hsqrt
    have hpair_bound : |inner ℝ x φ| ≤ ‖x‖ * ε := by
      have ht : Tendsto (fun n =>
          |((sobolevVolumeLoad x).comp S.space.subtypeL) (w n)| + ‖x‖ * ε)
          atTop (𝓝 (‖x‖ * ε)) := by
        simpa only [zero_add] using hload_abs.add_const (‖x‖ * ε)
      apply ge_of_tendsto ht
      exact Eventually.of_forall fun n => by
        have hinner_close : |inner ℝ x (φ - (w n).val.1)| ≤ ‖x‖ * ε := by
          calc
            |inner ℝ x (φ - (w n).val.1)| ≤ ‖x‖ * ‖φ - (w n).val.1‖ := by
              simpa only [Real.norm_eq_abs] using
                (norm_inner_le_norm (𝕜 := ℝ) x (φ - (w n).val.1))
            _ ≤ ‖x‖ * ε := mul_le_mul_of_nonneg_left (by
              simpa only [norm_sub_rev] using hclose n) (norm_nonneg x)
        calc
          |inner ℝ x φ| = |inner ℝ x (w n).val.1 + inner ℝ x (φ - (w n).val.1)| := by
            rw [inner_sub_right]
            ring_nf
          _ ≤ |inner ℝ x (w n).val.1| + |inner ℝ x (φ - (w n).val.1)| :=
            abs_add_le _ _
          _ ≤ |((sobolevVolumeLoad x).comp S.space.subtypeL) (w n)| + ‖x‖ * ε := by
            rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
            exact add_le_add (le_refl _) hinner_close
    dsimp only [ε] at hpair_bound
    have hxnorm : 0 ≤ ‖x‖ := norm_nonneg x
    have hdenom : 0 < 2 * (‖x‖ + 1) := by positivity
    have hfactor : ‖x‖ / (2 * (‖x‖ + 1)) < 1 := by
      rw [div_lt_one hdenom]
      linarith only [hxnorm]
    have hrearrange : ‖x‖ * (|inner ℝ x φ| / (2 * (‖x‖ + 1))) =
        |inner ℝ x φ| * (‖x‖ / (2 * (‖x‖ + 1))) := by ring
    rw [hrearrange] at hpair_bound
    nlinarith only [hpair_bound, hpair_pos, hfactor]
  have hxzero : x = 0 := by
    have heq : (fun φ : DomainL2 Ω => inner ℝ x φ) = fun _ => 0 := by
      apply Continuous.ext_on hD
      · exact continuous_const.inner continuous_id
      · exact continuous_const
      · intro φ hφ
        exact hxD φ hφ
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact congrFun heq x
  simpa only [x, sub_eq_zero] using hxzero

end SubdiffusiveProcess
