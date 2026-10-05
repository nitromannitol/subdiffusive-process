module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepAxisCubeHarmonicExistence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellMomentAggregation

@[expose] public section

/-!
# Fourth-moment fold for translated Neumann cells

The Neumann comparison field in the one-step argument is split on each
translated parent cube into a zero-Dirichlet solution and a harmonic
remainder.  `OneStepAxisCubeHarmonicHessian` supplies the deterministic
arbitrary-center estimate for the latter.  This file performs the stochastic
fold which is common to every translated cell:

`B_N <= B_D + B_H` implies `E[B_N^4] <= 8 (E[B_D^4] + E[B_H^4])`.

The normalized finite-family form is the literal operation used before the
thermodynamic limit.  The proof follows the
finite-cell moment folds in
`Algsuperdiff/Section3/Provider/Diffusivity/ApproximateRecurrence/Closure/
SplitFoldCellMoments.lean`, specialized to the manuscript's fourth power.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The fourth-power loss in the Dirichlet plus harmonic Neumann split. -/
theorem add_four_le_eight_sum_four {D H : ℝ} (hD : 0 ≤ D) (hH : 0 ≤ H) :
    (D + H) ^ 4 ≤ 8 * (D ^ 4 + H ^ 4) := by
  have h := add_pow_le hD hH 4
  norm_num at h ⊢
  exact h

/-- A nonnegative Neumann cell observable dominated by the sum of two
measurable fourth-integrable pieces is itself fourth-integrable. -/
theorem integrable_four_of_le_dirichlet_add_harmonic
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {BN BD BH : Omega → ℝ}
    (hBN : Measurable BN)
    (hBN0 : 0 ≤ᵐ[mu] BN) (hBD0 : 0 ≤ᵐ[mu] BD) (hBH0 : 0 ≤ᵐ[mu] BH)
    (hdom : BN ≤ᵐ[mu] fun omega => BD omega + BH omega)
    (hBD4 : Integrable (fun omega => BD omega ^ 4) mu)
    (hBH4 : Integrable (fun omega => BH omega ^ 4) mu) :
    Integrable (fun omega => BN omega ^ 4) mu := by
  have hmajor : Integrable (fun omega => 8 * (BD omega ^ 4 + BH omega ^ 4)) mu :=
    (hBD4.add hBH4).const_mul 8
  refine hmajor.mono' (hBN.pow_const 4).aestronglyMeasurable ?_
  filter_upwards [hBN0, hBD0, hBH0, hdom] with omega hBNomega hBDomega hBHomega hle
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hBNomega 4)]
  exact (pow_le_pow_left₀ hBNomega hle 4).trans
    (add_four_le_eight_sum_four hBDomega hBHomega)

/-- One-cell expected fourth moment after the translated
Dirichlet/harmonic split. -/
theorem integral_four_le_eight_dirichlet_add_harmonic
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {BN BD BH : Omega → ℝ}
    (hBN : Measurable BN)
    (hBN0 : 0 ≤ᵐ[mu] BN) (hBD0 : 0 ≤ᵐ[mu] BD) (hBH0 : 0 ≤ᵐ[mu] BH)
    (hdom : BN ≤ᵐ[mu] fun omega => BD omega + BH omega)
    (hBD4 : Integrable (fun omega => BD omega ^ 4) mu)
    (hBH4 : Integrable (fun omega => BH omega ^ 4) mu) :
    ∫ omega, BN omega ^ 4 ∂mu ≤
      8 * (∫ omega, BD omega ^ 4 ∂mu) +
        8 * (∫ omega, BH omega ^ 4 ∂mu) := by
  have hBN4 := integrable_four_of_le_dirichlet_add_harmonic
    hBN hBN0 hBD0 hBH0 hdom hBD4 hBH4
  have hmajor : Integrable (fun omega => 8 * (BD omega ^ 4 + BH omega ^ 4)) mu :=
    (hBD4.add hBH4).const_mul 8
  calc
    ∫ omega, BN omega ^ 4 ∂mu ≤
        ∫ omega, 8 * (BD omega ^ 4 + BH omega ^ 4) ∂mu := by
      apply integral_mono_ae hBN4 hmajor
      filter_upwards [hBN0, hBD0, hBH0, hdom] with omega hBNomega hBDomega hBHomega hle
      exact (pow_le_pow_left₀ hBNomega hle 4).trans
        (add_four_le_eight_sum_four hBDomega hBHomega)
    _ = 8 * (∫ omega, BD omega ^ 4 ∂mu) +
        8 * (∫ omega, BH omega ^ 4 ∂mu) := by
      rw [integral_const_mul, integral_add hBD4 hBH4]
      ring

/-- The normalized finite-cell fourth-moment budget for the translated
Neumann comparison.  No uniform-in-cell estimate is inserted: both inputs are
the manuscript's normalized averages over the surviving interior cells. -/
theorem normalized_finset_integral_four_le_eight_dirichlet_add_harmonic
    {iota Omega : Type*} [DecidableEq iota] [MeasurableSpace Omega]
    {mu : Measure Omega} (s : Finset iota)
    (BN BD BH : iota → Omega → ℝ)
    (hBN : ∀ i ∈ s, Measurable (BN i))
    (hBN0 : ∀ i ∈ s, 0 ≤ᵐ[mu] BN i)
    (hBD0 : ∀ i ∈ s, 0 ≤ᵐ[mu] BD i)
    (hBH0 : ∀ i ∈ s, 0 ≤ᵐ[mu] BH i)
    (hdom : ∀ i ∈ s, BN i ≤ᵐ[mu] fun omega => BD i omega + BH i omega)
    (hBD4 : ∀ i ∈ s, Integrable (fun omega => BD i omega ^ 4) mu)
    (hBH4 : ∀ i ∈ s, Integrable (fun omega => BH i omega ^ 4) mu) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s, ∫ omega, BN i omega ^ 4 ∂mu ≤
      8 * (((s.card : ℝ)⁻¹) *
          ∑ i ∈ s, ∫ omega, BD i omega ^ 4 ∂mu) +
        8 * (((s.card : ℝ)⁻¹) *
          ∑ i ∈ s, ∫ omega, BH i omega ^ 4 ∂mu) := by
  have hcell : ∀ i ∈ s,
      ∫ omega, BN i omega ^ 4 ∂mu ≤
        8 * (∫ omega, BD i omega ^ 4 ∂mu) +
          8 * (∫ omega, BH i omega ^ 4 ∂mu) := by
    intro i hi
    exact integral_four_le_eight_dirichlet_add_harmonic
      (hBN i hi)
      (hBN0 i hi) (hBD0 i hi) (hBH0 i hi) (hdom i hi)
      (hBD4 i hi) (hBH4 i hi)
  have hinv : 0 ≤ ((s.card : ℝ)⁻¹) := by positivity
  calc
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s, ∫ omega, BN i omega ^ 4 ∂mu ≤
        ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
          (8 * (∫ omega, BD i omega ^ 4 ∂mu) +
            8 * (∫ omega, BH i omega ^ 4 ∂mu)) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i hi => hcell i hi) hinv
    _ = 8 * (((s.card : ℝ)⁻¹) *
          ∑ i ∈ s, ∫ omega, BD i omega ^ 4 ∂mu) +
        8 * (((s.card : ℝ)⁻¹) *
          ∑ i ∈ s, ∫ omega, BH i omega ^ 4 ∂mu) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- Insert separate averaged fourth-moment budgets for the Dirichlet and
harmonic pieces into the translated Neumann fold. -/
theorem normalized_finset_integral_four_le_of_split_budgets
    {iota Omega : Type*} [DecidableEq iota] [MeasurableSpace Omega]
    {mu : Measure Omega} (s : Finset iota)
    (BN BD BH : iota → Omega → ℝ)
    (hBN : ∀ i ∈ s, Measurable (BN i))
    (hBN0 : ∀ i ∈ s, 0 ≤ᵐ[mu] BN i)
    (hBD0 : ∀ i ∈ s, 0 ≤ᵐ[mu] BD i)
    (hBH0 : ∀ i ∈ s, 0 ≤ᵐ[mu] BH i)
    (hdom : ∀ i ∈ s, BN i ≤ᵐ[mu] fun omega => BD i omega + BH i omega)
    (hBD4 : ∀ i ∈ s, Integrable (fun omega => BD i omega ^ 4) mu)
    (hBH4 : ∀ i ∈ s, Integrable (fun omega => BH i omega ^ 4) mu)
    {D H : ℝ}
    (hDbudget : ((s.card : ℝ)⁻¹) *
      ∑ i ∈ s, ∫ omega, BD i omega ^ 4 ∂mu ≤ D)
    (hHbudget : ((s.card : ℝ)⁻¹) *
      ∑ i ∈ s, ∫ omega, BH i omega ^ 4 ∂mu ≤ H) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s, ∫ omega, BN i omega ^ 4 ∂mu ≤
      8 * D + 8 * H := by
  exact (normalized_finset_integral_four_le_eight_dirichlet_add_harmonic
    s BN BD BH hBN hBN0 hBD0 hBH0 hdom hBD4 hBH4).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left hDbudget (by norm_num))
        (mul_le_mul_of_nonneg_left hHbudget (by norm_num)))



theorem normalized_finset_integral_four_le_of_common_multiplier
    {iota Omega : Type*} [DecidableEq iota] [MeasurableSpace Omega]
    {mu : Measure Omega} (s : Finset iota)
    (BH G : iota → Omega → ℝ) {K E : ℝ}
    (hK : 0 ≤ K)
    (hBH : ∀ i ∈ s, Measurable (BH i))
    (hBH0 : ∀ i ∈ s, 0 ≤ᵐ[mu] BH i)
    (hG0 : ∀ i ∈ s, 0 ≤ᵐ[mu] G i)
    (hdom : ∀ i ∈ s, BH i ≤ᵐ[mu] fun omega ↦ K * G i omega)
    (hG4 : ∀ i ∈ s, Integrable (fun omega ↦ G i omega ^ 4) mu)
    (hGbudget : ((s.card : ℝ)⁻¹) *
      ∑ i ∈ s, ∫ omega, G i omega ^ 4 ∂mu ≤ E) :
    ((s.card : ℝ)⁻¹) *
        ∑ i ∈ s, ∫ omega, BH i omega ^ 4 ∂mu ≤ K ^ 4 * E := by
  have hcell : ∀ i ∈ s,
      ∫ omega, BH i omega ^ 4 ∂mu ≤
        K ^ 4 * ∫ omega, G i omega ^ 4 ∂mu := by
    intro i hi
    have hKG4 : Integrable (fun omega ↦ (K * G i omega) ^ 4) mu := by
      convert (hG4 i hi).const_mul (K ^ 4) using 1
      funext omega
      ring
    have hBH4 : Integrable (fun omega ↦ BH i omega ^ 4) mu := by
      refine hKG4.mono' ((hBH i hi).pow_const 4).aestronglyMeasurable ?_
      filter_upwards [hBH0 i hi, hG0 i hi, hdom i hi] with omega hBN hGN hle
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hBN 4)]
      exact pow_le_pow_left₀ hBN hle 4
    calc
      ∫ omega, BH i omega ^ 4 ∂mu ≤
          ∫ omega, (K * G i omega) ^ 4 ∂mu := by
        apply integral_mono_ae hBH4 hKG4
        filter_upwards [hBH0 i hi, hG0 i hi, hdom i hi] with omega hBN hGN hle
        exact pow_le_pow_left₀ hBN hle 4
      _ = K ^ 4 * ∫ omega, G i omega ^ 4 ∂mu := by
        rw [show (fun omega ↦ (K * G i omega) ^ 4) =
            fun omega ↦ K ^ 4 * G i omega ^ 4 by funext omega; ring,
          integral_const_mul]
  have hK4 : 0 ≤ K ^ 4 := pow_nonneg hK 4
  have hcard : 0 ≤ ((s.card : ℝ)⁻¹) := by positivity
  calc
    ((s.card : ℝ)⁻¹) *
        ∑ i ∈ s, ∫ omega, BH i omega ^ 4 ∂mu ≤
      ((s.card : ℝ)⁻¹) *
        ∑ i ∈ s, K ^ 4 * ∫ omega, G i omega ^ 4 ∂mu :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i hi ↦ hcell i hi) hcard
    _ = K ^ 4 * (((s.card : ℝ)⁻¹) *
        ∑ i ∈ s, ∫ omega, G i omega ^ 4 ∂mu) := by
      simp only [← Finset.mul_sum]
      ring
    _ ≤ K ^ 4 * E := mul_le_mul_of_nonneg_left hGbudget hK4

/-- The complete translated Neumann fourth-moment fold after the harmonic
piece has been reduced to a common parent-gradient observable. -/
theorem normalized_finset_neumann_four_le_of_dirichlet_and_parent_budgets
    {iota Omega : Type*} [DecidableEq iota] [MeasurableSpace Omega]
    {mu : Measure Omega} (s : Finset iota)
    (BN BD BH G : iota → Omega → ℝ)
    (hBN : ∀ i ∈ s, Measurable (BN i))
    (hBN0 : ∀ i ∈ s, 0 ≤ᵐ[mu] BN i)
    (hBD0 : ∀ i ∈ s, 0 ≤ᵐ[mu] BD i)
    (hBH0 : ∀ i ∈ s, 0 ≤ᵐ[mu] BH i)
    (hG0 : ∀ i ∈ s, 0 ≤ᵐ[mu] G i)
    (hBHmeas : ∀ i ∈ s, Measurable (BH i))
    (hsplit : ∀ i ∈ s, BN i ≤ᵐ[mu] fun omega ↦ BD i omega + BH i omega)
    (hBD4 : ∀ i ∈ s, Integrable (fun omega ↦ BD i omega ^ 4) mu)
    (hBH4 : ∀ i ∈ s, Integrable (fun omega ↦ BH i omega ^ 4) mu)
    (hG4 : ∀ i ∈ s, Integrable (fun omega ↦ G i omega ^ 4) mu)
    {K D E : ℝ} (hK : 0 ≤ K)
    (hBHdom : ∀ i ∈ s, BH i ≤ᵐ[mu] fun omega ↦ K * G i omega)
    (hDbudget : ((s.card : ℝ)⁻¹) *
      ∑ i ∈ s, ∫ omega, BD i omega ^ 4 ∂mu ≤ D)
    (hGbudget : ((s.card : ℝ)⁻¹) *
      ∑ i ∈ s, ∫ omega, G i omega ^ 4 ∂mu ≤ E) :
    ((s.card : ℝ)⁻¹) *
      ∑ i ∈ s, ∫ omega, BN i omega ^ 4 ∂mu ≤
        8 * D + 8 * (K ^ 4 * E) := by
  have hHbudget := normalized_finset_integral_four_le_of_common_multiplier
    s BH G hK hBHmeas
    hBH0 hG0 hBHdom hG4 hGbudget
  exact normalized_finset_integral_four_le_of_split_budgets
    s BN BD BH hBN hBN0 hBD0 hBH0 hsplit hBD4 hBH4 hDbudget hHbudget

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
