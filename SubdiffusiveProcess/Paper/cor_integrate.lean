module

public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.ResponseMoments.Forms
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.ResponseMoments.ResamplingV2
public import SubdiffusiveProcess.ResponseMoments.UpperDensity
public import SubdiffusiveProcess.ResponseMoments.BandFiltration
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import SubdiffusiveProcess.Probability.ResponseCompactness
public import SubdiffusiveProcess.Variational.QuadraticSaving
public import SubdiffusiveProcess.Compactness.OperatorLimits
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem cor_integrate
    (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (Q : Type) [MeasurableSpace Q]
    (theta : ℝ) (hth : 0 ≤ theta)
    (Bw : Om → ℝ) (_hBmeas : Measurable Bw) (hB0 : ∀ ω : Om, 0 ≤ Bw ω)
    (bad : Om → ℕ → Set Q)
    (hbad : ∀ (ω : Om) (j : ℕ), MeasurableSet (bad ω j))
    (hchain : ∀ᵐ ω ∂P, ∀ J : ℕ, 1 ≤ J → ∀ x : Q,
      (({j : ℕ | j ∈ Finset.Icc 1 J ∧ x ∈ bad ω j}.ncard : ℝ)) ≤
        theta * (J : ℝ) + Bw ω) :
    ∀ᵐ ω ∂P, ∀ lam : Measure Q, IsFiniteMeasure lam → ∀ J : ℕ, 1 ≤ J →
      (∑ j ∈ Finset.Icc 1 J, (lam (bad ω j)).toReal) ≤
        (theta * (J : ℝ) + Bw ω) * (lam Set.univ).toReal := by
  filter_upwards [hchain] with ω hω
  intro lam hlam J hJ
  classical
  let s : Finset ℕ := Finset.Icc 1 J
  let c : ℝ := theta * (J : ℝ) + Bw ω
  have hc : 0 ≤ c := by
    dsimp [c]
    exact add_nonneg (mul_nonneg hth (Nat.cast_nonneg J)) (hB0 ω)
  have hpoint (x : Q) :
      (∑ j ∈ s, (bad ω j).indicator (fun _ => (1 : ℝ≥0∞)) x) =
        (↑({j : ℕ | j ∈ s ∧ x ∈ bad ω j}.ncard) : ℝ≥0∞) := by
    have hset : {j : ℕ | j ∈ s ∧ x ∈ bad ω j} =
        (s.filter (fun j => x ∈ bad ω j) : Set ℕ) := by
      ext j
      simp
    simp only [Set.indicator_apply]
    rw [Finset.sum_boole, hset, Set.ncard_coe_finset]
  have hpoint_le (x : Q) :
      (∑ j ∈ s, (bad ω j).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤
        ENNReal.ofReal c := by
    rw [hpoint]
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    simpa [s, c] using hω J hJ x
  have hint :
      (∫⁻ x, ∑ j ∈ s, (bad ω j).indicator (fun _ => (1 : ℝ≥0∞)) x ∂lam) ≤
        ENNReal.ofReal c * lam Set.univ := by
    calc
      (∫⁻ x, ∑ j ∈ s, (bad ω j).indicator (fun _ => (1 : ℝ≥0∞)) x ∂lam) ≤
          ∫⁻ _ : Q, ENNReal.ofReal c ∂lam := lintegral_mono hpoint_le
      _ = ENNReal.ofReal c * lam Set.univ := lintegral_const _
  have hsum :
      (∑ j ∈ s, lam (bad ω j)) =
        ∫⁻ x, ∑ j ∈ s, (bad ω j).indicator (fun _ => (1 : ℝ≥0∞)) x ∂lam := by
    symm
    rw [lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact lintegral_indicator_one (hbad ω j)
    · intro j hj
      exact measurable_const.indicator (hbad ω j)
  have hsum_le :
      (∑ j ∈ s, lam (bad ω j)) ≤ ENNReal.ofReal c * lam Set.univ := by
    rw [hsum]
    exact hint
  have hsum_ne_top : (∑ j ∈ s, lam (bad ω j)) ≠ ∞ := by
    exact ENNReal.sum_ne_top.2 (fun j hj => measure_ne_top lam _)
  have hprod_ne_top : ENNReal.ofReal c * lam Set.univ ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top lam _)
  have hreal := (ENNReal.toReal_le_toReal hsum_ne_top hprod_ne_top).2 hsum_le
  rw [ENNReal.toReal_sum (by finiteness)] at hreal
  simpa [s, c, ENNReal.toReal_ofReal hc, ENNReal.toReal_mul] using hreal

end SubdiffusiveProcess.Paper
