module

public import SubdiffusiveProcess.Paper.in_stopped_passage

@[expose] public section

/-! Supports: mfd_lem_killing.
Internal fixed-test stopping identification. Only the constant source needs
uniform boundary control; the selected test only needs pointwise convergence.
This minimizes the common-subsequence work needed by the source application.
-/
open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal LevyProkhorov
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
theorem aux_mfd_lem_killing_identify_one_test {d : ℕ} (z : SpatialCoordinates d) {ρ : ℝ}
    (hρ : 0 < ρ) {lam : ℝ} (hlam : 0 < lam)
    (μN : ℕ → SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (μ : ProbabilityMeasure (DiffusionPath d))
    (hrestart : ∀ (N : ℕ) (x : SpatialCoordinates d) (t : ℝ≥0) (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t] A →
        ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
          (∫⁻ p in A, F (ContinuousPath.shift t p) ∂(μN N x : Measure _)) =
            ∫⁻ p in A, ∫⁻ q, F q ∂(μN N (p t) : Measure _) ∂(μN N x : Measure _))
    (Rone : SpatialCoordinates d → ℝ)
    (hRc : ContinuousOn Rone (Metric.closedBall z ρ))
    (hR0 : ∀ y ∈ Metric.sphere z ρ, Rone y = 0)
    (hunifone : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ y ∈ Metric.closedBall z ρ,
        |∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam
            (BoundedContinuousFunction.const _ 1) p ∂(μN N y : Measure _) - Rone y| < ε)
    (x : SpatialCoordinates d) (hx : x ∈ Metric.ball z ρ)
    (hμ : Tendsto (fun j => μN j x) atTop (𝓝 μ))
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (Rf : ℝ)
    (hLf : Tendsto (fun N => ∫ p,
      aux_in_stopped_passage_occ (Metric.ball z ρ) lam f p ∂(μN N x : Measure _))
      atTop (𝓝 Rf)) :
    Rf = ∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam f p ∂(μ : Measure _) := by
  have hQ : IsOpen (Metric.ball z ρ) := Metric.isOpen_ball
  have hxcl : x ∈ Metric.closedBall z ρ := Metric.ball_subset_closedBall hx
  have hLone : Tendsto (fun N => ∫ p,
      aux_in_stopped_passage_occ (Metric.ball z ρ) lam
        (BoundedContinuousFunction.const _ 1) p ∂(μN N x : Measure _))
      atTop (𝓝 (Rone x)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N0, hN0⟩ := hunifone ε hε
    exact ⟨N0, fun N hN => by rw [Real.dist_eq]; exact hN0 N hN x hxcl⟩
  set one : BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
    BoundedContinuousFunction.const _ 1 with hone
  set c : ℝ := ‖f‖ with hc
  set g₁ : BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
    f + BoundedContinuousFunction.const _ c with hg₁
  set g₂ : BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
    BoundedContinuousFunction.const _ c - f with hg₂
  have hfb : ∀ y, |f y| ≤ c := fun y => by
    rw [← Real.norm_eq_abs]
    exact f.norm_coe_le_norm y
  have hg₁nn : ∀ y, 0 ≤ g₁ y := fun y => by
    simp only [hg₁, BoundedContinuousFunction.add_apply, BoundedContinuousFunction.const_apply]
    linarith [(abs_le.mp (hfb y)).1]
  have hg₂nn : ∀ y, 0 ≤ g₂ y := fun y => by
    simp only [hg₂, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply]
    linarith [(abs_le.mp (hfb y)).2]
  have honenn : ∀ y, 0 ≤ one y := fun y => by
    simp only [hone, BoundedContinuousFunction.const_apply]
    exact zero_le_one
  have hg₁lin : ∀ y, g₁ y = 1 * f y + c * one y := fun y => by
    simp only [hg₁, hone, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.const_apply]
    ring
  have hg₂lin : ∀ y, g₂ y = c * one y + (-1) * f y := fun y => by
    simp only [hg₂, hone, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.const_apply]
    ring
  have hlim1 : Tendsto (fun N => ∫ p,
      aux_in_stopped_passage_occ (Metric.ball z ρ) lam g₁ p ∂(μN N x : Measure _))
      atTop (𝓝 (1 * Rf + c * Rone x)) := by
    refine ((hLf.const_mul 1).add (hLone.const_mul c)).congr fun N => ?_
    exact (aux_in_stopped_passage_integral_occ_lin _ hQ hlam g₁ f one 1 c hg₁lin _).symm
  have hlim2 : Tendsto (fun N => ∫ p,
      aux_in_stopped_passage_occ (Metric.ball z ρ) lam g₂ p ∂(μN N x : Measure _))
      atTop (𝓝 (c * Rone x + (-1) * Rf)) := by
    refine ((hLone.const_mul c).add (hLf.const_mul (-1))).congr fun N => ?_
    exact (aux_in_stopped_passage_integral_occ_lin _ hQ hlam g₂ one f c (-1) hg₂lin _).symm
  -- the two halves
  have hA₁ := aux_in_stopped_passage_lower _ hQ hlam g₁ hg₁nn hμ hlim1
  have hA₂ := aux_in_stopped_passage_lower _ hQ hlam g₂ hg₂nn hμ hlim2
  have hB := aux_in_stopped_passage_upper_one z hρ hlam μN μ hrestart Rone hRc hR0
    hunifone id strictMono_id x hx hμ
  rw [aux_in_stopped_passage_integral_occ_lin _ hQ hlam g₁ f one 1 c hg₁lin] at hA₁
  rw [aux_in_stopped_passage_integral_occ_lin _ hQ hlam g₂ one f c (-1) hg₂lin] at hA₂
  have hc0 : 0 ≤ c := norm_nonneg f
  nlinarith

end Paper
