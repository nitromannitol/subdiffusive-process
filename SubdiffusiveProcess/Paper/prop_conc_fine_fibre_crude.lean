module

public import SubdiffusiveProcess.Paper.prop_conc_fine_fibre_es

@[expose] public section

/-! The crude fibre estimate of the fine-layer step (scales at most a fixed number of octaves below the cell): the
relative response `θ_X(y - x0)` of a layer sample is within `C G e^{CG} (M - m)` of the response of the
unperturbed pair, `G = S y + S x0` the layer norms (relative variation with `B = q`), so the resampling
difference is at most twice that in `L^p(μ)`.  No growth constant, grid or Efron--Stein is used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Envelope of the crude estimate. -/
def aux_prop_conc_fine_fibre_crude_env (CL gap s s0 : ℝ) : ℝ :=
  CL * (s + s0) * Real.exp (CL * (s + s0)) * gap

theorem prop_conc_fine_fibre_crude (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    ∃ CL : ℝ, 0 < CL ∧
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {m M : ℝ}
      (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Set.Icc m M →
      ∀ p ∈ aux_prop_conc_pair_data_slopes d,
      ∀ (x0 : C(SpatialCoordinates d, ℝ))
        (μ : Measure C(SpatialCoordinates d, ℝ)) [IsProbabilityMeasure μ],
      ∀ (f : C(SpatialCoordinates d, ℝ) → ℝ), Measurable f →
        (∀ᵐ y ∂μ, f y = aux_prop_conc_pair_data_theta X c p (fun x => y x - x0 x)) →
      ∀ (pe : ℝ), 1 ≤ pe →
        eLpNorm (fun yy : C(SpatialCoordinates d, ℝ) × C(SpatialCoordinates d, ℝ) => f yy.1 - f yy.2)
            (ENNReal.ofReal pe) (μ.prod μ) ≤
          2 * eLpNorm (fun y => aux_prop_conc_fine_fibre_crude_env CL (M - m)
              (aux_prop_conc_fine_fibre_det_S z r y) (aux_prop_conc_fine_fibre_det_S z r x0))
            (ENNReal.ofReal pe) μ := by
  obtain ⟨-, ⟨CL, hCL, hlip⟩, -, -⟩ := prop_conc_fine_pair_step C0 hC0 d
  refine ⟨CL, hCL, ?_⟩
  intro _ _ Q z r hr m M X c hc p hp x0 μ _ f hf hfX pe hpe
  set a₀ : ℝ := aux_prop_conc_pair_data_theta X c p (fun _ => 0) with ha₀
  have hfour := aux_prop_conc_fine_fibre_es_fourterm μ f (fun _ => a₀) a₀ hf measurable_const pe hpe
  have h2 : eLpNorm (fun _ : C(SpatialCoordinates d, ℝ) => a₀ - a₀) (ENNReal.ofReal pe) μ = 0 := by
    simp
  rw [h2] at hfour
  simp only [mul_zero, add_zero] at hfour
  refine hfour.trans ?_
  gcongr
  have hm : AEStronglyMeasurable (fun y => f y - a₀) μ :=
    hf.aestronglyMeasurable.sub aestronglyMeasurable_const
  refine eLpNorm_mono_ae hm ?_
  filter_upwards [hfX] with y hy
  set S := aux_prop_conc_fine_fibre_det_S z r y
  set S0 := aux_prop_conc_fine_fibre_det_S z r x0
  have hS0 := aux_prop_conc_fine_fibre_det_S_nonneg z r y
  have hS00 := aux_prop_conc_fine_fibre_det_S_nonneg z r x0
  have hgap : 0 ≤ M - m := sub_nonneg.mpr X.hmM
  have hwm := aux_prop_conc_fine_fibre_det_wY_measurable z r hr x0 y
  have hK := aux_prop_conc_fine_fibre_det_wY_bound z r hr x0 y
  have h1 := hlip X c hc p hp _ (fun _ => 0) hwm measurable_const (S + S0) hK
    (fun x => by simp; linarith) (S + S0) (by linarith)
    (fun x hx => by
      have := hK x
      simpa using this)
  have hθ : aux_prop_conc_pair_data_theta X c p (fun x => y x - x0 x) =
      aux_prop_conc_pair_data_theta X c p (aux_prop_conc_fine_fibre_det_wY z r hr x0 y) := by
    refine aux_prop_conc_fine_pair_step_theta_congr X c p _ _ (fun x hx => ?_)
    simp [aux_prop_conc_fine_fibre_det_wY, Set.indicator_of_mem hx]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hy, hθ]
  have hn : 0 ≤ aux_prop_conc_fine_fibre_crude_env CL (M - m) S S0 := by
    unfold aux_prop_conc_fine_fibre_crude_env; positivity
  rw [abs_of_nonneg hn]
  unfold aux_prop_conc_fine_fibre_crude_env
  calc _ ≤ CL * (S + S0) * Real.exp (CL * (S + S0)) * (M - m) := h1
    _ = _ := rfl

end
end SubdiffusiveProcess.Paper
