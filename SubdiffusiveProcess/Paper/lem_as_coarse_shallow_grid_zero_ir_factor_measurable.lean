module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_oscillation_moments
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set Metric ProbabilityTheory TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The actual infrared-free factor is measurable without assuming that the
zero field satisfies the model's infrared characterization. -/
theorem lem_as_coarse_shallow_grid_zero_ir_factor_measurable
    (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (N k : ℕ) (y : SpatialCoordinates d) :
    let G0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun k ω x => ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
    let s0 : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun N k ω x =>
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (G0 k ω x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
    let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
    let oscSet0 : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
      fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
        ∃ x' ∈ Metric.closedBall y (3 * R k),
          v = |G0 k ω x - G0 k ω x'|}
    let osc0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun k ω y => sSup (oscSet0 k ω y)
    AEStronglyMeasurable
      (fun ω => Real.exp (osc0 k ω y) *
        (s0 N k ω y + (s0 N k ω y)⁻¹))
      (chaosSampleLaw M).toMeasure := by
  intro G0 s0 R oscSet0 osc0
  let r : ℝ := 3 * R k
  have hr : 0 < r := by
    dsimp [r, R]
    positivity
  have hUopen : IsOpen (Metric.ball y r ×ˢ Metric.ball y r) :=
    isOpen_ball.prod isOpen_ball
  let U : Set (SpatialCoordinates d × SpatialCoordinates d) :=
    Metric.ball y r ×ˢ Metric.ball y r
  let Kpair : Set (SpatialCoordinates d × SpatialCoordinates d) :=
    Metric.closedBall y r ×ˢ Metric.closedBall y r
  have hUsub : U ⊆ Kpair := by
    intro z hz
    exact ⟨mem_ball.mp hz.1 |>.le, mem_ball.mp hz.2 |>.le⟩
  have hKsub : Kpair ⊆ closure U := by
    intro z hz
    change z ∈ closure (Metric.ball y r ×ˢ Metric.ball y r)
    rw [closure_prod_eq, closure_ball y hr.ne']
    exact ⟨hz.1, hz.2⟩
  have hKne : Kpair.Nonempty := by
    exact ⟨(y, y), ⟨Metric.mem_closedBall_self hr.le, Metric.mem_closedBall_self hr.le⟩⟩
  let F : BilateralField d → SpatialCoordinates d × SpatialCoordinates d → ℝ :=
    fun ω z => |G0 k ω z.1 - G0 k ω z.2|
  have hFcont : ∀ ω, Continuous (F ω) := by
    intro ω
    have hsum : Continuous (fun x : SpatialCoordinates d =>
        ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x) :=
      continuous_finsetSum (Finset.range k) (by
        intro j hj
        exact (ω (-(j : ℤ))).continuous)
    exact continuous_abs.comp ((hsum.comp continuous_fst).sub (hsum.comp continuous_snd))
  have hFmeas : ∀ z : SpatialCoordinates d × SpatialCoordinates d,
      Measurable (fun ω => F ω z) := by
    intro z
    have hsum1 : Measurable (fun ω : BilateralField d =>
        ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) z.1) :=
      Finset.measurable_sum (Finset.range k) (by
        intro j hj
        have heval : Measurable (fun ω : BilateralField d =>
            ω (-(j : ℤ))) := measurable_pi_apply _
        simpa only [Function.comp_def] using!
          ((continuous_eval_const z.1).measurable.comp heval))
    have hsum2 : Measurable (fun ω : BilateralField d =>
        ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) z.2) :=
      Finset.measurable_sum (Finset.range k) (by
        intro j hj
        have heval : Measurable (fun ω : BilateralField d =>
            ω (-(j : ℤ))) := measurable_pi_apply _
        simpa only [Function.comp_def] using!
          ((continuous_eval_const z.2).measurable.comp heval))
    have hsub : Measurable (fun ω => G0 k ω z.1 - G0 k ω z.2) := by
      dsimp [G0]
      exact (hsum1).sub (hsum2)
    exact measurable_abs.comp hsub
  have hAbdd : ∀ ω, BddAbove {v : ℝ | ∃ z ∈ Kpair, v = F ω z} := by
    intro ω
    have hcompact : IsCompact Kpair := by
      dsimp [Kpair]
      exact (isCompact_closedBall y r).prod (isCompact_closedBall y r)
    have himage := hcompact.bddAbove_image (hFcont ω).continuousOn
    apply himage.mono
    rintro v ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  have hSupOpen : Measurable (fun ω =>
      sSup {v : ℝ | ∃ z ∈ U, v = F ω z}) :=
    aux_reference_oscillation_moments_measurable_sup_open
      hUopen hFcont hFmeas (by
        intro ω
        have himage := hAbdd ω
        exact himage.mono (by
          rintro v ⟨z, hz, rfl⟩
          exact ⟨z, hUsub hz, rfl⟩))
  have hSupMeas : Measurable (fun ω =>
      sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = F ω (x, x')}) := by
    have heq : (fun ω => sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = F ω (x, x')}) =
        (fun ω => sSup {v : ℝ | ∃ z ∈ U, v = F ω z}) := by
      funext ω
      calc
        sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
            ∃ x' ∈ Metric.closedBall y r, v = F ω (x, x')} =
            sSup {v : ℝ | ∃ z ∈ Kpair, v = F ω z} := by
              apply congrArg sSup
              ext v
              constructor
              · rintro ⟨x, hx, x', hx', hv⟩
                exact ⟨(x, x'), ⟨hx, hx'⟩, hv⟩
              · rintro ⟨z, hz, hv⟩
                exact ⟨z.1, hz.1, z.2, hz.2, hv⟩
        _ = sSup {v : ℝ | ∃ z ∈ U, v = F ω z} :=
          aux_reference_oscillation_moments_sup_closed_eq_sup_open
            hUsub hKsub hKne (hFcont ω) (hAbdd ω)
    rw [heq]
    exact hSupOpen
  have hOscMeas : Measurable (fun ω => osc0 k ω y) := by
    have : (fun ω => sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = |G0 k ω x - G0 k ω x'|}) =
        (fun ω => sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
          ∃ x' ∈ Metric.closedBall y r, v = F ω (x, x')}) := by
      funext ω
      simp [F]
    have hmeas : Measurable (fun ω => sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = |G0 k ω x - G0 k ω x'|}) := by
      rw [this]
      exact hSupMeas
    simpa [osc0, oscSet0, r] using hmeas
  have hExpMeas : Measurable (fun ω => Real.exp (osc0 k ω y)) :=
    hOscMeas.exp
  have hs0Meas : Measurable (fun ω => s0 N k ω y) := by
    dsimp [s0, G0]
    have hsum : Measurable (fun (ω' : BilateralField d) =>
        ∑ j ∈ Finset.range k, (ω' (-(j : ℤ))) y) :=
      Finset.measurable_sum (Finset.range k) (by
        intro j hj
        have heval : Measurable (fun (ω' : BilateralField d) =>
            ω' (-(j : ℤ))) := measurable_pi_apply _
        simpa only [Function.comp_def] using!
          ((continuous_eval_const y).measurable.comp heval))
    have hexp_arg : Measurable (fun (ω' : BilateralField d) =>
        (∑ j ∈ Finset.range k, (ω' (-(j : ℤ))) y) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) :=
      hsum.sub measurable_const
    have hexp : Measurable (fun (ω' : BilateralField d) =>
        Real.exp ((∑ j ∈ Finset.range k, (ω' (-(j : ℤ))) y) -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) :=
      hexp_arg.exp
    have hcoef : Measurable (fun (_ : BilateralField d) =>
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) :=
      measurable_const
    exact hcoef.mul hexp
  have hSumMeas : Measurable (fun ω => s0 N k ω y + (s0 N k ω y)⁻¹) := by
    have hinv : Measurable (fun ω => (s0 N k ω y)⁻¹) :=
      Measurable.inv hs0Meas
    exact hs0Meas.add hinv
  have hProdMeas : Measurable (fun ω =>
      Real.exp (osc0 k ω y) * (s0 N k ω y + (s0 N k ω y)⁻¹)) :=
    hExpMeas.mul hSumMeas
  exact hProdMeas.aestronglyMeasurable

end SubdiffusiveProcess.Paper

