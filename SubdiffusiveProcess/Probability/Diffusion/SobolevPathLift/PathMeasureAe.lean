module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.L2Bookkeeping

@[expose] public section

/-!
# almost-everywhere plumbing for the path measure

Three facts about `pathMeasure d = ∫ₓ P_x dx` that the assembly of `sobolevPathLiftGoal` needs,
and which are pure plumbing:

* `ae_laplacianLaw_of_ae_pathMeasure` converts a `pathMeasure`-a.e. statement about a measurable
  event into the goal's iterated form `∀ᵐ x ∂volume, ∀ᵐ ω ∂P_x`.  This is the only place the
  `Measure.bind` structure is used, and it is where the two-parameter `(x, ω)` framing
  collapses to a single measure.
* `lintegral_pathMeasure_eval`: for **every** time `t` (including `t = 0`), the law of `ω ↦ ω t`
  under the path measure is Lebesgue measure.  For `t > 0` this is `lintegral_path_eval_invariant`
  (Gaussian stationarity); at `t = 0` the kernel is a Dirac mass and the `x`-integral supplies the
  same answer, so no positivity hypothesis survives into the statement.
* `ae_eval_zero_eq`: under `P_x` the path starts at `x` almost surely -- the hypothesis
  `omega 0 ∈ U` of `zero_at_exit_of_tendstoUniformlyOn`.
-/

set_option autoImplicit false

open Filter Homogenization MeasureTheory MarkovProcess ProbabilityTheory Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

variable {d : ℕ}

/-- A `pathMeasure`-a.e. statement about a measurable event is the goal's iterated `a.e. x, a.e. ω`
statement. -/
theorem ae_laplacianLaw_of_ae_pathMeasure {s : Set (ContinuousPath (Vec d))}
    (hs : MeasurableSet s) (h : ∀ᵐ ω ∂(pathMeasure d), ω ∈ s) :
    ∀ᵐ x ∂volume, ∀ᵐ ω ∂(laplacianContinuousLaw d x), ω ∈ s := by
  rw [ae_iff] at h
  have hb : (pathMeasure d) sᶜ = ∫⁻ x, (laplacianContinuousLaw d x) sᶜ ∂volume :=
    Measure.bind_apply hs.compl (laplacianContinuousLaw d).measurable.aemeasurable
  have h' : (pathMeasure d) sᶜ = 0 := h
  rw [hb] at h'
  have h0 : ∀ᵐ x ∂volume, (laplacianContinuousLaw d x) sᶜ = 0 := by
    refine (lintegral_eq_zero_iff' ?_).mp h'
    exact ((laplacianContinuousLaw d).measurable_coe hs.compl).aemeasurable
  filter_upwards [h0] with x hx
  rw [ae_iff]
  exact hx

/-- For **every** time the law of `ω ↦ ω t` under the path measure is Lebesgue measure. -/
theorem lintegral_pathMeasure_eval {G : Vec d → ℝ≥0∞} (hG : Measurable G) (t : ℝ≥0) :
    (∫⁻ ω, G (ω t) ∂(pathMeasure d)) = ∫⁻ y, G y ∂volume := by
  have hmeas : Measurable fun ω : ContinuousPath (Vec d) => G (ω t) :=
    hG.comp (ContinuousPath.measurable_coordinateProcess t)
  rw [lintegral_pathMeasure hmeas]
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
  · have ht : t = 0 := h.symm
    subst ht
    simp only [lintegral_path_eval_zero hG]
  · exact lintegral_path_eval_invariant (by exact_mod_cast h) hG

/-! ## The starting point -/

theorem map_eval_zero (x : Vec d) :
    (laplacianContinuousLaw d x).map (fun ω : ContinuousPath (Vec d) => ω (0 : ℝ≥0))
      = Measure.dirac x := by
  have heval : Measurable fun w : ContinuousPath (Vec d) => w (0 : ℝ≥0) :=
    ContinuousPath.measurable_coordinateProcess 0
  have h1 : (laplacianContinuousLaw d x).map (fun ω : ContinuousPath (Vec d) => ω (0 : ℝ≥0))
      = ((laplacianContinuousLaw d).map
        (fun w : ContinuousPath (Vec d) => w (0 : ℝ≥0))) x :=
    (Kernel.map_apply _ heval x).symm
  rw [h1, laplacianContinuousLaw_map_eval (0 : ℝ≥0)]
  show ((laplacianSemigroup d).kernel 0) x = Measure.dirac x
  rw [(laplacianSemigroup d).kernel_zero, Kernel.id_apply]

/-- Under `P_x` the path starts at `x` almost surely. -/
theorem ae_eval_zero_eq (x : Vec d) :
    ∀ᵐ ω ∂(laplacianContinuousLaw d x), ω (0 : ℝ≥0) = x := by
  have heval : Measurable fun w : ContinuousPath (Vec d) => w (0 : ℝ≥0) :=
    ContinuousPath.measurable_coordinateProcess 0
  have hset : MeasurableSet {z : Vec d | z ≠ x} := (measurableSet_singleton x).compl
  rw [ae_iff]
  have hpre : {ω : ContinuousPath (Vec d) | ¬ (ω (0 : ℝ≥0) = x)}
      = (fun w : ContinuousPath (Vec d) => w (0 : ℝ≥0)) ⁻¹' {z : Vec d | z ≠ x} := rfl
  rw [hpre, ← Measure.map_apply heval hset, map_eval_zero, Measure.dirac_apply' _ hset]
  simp

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
