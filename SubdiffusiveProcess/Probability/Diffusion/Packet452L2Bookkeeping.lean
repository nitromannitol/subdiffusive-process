module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452PathLiftConstruction

@[expose] public section

/-!
#  moving between `eLpNorm`, `lintegral` and Bochner squares

`maximalEstimateGoal` is stated with **Bochner** integrals of squares on its right-hand side, while
`global_sobolev_approximation` delivers its convergences as `eLpNorm … 2 volume`, an `ℝ≥0∞`
quantity.  This file is the dictionary between them, together with the two small `ℝ≥0∞` facts the
Fatou step of B8 §2.3 Step 8 needs.

The dictionary is deliberately phrased so that **no finiteness ever has to be carried**:
`lintegral_ofReal_sq_eq_eLpNorm_sq` is an unconditional identity (it is just the definition of
`eLpNorm` unfolded), and only the passage to the Bochner integral asks for integrability -- which,
for the continuous compactly supported functions this collection uses, is automatic.

`maximalEstimate_sub` is `maximalEstimateGoal` applied to a difference of two `C²_c` functions with
the derivative of the difference already split; `maximalEstimate_approxDiff`
(`Packet452PathLift.lean`) is its instance at two members of `H10Function.approx`.
-/

set_option autoImplicit false

open Filter Homogenization MeasureTheory MarkovProcess Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-! ## `eLpNorm` versus integrals of squares -/

/-- The unconditional identity: `∫⁻ ofReal (f²) = ‖f‖₂²`.  No measurability, no finiteness. -/
theorem lintegral_ofReal_sq_eq_eLpNorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) :
    (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ) = (SubdiffusiveProcess.RawLp.eLpNorm f 2 μ) ^ 2 := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (p := 2) (by norm_num) (by norm_num)]
  have h1 : ∀ x : α, ‖f x‖ₑ ^ ((2 : ℝ≥0∞).toReal) = ENNReal.ofReal ((f x) ^ 2) := by
    intro x
    rw [ENNReal.toReal_ofNat, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  simp only [h1]
  rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

theorem ofReal_integral_sq_eq_eLpNorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable (fun x => (f x) ^ 2) μ) :
    ENNReal.ofReal (∫ x, (f x) ^ 2 ∂μ) = (SubdiffusiveProcess.RawLp.eLpNorm f 2 μ) ^ 2 := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall fun x => sq_nonneg _), lintegral_ofReal_sq_eq_eLpNorm_sq]

theorem ofReal_integral_sum_sq_eq_sum_eLpNorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : Fin d → α → ℝ} (hg : ∀ i, Integrable (fun x => (g i x) ^ 2) μ) :
    ENNReal.ofReal (∫ x, ∑ i : Fin d, (g i x) ^ 2 ∂μ)
      = ∑ i : Fin d, (SubdiffusiveProcess.RawLp.eLpNorm (g i) 2 μ) ^ 2 := by
  rw [integral_finsetSum _ fun i _ => hg i,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg fun x => sq_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => ofReal_integral_sq_eq_eLpNorm_sq (hg i)

/-! ## Integrability of the squares that occur -/

theorem integrable_sq_of_continuous_of_hasCompactSupport {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {f : α → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x => (f x) ^ 2) μ := by
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  simpa only [pow_two] using! (hfc.mul_right : HasCompactSupport (f * f))

/-- The coordinate derivatives of a `C²` function with compact support are continuous with compact
support. -/
theorem continuous_fderiv_apply {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin d) :
    Continuous fun x => fderiv ℝ f x (Pi.single i 1) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem hasCompactSupport_fderiv_apply {f : Vec d → ℝ}
    (hfc : HasCompactSupport f) (i : Fin d) :
    HasCompactSupport fun x => fderiv ℝ f x (Pi.single i 1) :=
  (hfc.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) rfl

/-! ## The `ℝ≥0∞` Fatou bookkeeping -/

theorem liminf_le_of_le_of_tendsto {F G : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (h : ∀ k, F k ≤ G k) (hG : Tendsto G atTop (𝓝 L)) :
    liminf F atTop ≤ L := by
  calc liminf F atTop ≤ liminf G atTop := liminf_le_liminf (.of_forall h)
    _ = L := hG.liminf_eq

/-! ## The maximal estimate on a difference -/

/-- `maximalEstimateGoal` applied to `f − g`, with the derivative of the difference split.
`maximalEstimate_approxDiff` is its instance at two members of `H10Function.approx`. -/
theorem maximalEstimate_sub (hmax : maximalEstimateGoal d) {f g : Vec d → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (T : ℝ≥0) :
    (∫⁻ x, ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
        ENNReal.ofReal ((f (ω t) - g (ω t)) ^ 2)) ∂(laplacianContinuousLaw d x) ∂volume)
      ≤ ENNReal.ofReal (32 * ((∫ x, (f x - g x) ^ 2)
          + (T : ℝ) * ∫ x, ∑ i : Fin d,
            (fderiv ℝ f x (Pi.single i 1) - fderiv ℝ g x (Pi.single i 1)) ^ 2)) := by
  have hdf : ∀ x : Vec d, DifferentiableAt ℝ f x := fun x =>
    (hf.differentiable (by norm_num)).differentiableAt
  have hdg : ∀ x : Vec d, DifferentiableAt ℝ g x := fun x =>
    (hg.differentiable (by norm_num)).differentiableAt
  have hgrad : ∀ (x : Vec d) (i : Fin d),
      fderiv ℝ (fun y => f y - g y) x (Pi.single i 1)
        = fderiv ℝ f x (Pi.single i 1) - fderiv ℝ g x (Pi.single i 1) := by
    intro x i
    rw [((hdf x).hasFDerivAt.fun_sub (hdg x).hasFDerivAt).fderiv]
    rfl
  have h := hmax (fun x => f x - g x) (hf.sub hg) (hfc.sub hgc) T
  simpa only [hgrad] using h

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
