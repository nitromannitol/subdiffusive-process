module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452MaximalSeed

@[expose] public section




set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- The free Gaussian kernel is symmetric in its two space arguments. -/
theorem laplacianDensity_symm (t : ℝ) (x y : Vec d) :
    laplacianDensity t x y = laplacianDensity t y x := by
  unfold laplacianDensity gaussianPDFReal
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show (y i - x i) ^ 2 = (x i - y i) ^ 2 by ring]

/-- Integrating the free Gaussian kernel in its **starting** point gives one: the mass that
`isConservative_laplacianSemigroup` supplies in the terminal point, transported by symmetry. -/
theorem lintegral_laplacianDensity_start {t : ℝ} (ht : 0 < t) (y : Vec d) :
    ∫⁻ x, ENNReal.ofReal (laplacianDensity t x y) ∂volume = 1 := by
  have hsymm : ∀ x : Vec d, laplacianDensity t x y = laplacianDensity t y x :=
    fun x => laplacianDensity_symm t x y
  simp only [hsymm]
  have hw := laplacianSemigroup_eq_withDensity ht y
  have hone : laplacianSemigroup d (Real.toNNReal t) y univ = 1 :=
    isConservative_laplacianSemigroup (Real.toNNReal t) y
  rw [hw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hone
  exact hone

/-- **Lebesgue measure is invariant for the Brownian semigroup.**  This is the "Gaussian
stationarity" input of `ledger/reports/P-452-agent1.md` §2.2: symmetry of the kernel turns the
conservativity in the terminal point into invariance of the infinite initial measure. -/
theorem lintegral_laplacianSemigroup_invariant {t : ℝ} (ht : 0 < t) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, (∫⁻ y, f y ∂(laplacianSemigroup d (Real.toNNReal t) x)) ∂volume
      = ∫⁻ y, f y ∂volume := by
  have hdens : ∀ x : Vec d, Measurable fun y : Vec d => ENNReal.ofReal (laplacianDensity t x y) :=
    fun x => ((measurable_uncurry_laplacianDensity (d := d) t).of_uncurry_left (x := x)).ennreal_ofReal
  have hrw : ∀ x : Vec d, (∫⁻ y, f y ∂(laplacianSemigroup d (Real.toNNReal t) x))
      = ∫⁻ y, ENNReal.ofReal (laplacianDensity t x y) * f y ∂volume := by
    intro x
    rw [laplacianSemigroup_eq_withDensity ht x,
      lintegral_withDensity_eq_lintegral_mul _ (hdens x) hf]
    rfl
  simp only [hrw]
  have hjoint : Measurable fun p : Vec d × Vec d =>
      ENNReal.ofReal (laplacianDensity t p.1 p.2) * f p.2 :=
    ((measurable_uncurry_laplacianDensity (d := d) t).ennreal_ofReal).mul (hf.comp measurable_snd)
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  have hinner : ∀ y : Vec d,
      (∫⁻ x, ENNReal.ofReal (laplacianDensity t x y) * f y ∂volume) = f y := by
    intro y
    have hmy : Measurable fun x : Vec d => ENNReal.ofReal (laplacianDensity t x y) :=
      ((measurable_uncurry_laplacianDensity (d := d) t).of_uncurry_right (y := y)).ennreal_ofReal
    rw [lintegral_mul_const _ hmy, lintegral_laplacianDensity_start ht y, one_mul]
  simp only [hinner]

/-- **Gaussian stationarity in path form.**  For every positive time, the law of `ω ↦ ω t` under
`∫ P_x(·) dx` is Lebesgue measure itself. -/
theorem lintegral_path_eval_invariant {t : ℝ≥0} (ht : 0 < (t : ℝ)) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, (∫⁻ w, f (w t) ∂(laplacianContinuousLaw d x)) ∂volume = ∫⁻ y, f y ∂volume := by
  have heval : Measurable fun w : ContinuousPath (Vec d) => w t :=
    ContinuousPath.measurable_coordinateProcess t
  have hstep : ∀ x : Vec d, (∫⁻ w, f (w t) ∂(laplacianContinuousLaw d x))
      = ∫⁻ y, f y ∂(laplacianSemigroup d t x) := by
    intro x
    rw [← laplacianContinuousLaw_map_eval t, Kernel.map_apply _ heval,
      lintegral_map hf heval]
  simp only [hstep]
  have hcast : Real.toNNReal (t : ℝ) = t := Real.toNNReal_coe
  rw [← hcast]
  exact lintegral_laplacianSemigroup_invariant ht hf

/-! ## Alignment with the report's exact targets -/

/-- The exact open target `maximalEstimateGoal`, copied from `ledger/reports/P-452-agent1.md` §4.
The supremum is an `ℝ≥0∞` `iSup` over `t ≤ T`, so no measurability of a real supremum is needed;
the outer integral is a `lintegral` against `volume`, which is infinite in positive dimension. -/
def maximalEstimateGoal (d : ℕ) : Prop :=
  ∀ phi : Vec d → ℝ, ContDiff ℝ 2 phi → HasCompactSupport phi → ∀ T : ℝ≥0,
    (∫⁻ x, ∫⁻ omega, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
      ENNReal.ofReal ((phi (omega t)) ^ 2)) ∂laplacianContinuousLaw d x ∂volume) ≤
      ENNReal.ofReal (32 * ((∫ x, (phi x) ^ 2) + (T : ℝ) *
        ∫ x, ∑ i : Fin d, (fderiv ℝ phi x (Pi.single i 1)) ^ 2))

/-- **Alignment, energy.**  The target's energy integrand is literally `energyDensity`: the
coordinate sum, not the square of the ambient (sup) norm of the gradient. -/
theorem maximalEstimateGoal_energy_eq (phi : Vec d → ℝ) :
    (∫ x, ∑ i : Fin d, (fderiv ℝ phi x (Pi.single i (1 : ℝ))) ^ 2)
      = ∫ x, energyDensity phi x := rfl

/-- **Alignment, Laplacian.**  The Laplacian of `mollifiedVariationalGoal` is literally
`fullLaplacian`: the full Laplacian, matching `generator_laplacianSemigroup`. -/
theorem mollifiedVariationalGoal_laplacian_eq (phi : Vec d → ℝ) (x : Vec d) :
    (∑ i : Fin d, iteratedFDeriv ℝ 2 phi x ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)])
      = fullLaplacian phi x := rfl

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
