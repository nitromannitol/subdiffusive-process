module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.PathMeasureAe

@[expose] public section

/-!
# the approximating sequence with a geometric rate

  §2.3, Step 2
extracts a subsequence "diagonally in `n`" so that `e_{n_k,n_{k+1}}(T) ≤ 4^{-k}` **for the fixed
`T`**, and Step 3 then diagonalises over the horizons `T = 1, 2, 3, …`.

**Neither extraction is needed.**  `maximalEstimateGoal`'s right-hand side is
`32(‖φ‖₂² + T · E(φ))`, in which the horizon multiplies only the energy term.  So a subsequence
chosen once, with a geometric rate in the `H¹` graph norm *alone*, controls every horizon
simultaneously -- the horizon enters as a factor `(1 + T d)` in the constant, and the geometric
factor `16^{-k}` beats the weight `4^k` of `ae_tsum_lt_top_of_lintegral_sq` with room to spare.

`RateApprox` packages such a sequence: `C^∞_c` functions supported in `U`, converging to
`u.zeroExtension` and (coordinatewise) to `u.zeroExtensionGrad` at rate `4^{-k}`.
`exists_rateApprox` produces one from `global_sobolev_approximation`.
-/

set_option autoImplicit false

open Filter Homogenization MeasureTheory MarkovProcess Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

variable {d : ℕ}

/-! ## A triangle inequality for `eLpNorm` of differences -/

theorem eLpNorm_sub_le_add {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g h : α → ℝ}
    (_hf : AEStronglyMeasurable f μ) (_hg : AEStronglyMeasurable g μ)
    (_hh : AEStronglyMeasurable h μ) :
    eLpNorm (fun x => f x - g x) 2 μ
      ≤ eLpNorm (fun x => f x - h x) 2 μ + eLpNorm (fun x => h x - g x) 2 μ := by
  have hrw : (fun x => f x - g x) = (fun x => f x - h x) + (fun x => h x - g x) := by
    funext x; simp
  rw [hrw]
  exact eLpNorm_add_le one_le_two

/-! ## The rate-controlled approximating sequence -/

/-- A sequence of `C²`, compactly supported functions with `tsupport ⊆ U`, approximating
`u.zeroExtension` and its gradient in `L²(volume)` at the geometric rate `4^{-k}`. -/
structure RateApprox (d : ℕ) (U : Set (Vec d)) (u : H10Function U) where
  /-- the approximating functions, bundled as continuous maps -/
  fn : ℕ → C(Vec d, ℝ)
  /-- each is `C²` -/
  smooth : ∀ k, ContDiff ℝ 2 (fn k)
  /-- each has compact support -/
  compact : ∀ k, HasCompactSupport (fn k)
  /-- each is supported inside `U` -/
  support : ∀ k, tsupport (fn k) ⊆ U
  /-- the `L²` rate -/
  rate : ∀ k, eLpNorm (fun x => fn k x - u.zeroExtension x) 2 volume ≤ ((4 : ℝ≥0∞)⁻¹) ^ k
  /-- the coordinatewise gradient `L²` rate -/
  rateGrad : ∀ (k : ℕ) (i : Fin d),
    eLpNorm (fun x => fderiv ℝ (fn k) x (Pi.single i 1) - u.zeroExtensionGrad x i) 2 volume
      ≤ ((4 : ℝ≥0∞)⁻¹) ^ k

theorem exists_rateApprox {U : Set (Vec d)} (hU : IsOpen U) (u : H10Function U) :
    Nonempty (RateApprox d U u) := by
  obtain ⟨phi, hsmooth, hcompact, hsupp, hL2, hgrad⟩ := _root_.SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.ScopeChecks.global_sobolev_approximation hU u
  have hpos : ∀ k : ℕ, (0 : ℝ≥0∞) < ((4 : ℝ≥0∞)⁻¹) ^ k := fun k =>
    pos_iff_ne_zero.mpr (pow_ne_zero k (ENNReal.inv_ne_zero.mpr (by norm_num)))
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop,
      eLpNorm (fun x => phi n x - u.zeroExtension x) 2 volume < ((4 : ℝ≥0∞)⁻¹) ^ k ∧
      ∀ i : Fin d, eLpNorm (fun x => fderiv ℝ (phi n) x (Pi.single i 1)
        - u.zeroExtensionGrad x i) 2 volume < ((4 : ℝ≥0∞)⁻¹) ^ k := by
    intro k
    refine ((tendsto_order.1 hL2).2 _ (hpos k)).and ?_
    exact eventually_all.mpr fun i => (tendsto_order.1 (hgrad i)).2 _ (hpos k)
  choose n hn using fun k : ℕ => (hev k).exists
  refine ⟨{
    fn := fun k => ⟨phi (n k), (hsmooth (n k)).continuous⟩
    smooth := fun k => (hsmooth (n k)).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    compact := fun k => hcompact (n k)
    support := fun k => hsupp (n k)
    rate := fun k => (hn k).1.le
    rateGrad := fun k i => ((hn k).2 i).le }⟩

/-! ## Consequences of the rate -/

variable {U : Set (Vec d)} {u : H10Function U}

theorem RateApprox.aestronglyMeasurable (a : RateApprox d U u) (k : ℕ) :
    AEStronglyMeasurable (a.fn k) volume :=
  (a.fn k).continuous.aestronglyMeasurable

theorem RateApprox.aestronglyMeasurable_grad (a : RateApprox d U u) (k : ℕ) (i : Fin d) :
    AEStronglyMeasurable (fun x => fderiv ℝ (a.fn k) x (Pi.single i 1)) volume :=
  (continuous_fderiv_apply (a.smooth k) i).aestronglyMeasurable

/-- The increment bound: consecutive members differ by at most `2 · 4^{-k}` in `L²`. -/
theorem RateApprox.rate_sub (a : RateApprox d U u)
    (hz : AEStronglyMeasurable u.zeroExtension volume) (k : ℕ) :
    eLpNorm (fun x => a.fn (k + 1) x - a.fn k x) 2 volume ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ k := by
  have hsymm : eLpNorm (fun x => u.zeroExtension x - a.fn k x) 2 volume
      = eLpNorm (fun x => a.fn k x - u.zeroExtension x) 2 volume := by
    have h1 : (fun x => a.fn k x - u.zeroExtension x)
        = -(fun x => u.zeroExtension x - a.fn k x) := by funext x; simp
    rw [h1, eLpNorm_neg]
  calc eLpNorm (fun x => a.fn (k + 1) x - a.fn k x) 2 volume
      ≤ eLpNorm (fun x => a.fn (k + 1) x - u.zeroExtension x) 2 volume
        + eLpNorm (fun x => u.zeroExtension x - a.fn k x) 2 volume :=
        eLpNorm_sub_le_add (a.aestronglyMeasurable (k + 1)) (a.aestronglyMeasurable k) hz
    _ ≤ ((4 : ℝ≥0∞)⁻¹) ^ (k + 1) + ((4 : ℝ≥0∞)⁻¹) ^ k := by
        rw [hsymm]; exact add_le_add (a.rate (k + 1)) (a.rate k)
    _ ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ k := by
        rw [two_mul, pow_succ]
        refine add_le_add ?_ le_rfl
        calc ((4 : ℝ≥0∞)⁻¹) ^ k * (4 : ℝ≥0∞)⁻¹ ≤ ((4 : ℝ≥0∞)⁻¹) ^ k * 1 := by
              gcongr
              exact ENNReal.inv_le_one.mpr (by norm_num)
          _ = ((4 : ℝ≥0∞)⁻¹) ^ k := mul_one _

/-- The coordinatewise increment bound. -/
theorem RateApprox.rateGrad_sub (a : RateApprox d U u) (i : Fin d)
    (hz : AEStronglyMeasurable (fun x => u.zeroExtensionGrad x i) volume) (k : ℕ) :
    eLpNorm (fun x => fderiv ℝ (a.fn (k + 1)) x (Pi.single i 1)
      - fderiv ℝ (a.fn k) x (Pi.single i 1)) 2 volume ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ k := by
  have hsymm : eLpNorm (fun x => u.zeroExtensionGrad x i
        - fderiv ℝ (a.fn k) x (Pi.single i 1)) 2 volume
      = eLpNorm (fun x => fderiv ℝ (a.fn k) x (Pi.single i 1)
        - u.zeroExtensionGrad x i) 2 volume := by
    have h1 : (fun x => fderiv ℝ (a.fn k) x (Pi.single i 1) - u.zeroExtensionGrad x i)
        = -(fun x => u.zeroExtensionGrad x i
          - fderiv ℝ (a.fn k) x (Pi.single i 1)) := by funext x; simp
    rw [h1, eLpNorm_neg]
  calc eLpNorm (fun x => fderiv ℝ (a.fn (k + 1)) x (Pi.single i 1)
        - fderiv ℝ (a.fn k) x (Pi.single i 1)) 2 volume
      ≤ eLpNorm (fun x => fderiv ℝ (a.fn (k + 1)) x (Pi.single i 1)
          - u.zeroExtensionGrad x i) 2 volume
        + eLpNorm (fun x => u.zeroExtensionGrad x i
          - fderiv ℝ (a.fn k) x (Pi.single i 1)) 2 volume :=
        eLpNorm_sub_le_add (a.aestronglyMeasurable_grad (k + 1) i)
          (a.aestronglyMeasurable_grad k i) hz
    _ ≤ ((4 : ℝ≥0∞)⁻¹) ^ (k + 1) + ((4 : ℝ≥0∞)⁻¹) ^ k := by
        rw [hsymm]; exact add_le_add (a.rateGrad (k + 1) i) (a.rateGrad k i)
    _ ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ k := by
        rw [two_mul, pow_succ]
        refine add_le_add ?_ le_rfl
        calc ((4 : ℝ≥0∞)⁻¹) ^ k * (4 : ℝ≥0∞)⁻¹ ≤ ((4 : ℝ≥0∞)⁻¹) ^ k * 1 := by
              gcongr
              exact ENNReal.inv_le_one.mpr (by norm_num)
          _ = ((4 : ℝ≥0∞)⁻¹) ^ k := mul_one _

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
