module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.Symmetry
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Self-adjointness of the Brownian semigroup, in the real (Bochner) form

`SobolevPathLift/Symmetry.lean` proved self-adjointness in `ℝ≥0∞`, where no integrability side condition
is needed.  The stationary expansion ( §2.3)
uses it on **signed** functions, inside a Bochner integral, to move the time derivative from one
slot of the pairing to the other:

```text
⟨φ, P_t Δφ⟩ = ⟨Δφ, P_t φ⟩,
```

which is what lets `H(t) = ⟨Δφ, P_t φ⟩` be differentiated a second time (`SobolevPathLift.SemigroupFTC`
differentiates the **orbit** slot, and with `φ` only `C²` the function `Δφ` is *not* in the
generator domain, so the pairing slot is where `Δφ` has to sit).

The route is Fubini against the symmetric density, not a four-fold decomposition into positive and
negative parts: `⟨w, P_t g⟩ = ∫∫ w(x) p_t(x,y) g(y)`, swap, `p_t(x,y) = p_t(y,x)`, read back.  The
only real work is the product integrability, and it is asymmetric in a way worth recording: the
hypotheses are `w` **integrable and measurable**, `g` **measurable and bounded** -- `g` need not be
integrable and `w` need not be bounded.  That asymmetry is exactly what the two applications want
(`w = φ`, `g = Δφ` and the other way round, both compactly supported and continuous, hence both).

* `lintegral_laplacianDensity_row`, `integral_laplacianDensity_row`, `integrable_laplacianDensity_row`
  -- the transition density is a probability density in its terminal variable.  (The *initial*
  variable is `lintegral_laplacianDensity_start`, already proved; the row version is the direct
  conservativity readout.)
* `integral_semigroup_eq_density` -- the Bochner readout of the semigroup average.  It needs no
  integrability hypothesis at all: `integral_withDensity_eq_integral_smul` is unconditional.
* `integral_semigroup_symm` -- the payoff.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

variable {d : ℕ}

/-! ## The transition density as a probability density -/

/-- Integrating the free Gaussian kernel in its **terminal** point gives one: this is the direct
conservativity readout (the initial point is `lintegral_laplacianDensity_start`). -/
theorem lintegral_laplacianDensity_row {t : ℝ} (ht : 0 < t) (x : Vec d) :
    ∫⁻ y, ENNReal.ofReal (laplacianDensity t x y) ∂volume = 1 := by
  have hone : laplacianSemigroup d (Real.toNNReal t) x univ = 1 :=
    isConservative_laplacianSemigroup (Real.toNNReal t) x
  rw [laplacianSemigroup_eq_withDensity ht x, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at hone
  exact hone

theorem measurable_laplacianDensity_row (t : ℝ) (x : Vec d) :
    Measurable fun y : Vec d => laplacianDensity t x y :=
  (measurable_uncurry_laplacianDensity (d := d) t).of_uncurry_left (x := x)

theorem integrable_laplacianDensity_row {t : ℝ} (ht : 0 < t) (x : Vec d) :
    Integrable (fun y : Vec d => laplacianDensity t x y) volume := by
  refine ⟨(measurable_laplacianDensity_row t x).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun y => laplacianDensity_nonneg t x y),
    lintegral_laplacianDensity_row ht x]
  exact ENNReal.one_lt_top

theorem integral_laplacianDensity_row {t : ℝ} (ht : 0 < t) (x : Vec d) :
    ∫ y : Vec d, laplacianDensity t x y ∂volume = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun y => laplacianDensity_nonneg t x y)
    (measurable_laplacianDensity_row t x).aestronglyMeasurable,
    lintegral_laplacianDensity_row ht x]
  simp

/-! ## The Bochner readout of the semigroup average -/

/-- The semigroup average of a function, written against the kernel density.  No integrability
hypothesis is needed: `integral_withDensity_eq_integral_smul` handles the non-integrable case by
making both sides vanish. -/
theorem integral_semigroup_eq_density {t : ℝ} (ht : 0 < t) (g : Vec d → ℝ) (x : Vec d) :
    (∫ y, g y ∂(laplacianSemigroup d (Real.toNNReal t) x))
      = ∫ y, laplacianDensity t x y * g y ∂volume := by
  have hmeas : Measurable fun y : Vec d => Real.toNNReal (laplacianDensity t x y) :=
    (measurable_laplacianDensity_row t x).real_toNNReal
  have hdens : (fun y : Vec d => ENNReal.ofReal (laplacianDensity t x y))
      = fun y : Vec d => ((Real.toNNReal (laplacianDensity t x y) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [laplacianSemigroup_eq_withDensity ht x, hdens,
    integral_withDensity_eq_integral_smul hmeas]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (laplacianDensity_nonneg t x y)]

/-! ## Self-adjointness on signed functions -/

/-- **The Brownian semigroup is self-adjoint, in the real (Bochner) form.**  `w` is integrable and
measurable; `g` is measurable and bounded.  Neither needs the other's hypothesis. -/
theorem integral_semigroup_symm {t : ℝ} (ht : 0 < t) {w g : Vec d → ℝ} {C : ℝ}
    (hwm : Measurable w) (hw : Integrable w) (hgm : Measurable g) (hgb : ∀ y, |g y| ≤ C) :
    (∫ x, w x * (∫ y, g y ∂(laplacianSemigroup d (Real.toNNReal t) x)) ∂volume)
      = ∫ y, g y * (∫ x, w x ∂(laplacianSemigroup d (Real.toNNReal t) y)) ∂volume := by
  classical
  have hCnn : 0 ≤ C := le_trans (abs_nonneg (g 0)) (hgb 0)
  -- the integrand on the product
  set F : Vec d × Vec d → ℝ := fun p => w p.1 * (laplacianDensity t p.1 p.2 * g p.2) with hF
  have hFmeas : Measurable F :=
    (hwm.comp measurable_fst).mul
      ((measurable_uncurry_laplacianDensity (d := d) t).mul (hgm.comp measurable_snd))
  -- slices in the second variable
  have hslice : ∀ x : Vec d, Integrable (fun y => F (x, y)) volume := by
    intro x
    have h1 : Integrable (fun y : Vec d => laplacianDensity t x y * g y) volume :=
      (integrable_laplacianDensity_row ht x).mul_bdd hgm.aestronglyMeasurable
        (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hgb y)
    exact h1.const_mul (w x)
  -- the partial-norm integral is dominated by `C * |w|`
  have hbound : ∀ x : Vec d, ∫ y, ‖F (x, y)‖ ∂volume ≤ C * |w x| := by
    intro x
    have hrw : ∀ y : Vec d, ‖F (x, y)‖ = |w x| * (laplacianDensity t x y * |g y|) := by
      intro y
      rw [hF]
      simp only [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (laplacianDensity_nonneg t x y)]
    simp only [hrw]
    rw [integral_const_mul]
    have hle : ∫ y, laplacianDensity t x y * |g y| ∂volume ≤ C := by
      have h1 : Integrable (fun y : Vec d => laplacianDensity t x y * |g y|) volume :=
        (integrable_laplacianDensity_row ht x).mul_bdd hgm.abs.aestronglyMeasurable
          (Eventually.of_forall fun y => by
            simpa [Real.norm_eq_abs, abs_abs] using hgb y)
      have h2 : Integrable (fun y : Vec d => laplacianDensity t x y * C) volume :=
        (integrable_laplacianDensity_row ht x).mul_const C
      have hmono : ∫ y, laplacianDensity t x y * |g y| ∂volume
          ≤ ∫ y, laplacianDensity t x y * C ∂volume := by
        refine integral_mono h1 h2 fun y => ?_
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (by simpa using hgb y))
          (laplacianDensity_nonneg t x y)
      rw [integral_mul_const, integral_laplacianDensity_row ht x, one_mul] at hmono
      exact hmono
    calc |w x| * ∫ y, laplacianDensity t x y * |g y| ∂volume ≤ |w x| * C :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = C * |w x| := mul_comm _ _
  -- product integrability
  have hprod : Integrable F (volume.prod volume) := by
    refine (integrable_prod_iff hFmeas.aestronglyMeasurable).2
      ⟨Eventually.of_forall hslice, ?_⟩
    refine Integrable.mono' (hw.abs.const_mul C)
      hFmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    exact hbound x
  -- the swap
  have hleft : (∫ x, w x * (∫ y, g y ∂(laplacianSemigroup d (Real.toNNReal t) x)) ∂volume)
      = ∫ x, ∫ y, F (x, y) ∂volume ∂volume := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [integral_semigroup_eq_density ht g x]
    simp only [hF]
    rw [integral_const_mul]
  have hright : (∫ y, g y * (∫ x, w x ∂(laplacianSemigroup d (Real.toNNReal t) y)) ∂volume)
      = ∫ y, ∫ x, F (x, y) ∂volume ∂volume := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [integral_semigroup_eq_density ht w y]
    have hswap : ∀ x : Vec d, F (x, y) = g y * (laplacianDensity t y x * w x) := by
      intro x
      simp only [hF]
      rw [laplacianDensity_symm t x y]
      ring
    simp only [hswap]
    rw [integral_const_mul]
  rw [hleft, hright]
  exact integral_integral_swap hprod

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
