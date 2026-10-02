import SubdiffusiveProcess.Probability.Diffusion.Packet452SymmetryReal

/-!
# P-452 seed (i): invariance of Lebesgue measure, in the real (Bochner) form

`Packet452Stationarity.lean` proved invariance in `ℝ≥0∞` (`lintegral_laplacianSemigroup_invariant`,
`lintegral_path_eval_invariant`).  The stationary expansion works with **signed** integrands inside
Bochner integrals, so it needs

```text
∫ₓ (P_t F)(x) dx = ∫ F dy
```

for `F` integrable.  Two things are worth recording about the hypotheses.

* **Boundedness of `F` is not needed** -- only integrability.  The product integrability that
  Fubini asks for comes out exactly: `∫ₓ ‖p_t(x,y) F(y)‖ dx = |F(y)|`, because `p_t(·, y)` is a
  probability density in its **initial** variable too (`lintegral_laplacianDensity_start`, itself a
  consequence of kernel symmetry).  So the dominating function is `|F|` itself, with no constant.
* The path form `integral_path_eval_invariant` follows by the same rewriting of the path law as in
  the `ℝ≥0∞` proof, so no new probability enters.

`integral_semigroup_invariant` is the workhorse for §2.1/§2.2 of
`ledger/proofplans/brownian-sobolev-maximal-estimate.md`: every term of the expansion of
`∫ E_x M_T² dx` is reduced by it (together with self-adjointness) to a pairing of `φ` and `Δφ`
against the semigroup.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-! ## The density as a probability density in its initial variable -/

theorem measurable_laplacianDensity_column (t : ℝ) (y : Vec d) :
    Measurable fun x : Vec d => laplacianDensity t x y :=
  (measurable_uncurry_laplacianDensity (d := d) t).of_uncurry_right (y := y)

theorem integrable_laplacianDensity_column {t : ℝ} (ht : 0 < t) (y : Vec d) :
    Integrable (fun x : Vec d => laplacianDensity t x y) volume := by
  refine ⟨(measurable_laplacianDensity_column t y).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun x => laplacianDensity_nonneg t x y),
    lintegral_laplacianDensity_start ht y]
  exact ENNReal.one_lt_top

theorem integral_laplacianDensity_column {t : ℝ} (ht : 0 < t) (y : Vec d) :
    ∫ x : Vec d, laplacianDensity t x y ∂volume = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => laplacianDensity_nonneg t x y)
    (measurable_laplacianDensity_column t y).aestronglyMeasurable,
    lintegral_laplacianDensity_start ht y]
  simp

/-! ## Invariance -/

/-- **Lebesgue measure is invariant for the Brownian semigroup**, in the real (Bochner) form.
Only integrability of `F` is needed: the dominating function for Fubini is `|F|` itself. -/
theorem integral_semigroup_invariant {t : ℝ} (ht : 0 < t) {F : Vec d → ℝ}
    (hFm : Measurable F) (hF : Integrable F) :
    (∫ x, (∫ y, F y ∂(laplacianSemigroup d (Real.toNNReal t) x)) ∂volume) = ∫ y, F y ∂volume := by
  classical
  set G : Vec d × Vec d → ℝ := fun p => laplacianDensity t p.1 p.2 * F p.2 with hG
  have hGmeas : Measurable G :=
    (measurable_uncurry_laplacianDensity (d := d) t).mul (hFm.comp measurable_snd)
  have hcol : ∀ y : Vec d, Integrable (fun x => G (x, y)) volume := fun y =>
    (integrable_laplacianDensity_column ht y).mul_const (F y)
  have hnorm : ∀ y : Vec d, (∫ x, ‖G (x, y)‖ ∂volume) = |F y| := by
    intro y
    have hrw : ∀ x : Vec d, ‖G (x, y)‖ = laplacianDensity t x y * |F y| := by
      intro x
      rw [hG]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (laplacianDensity_nonneg t x y)]
    simp only [hrw]
    rw [integral_mul_const, integral_laplacianDensity_column ht y, one_mul]
  have hprod : Integrable G (volume.prod volume) := by
    refine (integrable_prod_iff' hGmeas.aestronglyMeasurable).2
      ⟨Eventually.of_forall hcol, ?_⟩
    refine Integrable.congr hF.abs (Eventually.of_forall fun y => (hnorm y).symm)
  have hleft : (∫ x, (∫ y, F y ∂(laplacianSemigroup d (Real.toNNReal t) x)) ∂volume)
      = ∫ x, ∫ y, G (x, y) ∂volume ∂volume := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [integral_semigroup_eq_density ht F x]
  have hright : (∫ y, ∫ x, G (x, y) ∂volume ∂volume) = ∫ y, F y ∂volume := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    simp only [hG]
    rw [integral_mul_const, integral_laplacianDensity_column ht y, one_mul]
  rw [hleft, ← hright]
  exact integral_integral_swap hprod

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
