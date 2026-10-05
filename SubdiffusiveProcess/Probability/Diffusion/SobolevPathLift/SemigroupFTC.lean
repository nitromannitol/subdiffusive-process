module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.SemigroupPairing
public import MarkovProcess.Semigroup.OrbitProductRule

@[expose] public section

/-!
# the fundamental theorem of calculus for the semigroup pairing

The stationary calculation closes the
expansion by **two nested applications of the fundamental theorem of calculus** to the pairings
`G(t) = ⟨φ, P_t φ⟩` and `H(t) = ⟨Δφ, P_t φ⟩`.  This file provides the single reusable step both
applications are instances of:

```text
∫₀ᵀ ⟨w, P_v (L ψ)⟩ dv = ⟨w, P_T ψ⟩ − ⟨w, ψ⟩      (w ∈ L¹, ψ in the generator domain)
```

and its specialization `integral_pairing_laplacian_eq_sub`, where `L ψ` is written as the **full**
Laplacian through `generator_laplacianSemigroup`.

The three inputs, each already available:

* the orbit derivative `d/dy [P_y ψ] = P_y (L ψ)`, one-sided on `Ioi s`, from MarkovProcess's
  `hasDerivWithinAt_operator_apply` specialized to the **constant** curve `v y = ψ` (so `v' = 0`
  and the product rule degenerates to the plain orbit ODE);
* the pairing as a **continuous linear functional** `pairingCLM` on `C₀`, whose bound is the
  `∫|w|·‖·‖_∞` estimate of `SobolevPathLift/SemigroupPairing.lean`.  A bounded linear map commutes with
  the derivative, so the orbit ODE becomes a scalar one-sided ODE with no further analysis;
* `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, which asks for exactly what is
  available: continuity on the closed interval (the pairing's time-continuity), **right**
  derivatives on the open interval (the semigroup orbit is differentiable only from the right),
  and interval integrability of the derivative (again from continuity).

Nothing here needs `ψ` to be twice in the domain: the derivative is taken in the *orbit* slot and
the pairing slot stays fixed, which is why `H(t) = ⟨Δφ, P_t φ⟩` -- rather than the superficially
more natural `⟨φ, P_t Δφ⟩` -- is the form §2.3 differentiates a second time.  (Moving between the
two is semigroup self-adjointness, `lintegral_semigroup_symm`, and is not needed here.)
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The Brownian semigroup, acting on `C₀(Vec d, ℝ)` as a strongly continuous contraction
semigroup.  This is the object `LaplacianGenerator.lean` computes the generator of. -/
abbrev brownianSemigroup (d : ℕ) :
    Semigroup.StronglyContinuousContractionSemigroup C₀(Vec d, ℝ) :=
  (isFeller_laplacianSemigroup (d := d)).c0Semigroup

/-! ## The pairing as a continuous linear functional -/

/-- Pairing against a fixed `L¹` function, as a continuous linear functional on `C₀`.  The bound
is `|⟨w, u⟩| ≤ (∫|w|)·‖u‖_∞`. -/
def pairingCLM {w : Vec d → ℝ} (hw : Integrable w) : C₀(Vec d, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x, w x * u x
      map_add' := fun u v => by
        simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply]
        rw [← integral_add (integrable_mul_c0 hw u) (integrable_mul_c0 hw v)]
        exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      map_smul' := fun c u => by
        simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun x => by ring) }
    (∫ x, |w x|) fun u => by
      simpa [Real.norm_eq_abs] using! abs_integral_mul_c0_le hw u

@[simp] theorem pairingCLM_apply {w : Vec d → ℝ} (hw : Integrable w) (u : C₀(Vec d, ℝ)) :
    pairingCLM hw u = ∫ x, w x * u x := rfl

/-! ## The orbit derivative and the FTC -/

/-- **The semigroup orbit ODE**, `d/dy [P_y ψ] = P_y (L ψ)`, one-sided at every nonnegative time.
This is `hasDerivWithinAt_operator_apply` at the constant curve. -/
theorem hasDerivWithinAt_brownian_orbit {ψ : C₀(Vec d, ℝ)}
    (hmem : ψ ∈ (brownianSemigroup d).generatorDomain) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun y : ℝ => (brownianSemigroup d) (Real.toNNReal y) ψ)
      ((brownianSemigroup d) (Real.toNNReal s)
        ((brownianSemigroup d).generator ⟨ψ, hmem⟩)) (Ioi s) s := by
  have h := Semigroup.StronglyContinuousContractionSemigroup.hasDerivWithinAt_operator_apply
    (brownianSemigroup d) (v := fun _ : ℝ => ψ) (v' := 0) hs hmem
    (hasDerivWithinAt_const s (Ioi s) ψ)
  simpa using! h

/-- The pairing of the orbit with a fixed `L¹` function has the same one-sided derivative, the
pairing being a bounded linear functional. -/
theorem hasDerivWithinAt_pairing_orbit {w : Vec d → ℝ} (hw : Integrable w)
    {ψ : C₀(Vec d, ℝ)} (hmem : ψ ∈ (brownianSemigroup d).generatorDomain) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun y : ℝ => ∫ x, w x * (brownianSemigroup d) (Real.toNNReal y) ψ x)
      (∫ x, w x * (brownianSemigroup d) (Real.toNNReal s)
        ((brownianSemigroup d).generator ⟨ψ, hmem⟩) x) (Ioi s) s := by
  have h := (pairingCLM hw).hasFDerivAt.comp_hasDerivWithinAt s
    (hasDerivWithinAt_brownian_orbit hmem hs)
  simpa only [Function.comp_def] using! h

/-- **The fundamental theorem of calculus for the semigroup pairing.** -/
theorem integral_pairing_orbit_eq_sub {w : Vec d → ℝ} (hw : Integrable w)
    {ψ : C₀(Vec d, ℝ)} (hmem : ψ ∈ (brownianSemigroup d).generatorDomain) {T : ℝ} (hT : 0 ≤ T) :
    (∫ v in (0 : ℝ)..T, ∫ x, w x * (brownianSemigroup d) (Real.toNNReal v)
        ((brownianSemigroup d).generator ⟨ψ, hmem⟩) x)
      = (∫ x, w x * (brownianSemigroup d) (Real.toNNReal T) ψ x) - ∫ x, w x * ψ x := by
  have hzero : (fun y : ℝ => ∫ x, w x * (brownianSemigroup d) (Real.toNNReal y) ψ x) 0
      = ∫ x, w x * ψ x := by
    simp
  rw [← hzero]
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT
    (continuous_semigroup_pairing_real hw ψ).continuousOn
    (fun y hy => hasDerivWithinAt_pairing_orbit hw hmem (le_of_lt hy.1)) ?_
  exact (continuous_semigroup_pairing_real hw
    ((brownianSemigroup d).generator ⟨ψ, hmem⟩)).intervalIntegrable 0 T

/-- The same, with the generator written as the **full** Laplacian: for `f` a compactly supported
`C²` member of `C₀` and `g` its full Laplacian,

```text
∫₀ᵀ ⟨w, P_v g⟩ dv = ⟨w, P_T f⟩ − ⟨w, f⟩.
```
-/
theorem integral_pairing_laplacian_eq_sub {w : Vec d → ℝ} (hw : Integrable w)
    (f g : C₀(Vec d, ℝ)) (hf : ContDiff ℝ 2 (f : Vec d → ℝ))
    (hsupp : HasCompactSupport (f : Vec d → ℝ))
    (hg : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)])
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ v in (0 : ℝ)..T, ∫ x, w x * (brownianSemigroup d) (Real.toNNReal v) g x)
      = (∫ x, w x * (brownianSemigroup d) (Real.toNNReal T) f x) - ∫ x, w x * f x := by
  have hmem := mem_generatorDomain_laplacianSemigroup f g hf hsupp hg
  have hgen := generator_laplacianSemigroup f g hf hsupp hg
  have h := integral_pairing_orbit_eq_sub hw hmem hT
  rwa [hgen] at h

end SubdiffusiveProcess.Probability.Diffusion
