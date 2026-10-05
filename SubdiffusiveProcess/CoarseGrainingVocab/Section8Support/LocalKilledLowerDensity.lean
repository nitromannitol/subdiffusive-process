module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationDensity

@[expose] public section

/-!
# Killed-density identities for the local lower bound

The Cauchy–Schwarz and semigroup identities are used in the density estimate.

The killed transition kernel of a `LocalDiffusion` has the killed density as its
Radon–Nikodym derivative with respect to the weighted measure of the domain, so
the kernel semigroup identity becomes an almost-everywhere Chapman–Kolmogorov
identity for the density, and the kernel rectangle symmetry becomes symmetry of
the density.  Because the density is jointly continuous on `Ioi 0 ×ˢ U ×ˢ U` and
the weighted measure charges every open subset of `U`, both upgrade to genuine
pointwise statements: the Chapman–Kolmogorov identity as an inequality
(`ofReal_density_lintegral_le`, all that the lower bound needs) and the symmetry
as an equality (`density_symm`).
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}
  {p : ℝ → Vec d → Vec d → ℝ}

/-- The killed density at a fixed time and starting point is measurable. -/
theorem measurable_density (hp : IsKilledDensity law rho U p) {t : ℝ} (ht : 0 < t) (x : Vec d) :
    Measurable (fun y => ENNReal.ofReal (p t x y)) :=
  ((hp.1 t ht).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal

/-- The killed density at a fixed time and endpoint is measurable. -/
theorem measurable_density_left (hp : IsKilledDensity law rho U p) {t : ℝ} (ht : 0 < t)
    (y : Vec d) : Measurable (fun x => ENNReal.ofReal (p t x y)) :=
  ((hp.1 t ht).comp (measurable_id.prodMk measurable_const)).ennreal_ofReal

/-- The killed density in both variables at a fixed time is measurable. -/
theorem measurable_density_prod (hp : IsKilledDensity law rho U p) {t : ℝ} (ht : 0 < t) :
    Measurable (fun z : Vec d × Vec d => ENNReal.ofReal (p t z.1 z.2)) :=
  (hp.1 t ht).ennreal_ofReal

/-- The killed transition kernel is the weighted measure with the density. -/
theorem killedKernel_eq_withDensity (hU : IsOpen U) (hp : IsKilledDensity law rho U p)
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    killedKernel law U hU (Real.toNNReal t) x
      = ((weightedMeasure rho).restrict U).withDensity (fun y => ENNReal.ofReal (p t x y)) := by
  refine Measure.ext fun B hB => ?_
  rw [killedKernel_apply_eq_density hU hp t ht x hx B hB, withDensity_apply _ hB]

/-- Integration against the killed transition kernel is integration against the density. -/
theorem lintegral_killedKernel (hU : IsOpen U) (hp : IsKilledDensity law rho U p)
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) {g : Vec d → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ y, g y ∂(killedKernel law U hU (Real.toNNReal t) x))
      = ∫⁻ y, ENNReal.ofReal (p t x y) * g y ∂((weightedMeasure rho).restrict U) := by
  rw [killedKernel_eq_withDensity hU hp ht hx,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_density hp ht x) hg]
  rfl

/-- The Chapman–Kolmogorov identity of the killed density, almost everywhere in the endpoint. -/
theorem density_semigroup_ae (hD : LocalDiffusion c rho law) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hp : IsKilledDensity law rho U p)
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) {x : Vec d} (hx : x ∈ U) :
    ∀ᵐ w ∂((weightedMeasure rho).restrict U),
      ENNReal.ofReal (p (t₁ + t₂) x w)
        = ∫⁻ y, ENNReal.ofReal (p t₁ x y) * ENNReal.ofReal (p t₂ y w)
            ∂((weightedMeasure rho).restrict U) := by
  have hfin : (weightedMeasure rho) U ≠ ∞ :=
    KilledDensityExistence.weightedMeasure_ne_top_of_localDiffusion hD hU hUb
  have : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
  set mu := (weightedMeasure rho).restrict U with hmu
  have hfinite : IsFiniteMeasure mu := by
    refine ⟨?_⟩
    rw [hmu, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact lt_of_le_of_ne le_top hfin
  have hjoint : Measurable (fun z : Vec d × Vec d =>
      ENNReal.ofReal (p t₁ x z.1) * ENNReal.ofReal (p t₂ z.1 z.2)) :=
    ((measurable_density hp ht₁ x).comp measurable_fst).mul (measurable_density_prod hp ht₂)
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (measurable_density hp (by linarith) x)
    (hjoint.lintegral_prod_left') (fun B hB _ => ?_)
  have hsum : Real.toNNReal (t₁ + t₂) = Real.toNNReal t₁ + Real.toNNReal t₂ :=
    Real.toNNReal_add ht₁.le ht₂.le
  have hleft : (∫⁻ w in B, ENNReal.ofReal (p (t₁ + t₂) x w) ∂mu)
      = killedKernel law U hU (Real.toNNReal t₁ + Real.toNNReal t₂) x B := by
    rw [← hsum, killedKernel_apply_eq_density hU hp (t₁ + t₂) (by linarith) x hx B hB]
  have hcomp : killedKernel law U hU (Real.toNNReal t₁ + Real.toNNReal t₂) x B
      = ∫⁻ y, killedKernel law U hU (Real.toNNReal t₂) y B
          ∂(killedKernel law U hU (Real.toNNReal t₁) x) := by
    rw [semigroup law hD.1 U hU (Real.toNNReal t₁) (Real.toNNReal t₂),
      Kernel.comp_apply' _ _ _ hB]
  have hinner : (∫⁻ y, killedKernel law U hU (Real.toNNReal t₂) y B
        ∂(killedKernel law U hU (Real.toNNReal t₁) x))
      = ∫⁻ y, ENNReal.ofReal (p t₁ x y) *
          killedKernel law U hU (Real.toNNReal t₂) y B ∂mu :=
    lintegral_killedKernel hU hp ht₁ hx
      ((killedKernel law U hU (Real.toNNReal t₂)).measurable_coe hB)
  have hrow : ∀ᵐ y ∂mu, ENNReal.ofReal (p t₁ x y) *
      killedKernel law U hU (Real.toNNReal t₂) y B
        = ENNReal.ofReal (p t₁ x y) * ∫⁻ w in B, ENNReal.ofReal (p t₂ y w) ∂mu := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    rw [killedKernel_apply_eq_density hU hp t₂ ht₂ y hy B hB]
  have hswap : (∫⁻ y, ENNReal.ofReal (p t₁ x y) *
        ∫⁻ w in B, ENNReal.ofReal (p t₂ y w) ∂mu ∂mu)
      = ∫⁻ w in B, ∫⁻ y, ENNReal.ofReal (p t₁ x y) * ENNReal.ofReal (p t₂ y w) ∂mu ∂mu := by
    rw [show (fun y => ENNReal.ofReal (p t₁ x y) * ∫⁻ w in B, ENNReal.ofReal (p t₂ y w) ∂mu)
        = fun y => ∫⁻ w in B, ENNReal.ofReal (p t₁ x y) * ENNReal.ofReal (p t₂ y w) ∂mu from
      funext fun y => (lintegral_const_mul _ (measurable_density hp ht₂ y)).symm]
    exact lintegral_lintegral_swap hjoint.aemeasurable
  rw [hleft, hcomp, hinner, lintegral_congr_ae hrow, hswap]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
