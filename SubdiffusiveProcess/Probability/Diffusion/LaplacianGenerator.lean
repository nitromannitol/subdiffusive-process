module

public import SubdiffusiveProcess.Probability.Diffusion.GaussianDifferenceQuotient
public import SubdiffusiveProcess.Probability.Diffusion.Brownian

@[expose] public section

/-!
# The generator of the Laplacian semigroup on compactly supported `C²` functions

For the Brownian witness: the uniform difference-quotient limit of
`GaussianDifferenceQuotient.lean` is transported to `laplacianSemigroup d` and read in the `C₀`
norm, which is what `MarkovProcess`'s generator API consumes.

The transport is one change of clock.  `laplacianSemigroup d t` is the Gaussian semigroup at
variance `2t` -- that factor of two is the  normalization, fixed so that the weak
equation of `LocalDiffusion 1 1` is the FULL Laplacian
 -- and `gaussianVec_eq_map` writes its law as the push-forward
of the standard Gaussian under `z ↦ x + √(2t) • z`.  With `σ = √(2t)` we have `σ² = 2t`, so the
semigroup difference quotient `t⁻¹(S_t f (x) − f(x))` is *literally* the quantity
`2(∫ f(x+σz) dγ − f(x))/σ²` of the uniform limit, which is why that theorem carries the factor
`2` and the `σ²`.  The index change `t ↦ √(2t)` maps `𝓝[>] 0` in `NNReal` to `𝓝[>] 0` in `ℝ`
(`tendsto_sqrt_two_mul`), so the uniformity transports without any new estimate.

* `integral_laplacianSemigroup_eq` — the change of variables.
* `tendstoUniformly_laplacianSemigroup_differenceQuotient` — the uniform limit in `t`.
* `tendsto_differenceQuotient_laplacianSemigroup` — the same limit in the `C₀` norm, via
  `ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly`.
* `mem_generatorDomain_laplacianSemigroup`, `generator_laplacianSemigroup` — generator membership
  and the value of the generator, through `mem_generatorDomain_of_tendsto` and
  `generator_mk_eq` of `MarkovProcess/Semigroup/Generator.lean`.

The generator is the **full** Laplacian `∑ i, D²f(x)[e_i, e_i]`, not half of it: the
one-dimensional template in `MarkovProcess/Examples/HeatGenerator.lean` runs at variance `t` and
therefore lands on `f''/2`.

Nothing here characterizes the generator domain; it is only shown to contain the compactly
supported `C²` functions of `C₀`, which is what the discounted Dynkin step needs.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.Model.HeatSemigroupVec
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The transition average of a bounded continuous function, rescaled to the standard Gaussian. -/
theorem integral_laplacianSemigroup_eq {ψ : Vec d → ℝ} (hcont : Continuous ψ)
    (t : NNReal) (x : Vec d) :
    ∫ y : Vec d, ψ y ∂(laplacianSemigroup d t x)
      = ∫ z : Vec d, ψ (x + Real.sqrt (2 * t) • z) ∂(stdGaussianVec d) := by
  rw [laplacianSemigroup_apply, gaussianVec_eq_map]
  rw [integral_map (by fun_prop) hcont.aestronglyMeasurable]
  push_cast
  rfl

/-- The scale change `t ↦ √(2t)` maps the one-sided limit at `0` in `NNReal` to the one-sided
limit at `0` in `ℝ`. -/
theorem tendsto_sqrt_two_mul : Tendsto (fun t : NNReal => Real.sqrt (2 * (t : ℝ)))
    (𝓝[>] (0 : NNReal)) (𝓝[>] (0 : ℝ)) := by
  have hcont : Tendsto (fun t : NNReal => Real.sqrt (2 * (t : ℝ))) (𝓝 (0 : NNReal)) (𝓝 0) := by
    have hc : Continuous (fun t : NNReal => Real.sqrt (2 * (t : ℝ))) := by fun_prop
    simpa using hc.tendsto (0 : NNReal)
  rw [tendsto_nhdsWithin_iff]
  refine ⟨hcont.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  exact Real.sqrt_pos.mpr (by linarith)

/-- **The difference quotients of the Laplacian semigroup converge to the full Laplacian,
uniformly in the starting point.** -/
theorem tendstoUniformly_laplacianSemigroup_differenceQuotient {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hsupp : HasCompactSupport ψ) :
    TendstoUniformly
      (fun (t : NNReal) (x : Vec d) =>
        (t : ℝ)⁻¹ * ((∫ y : Vec d, ψ y ∂(laplacianSemigroup d t x)) - ψ x))
      (fun x => ∑ i, iteratedFDeriv ℝ 2 ψ x ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)])
      (𝓝[>] (0 : NNReal)) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hσ := Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_gaussian_differenceQuotient hψ hsupp) ε hε
  filter_upwards [tendsto_sqrt_two_mul.eventually hσ, self_mem_nhdsWithin] with t hts ht
  intro x
  have htpos : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hsq : Real.sqrt (2 * (t : ℝ)) ^ 2 = 2 * (t : ℝ) := Real.sq_sqrt (by linarith)
  have heq : (t : ℝ)⁻¹ * ((∫ y : Vec d, ψ y ∂(laplacianSemigroup d t x)) - ψ x)
      = 2 * ((∫ z : Vec d, ψ (x + Real.sqrt (2 * (t:ℝ)) • z) ∂(stdGaussianVec d)) - ψ x)
        / Real.sqrt (2 * (t : ℝ)) ^ 2 := by
    rw [integral_laplacianSemigroup_eq hψ.continuous, hsq]
    field_simp
  rw [heq]
  exact hts x

/-- **The difference quotients of the Laplacian semigroup converge in the `C₀` norm.** -/
theorem tendsto_differenceQuotient_laplacianSemigroup (f g : C₀(Vec d, ℝ))
    (hf : ContDiff ℝ 2 (f : Vec d → ℝ)) (hsupp : HasCompactSupport (f : Vec d → ℝ))
    (hg : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)]) :
    Tendsto (fun t : NNReal =>
        (t : ℝ)⁻¹ • (isFeller_laplacianSemigroup.c0Semigroup t f - f))
      (𝓝[>] (0 : NNReal)) (𝓝 g) := by
  rw [ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly]
  have huniform := tendstoUniformly_laplacianSemigroup_differenceQuotient hf hsupp
  have hfun : (fun t : NNReal =>
        ⇑((t : ℝ)⁻¹ • (isFeller_laplacianSemigroup.c0Semigroup t f - f)))
      = fun (t : NNReal) (x : Vec d) =>
        (t : ℝ)⁻¹ * ((∫ y : Vec d, (f : Vec d → ℝ) y ∂(laplacianSemigroup d t x)) - f x) := by
    funext t x
    simp [SubMarkovKernelSemigroup.IsFellerKernelSemigroup.c0Semigroup_apply_apply,
      kernelIntegral]
  have hlim : (⇑g) = fun x => ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)] := funext hg
  rw [hfun, hlim]
  exact huniform

/-- **Compactly supported `C²` functions lie in the generator domain of the Laplacian
semigroup.**  In the form the discounted Dynkin theorem consumes. -/
theorem mem_generatorDomain_laplacianSemigroup (f g : C₀(Vec d, ℝ))
    (hf : ContDiff ℝ 2 (f : Vec d → ℝ)) (hsupp : HasCompactSupport (f : Vec d → ℝ))
    (hg : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)]) :
    f ∈ (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain :=
  Semigroup.StronglyContinuousContractionSemigroup.mem_generatorDomain_of_tendsto _
    (tendsto_differenceQuotient_laplacianSemigroup f g hf hsupp hg)

/-- **The generator of the Laplacian semigroup is the FULL Laplacian** on compactly supported
`C²` functions -- not half of it: the semigroup runs at variance `2t`. -/
theorem generator_laplacianSemigroup (f g : C₀(Vec d, ℝ))
    (hf : ContDiff ℝ 2 (f : Vec d → ℝ)) (hsupp : HasCompactSupport (f : Vec d → ℝ))
    (hg : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)]) :
    (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generator
      ⟨f, mem_generatorDomain_laplacianSemigroup f g hf hsupp hg⟩ = g :=
  Semigroup.StronglyContinuousContractionSemigroup.generator_mk_eq _
    (tendsto_differenceQuotient_laplacianSemigroup f g hf hsupp hg)

end SubdiffusiveProcess.Probability.Diffusion
