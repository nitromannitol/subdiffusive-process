module

public import MarkovProcess.Semigroup.Resolvent
public import MarkovProcess.Kernel.Integral
public import MarkovProcess.Trajectory.FeynmanKacFunctional
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section




set_option autoImplicit false

open MeasureTheory ProbabilityTheory MarkovProcess MarkovProcess.Semigroup Set Filter
open MarkovProcess.SubMarkovKernelSemigroup
open scoped NNReal ENNReal Topology

noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower

/-- The zero-boundary Sobolev graph, specified solely by `L²` approximation
of a scalar function and its coordinate derivatives. -/
def DirichletSobolevPair {d : ℕ} (W : Set (Fin d → ℝ))
    (u : (Fin d → ℝ) → ℝ) (g : (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  MemLp u 2 (volume.restrict W) ∧
    (∀ i : Fin d, MemLp (fun x => g x i) 2 (volume.restrict W)) ∧
    ∃ f : ℕ → (Fin d → ℝ) → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      (∀ n, tsupport (f n) ⊆ W) ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 (volume.restrict W)) atTop (𝓝 0) ∧
      ∀ i : Fin d, Tendsto
        (fun n => eLpNorm (fun x => fderiv ℝ (f n) x (Pi.single i 1) - g x i)
          2 (volume.restrict W)) atTop (𝓝 0)

/-- A Dirichlet Feynman--Kac construction with its ground-state transform,
specified on the ordinary weighted `L²` space and the explicit Sobolev graph. -/
structure DirichletFeynmanKacModel {d : ℕ} (a : (Fin d → ℝ) → ℝ)
    (W : Set (Fin d → ℝ)) (V : (Fin d → ℝ) → ℝ)
    (k0 : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ) where
  pathLaw : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))
  density : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ
  kernel : NNReal → Kernel (Fin d → ℝ) (Fin d → ℝ)
  semigroup : StronglyContinuousContractionSemigroup
    (Lp ℝ 2 ((volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict W))
  kernel_subMarkov : ∀ t, IsSubMarkovKernel (kernel t)
  kernel_subinvariant : ∀ t, kernel t ∘ₘ
    (volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict W ≤
    (volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict W
  associated : ∀ t (f : Lp ℝ 2 ((volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict W)),
    semigroup t f =ᵐ[(volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict W]
      kernelIntegral (kernel t) f
  density_measurable : ∀ s : ℝ, 0 < s →
    Measurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => density s z.1 z.2)
  density_nonneg : ∀ s : ℝ, 0 < s → ∀ z ∈ W, ∀ w ∈ W, 0 ≤ density s z w
  density_continuous : ContinuousOn
    (fun z : ℝ × (Fin d → ℝ) × (Fin d → ℝ) => density z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ W ×ˢ W)
  kernel_density : ∀ s : ℝ, 0 < s → ∀ z ∈ W,
    kernel (Real.toNNReal s) z =
      ((volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict W).withDensity
        (fun y => ENNReal.ofReal (density s z y))
  resolvent_one : ∀ f : Lp ℝ 2 ((volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict W),
    ∃ u : (Fin d → ℝ) → ℝ, ∃ g : (Fin d → ℝ) → Fin d → ℝ,
      DirichletSobolevPair W u g ∧
      (semigroup.resolvent ⟨1, mem_Ioi.2 zero_lt_one⟩ f
        =ᵐ[(volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict W] u) ∧
      ∀ v : (Fin d → ℝ) → ℝ, ∀ h : (Fin d → ℝ) → Fin d → ℝ, DirichletSobolevPair W v h →
        (∫ x in W, a x * u x * v x) + (∫ x in W, ∑ i, a x * g x i * h x i) =
          ∫ x in W, a x * f x * v x
  laplacian_representation : ∀ s : ℝ, 0 < s → ∀ z ∈ W,
    ∀ A : Set (Fin d → ℝ), MeasurableSet A →
      pathLaw z {omega | (∀ r : NNReal, r ≤ Real.toNNReal s → omega r ∈ W) ∧
          omega (Real.toNNReal s) ∈ A} =
        ∫⁻ y in A ∩ W, ENNReal.ofReal (k0 s z y) ∂volume
  feynmanKac_representation : ∀ s : ℝ, 0 < s → ∀ z ∈ W,
    ∀ A : Set (Fin d → ℝ), MeasurableSet A →
      (∫⁻ omega in {omega | (∀ r : NNReal, r ≤ Real.toNNReal s → omega r ∈ W) ∧
          omega (Real.toNNReal s) ∈ A},
        ENNReal.ofReal (Real.exp (-feynmanKacAdditiveFunctional V (Real.toNNReal s) omega))
        ∂pathLaw z) =
      ∫⁻ y in A ∩ W, ENNReal.ofReal (Real.sqrt (a z * a y) * density s z y) ∂volume

/-- The remaining existence theorem. It takes a bounded measurable weak
potential already constructed from a differentiable logarithm with bounded
Lipschitz coordinate derivatives. The cube and Laplacian series are written
explicitly, so all objects in this obligation are Mathlib or MarkovProcess
objects after unfolding the two preceding definitions. -/
def DirichletFeynmanKacConstructionInput (d : ℕ) : Prop :=
  ∀ a : (Fin d → ℝ) → ℝ, (∀ x, 0 < a x) → ∀ z : Fin d → ℝ, ∀ L : ℝ, 0 < L →
    let W : Set (Fin d → ℝ) := pi univ (fun i => Ioo (z i - L / 2) (z i - L / 2 + L))
    AEStronglyMeasurable a (volume.restrict W) →
    (∃ lo hi : ℝ, 0 < lo ∧ ∀ᵐ x ∂volume.restrict W, lo ≤ a x ∧ a x ≤ hi) →
    (∀ x ∈ W, DifferentiableAt ℝ (fun y => Real.log (a y)) x) →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ W, ∀ i : Fin d,
      |fderiv ℝ (fun y => Real.log (a y)) x (Pi.single i 1)| ≤ M) →
    (∃ C : ℝ≥0, ∀ i : Fin d, LipschitzOnWith C
      (fun x => fderiv ℝ (fun y => Real.log (a y)) x (Pi.single i 1)) W) →
    ∀ V : (Fin d → ℝ) → ℝ, Measurable V → (∃ Q : ℝ, ∀ x, |V x| ≤ Q) →
    (∀ phi : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
      tsupport phi ⊆ W →
      (∫ x in W, V x * phi x) =
        -(1 / 2) * (∫ x in W, ∑ i,
          fderiv ℝ (fun y => Real.log (a y)) x (Pi.single i 1) * fderiv ℝ phi x (Pi.single i 1)) +
        (1 / 4) * ∫ x in W, (∑ i,
          fderiv ℝ (fun y => Real.log (a y)) x (Pi.single i 1) *
            fderiv ℝ (fun y => Real.log (a y)) x (Pi.single i 1)) * phi x) →
    Nonempty (DirichletFeynmanKacModel a W V (fun s x y =>
      (L ^ d)⁻¹ * ∏ i : Fin d, (2 * ∑' n : ℕ,
        Real.exp (-(Real.pi ^ 2 * (s / L ^ 2)) * ((n : ℝ) + 1) ^ 2) *
          (Real.sin (Real.pi * ((n : ℝ) + 1) * ((x i - z i) / L + 1 / 2)) *
            Real.sin (Real.pi * ((n : ℝ) + 1) * ((y i - z i) / L + 1 / 2))))))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower
