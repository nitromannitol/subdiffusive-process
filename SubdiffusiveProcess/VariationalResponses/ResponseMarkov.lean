/-
Gradient-energy structure for the finite-cutoff response form.

The response-form estimate carries the gradient-energy structure and the
Stampacchia contraction chain-rule input `SubdiffusiveProcess.DirichletForm.HasContractionChainRule`.
-/
module

public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.DirichletForm.All

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- **Markov property of the finite-cutoff form.**  Composition with a normal
contraction `T` (`T 0 = 0`, `1`-Lipschitz, not assumed monotone) produces an
element of the same response space — the killed space when `S.space` is the
killed graph — whose value is `T ∘ u` almost everywhere and whose energy is at
most that of `u`.  Energy without the factor `1/2`, as everywhere in this
project.

`G` is the gradient-energy structure of `responseForm S a`
(`G.integrand x ξ = a.val x * ∑ i, (ξ i)^2`, `G.grad u x i = (u : SobolevData Ω).2 i x`)
and `hchain` is the Stampacchia chain-rule external input for it. -/
theorem responseForm_normalContraction_le
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (G : _root_.SubdiffusiveProcess.DirichletForm.GradientEnergy
      (volume.restrict (Ω : Set (SpatialCoordinates d))) (Fin d → ℝ) S.space)
    (hvalue : ∀ u : S.space,
      G.value u = fun x => ((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ) x)
    (henergy : ∀ u : S.space, G.energy u = responseForm S a u u)
    (hchain : _root_.SubdiffusiveProcess.DirichletForm.HasContractionChainRule G
      (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (T : ℝ → ℝ) (hT0 : T 0 = 0) (hTlip : ∀ s t : ℝ, |T s - T t| ≤ |s - t|)
    (u : S.space) :
    ∃ v : S.space,
      ((v : SobolevData Ω).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
          (fun x => T (((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ) x)) ∧
      responseForm S a v v ≤ responseForm S a u u := by
  obtain ⟨v, hval, hle⟩ := G.exists_comp_energy_le hchain u T ⟨hT0, hTlip⟩
  refine ⟨v, ?_, ?_⟩
  · rw [hvalue u, hvalue v] at hval
    exact hval
  · rw [← henergy v, ← henergy u]
    exact hle

end SubdiffusiveProcess
