module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Mathlib.Tactic

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Killed solutions with Hölder representatives (bundle fields `u, uc, hU, hUrep, hUconv,
hUholder`).**  On one cube, let `usrc g n` be the killed solution of the source `g ∈ D` for the
coefficient `a n`, with continuous Hölder representative `srcRep g n` vanishing on the frontier
and Hölder norm bounded in `n`; let the killed solutions of every `f ∈ L²(Q)` converge to `G f`.
Then `u f n := responseSolution S (a n) (load f)` with a.e. representatives `uc` that agree with
`srcRep` on `D` satisfy all of the corresponding fields of `in_represented_bounds_seq`. -/
theorem conv_represented_bounds_env_holder
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr)) (alpha : ℝ)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (usrc : D → ℕ → S.space)
    (srcRep : D → ℕ → SpatialCoordinates d → ℝ)
    (hU : ∀ (g : D) (n : ℕ), usrc g n =
      responseSolution S (a n) ((sobolevVolumeLoad g.val).comp S.space.subtypeL))
    (hrep : ∀ (g : D) (n : ℕ), ((usrc g n).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] srcRep g n)
    (hHolder : ∀ g : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ n : ℕ,
      ContinuousOn (srcRep g n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
        (srcRep g n) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
        (srcRep g n) ≤ Kf ∧
      ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), srcRep g n x = 0)
    (hconv : ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto (fun n => (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) atTop (𝓝 (G f))) :
    ∃ (u : DomainL2 (centeredCube z r hr) → ℕ → S.space)
      (uc : DomainL2 (centeredCube z r hr) → ℕ → SpatialCoordinates d → ℝ),
      (∀ (f : DomainL2 (centeredCube z r hr)) (n : ℕ),
        u f n = responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)) ∧
      (∀ (f : DomainL2 (centeredCube z r hr)) (n : ℕ),
        (u f n).val.1 =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          uc f n) ∧
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => (u f n).val.1) atTop (𝓝 (G f))) ∧
      (∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ n : ℕ,
        ContinuousOn (uc f.val n)
          (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          (uc f.val n) ∧
        _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          (uc f.val n) ≤ Kf ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), uc f.val n x = 0) := by
  classical
  let u : DomainL2 (centeredCube z r hr) → ℕ → S.space := fun f n =>
    responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)
  let uc : DomainL2 (centeredCube z r hr) → ℕ → SpatialCoordinates d → ℝ := fun f n =>
    if h : ∃ g : D, g.val = f then srcRep h.choose n
    else (Lp.aestronglyMeasurable ((u f n).val.1 : DomainL2 (centeredCube z r hr))).mk _
  have hucD : ∀ (g : D) (n : ℕ), uc g.val n = srcRep g n := by
    intro g n
    have h : ∃ g' : D, g'.val = g.val := ⟨g, rfl⟩
    have hgg : h.choose = g := Subtype.ext h.choose_spec
    simp only [uc, dite_eq_left h, hgg]
  refine ⟨u, uc, fun f n => rfl, ?_, fun f => hconv f, ?_⟩
  · intro f n
    by_cases h : ∃ g : D, g.val = f
    · obtain ⟨g, rfl⟩ := h
      rw [hucD]
      have := hrep g n
      rwa [hU g n] at this
    · simp only [uc, dite_eq_right h]
      exact (Lp.aestronglyMeasurable ((u f n).val.1 : DomainL2 (centeredCube z r hr))).ae_eq_mk
  · intro g
    obtain ⟨Kf, hK0, hK⟩ := hHolder g
    refine ⟨Kf, hK0, fun n => ?_⟩
    rw [hucD]
    exact hK n

end SubdiffusiveProcess.Paper
