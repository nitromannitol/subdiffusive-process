import SubdiffusiveProcess.Paper.killed_inverse_mosco
import SubdiffusiveProcess.Paper.prop_killed_inverse_collective_compactness
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.MeshGluing
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.ExternalInputs

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem prop_killed_inverse_injectivity
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (GN : ℕ → DomainL2 (centeredCube z R hR) →L[ℝ]
      DomainL2 (centeredCube z R hR))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ]
      DomainL2 (centeredCube z R hR))
    (hGN : ∀ (n : ℕ) (f : DomainL2 (centeredCube z R hR)), GN n f =
      (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hG : Tendsto GN atTop (𝓝 G))
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    (hDdense : Dense (D : Set (DomainL2 (centeredCube z R hR))))
    (hDsmooth : ∀ f : D,
      ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
        HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (f.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fc)
    (hmesh : ∀ φ : DomainL2 (centeredCube z R hR),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
        HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm S (a n) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε)) :
    Function.Injective G := by
  refine injective_limit_of_volumeResponse_approximations S a G
    (D : Set (DomainL2 (centeredCube z R hR))) hDdense ?_ ?_
  · intro f
    have h1 : Tendsto (fun n => GN n f) atTop (𝓝 (G f)) :=
      ((continuous_id.clm_apply continuous_const).tendsto G).comp hG
    have h2 : Tendsto (fun n => inner ℝ f (GN n f)) atTop (𝓝 (inner ℝ f (G f))) :=
      tendsto_const_nhds.inner h1
    apply h2.congr'
    filter_upwards with n
    rw [hGN n f, inverseResponse_eq_load]
    rfl
  · intro φ hφ ε hε
    exact hmesh φ (hDsmooth ⟨φ, hφ⟩) ε hε


end Paper
