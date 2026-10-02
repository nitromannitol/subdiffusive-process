import Mathlib
import SubdiffusiveProcess.Paper.classical_countable_smooth_test_bank
import SubdiffusiveProcess.Sobolev.EnlargedSmoothSources

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Catalogue sources (clauses D2, D3, D4 of `conv_represented_estimates`), one cube.**  Every cube has
a countable dense rational catalogue `D ≤ L²(Q)` of classes with `C_c^∞` representatives `f g` supported in `Q`,
and moreover, for every `C_c^∞` test function `phi` supported in `Q`, one compact `K ⊆ Q` and a sequence
`g_n ∈ D` of elements supported in `K` such that every iterated derivative of `f g_n - phi` converges to `0`
uniformly.  The derivative-approximation bank is the frozen classical input
`classical_countable_smooth_test_bank` (separability of `C_c^∞(Q)`), the `L²` density and the rational
submodule structure come from the cube smooth-source library. -/
theorem conv_represented_catalogue_sources (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ (D : Submodule ℚ (DomainL2 (centeredCube z r hr))) (_ : Countable D)
      (f : D → SpatialCoordinates d → ℝ),
      Dense (D : Set (DomainL2 (centeredCube z r hr))) ∧
      (∀ g : D,
        ContDiff ℝ ∞ (f g) ∧ HasCompactSupport (f g) ∧
          tsupport (f g) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (g.val : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f g) ∧
      (∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        ∃ K : Set (SpatialCoordinates d), ∃ g : ℕ → D,
          IsCompact K ∧ K ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          tsupport phi ⊆ K ∧ (∀ n : ℕ, tsupport (f (g n)) ⊆ K) ∧
          ∀ k : ℕ, TendstoUniformly
            (fun n x => iteratedFDeriv ℝ k (fun y => f (g n) y - phi y) x)
            (fun _ => 0) atTop) := by
  classical
  obtain ⟨b, hb, hbank⟩ := classical_countable_smooth_test_bank d
    (centeredCube z r hr : Set (SpatialCoordinates d)) (centeredCube z r hr).isOpen
  -- classes of the bank
  have hbmem : ∀ n, MemLp (b n) 2 (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) := fun n =>
    ((hb n).1.continuous.memLp_of_hasCompactSupport (hb n).2.1 (μ := volume)).restrict _
  let B : ℕ → DomainL2 (centeredCube z r hr) := fun n => (hbmem n).toLp (b n)
  have hBmem : ∀ n, B n ∈ SmoothSources.compactSmoothSourceSubmodule z r hr := fun n =>
    ⟨b n, (hb n).1, (hb n).2.1, (hb n).2.2, (hbmem n).coeFn_toLp⟩
  obtain ⟨D, hDc, hDd, hDle, hBD⟩ :=
    SmoothSources.exists_countable_dense_smooth_submodule_containing z r hr B hBmem
  haveI : Countable D := hDc
  have hrep : ∀ g : D, ∃ fc : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (g.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc :=
    fun g => hDle g.2
  choose f hf using hrep
  refine ⟨D, inferInstance, f, hDd, hf, ?_⟩
  intro phi hphi hphic hphis
  obtain ⟨K, index, hK, hKsub, hphiK, hbK, hunif⟩ := hbank phi hphi hphic hphis
  -- the chosen representative of `B n` is `b n`
  have hfb : ∀ n, f ⟨B n, hBD n⟩ = b n := fun n => by
    obtain ⟨h1, h2, h3, h4⟩ := hf ⟨B n, hBD n⟩
    refine SmoothSources.eq_of_continuous_supported_ae_eq (centeredCube z r hr).isOpen
      h1.continuous (hb n).1.continuous h3 (hb n).2.2 ?_
    exact h4.symm.trans ((hbmem n).coeFn_toLp)
  refine ⟨K, fun n => ⟨B (index n), hBD (index n)⟩, hK, hKsub, hphiK, fun n => ?_, fun k => ?_⟩
  · rw [hfb]; exact hbK n
  · simpa only [hfb] using hunif k

end Paper
