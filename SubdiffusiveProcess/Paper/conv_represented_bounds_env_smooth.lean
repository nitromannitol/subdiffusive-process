import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Sobolev.UniformSmoothSources
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Tactic

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Source module, smooth H¹ representatives, and uniform approximation of test functions.**
On one cube `Q = centeredCube z r hr`, let `D` be a countable rational module of `L²(Q)` whose
elements have smooth compactly supported representatives `f g` inside `Q`, let `theta h` be smooth
functions with H¹ representatives `thetaH1 h` (`thetaH1 h` has values `theta h`), containing every
`f g`, and let smooth compactly supported test functions be approximated in every `C^k` norm by
sources `f (g n)`.  Then the sources have H¹ representatives `phi g` (with the class of `g` as
L²-part) and every continuous compactly supported function in `Q` is uniformly approximated by
`phi g`, `g ∈ D` (first `C_c` mollification, then the source approximation).  These are the data
`D, phi, hPhi, hsmooth` of `in_represented_bounds_seq`. -/
theorem conv_represented_bounds_env_smooth
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (f : D → SpatialCoordinates d → ℝ)
    (T : Type) (theta : T → SpatialCoordinates d → ℝ)
    (thetaH1 : T → H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hf : ∀ g : D, ContDiff ℝ ∞ (f g) ∧ HasCompactSupport (f g) ∧
      tsupport (f g) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      ((g.val : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f g)
    (hT : ∀ h : T, (thetaH1 h).toFun = theta h)
    (hTf : ∀ g : D, ∃ h : T, theta h = f g)
    (hdens : ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (K : Set (SpatialCoordinates d)) (g : ℕ → D), IsCompact K ∧
        K ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧ tsupport phi ⊆ K ∧
        (∀ n : ℕ, tsupport (f (g n)) ⊆ K) ∧
        ∀ k : ℕ, TendstoUniformly
          (fun n x => iteratedFDeriv ℝ k (fun y => f (g n) y - phi y) x)
          (fun _ => 0) atTop) :
    ∃ phi : D → H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      (∀ g : D, (phi g).toFun = f g) ∧
      (∀ g : D, ContDiff ℝ (⊤ : ℕ∞) (phi g).toFun ∧ HasCompactSupport (phi g).toFun ∧
        tsupport (phi g).toFun ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (sobolevDataOfH1 (phi g)).1 = g.val) ∧
      (∀ fc : SpatialCoordinates d → ℝ, Continuous fc → HasCompactSupport fc →
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        ∀ ε : ℝ, 0 < ε → ∃ g : D, ∀ x : SpatialCoordinates d, |(phi g).toFun x - fc x| ≤ ε) := by
  classical
  choose h hh using hTf
  refine ⟨fun g => thetaH1 (h g), ?_, ?_, ?_⟩
  · intro g
    show (thetaH1 (h g)).toFun = f g
    rw [hT, hh]
  · intro g
    have hfun : (thetaH1 (h g)).toFun = f g := by rw [hT, hh]
    obtain ⟨h1, h2, h3, h4⟩ := hf g
    refine ⟨?_, ?_, ?_, ?_⟩
    · show ContDiff ℝ (⊤ : ℕ∞) (thetaH1 (h g)).toFun
      rw [hfun]; exact h1
    · show HasCompactSupport (thetaH1 (h g)).toFun
      rw [hfun]; exact h2
    · show tsupport (thetaH1 (h g)).toFun ⊆ _
      rw [hfun]; exact h3
    · have hc := sobolevDataOfH1_fst_coeFn (thetaH1 (h g))
      rw [hfun] at hc
      exact Lp.ext (hc.trans h4.symm)
  · intro fc hfc hfs hfU ε hε
    obtain ⟨psi, hpsi, hpsis, hpsiU, hpsi_close⟩ :=
      SubdiffusiveProcess.SmoothSources.exists_uniform_smooth_approximation fc hfc hfs
        (centeredCube z r hr : Set (SpatialCoordinates d)) hfU (ε / 2) (half_pos hε)
    obtain ⟨K, g, _, _, _, _, hunif⟩ := hdens psi hpsi hpsis hpsiU
    have h0 := hunif 0
    rw [Metric.tendstoUniformly_iff] at h0
    obtain ⟨n, hn⟩ := (h0 (ε / 2) (half_pos hε)).exists
    refine ⟨g n, fun x => ?_⟩
    have hx := hn x
    rw [dist_eq_norm, zero_sub, norm_neg, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hx
    have hfun : (thetaH1 (h (g n))).toFun = f (g n) := by rw [hT, hh]
    show |(thetaH1 (h (g n))).toFun x - fc x| ≤ ε
    rw [hfun]
    have h2 := hpsi_close x
    calc |f (g n) x - fc x| = |(f (g n) x - psi x) + (psi x - fc x)| := by ring_nf
      _ ≤ |f (g n) x - psi x| + |psi x - fc x| := abs_add_le _ _
      _ ≤ ε := by linarith

end Paper
