import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.CompactSupportCubeFamily
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.PointwiseMonotoneLimit

/-!
# Pointwise limit of the massive cube exhaustion

This file changes the a.e.-ordered zero extensions of the nonnegative cube
solutions into everywhere ordered representatives.  Each representative is
clipped to the maximum-principle interval and recursive finite maxima remove
the countable exceptional sets.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}

private theorem zeroExtension_nonneg_ae {U : Set (Vec d)}
    (hU : MeasurableSet U) (u : H10Function U)
    (hu : 0 ≤ᵐ[volume.restrict U] u.toH1Function.toFun) :
    0 ≤ᵐ[volume] u.zeroExtension := by
  have hu' := (ae_restrict_iff' hU).1 hu
  filter_upwards [hu'] with x hx
  by_cases hxU : x ∈ U
  · simpa only [u.zeroExtension_apply_of_mem hxU] using hx hxU
  · rw [u.zeroExtension_apply_of_not_mem hxU]
    exact le_rfl

private theorem zeroExtension_le_ae {U : Set (Vec d)}
    (hU : MeasurableSet U) (u : H10Function U) {C : ℝ} (hC : 0 ≤ C)
    (hu : u.toH1Function.toFun ≤ᵐ[volume.restrict U] fun _ ↦ C) :
    u.zeroExtension ≤ᵐ[volume] fun _ ↦ C := by
  have hu' := (ae_restrict_iff' hU).1 hu
  filter_upwards [hu'] with x hx
  by_cases hxU : x ∈ U
  · simpa only [u.zeroExtension_apply_of_mem hxU] using hx hxU
  · simpa only [u.zeroExtension_apply_of_not_mem hxU] using hC

private theorem zeroExtension_mono_ae {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V)
    (u : H10Function U) (v : H10Function V)
    (huv : u.toH1Function.toFun ≤ᵐ[volume.restrict U] v.toH1Function.toFun)
    (hv : 0 ≤ᵐ[volume.restrict V] v.toH1Function.toFun) :
    u.zeroExtension ≤ᵐ[volume] v.zeroExtension := by
  have huv' := (ae_restrict_iff' hU).1 huv
  have hv' := (ae_restrict_iff' hV).1 hv
  filter_upwards [huv', hv'] with x hxuv hxv
  by_cases hxU : x ∈ U
  · have hxV : x ∈ V := hUV hxU
    simpa only [u.zeroExtension_apply_of_mem hxU,
      v.zeroExtension_apply_of_mem hxV] using hxuv hxU
  · by_cases hxV : x ∈ V
    · simpa only [u.zeroExtension_apply_of_not_mem hxU,
        v.zeroExtension_apply_of_mem hxV] using hxv hxV
    · rw [u.zeroExtension_apply_of_not_mem hxU,
        v.zeroExtension_apply_of_not_mem hxV]

/-- For nonnegative compactly supported data, the cube exhaustion admits
everywhere nonnegative, bounded and monotone representatives converging
pointwise.  Each representative agrees a.e. with the literal zero extension
of the corresponding zero-Dirichlet solution. -/
theorem exists_pointwiseMonotoneMassiveCubeLimit_of_compactSupport [NeZero d]
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ))
    (hf : ∀ x, 0 ≤ f x) :
    ∃ uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)),
      ∃ v : ℕ → Vec d → ℝ, ∃ u : Vec d → ℝ,
        (∀ n, IsControlledMassiveCubeSolution c rho mu f n (uCube n)) ∧
        (∀ n, v n =ᵐ[volume] (uCube n).zeroExtension) ∧
        (∀ x, Monotone fun n ↦ v n x) ∧
        (∀ n x, 0 ≤ v n x ∧ v n x ≤ ‖compactSupportToC0 f‖ / mu) ∧
        ∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x)) := by
  obtain ⟨uCube, hu, hmono⟩ :=
    exists_monotoneMassiveCubeSolutionFamily_of_compactSupport B hmu f hf
  let C : ℝ := ‖compactSupportToC0 f‖ / mu
  have hC : 0 ≤ C := div_nonneg (norm_nonneg _) hmu.le
  have hnonneg : ∀ n, 0 ≤ᵐ[volume] (uCube n).zeroExtension := by
    intro n
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
    have hfL2 : MemL2On (cube d (n : ℤ)) f :=
      (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).restrict _
    have hlocal := ae_nonneg_of_isMassiveWeakSolutionOn hW hmu
      (B.rhoMin_pos n) (B.lam_pos n) (B.coeff_lower n)
      (B.rho_measurable n) (B.rho_lower n) (B.rho_bounded n) hfL2
      (fun x _ ↦ hf x) (hu n).1
    exact zeroExtension_nonneg_ae hW.isOpen.measurableSet (uCube n) hlocal
  have hle : ∀ n, (uCube n).zeroExtension ≤ᵐ[volume] fun _ ↦ C := by
    intro n
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
    have hlocal : (uCube n).toH1Function.toFun ≤ᵐ[volume.restrict (cube d (n : ℤ))]
        fun _ ↦ C := by
      filter_upwards [(hu n).2.2.2] with x hx
      exact (le_abs_self _).trans hx
    exact zeroExtension_le_ae hW.isOpen.measurableSet (uCube n) hC hlocal
  have hmonoGlobal : ∀ n,
      (uCube n).zeroExtension ≤ᵐ[volume] (uCube (n + 1)).zeroExtension := by
    intro n
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
    have hV := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d ((n + 1 : ℕ) : ℤ)
    have hWV : cube d (n : ℤ) ⊆ cube d ((n + 1 : ℕ) : ℤ) :=
      Section6ExcessDecay.cube_subset_cube_of_le (by omega)
    have hvLocal : 0 ≤ᵐ[volume.restrict (cube d ((n + 1 : ℕ) : ℤ))]
        (uCube (n + 1)).toH1Function.toFun := by
      have hfL2 : MemL2On (cube d ((n + 1 : ℕ) : ℤ)) f :=
        (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).restrict _
      exact ae_nonneg_of_isMassiveWeakSolutionOn hV hmu
        (B.rhoMin_pos (n + 1)) (B.lam_pos (n + 1)) (B.coeff_lower (n + 1))
        (B.rho_measurable (n + 1)) (B.rho_lower (n + 1))
        (B.rho_bounded (n + 1)) hfL2 (fun x _ ↦ hf x) (hu (n + 1)).1
    exact zeroExtension_mono_ae hW.isOpen.measurableSet hV.isOpen.measurableSet
      hWV (uCube n) (uCube (n + 1)) (hmono n) hvLocal
  obtain ⟨v, u, hvEq, hvMono, hvBounds, hvLim⟩ :=
    exists_pointwise_monotone_limit volume hC
      (fun n ↦ (uCube n).zeroExtension) hnonneg hle hmonoGlobal
  exact ⟨uCube, v, u, hu, hvEq, hvMono, hvBounds, hvLim⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
