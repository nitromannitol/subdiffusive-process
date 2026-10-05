module

public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.in_deterministic

@[expose] public section

/-!+# Harmonic replacement of a Hölder trace

The standing Sobolev trace right inverse supplies a continuous Sobolev datum
on every cube. Its harmonic replacement realizes the prescribed frontier
values. No candidate estimate or stochastic input is used here.
-/

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The unit trace right inverse gives a continuous Sobolev extension on every positive cube. -/
theorem aux_candidate_holder_harmonic_extension_datum
    {d : ℕ} (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (U : SpatialCoordinates d → ℝ)
    (hU : IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) U) :
    ∃ (b : weakSobolevGraph (centeredCube z r hr)) (B : SpatialCoordinates d → ℝ),
      Continuous B ∧
      (b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] B ∧
      ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), B x = U x := by
  have hUnit := aux_lem_extension_isHolderOn_dilation z r hr beta U hU
  obtain ⟨b0, B0, hB0, hb0, htrace0, _⟩ :=
    Sob.traceRightInverse beta hbeta 0 1 one_pos rfl
      (fun x => U (cubeDilation z 0 r x)) hUnit
  obtain ⟨b, hb⟩ := aux_lem_extension_weak_pushforward z hr one_pos b0
  let B : SpatialCoordinates d → ℝ := fun x => B0 (r⁻¹ • (x - z))
  have hchart : Continuous (fun x : SpatialCoordinates d => r⁻¹ • (x - z)) := by
    fun_prop
  have hB : Continuous B := hB0.comp hchart
  refine ⟨b, B, hB, ?_, ?_⟩
  · apply (aux_lem_extension_ae_dilation_iff z hr one_pos _).mpr
    filter_upwards [hb, hb0] with x hbx hb0x
    change b.val.1 (cubeDilation z 0 r x) = B0 (r⁻¹ • (cubeDilation z 0 r x - z))
    rw [← hbx, hb0x, aux_lem_extension_cubeDilation_inv' z hr]
  · intro x hx
    have hfront : r⁻¹ • (x - z) ∈
        frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
      apply (aux_lem_extension_frontier_dilation z hr one_pos _).mp
      rw [aux_lem_extension_cubeDilation_inv z hr]
      exact hx
    change B0 (r⁻¹ • (x - z)) = U x
    rw [htrace0 _ hfront, aux_lem_extension_cubeDilation_inv z hr]

/-- Every Hölder trace of exponent greater than one half has a continuous weak harmonic extension. -/
theorem candidate_holder_harmonic_extension
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (U : SpatialCoordinates d → ℝ)
    (hU : IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) U) :
    ∃ (v : weakSobolevGraph (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = U x) ∧
      ∀ psi : killedSobolevGraph (centeredCube z r hr),
        inner ℝ (sobolevGradient v.val)
          (subspaceGradient (killedSobolevGraph (centeredCube z r hr)) psi) = 0 := by
  obtain ⟨b, B, hB, hb, htrace⟩ :=
    aux_candidate_holder_harmonic_extension_datum hd Sob beta hbeta z r hr U hU
  obtain ⟨bH, hbH, _⟩ := exists_nativeH1Function_of_weakSobolevGraph b
  have hbHrep : bH.toFun =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] B := by
    filter_upwards [hb] with x hx
    exact (congrFun hbH x).trans hx
  obtain ⟨w, hwH, _, V, hV, hVrep, hVtrace⟩ :=
    aux_in_deterministic_core_boundary_harmonic hd z r hr isOpen_univ
      (subset_univ _) B hB.continuousOn bH hbHrep
  let v : weakSobolevGraph (centeredCube z r hr) :=
    ⟨sobolevDataOfH1 (Ω := centeredCube z r hr) w,
      sobolevDataOfH1_mem_weak (Ω := centeredCube z r hr) w⟩
  refine ⟨v, V, hV, ?_, ?_, ?_⟩
  · exact (sobolevDataOfH1_fst_coeFn (Ω := centeredCube z r hr) w).trans hVrep.symm
  · intro x hx
    exact (hVtrace x hx).trans (htrace x hx)
  · exact aux_in_deterministic_core_native_harmonic (Ω := centeredCube z r hr) w hwH

end SubdiffusiveProcess.Paper
