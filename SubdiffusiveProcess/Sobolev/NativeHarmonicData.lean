module

public import SubdiffusiveProcess.Sobolev.NativeBoundaryMinimizer
public import SubdiffusiveProcess.Sobolev.NativeHarmonicMinimum

@[expose] public section

/-! Native harmonic representatives are the actual graph minimizers for any
boundary datum agreeing almost everywhere. No convergence result is asserted. -/

open MeasureTheory Set TopologicalSpace _root_.SubdiffusiveProcess.EllipticRegularity Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped NNReal

namespace SubdiffusiveProcess

/-- Two weak Sobolev graph elements with the same function class have the same gradient and coincide. -/
theorem weakSobolevGraph_eq_of_fst_eq
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (u v : weakSobolevGraph Q) (h : u.val.1 = v.val.1) : u = v := by
  apply Subtype.ext
  apply Prod.ext h
  apply weakSobolevGraph_gradient_unique (u := v.val.1)
  · rw [← h]
    exact u.property
  · exact v.property

/-- A native harmonic extension equals the graph minimizer with any almost-everywhere equal boundary datum. -/
theorem native_harmonic_minimizer_eq_of_ae_datum
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) w‖)
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (beta v : H1Function (Q : Set (SpatialCoordinates d))) (b : weakSobolevGraph Q)
    (hb : (b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (Q : Set (SpatialCoordinates d))] beta.toFun)
    (htrace : HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) v beta)
    (hharm : IsWeaklyHarmonicOn c (Q : Set (SpatialCoordinates d)) v) :
    (⟨sobolevDataOfH1 v, sobolevDataOfH1_mem_weak v⟩ : weakSobolevGraph Q) =
      dirichletMinimizer (killedResponseSpace hP) a b := by
  have hbeta : (⟨sobolevDataOfH1 beta, sobolevDataOfH1_mem_weak beta⟩ : weakSobolevGraph Q) = b :=
    weakSobolevGraph_eq_of_fst_eq _ _ (Lp.ext ((sobolevDataOfH1_fst_coeFn beta).trans hb.symm))
  rw [native_boundary_minimizer_eq hP a c hc beta v htrace
    (native_harmonic_energy_eq_infimum a c hc beta v htrace hharm).le, hbeta]

end SubdiffusiveProcess
