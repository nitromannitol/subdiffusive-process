module

public import SubdiffusiveProcess.Paper.candidate_holder_harmonic_extension
public import SubdiffusiveProcess.Sobolev.HarmonicTraceLimit

@[expose] public section

/-!+# The harmonic comparison passage with an actual Hölder trace

An eventual finite comparison bank passes to the harmonic extension of its
limiting Hölder trace. All finite estimates and the source convergence refer
to the same sequence. This module does not supply that finite bank.
-/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal

noncomputable section
namespace Paper

/-- An eventual harmonic comparison bank passes through uniform source convergence without a gradient-bound premise. -/
theorem candidate_harmonic_comparison_passage
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (htrace : IsHolderOn beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) U)
    (hUlim : TendstoUniformlyOn UN U atTop
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (W : Set (SpatialCoordinates d))
    (hW : W ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hWm : MeasurableSet W) (hWpos : 0 < volume.real W) (hWtop : volume W ≠ ⊤)
    (hUN : ∀ n, MemLp (UN n) 2 (volume.restrict W))
    (hU : MemLp U 2 (volume.restrict W))
    (BN : ℕ → ℝ) (B : ℝ) (hB : Tendsto BN atTop (𝓝 B))
    (hbank : ∀ᶠ n in atTop,
      ∃ (v : weakSobolevGraph (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
        ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = UN n x) ∧
        (∀ psi : killedSobolevGraph (centeredCube z r hr),
          inner ℝ (sobolevGradient v.val)
            (subspaceGradient (killedSobolevGraph (centeredCube z r hr)) psi) = 0) ∧
        normalizedL2On W (fun x => UN n x - V x) ≤ BN n) :
    ∃ (v : weakSobolevGraph (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = U x) ∧
      (∀ psi : killedSobolevGraph (centeredCube z r hr),
        inner ℝ (sobolevGradient v.val)
          (subspaceGradient (killedSobolevGraph (centeredCube z r hr)) psi) = 0) ∧
      normalizedL2On W (fun x => U x - V x) ≤ B := by
  obtain ⟨v, V, hVc, hVr, hVt, hVh⟩ :=
    candidate_holder_harmonic_extension hd Sob beta hbeta z r hr U htrace
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hbank
  have hbank' := fun n : ℕ => hn0 (n + n0) (Nat.le_add_left n0 n)
  choose vN VN hNc hNr hNt hNh hNb using hbank'
  have hUlim' : TendstoUniformlyOn (fun n => UN (n + n0)) U atTop
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    exact (tendsto_add_atTop_nat n0).eventually
      (Metric.tendstoUniformlyOn_iff.mp hUlim eps heps)
  have hVlim := tendstoUniformlyOn_harmonic_of_tendstoUniformlyOn_frontier
    (aux_lem_extension_isOpenBoundedConvexDomain_centeredCube z hr) vN v
    hNh hVh VN V hNc hVc hNr hVr (fun n => UN (n + n0)) U hNt hVt
    (hUlim'.mono frontier_subset_closure)
  have hVp : MemLp V 2 (volume.restrict W) :=
    ((Lp.memLp v.val.1).ae_eq hVr).mono_measure (Measure.restrict_mono hW le_rfl)
  have hVNp : ∀ n, MemLp (VN n) 2 (volume.restrict W) := fun n =>
    ((Lp.memLp (vN n).val.1).ae_eq (hNr n)).mono_measure
      (Measure.restrict_mono hW le_rfl)
  refine ⟨v, V, hVc, hVr, hVt, hVh, ?_⟩
  exact normalizedL2_comparison_le_of_uniform_limits W hWm hWpos hWtop
    (fun n => UN (n + n0)) VN U V (fun n => hUN (n + n0)) hVNp hU hVp
    (hUlim'.mono (hW.trans subset_closure)) (hVlim.mono (hW.trans subset_closure))
    (fun n => BN (n + n0)) B (hB.comp (tendsto_add_atTop_nat n0))
    (Filter.Eventually.of_forall hNb)

end Paper
