import SubdiffusiveProcess.Sobolev.WeightedHarmonicBoundaryMaximum
import SubdiffusiveProcess.Compactness.UniformApproximation

/-! Compactness for harmonic solutions with a uniformly approximable fixed trace.
Equicontinuity of the approximating trace problems and the maximum principle
give compactness for the original trace; no limit-form energy claim is made.
-/

open Filter MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology

noncomputable section
namespace SubdiffusiveProcess

/-- Uniform boundary approximation transfers compactness from regular trace problems to the given trace. -/
theorem exists_uniform_harmonic_trace_subseq
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W) (hWne : W.Nonempty)
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Measurable (a n))
    (lam Lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (hbounds : ∀ n x, x ∈ W → lam n ≤ a n x ∧ a n x ≤ Lam n)
    (u : ℕ → H1Function W) (hu : ∀ n, IsWeaklyHarmonicOn (a n) W (u n))
    (V : ℕ → SpatialCoordinates d → ℝ)
    (hVc : ∀ n, ContinuousOn (V n) (closure W))
    (hVr : ∀ n, (u n).toFun =ᵐ[volume.restrict W] V n)
    (b : SpatialCoordinates d → ℝ)
    (hVb : ∀ n x, x ∈ frontier W → V n x = b x)
    (M : ℝ) (hM : ∀ x ∈ frontier W, |b x| ≤ M)
    (bN : ℕ → SpatialCoordinates d → ℝ)
    (hbN : TendstoUniformlyOn bN b atTop (frontier W))
    (uN : ℕ → ℕ → H1Function W)
    (huN : ∀ m n, IsWeaklyHarmonicOn (a n) W (uN m n))
    (VN : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (hVNc : ∀ m n, ContinuousOn (VN m n) (closure W))
    (hVNr : ∀ m n, (uN m n).toFun =ᵐ[volume.restrict W] VN m n)
    (hVNb : ∀ m n x, x ∈ frontier W → VN m n x = bN m x)
    (hEqui : ∀ m, Equicontinuous (fun n (x : closure W) => VN m n x)) :
    ∃ (U : SpatialCoordinates d → ℝ) (ns : ℕ → ℕ), StrictMono ns ∧
      ContinuousOn U (closure W) ∧
      TendstoUniformlyOn (fun n => V (ns n)) U atTop (closure W) ∧
      (∀ x ∈ frontier W, U x = b x) := by
  classical
  let K := closure W
  letI hKcompact : CompactSpace K := isCompact_iff_compactSpace.mp
    hW.isBoundedDomain.isBounded.isCompact_closure
  letI hKnonempty : Nonempty K := hWne.closure.to_subtype
  let F : ℕ → K → ℝ := fun n x => V n x
  let A : ℕ → ℕ → K → ℝ := fun m n x => VN m n x
  have happrox : ∀ eps : ℝ, 0 < eps → ∃ m, ∀ n x, dist (F n x) (A m n x) < eps := by
    intro eps heps
    obtain ⟨m, hm⟩ := (Metric.tendstoUniformlyOn_iff.mp hbN (eps / 2) (half_pos heps)).exists
    refine ⟨m, ?_⟩
    intro n x
    have hbd : ∀ y ∈ frontier W, |V n y - VN m n y| ≤ eps / 2 := by
      intro y hy
      rw [hVb n y hy, hVNb m n y hy]
      simpa only [Real.dist_eq] using (hm y hy).le
    have hmax := abs_sub_le_on_closure_of_harmonic_of_frontier_le hW (a n) (ha n)
      (lam n) (Lam n) (hlam n) (hbounds n) (u n) (uN m n) (hu n) (huN m n)
      (V n) (VN m n) (hVc n) (hVNc m n) (hVr n) (hVNr m n) (eps / 2) hbd
    exact (show dist (F n x) (A m n x) ≤ eps / 2 by
      simpa only [F, A, Real.dist_eq] using hmax x x.property).trans_lt (half_lt_self heps)
  have hbound : ∀ x : K, ∃ C : ℝ, ∀ n, ‖F n x‖ ≤ C := by
    intro x
    refine ⟨M, ?_⟩
    intro n
    have hb : ∀ᵐ y ∂volume.restrict W, lam n ≤ a n y ∧ a n y ≤ Lam n := by
      filter_upwards [self_mem_ae_restrict hW.isOpen.measurableSet] with y hy
      exact hbounds n y hy
    have hbd : ∀ y ∈ frontier W, |V n y| ≤ M := by
      intro y hy
      rw [hVb n y hy]
      exact hM y hy
    simpa only [F, Real.norm_eq_abs] using
      abs_le_on_closure_of_harmonic_of_frontier_le hW (a n) (lam n) (Lam n) (hlam n)
        (ha n).aestronglyMeasurable hb (u n) (hu n) (V n) (hVc n) (hVr n) M hbd x x.property
  obtain ⟨g, ns, hns, hgc, hlim⟩ :=
    exists_uniform_subseq_of_uniform_approximation F A hEqui happrox hbound
  let U : SpatialCoordinates d → ℝ := fun x => if hx : x ∈ K then g ⟨x, hx⟩ else 0
  have hUc : ContinuousOn U K := by
    rw [continuousOn_iff_continuous_restrict]
    exact hgc.congr (fun x => by dsimp [U]; rw [dif_pos x.property])
  have huni : TendstoUniformlyOn (fun n => V (ns n)) U atTop K := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [F, U, Function.comp_def, Subtype.coe_prop, dif_pos] using hlim
  refine ⟨U, ns, hns, hUc, huni, ?_⟩
  intro x hx
  have hpoint := huni.tendsto_at (frontier_subset_closure hx)
  have heq : (fun n => V (ns n) x) = fun _ : ℕ => b x :=
    funext (fun n => hVb (ns n) x hx)
  rw [heq] at hpoint
  exact tendsto_nhds_unique hpoint tendsto_const_nhds

end SubdiffusiveProcess
