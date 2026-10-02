import SubdiffusiveProcess.Sobolev.HarmonicBoundaryMaximum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.EstimateLimits
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum

/-!+# Stability of continuous harmonic replacements under uniform trace convergence

The boundary maximum principle gives uniform convergence to an existing
harmonic replacement. Normalized comparison estimates then pass without a
loss in their constants. Existence of the limit replacement is a separate input.
-/

open Filter MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal

namespace SubdiffusiveProcess

/-- Uniform convergence on a finite positive-volume set gives convergence of normalized L2 differences. -/
theorem tendsto_normalizedL2_sub_of_tendstoUniformlyOn
    {d : ℕ} (W : Set (SpatialCoordinates d)) (hWm : MeasurableSet W)
    (hWpos : 0 < volume.real W) (hWtop : volume W ≠ ⊤)
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hN : ∀ n, MemLp (UN n) 2 (volume.restrict W))
    (hU : MemLp U 2 (volume.restrict W))
    (hlim : TendstoUniformlyOn UN U atTop W) :
    Tendsto (fun n => normalizedL2On W (fun x => UN n x - U x)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim (eps / 2) (half_pos heps)] with n hn
  have hb := Section6SchauderDatum.normalizedL2On_le_of_ae_abs_le
    hWpos hWtop (half_pos heps).le ((hN n).sub hU) (by
      filter_upwards [ae_restrict_mem hWm] with x hx
      simpa only [Real.dist_eq, abs_sub_comm] using (hn x hx).le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show
    0 ≤ normalizedL2On W (fun x => UN n x - U x) from Real.sqrt_nonneg _)]
  exact hb.trans_lt (half_lt_self heps)

/-- Uniform convergence on a finite positive-volume set preserves its normalized L2 norm. -/
theorem tendsto_normalizedL2_of_tendstoUniformlyOn
    {d : ℕ} (W : Set (SpatialCoordinates d)) (hWm : MeasurableSet W)
    (hWpos : 0 < volume.real W) (hWtop : volume W ≠ ⊤)
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hN : ∀ n, MemLp (UN n) 2 (volume.restrict W))
    (hU : MemLp U 2 (volume.restrict W))
    (hlim : TendstoUniformlyOn UN U atTop W) :
    Tendsto (fun n => normalizedL2On W (UN n)) atTop (𝓝 (normalizedL2On W U)) := by
  exact Section6TheoremC.tendsto_normalizedL2On_of_tendsto_sub hN hU
    (tendsto_normalizedL2_sub_of_tendstoUniformlyOn W hWm hWpos hWtop UN U hN hU hlim)

/-- Uniformly convergent frontier data give uniformly convergent harmonic graph representatives. -/
theorem tendstoUniformlyOn_harmonic_of_tendstoUniformlyOn_frontier
    {d : ℕ} [NeZero d] {W : Opens (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain (W : Set (SpatialCoordinates d)))
    (vN : ℕ → weakSobolevGraph W) (v : weakSobolevGraph W)
    (hN : ∀ n, ∀ psi : killedSobolevGraph W,
      inner ℝ (sobolevGradient (vN n).val)
        (subspaceGradient (killedSobolevGraph W) psi) = 0)
    (hv : ∀ psi : killedSobolevGraph W,
      inner ℝ (sobolevGradient v.val)
        (subspaceGradient (killedSobolevGraph W) psi) = 0)
    (VN : ℕ → SpatialCoordinates d → ℝ) (V : SpatialCoordinates d → ℝ)
    (hVcN : ∀ n, ContinuousOn (VN n) (closure (W : Set (SpatialCoordinates d))))
    (hVc : ContinuousOn V (closure (W : Set (SpatialCoordinates d))))
    (hrepN : ∀ n, ((vN n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (W : Set (SpatialCoordinates d))] VN n)
    (hrep : (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (W : Set (SpatialCoordinates d))] V)
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (htraceN : ∀ n, ∀ x ∈ frontier (W : Set (SpatialCoordinates d)), VN n x = UN n x)
    (htrace : ∀ x ∈ frontier (W : Set (SpatialCoordinates d)), V x = U x)
    (hlim : TendstoUniformlyOn UN U atTop (frontier (W : Set (SpatialCoordinates d)))) :
    TendstoUniformlyOn VN V atTop (closure (W : Set (SpatialCoordinates d))) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim (eps / 2) (half_pos heps)] with n hn
  have hb : ∀ x ∈ frontier (W : Set (SpatialCoordinates d)), |VN n x - V x| ≤ eps / 2 := by
    intro x hx
    rw [htraceN n x hx, htrace x hx]
    simpa only [Real.dist_eq, abs_sub_comm] using (hn x hx).le
  have hb' := abs_sub_le_on_closure_of_weakSobolevGraph_frontier hW (vN n) v
    (hN n) hv (VN n) V (hVcN n) hVc (hrepN n) hrep (eps / 2) hb
  intro x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (hb' x hx).trans_lt (half_lt_self heps)

/-- Comparison inequalities pass through uniform convergence with their exact limiting bound. -/
theorem normalizedL2_comparison_le_of_uniform_limits
    {d : ℕ} (W : Set (SpatialCoordinates d)) (hWm : MeasurableSet W)
    (hWpos : 0 < volume.real W) (hWtop : volume W ≠ ⊤)
    (UN VN : ℕ → SpatialCoordinates d → ℝ) (U V : SpatialCoordinates d → ℝ)
    (hUN : ∀ n, MemLp (UN n) 2 (volume.restrict W))
    (hVN : ∀ n, MemLp (VN n) 2 (volume.restrict W))
    (hU : MemLp U 2 (volume.restrict W)) (hV : MemLp V 2 (volume.restrict W))
    (hUlim : TendstoUniformlyOn UN U atTop W)
    (hVlim : TendstoUniformlyOn VN V atTop W)
    (BN : ℕ → ℝ) (B : ℝ) (hB : Tendsto BN atTop (𝓝 B))
    (hbound : ∀ᶠ n in atTop, normalizedL2On W (fun x => UN n x - VN n x) ≤ BN n) :
    normalizedL2On W (fun x => U x - V x) ≤ B := by
  have hlim := tendsto_normalizedL2_of_tendstoUniformlyOn W hWm hWpos hWtop
    (fun n x => UN n x - VN n x) (fun x => U x - V x)
    (fun n => (hUN n).sub (hVN n)) (hU.sub hV) (hUlim.sub hVlim)
  exact le_of_tendsto_of_tendsto hlim hB hbound

end SubdiffusiveProcess
