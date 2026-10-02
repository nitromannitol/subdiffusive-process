import SubdiffusiveProcess.Sobolev.ResponsePositivity
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.KilledGraph
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Killed volume responses: norm bound and extension from a dense set of data

For the killed response space of a cube and a coefficient satisfying the coercivity bound
`‖v‖² ≤ K · E_a(v, v)` on the killed graph, the volume-source solution operator has operator norm
at most `K`.  A uniform such bound and convergence of the solutions on a dense set of data
therefore give convergence for all data.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace Topology
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- The `L²` component of the volume-source solution of the killed response space. -/
def killedVolumeResponse
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Q,
      ‖(z : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) z‖)
    (a : PositiveCoefficient Q) (f : DomainL2 Q) : DomainL2 Q :=
  (responseSolution (killedResponseSpace (Ω := Q) hP) a
    ((sobolevVolumeLoad f).comp (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1

/-- Operator-norm bound of the killed volume response from the coercivity bound. -/
theorem killedVolumeResponse_norm_le
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Q,
      ‖(z : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) z‖)
    (a : PositiveCoefficient Q) (K : ℝ) (hK : 0 ≤ K)
    (hcoer : ∀ v : killedSobolevGraph Q,
      ‖(v : SobolevData Q).1‖ ^ 2 ≤ K * sobolevCoefficientForm a v v)
    (f : DomainL2 Q) : ‖killedVolumeResponse hP a f‖ ≤ K * ‖f‖ := by
  set S := killedResponseSpace (Ω := Q) hP with hS
  set L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad f).comp S.space.subtypeL with hL
  set u : S.space := responseSolution S a L with hu
  have hspec : responseForm S a u u = L u := responseSolution_spec S a L u
  have hform : responseForm S a u u = sobolevCoefficientForm a (u : SobolevData Q)
      (u : SobolevData Q) := rfl
  have hLu : L u = inner ℝ f (u : SobolevData Q).1 := rfl
  have h1 : ‖(u : SobolevData Q).1‖ ^ 2 ≤ K * (‖f‖ * ‖(u : SobolevData Q).1‖) := by
    have h2 := hcoer u
    rw [← hform, hspec, hLu] at h2
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hx : killedVolumeResponse hP a f = (u : SobolevData Q).1 := rfl
  rw [hx]
  rcases eq_or_lt_of_le (norm_nonneg (u : SobolevData Q).1) with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hK (norm_nonneg _)
  · have h3 : ‖(u : SobolevData Q).1‖ * ‖(u : SobolevData Q).1‖ ≤
        (K * ‖f‖) * ‖(u : SobolevData Q).1‖ := by
      calc ‖(u : SobolevData Q).1‖ * ‖(u : SobolevData Q).1‖ = ‖(u : SobolevData Q).1‖ ^ 2 :=
            (sq _).symm
        _ ≤ K * (‖f‖ * ‖(u : SobolevData Q).1‖) := h1
        _ = (K * ‖f‖) * ‖(u : SobolevData Q).1‖ := by ring
    exact le_of_mul_le_mul_right h3 hpos

/-- Extension from a dense set of data: uniformly bounded killed volume responses that converge on
a dense set of data converge for all data. -/
theorem killedVolumeResponse_tendsto_of_dense
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Q,
      ‖(z : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) z‖)
    (a : ℕ → PositiveCoefficient Q) (K : ℕ → ℝ) (Mb : ℝ)
    (hK0 : ∀ k, 0 ≤ K k) (hKb : ∀ k, K k ≤ Mb)
    (hcoer : ∀ k (v : killedSobolevGraph Q),
      ‖(v : SobolevData Q).1‖ ^ 2 ≤ K k * sobolevCoefficientForm (a k) v v)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (D : Set (DomainL2 Q)) (hD : Dense D)
    (hDconv : ∀ f ∈ D,
      Tendsto (fun k => killedVolumeResponse hP (a k) f) atTop (𝓝 (G f)))
    (f : DomainL2 Q) :
    Tendsto (fun k => killedVolumeResponse hP (a k) f) atTop (𝓝 (G f)) := by
  have hMb0 : 0 ≤ Mb := (hK0 0).trans (hKb 0)
  choose A hA using fun k =>
    (existsUnique_volumeResponseOperator (killedResponseSpace (Ω := Q) hP) (a k)).exists
  have hAeq : ∀ k g, A k g = killedVolumeResponse hP (a k) g := fun k g => hA k g
  have hAnorm : ∀ k g, ‖A k g‖ ≤ Mb * ‖g‖ := fun k g => by
    rw [hAeq]
    exact (killedVolumeResponse_norm_le hP (a k) (K k) (hK0 k) (hcoer k) g).trans
      (mul_le_mul_of_nonneg_right (hKb k) (norm_nonneg _))
  simp only [← hAeq] at hDconv ⊢
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C : ℝ := Mb + ‖G‖ + 1 with hC
  have hCpos : 0 < C := by
    have := norm_nonneg G
    linarith
  obtain ⟨g, hgD, hg⟩ := hD.exists_dist_lt f (show 0 < ε / (3 * C) by positivity)
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (hDconv g hgD) (ε / 3) (by positivity)
  refine ⟨N0, fun k hk => ?_⟩
  have h1 := hN0 k hk
  rw [dist_eq_norm] at h1 hg ⊢
  have hdec : A k f - G f = A k (f - g) + (A k g - G g) + G (g - f) := by
    simp only [map_sub]
    abel
  have hfg : ‖f - g‖ < ε / (3 * C) := hg
  have hgf : ‖g - f‖ < ε / (3 * C) := by rw [norm_sub_rev]; exact hg
  have hb1 : ‖A k (f - g)‖ ≤ Mb * ‖f - g‖ := hAnorm k _
  have hb2 : ‖G (g - f)‖ ≤ ‖G‖ * ‖g - f‖ := G.le_opNorm _
  have hε3 : ε / (3 * C) * C = ε / 3 := by field_simp
  calc ‖A k f - G f‖ ≤ ‖A k (f - g)‖ + ‖A k g - G g‖ + ‖G (g - f)‖ := by
        rw [hdec]; exact norm_add₃_le
    _ < ε := by
        have hMbn : Mb * ‖f - g‖ ≤ Mb * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_left hfg.le hMb0
        have hGn : ‖G‖ * ‖g - f‖ ≤ ‖G‖ * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_left hgf.le (norm_nonneg _)
        have hsum : Mb * (ε / (3 * C)) + ‖G‖ * (ε / (3 * C)) < 2 * (ε / 3) := by
          have h4 : (Mb + ‖G‖) * (ε / (3 * C)) < C * (ε / (3 * C)) :=
            mul_lt_mul_of_pos_right (by rw [hC]; linarith) (by positivity)
          have h5 : C * (ε / (3 * C)) = ε / 3 := by field_simp
          have h6 : Mb * (ε / (3 * C)) + ‖G‖ * (ε / (3 * C)) = (Mb + ‖G‖) * (ε / (3 * C)) := by
            ring
          linarith
        linarith

/-- A dense sequence in the `L²` space of a domain. -/
theorem exists_dense_seq_domainL2 (Q : Opens (SpatialCoordinates d)) :
    ∃ u : ℕ → DomainL2 Q, DenseRange u := by
  letI exponentAtLeastOne : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  letI finiteExponent : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  haveI domainSecondCountable : SecondCountableTopology (DomainL2 Q) := by
    change SecondCountableTopology (Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    infer_instance
  exact TopologicalSpace.exists_dense_seq (DomainL2 Q)

end SubdiffusiveProcess
