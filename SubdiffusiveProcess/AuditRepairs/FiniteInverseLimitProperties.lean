import SubdiffusiveProcess.Sobolev.VolumeResponseOperator

/-! Symmetry, positivity and quadratic response convergence follow directly from
norm convergence of the actual finite volume-source inverses. -/

open Filter MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped Topology

namespace SubdiffusiveProcess.AuditRepairs

theorem symmetric_positive_of_volume_response_tendsto
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hconv : Tendsto GN atTop (𝓝 G)) :
    (∀ f g : DomainL2 Q, inner ℝ (G f) g = inner ℝ f (G g)) ∧
    (∀ f : DomainL2 Q, 0 ≤ inner ℝ f (G f)) := by
  have happ : ∀ f : DomainL2 Q, Tendsto (fun n => GN n f) atTop (𝓝 (G f)) :=
    fun f => ((ContinuousLinearMap.apply ℝ (DomainL2 Q) f).continuous.tendsto G).comp hconv
  constructor
  · intro f g
    have hs : ∀ n, inner ℝ (GN n f) g = inner ℝ f (GN n g) := by
      intro n
      rw [hGN n f, hGN n g, real_inner_comm]
      exact volumeResponse_pairing_symm S (a n) g f
    exact tendsto_nhds_unique ((happ f).inner tendsto_const_nhds)
      ((tendsto_const_nhds.inner (happ g)).congr fun n => (hs n).symm)
  · intro f
    have ht : Tendsto (fun n => inner ℝ f (GN n f)) atTop (𝓝 (inner ℝ f (G f))) :=
      tendsto_const_nhds.inner (happ f)
    exact ge_of_tendsto' ht fun n => by
      rw [hGN n f]
      exact volumeResponse_pairing_nonneg S (a n) f

theorem inverse_response_tendsto_of_volume_operator_tendsto
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hconv : Tendsto GN atTop (𝓝 G)) (f : DomainL2 Q) :
    Tendsto (fun n => inverseResponse S (a n)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (𝓝 (inner ℝ f (G f))) := by
  have ht : Tendsto (fun n => inner ℝ f (GN n f)) atTop (𝓝 (inner ℝ f (G f))) :=
    tendsto_const_nhds.inner
      (((ContinuousLinearMap.apply ℝ (DomainL2 Q) f).continuous.tendsto G).comp hconv)
  apply ht.congr
  intro n
  rw [hGN n f, inverseResponse_eq_load]
  rfl

end SubdiffusiveProcess.AuditRepairs
