import SubdiffusiveProcess.Sobolev.ResponseInjectivity
import SubdiffusiveProcess.Compactness.OperatorLimits

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

theorem killedInverse_exists_unique
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGN : ∀ (n : ℕ) (f : DomainL2 Q), GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (D : Set (DomainL2 Q)) (hDdense : Dense D)
    (hDadd : ∀ x ∈ D, ∀ y ∈ D, x + y ∈ D)
    (hcompact : IsCompact (closure (⋃ n : ℕ,
      (GN n) '' Metric.closedBall (0 : DomainL2 Q) 1)))
    (hresponse : ∀ f ∈ D, CauchySeq (fun n => inner ℝ f (GN n f)))
    (hmesh : ∀ φ ∈ D, ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → S.space, ∃ C : ℝ,
      (∀ n : ℕ, responseForm S (a n) (w n) (w n) ≤ C) ∧
      (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε)) :
    ∃! G : DomainL2 Q →L[ℝ] DomainL2 Q,
      Tendsto GN atTop (𝓝 G) ∧ IsCompactOperator G ∧
      (∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) ∧ Function.Injective G := by
  have hsym : ∀ (n : ℕ) (x y : DomainL2 Q),
      inner ℝ (GN n x) y = inner ℝ x (GN n y) := by
    intro n x y
    rw [hGN, hGN, real_inner_comm]
    exact volumeResponse_pairing_symm S (a n) y x
  have hpos : ∀ (n : ℕ) (x : DomainL2 Q), 0 ≤ inner ℝ x (GN n x) := by
    intro n x
    rw [hGN]
    exact volumeResponse_pairing_nonneg S (a n) x
  obtain ⟨G, ⟨hGtend, hGcpt, hGsym, hGpos⟩, hGuniq⟩ :=
    existsUnique_limit_of_collectively_compact_quadratic_responses
      hDdense hDadd hsym hpos hcompact hresponse
  have hinner : ∀ f : DomainL2 Q,
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL))
        atTop (𝓝 (inner ℝ f (G f))) := by
    intro f
    have happ : Tendsto (fun n => GN n f) atTop (𝓝 (G f)) :=
      ((continuous_id.clm_apply continuous_const).tendsto G).comp hGtend
    have hfin : Tendsto (fun n => inner ℝ f (GN n f)) atTop (𝓝 (inner ℝ f (G f))) :=
      tendsto_const_nhds.inner happ
    refine hfin.congr ?_
    intro n
    rw [hGN n f, inverseResponse_eq_load]
    rfl
  have hinj : Function.Injective G :=
    injective_limit_of_volumeResponse_approximations S a G D hDdense hinner hmesh
  refine ⟨G, ⟨hGtend, hGcpt, hGsym, hGpos, hinj⟩, ?_⟩
  rintro G' ⟨hG'tend, -, -, -, -⟩
  exact tendsto_nhds_unique hG'tend hGtend

end SubdiffusiveProcess
