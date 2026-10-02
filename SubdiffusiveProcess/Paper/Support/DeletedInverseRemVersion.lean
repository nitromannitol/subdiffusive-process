import SubdiffusiveProcess.Paper.Support.DeletedInverseFamily








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.AuditRepairs
open Paper

theorem deleted_inverse_rem_version
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Rem : MeasurableSpace Ω)
    {d : ℕ} (Q : Opens (SpatialCoordinates d)) (S : ResponseSpace Q)
    (a : ℕ → Ω → PositiveCoefficient Q) (seq : ℕ → ℕ) (hseq : StrictMono seq)
    (E : Ω → _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : ∀ ω, DirichletForm.EnergyMeasure (E ω).toClosedForm)
    (ell : Ω → SpatialCoordinates d → ℝ) (G : Ω → DomainL2 Q →L[ℝ] DomainL2 Q)
    (hdata : ∀ᵐ ω ∂P, ∃ D : DeletedInverseData Q (E ω) (Gamma ω) (ell ω), D.operator = G ω)
    (hconv : ∀ f : DomainL2 Q, TendstoInMeasure P
      (fun n ω => inverseResponse S (a (seq n) ω)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (fun ω => inner ℝ f (G ω f)))
    (N0 : ℕ) (hfinite : ∀ N, N0 ≤ N → ∀ f : DomainL2 Q,
      Measurable[Rem] (fun ω => inverseResponse S (a N ω)
        ((sobolevVolumeLoad f).comp S.space.subtypeL))) :
    ∃ Gv : Ω → DomainL2 Q →L[ℝ] DomainL2 Q,
      Gv =ᵐ[P] G ∧
      (∀ f g : DomainL2 Q, Measurable[Rem] (fun ω => inner ℝ f (Gv ω g))) ∧
      (∀ᵐ ω ∂P, ∃ D : DeletedInverseData Q (E ω) (Gamma ω) (ell ω), D.operator = Gv ω) := by
  classical
  have hver : ∀ h : DomainL2 Q, ∃ φ : Ω → ℝ, Measurable[Rem] φ ∧
      φ =ᵐ[P] fun ω => inner ℝ h (G ω h) := by
    intro h
    exact aux_lem_borel_weights_rem_version P Rem _ _ N0
      (fun n hn => hfinite (seq n) (hn.trans (hseq.id_le n)) h) (hconv h)
  choose φ hφmeas hφae using hver
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq (DomainL2 Q)
  let ψ : ℕ × ℕ → Ω → ℝ := fun p ω =>
    (φ (e p.1 + e p.2) ω - φ (e p.1 - e p.2) ω) / 4
  have hψmeas : ∀ p, Measurable[Rem] (ψ p) := fun p =>
    ((hφmeas _).sub (hφmeas _)).div_const 4
  have hsymm : ∀ᵐ ω ∂P, ∀ f g : DomainL2 Q,
      inner ℝ f (G ω g) = inner ℝ (G ω f) g := by
    filter_upwards [hdata] with ω hω
    obtain ⟨D, hD⟩ := hω
    simpa only [hD] using D.symmetric
  have hψae : ∀ p, ψ p =ᵐ[P] fun ω => inner ℝ (e p.1) (G ω (e p.2)) := by
    intro p
    filter_upwards [hφae (e p.1 + e p.2), hφae (e p.1 - e p.2), hsymm] with ω h1 h2 h3
    have hs : inner ℝ (e p.2) (G ω (e p.1)) = inner ℝ (e p.1) (G ω (e p.2)) := by
      rw [h3]
      exact real_inner_comm _ _
    dsimp only [ψ]
    rw [h1, h2]
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right]
    rw [hs]
    ring
  obtain ⟨Gv, hGv, hmeas⟩ :=
    aux_lem_borel_weights_operator_version P Rem G e he ψ hψmeas hψae
  refine ⟨Gv, hGv, hmeas, ?_⟩
  filter_upwards [hdata, hGv] with ω hω hv
  obtain ⟨D, hD⟩ := hω
  exact ⟨D, hD.trans hv.symm⟩

end SubdiffusiveProcess.AuditRepairs
