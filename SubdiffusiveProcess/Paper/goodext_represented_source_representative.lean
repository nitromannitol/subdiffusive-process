import SubdiffusiveProcess.Paper.candidate_represented_source_bank

/-! Pulling source regularity through equal-law environments gives an almost sure compact source bank.
The source regularity estimate itself is a premise; no candidate Good event is assumed.
-/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Every smooth source response has a zero-boundary Hölder representative at almost every environment. -/
theorem goodext_represented_source_representative
    {d : ℕ} [NeZero d] {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (mu : Measure Ξ) (P : Measure Ω)
    (env : ℕ → Ω → Ξ) (henv : ∀ n, Measurable (env n))
    (hLaw : ∀ n, Measure.map (env n) P = mu) (phi : ℕ → ℕ)
    (Qc : SpatialCoordinates d) (Qr : ℝ) (hQr : 0 < Qr)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (S : ResponseSpace (centeredCube Qc Qr hQr))
    (hS : S.space = killedSobolevGraph (centeredCube Qc Qr hQr))
    (a : ℕ → Ξ → PositiveCoefficient (centeredCube Qc Qr hQr))
    (GN : ℕ → Ξ → DomainL2 (centeredCube Qc Qr hQr) →L[ℝ]
      DomainL2 (centeredCube Qc Qr hQr))
    (hGN : ∀ n xi fL2, GN n xi fL2 =
      (responseSolution S (a n xi) ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).val.1)
    (GE : Ω → DomainL2 (centeredCube Qc Qr hQr) →L[ℝ]
      DomainL2 (centeredCube Qc Qr hQr))
    (hGE : ∀ᵐ omega ∂P, Tendsto (fun n => GN (phi n) (env n omega)) atTop (𝓝 (GE omega)))
    (K : ℕ → Ξ → ℝ) (C : ℝ≥0)
    (hKmem : ∀ n, MemLp (K n) 1 mu) (hKnorm : ∀ n, eLpNorm (K n) 1 mu ≤ C)
    (hSource : ∀ᵐ xi ∂mu, ∀ (n : ℕ) (f : SpatialCoordinates d → ℝ) (Kf : ℝ),
      ContDiff ℝ ∞ f → 0 ≤ Kf →
      (∀ᵐ x ∂volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), |f x| ≤ Kf) →
      ∀ u : killedSobolevGraph (centeredCube Qc Qr hQr),
        (∀ psi : killedSobolevGraph (centeredCube Qc Qr hQr),
          sobolevCoefficientForm (a n xi) u.val psi.val =
            ∫ x in (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), f x * psi.val.1 x) →
        ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
          (u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), U x = 0) ∧
          IsHolderOn beta (closedCube Qc Qr hQr : Set (SpatialCoordinates d)) U ∧
          cAlphaNorm beta (closedCube Qc Qr hQr : Set (SpatialCoordinates d)) U ≤ K n xi * Kf) :
    ∀ᵐ omega ∂P, ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ fL2 : DomainL2 (centeredCube Qc Qr hQr),
        (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] f →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) ∧
          (GE omega fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), U x = 0) ∧
          IsHolderOn beta (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) U := by
  have hBank := candidate_represented_source_bank mu P env henv hLaw phi Qc Qr hQr
    beta hbeta S hS a GN hGN GE hGE K C hKmem hKnorm hSource
  have hcompact : IsCompact (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded Qc hQr).isCompact_closure
  filter_upwards [hBank] with omega hbank
  intro f hf fL2 hfL2
  have hfclosure : ContinuousOn f (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) :=
    hf.continuous.continuousOn.mono (subset_univ _)
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hfclosure
  have hbound : ∀ᵐ x ∂volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)),
      |f x| ≤ max B 0 := by
    apply ae_restrict_of_forall_mem (centeredCube Qc Qr hQr).isOpen.measurableSet
    intro x hx
    have hfx : ‖f x‖ ≤ B := hB x (subset_closure hx)
    have habs : |f x| ≤ B := by
      simpa only [Real.norm_eq_abs] using hfx
    exact le_trans habs (le_max_left B 0)
  obtain ⟨U, _, _, _, hUc, hUr, hUb, hUh, _, _⟩ :=
    hbank f (max B 0) hf (le_max_right B 0) hbound fL2 hfL2
  exact ⟨U, hUc, hUr, hUb, hUh⟩
end Paper
