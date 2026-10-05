module

public import SubdiffusiveProcess.Paper.candidate_source_compact_bank
public import SubdiffusiveProcess.Paper.candidate_good_estimates_finite_bank_support

@[expose] public section

/-! Pulling source regularity through equal-law environments gives an almost sure compact source bank.
The source regularity estimate itself is a premise; no candidate Good event is assumed.
-/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Uniform moments and actual cutoff source regularity yield almost sure uniform representative banks under resampling. -/
theorem candidate_represented_source_bank
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
    ∀ᵐ omega ∂P, ∀ (f : SpatialCoordinates d → ℝ) (Kf : ℝ),
      ContDiff ℝ ∞ f → 0 ≤ Kf →
      (∀ᵐ x ∂volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), |f x| ≤ Kf) →
      ∀ fL2 : DomainL2 (centeredCube Qc Qr hQr),
        (fL2 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] f →
        ∃ (U : SpatialCoordinates d → ℝ) (ns : ℕ → ℕ)
          (UN : ℕ → SpatialCoordinates d → ℝ), StrictMono ns ∧
          ContinuousOn U (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) ∧
          (GE omega fL2 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), U x = 0) ∧
          IsHolderOn beta (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) U ∧
          TendstoUniformlyOn UN U atTop
            (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) ∧
          ∀ n, Continuous (UN n) ∧
            (GN (phi (ns n)) (env (ns n) omega) fL2 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] UN n := by
  have hmp (n : ℕ) : MeasurePreserving (env n) P mu := ⟨henv n, hLaw n⟩
  have hBound := aux_candidate_good_estimates_finite_bank_support_moment_subseq P
    (fun n omega => K (phi n) (env n omega)) 1 one_ne_zero C
    (fun n => ((hKmem (phi n)).comp_measurePreserving (hmp n)).aestronglyMeasurable)
    (fun n => by
      change eLpNorm (K (phi n) ∘ env n) 1 P ≤ C
      rw [eLpNorm_comp_measurePreserving (hKmem (phi n)).aestronglyMeasurable (hmp n)]
      exact hKnorm (phi n))
  have hSourceEnv : ∀ᵐ omega ∂P, ∀ n,
      (∀ (N : ℕ) (f : SpatialCoordinates d → ℝ) (Kf : ℝ),
      ContDiff ℝ ∞ f → 0 ≤ Kf →
      (∀ᵐ x ∂volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), |f x| ≤ Kf) →
      ∀ u : killedSobolevGraph (centeredCube Qc Qr hQr),
        (∀ psi : killedSobolevGraph (centeredCube Qc Qr hQr),
          sobolevCoefficientForm (a N (env n omega)) u.val psi.val =
            ∫ x in (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), f x * psi.val.1 x) →
        ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
          (u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), U x = 0) ∧
          IsHolderOn beta (closedCube Qc Qr hQr : Set (SpatialCoordinates d)) U ∧
          cAlphaNorm beta (closedCube Qc Qr hQr : Set (SpatialCoordinates d)) U ≤
            K N (env n omega) * Kf) := by
    apply ae_all_iff.mpr
    intro n
    exact ae_of_ae_map (henv n).aemeasurable (by rw [hLaw n]; exact hSource)
  filter_upwards [hBound, hSourceEnv, hGE] with omega hb hs hg
  intro f Kf hf hKf hfbound fL2 hfL2
  obtain ⟨B, ms, hB, hms, hBound⟩ := hb
  obtain ⟨U, ns, UN, hns, hUc, hUr, hUb, hUh, hUni, hUN⟩ :=
    candidate_source_compact_bank Qc Qr hQr beta hbeta S hS
      (fun n => a (phi (ms n)) (env (ms n) omega))
      (fun n => GN (phi (ms n)) (env (ms n) omega))
      (fun n fL2 => hGN (phi (ms n)) (env (ms n) omega) fL2)
      (GE omega) (hg.comp hms.tendsto_atTop) f fL2 hfL2 (B * Kf) (mul_nonneg hB hKf)
      (by
        intro n u hsolve
        obtain ⟨V, hVc, hVr, hVb, hVh, hVnorm⟩ :=
          hs (ms n) (phi (ms n)) f Kf hf hKf hfbound u hsolve
        refine ⟨V, hVc, hVr, hVb, hVh, hVnorm.trans ?_⟩
        exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hBound n)) hKf)
  exact ⟨U, ms ∘ ns, UN, hms.comp hns, hUc, hUr, hUb, hUh, hUni, hUN⟩

end SubdiffusiveProcess.Paper
