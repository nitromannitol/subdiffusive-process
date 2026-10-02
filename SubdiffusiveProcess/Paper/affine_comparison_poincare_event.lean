import SubdiffusiveProcess.Paper.affine_comparison_poincare
import SubdiffusiveProcess.Paper.goodext_represented_local_trace_controls
import SubdiffusiveProcess.Paper.goodext_lower_ellipticity_from_error_limit
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative
import SubdiffusiveProcess.Lane4.Bridge

/-! Represented-level comparison Poincaré bound: along the represented cutoff sequence, almost
surely, a strictly subunit limiting homogenization error on a cube `q` inside the root gives the
coarse Poincaré bound for every limiting response `G f` on `q`, with the parent energy measured
by any energy measure of the limiting form. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace Paper

/-- Almost surely, a subunit limiting error on the cube gives the comparison Poincaré bound. -/
theorem affine_comparison_poincare_event
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (Qc : SpatialCoordinates d) (Qs : ℝ) (hQs : 0 < Qs)
        (S : ResponseSpace (centeredCube Qc Qs hQs))
        (hS : S.space = killedSobolevGraph (centeredCube Qc Qs hQs))
        (N : ℕ → ℕ) (hN : StrictMono N)
        (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (hEnv : ∀ n, Measurable (env n))
        (hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
        (GN : ℕ → BilateralField d → DomainL2 (centeredCube Qc Qs hQs) →L[ℝ]
          DomainL2 (centeredCube Qc Qs hQs))
        (hGN : ∀ n xi f, GN n xi f =
          (responseSolution S (cutoffPositiveCoefficient M H xi n Qc hQs)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (G : Omega → DomainL2 (centeredCube Qc Qs hQs) →L[ℝ] DomainL2 (centeredCube Qc Qs hQs))
        (hG : ∀ᵐ om ∂P, Tendsto (fun n => GN (N n) (env n om)) atTop (𝓝 (G om)))
        (E : Omega → DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))))
        (hE : ∀ om u, (E om).energy u = limitFormEnergy (G om) u)
        (Gamma : ∀ om, DirichletForm.EnergyMeasure (E om))
        (hcont : ∀ᵐ om ∂P, ∀ f : DomainL2 (centeredCube Qc Qs hQs),
          (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
            tsupport fc ⊆ (centeredCube Qc Qs hQs : Set (SpatialCoordinates d)) ∧
            (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))] fc) →
          ∃ U : SpatialCoordinates d → ℝ,
            ContinuousOn U (closure (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))) ∧
            (G om f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))] U ∧
            ∀ x ∈ frontier (centeredCube Qc Qs hQs : Set (SpatialCoordinates d)), U x = 0)
        (z : SpatialCoordinates d) (m : ℝ) (hm : 0 < m)
        (hcube : centeredCube z m hm ≤ centeredCube Qc Qs hQs)
        (parentCell : Set (SpatialCoordinates d)) (hparent : IsOpen parentCell)
        (hpad : closure (centeredCube z m hm : Set (SpatialCoordinates d)) ⊆ parentCell)
        (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (hs2 : 2 * s ≤ 1)
        (scale : ℕ → Omega → ℝ) (hscale : ∀ n om, 0 < scale n om) (sLim : Omega → ℝ)
        (hsLim : ∀ᵐ om ∂P, 0 < sLim om ∧ Tendsto (fun n => scale n om) atTop (𝓝 (sLim om)))
        (errLim : Omega → ℝ)
        (herr : TendstoInMeasure P (fun n om => I.err z m hm
          (cutoffPositiveCoefficient M H (env n om) (N n) z hm) z m (scale n om) s 2)
          atTop errLim),
      ∀ᵐ om ∂P, errLim om < 1 →
        ∀ (f : DomainL2 (centeredCube Qc Qs hQs)) (U : SpatialCoordinates d → ℝ),
          (G om f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))] U →
          (normalizedL2On (centeredCube z m hm : Set (SpatialCoordinates d))
            (fun x => U x - (volume.real (centeredCube z m hm : Set (SpatialCoordinates d)))⁻¹ *
              ∫ y in (centeredCube z m hm : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
            (Pin.C ^ 2 * m ^ 2 *
              ((Homogenization.Book.Ch02.geometricDiscount s 2 /
                Homogenization.Book.Ch02.geometricDiscount 1 1) * (1 / 5 : ℝ))⁻¹ /
                  volume.real (centeredCube z m hm : Set (SpatialCoordinates d))) * (sLim om)⁻¹ *
              ((Gamma om).measure (G om f) parentCell).toReal := by
  obtain ⟨delta0, hdelta0, hControls⟩ := goodext_represented_local_trace_controls d hd I Pin X W
    Cp Sob Interp t alpha beta ht htd ha ha1 hb
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta Qc Qs hQs S hS N hN Omega _ P _ env hEnv hLaw GN hGN G hG E hE
    Gamma hcont z m hm hcube parentCell hparent hpad s hs hs2 scale hscale sLim hsLim errLim herr
  obtain ⟨rho, hrho, hae⟩ := herr.exists_seq_tendsto_ae
  have hc := hControls M Rm Sreg It H hIR hdelta Qc Qs hQs S hS 0 Empty Empty.elim
    (fun n => N (rho n)) (hN.comp hrho) Omega P (fun n => env (rho n)) (fun n => hEnv (rho n))
    (fun n => hLaw (rho n))
  filter_upwards [hc, hae, hG, hsLim, hcont] with om hcom haeom hGom hsom hcontom
  intro herrlt f U hU
  obtain ⟨seq, hseq, ⟨A⟩, hcell, -⟩ := hcom
  have hrs : StrictMono (rho ∘ seq) := hrho.comp hseq
  have hlow : ∀ᶠ n in atTop, (1 / 5 : ℝ) * scale (rho (seq n)) om ≤
      I.lam z m hm (cutoffPositiveCoefficient M H (env (rho (seq n)) om) (N (rho (seq n))) z hm)
        z m s 2 := by
    have h := goodext_lower_ellipticity_from_error_limit I z m hm
      (fun n => cutoffPositiveCoefficient M H (env (rho (seq n)) om) (N (rho (seq n))) z hm)
      z m s hs (fun n => scale (rho (seq n)) om) (fun n => hscale _ _) (errLim om) herrlt
      (haeom.comp hseq.tendsto_atTop)
    filter_upwards [h] with n hn
    linarith only [hn]
  have hab : ∀ n, (cutoffPositiveCoefficient M H (env (rho (seq n)) om) (N (rho (seq n))) Qc hQs).val
      =ᵐ[volume.restrict (centeredCube z m hm : Set (SpatialCoordinates d))]
      (cutoffPositiveCoefficient M H (env (rho (seq n)) om) (N (rho (seq n))) z hm).val := by
    intro n
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hcube
      (cutoffPositiveCoefficient_representative M H (env (rho (seq n)) om) (N (rho (seq n)))
        Qc hQs).2.2.2,
      (cutoffPositiveCoefficient_representative M H (env (rho (seq n)) om) (N (rho (seq n)))
        z hm).2.2.2] with x hx hy
    exact hx.trans hy.symm
  have hell (n : ℕ) : ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube Qc Qs hQs : Set (SpatialCoordinates d)),
        lam ≤ cutoffCoefficient M H (env (rho (seq n)) om) (N (rho (seq n))) x ∧
        cutoffCoefficient M H (env (rho (seq n)) om) (N (rho (seq n))) x ≤ Lam := by
    obtain ⟨lo, hi, hlo, hbounds⟩ := cutoffCoefficient_closedCube_bounds M H
      (env (rho (seq n)) om) (N (rho (seq n))) Qc hQs
    exact ⟨lo, hi, hlo, fun x hx => hbounds x (centeredCube_subset_closedCube Qc hQs hx)⟩
  exact affine_comparison_poincare hd I Pin Qc Qs hQs S hS
    (fun n => cutoffPositiveCoefficient M H (env (rho (seq n)) om) (N (rho (seq n))) Qc hQs) A
    (fun n => cutoffCoefficient M H (env (rho (seq n)) om) (N (rho (seq n))))
    (fun n => cutoffCoefficient_continuous M H _ _) hell
    (fun n => (cutoffPositiveCoefficient_representative M H (env (rho (seq n)) om)
      (N (rho (seq n))) Qc hQs).2.2.2)
    t alpha ha hcell (fun n => GN (N (rho (seq n))) (env (rho (seq n)) om)) (G om)
    (fun n f => hGN _ _ f) (hGom.comp hrs.tendsto_atTop) (E om) (hE om) hcontom (Gamma om)
    f U hU z m hm hcube
    (fun n => cutoffPositiveCoefficient M H (env (rho (seq n)) om) (N (rho (seq n))) z hm) hab
    s (1 / 5) hs.1 hs2 (by norm_num) (fun n => scale (rho (seq n)) om) (sLim om)
    (fun n => hscale _ _) hsom.1 (hsom.2.comp hrs.tendsto_atTop) hlow parentCell hparent hpad

end Paper
