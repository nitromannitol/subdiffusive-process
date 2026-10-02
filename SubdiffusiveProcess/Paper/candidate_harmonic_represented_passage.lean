import SubdiffusiveProcess.Paper.candidate_represented_source_bank
import SubdiffusiveProcess.Paper.candidate_harmonic_window_passage
import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative
import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison

/-! The harmonic comparison holds for every continuous representative of the represented source.
The proof uses the finite deterministic window and the actual same-law source bank.
-/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The deterministic harmonic window passes to any continuous representative of the actual represented source. -/
theorem candidate_harmonic_represented_passage
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    (I : in_J d) (alpha beta s Charm E0 : ℝ)
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (hCharm : 0 ≤ Charm)
    (hwindow : aux_in_deterministic_core_harm_window d I alpha s Charm E0)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (env : ℕ → Ω → BilateralField d) (henv : ∀ n, Measurable (env n))
    (hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
    (phi : ℕ → ℕ)
    (Qc : SpatialCoordinates d) (Qr : ℝ) (hQr : 0 < Qr)
    (S : ResponseSpace (centeredCube Qc Qr hQr))
    (hS : S.space = killedSobolevGraph (centeredCube Qc Qr hQr))
    (GN : ℕ → BilateralField d → DomainL2 (centeredCube Qc Qr hQr) →L[ℝ]
      DomainL2 (centeredCube Qc Qr hQr))
    (hGN : ∀ n xi fL2, GN n xi fL2 =
      (responseSolution S (cutoffPositiveCoefficient M H xi n Qc hQr)
        ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).val.1)
    (GE : Ω → DomainL2 (centeredCube Qc Qr hQr) →L[ℝ] DomainL2 (centeredCube Qc Qr hQr))
    (hGE : ∀ᵐ omega ∂P, Tendsto (fun n => GN (phi n) (env n omega)) atTop (𝓝 (GE omega)))
    (K : ℕ → BilateralField d → ℝ) (C : ℝ≥0)
    (hKmem : ∀ n, MemLp (K n) 1 (chaosSampleLaw M).toMeasure)
    (hKnorm : ∀ n, eLpNorm (K n) 1 (chaosSampleLaw M).toMeasure ≤ C)
    (hSource : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (f : SpatialCoordinates d → ℝ) (Kf : ℝ),
      ContDiff ℝ ∞ f → 0 ≤ Kf →
      (∀ᵐ x ∂volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), |f x| ≤ Kf) →
      ∀ u : killedSobolevGraph (centeredCube Qc Qr hQr),
        (∀ psi : killedSobolevGraph (centeredCube Qc Qr hQr),
          sobolevCoefficientForm (cutoffPositiveCoefficient M H xi n Qc hQr) u.val psi.val =
            ∫ x in (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), f x * psi.val.1 x) →
        ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
          (u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), U x = 0) ∧
          IsHolderOn beta (closedCube Qc Qr hQr : Set (SpatialCoordinates d)) U ∧
          cAlphaNorm beta (closedCube Qc Qr hQr : Set (SpatialCoordinates d)) U ≤ K n xi * Kf)
    (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (l : ℤ) (hrl : r = (3 : ℝ) ^ (-l))
    (aN : ℕ → Ω → ℝ) (a : Ω → ℝ) (haN : ∀ n omega, 0 < aN n omega)
    (haLim : ∀ᵐ omega ∂P, 0 < a omega ∧ Tendsto (fun n => aN n omega) atTop (𝓝 (a omega)))
    (err : Ω → ℝ)
    (hErr : TendstoInMeasure P (fun n omega => I.err c r hr
      (cutoffPositiveCoefficient M H (env n omega) (phi n) c hr) c r (aN n omega) s 2) atTop err)
    (epshom Ctotal : ℝ) (hCtotal : Charm ≤ Ctotal) :
    ∀ᵐ omega ∂P, err omega < E0 → Charm * err omega ≤ epshom →
      ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ (fL2 : DomainL2 (centeredCube Qc Qr hQr)),
        (fL2 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] f →
      ∀ (U : SpatialCoordinates d → ℝ),
        ContinuousOn U (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) →
        (GE omega fL2 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] U →
      let fsup := sSup {v : ℝ | ∃ x ∈ closure
        (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), v = |f x|}
      let qc := centeredCube c (r / 81) (div_pos hr (by norm_num))
      let qi : Set (SpatialCoordinates d) := Metric.ball c (r / 1458)
      let qo : Set (SpatialCoordinates d) := Metric.ball c (r / 18)
      ∀ w : SpatialCoordinates d,
        Metric.closedBall c (r / 18) ⊆ Metric.ball w (27 * r / 2) →
        Metric.ball w (27 * r / 2) ⊆ (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)) →
        ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
          ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
          (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (qc : Set (SpatialCoordinates d))] V ∧
          (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
          (∀ psi : killedSobolevGraph qc,
            inner ℝ (sobolevGradient v.val) (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
          normalizedL2On qi (fun x => U x - V x) ≤
            epshom * normalizedL2On qo
              (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
            Ctotal * (r / 9) ^ 2 * (a omega)⁻¹ * fsup := by
  obtain ⟨ps, hps, hErrAe⟩ := hErr.exists_seq_tendsto_ae
  have hBank := candidate_represented_source_bank (chaosSampleLaw M).toMeasure P
    (fun n => env (ps n)) (fun n => henv (ps n)) (fun n => hLaw (ps n))
    (phi ∘ ps) Qc Qr hQr beta hbeta S hS
    (fun n xi => cutoffPositiveCoefficient M H xi n Qc hQr) GN hGN GE
    (hGE.mono fun _ h => h.comp hps.tendsto_atTop) K C hKmem hKnorm hSource
  filter_upwards [hBank, hErrAe, haLim] with omega hBank hErrAe ha
  intro hErrSmall hErrCoeff f hf fL2 hfL2 U hUc hUr
  dsimp only
  let Q := centeredCube Qc Qr hQr
  let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
  have hfsup : 0 ≤ fsup :=
    Real.sSup_nonneg (by rintro v ⟨x, hx, rfl⟩; exact abs_nonneg _)
  have hfbdd : BddAbove {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|} := by
    obtain ⟨B, hB⟩ := (centeredCube_isBounded Qc hQr).isCompact_closure.exists_bound_of_continuousOn
      hf.continuous.continuousOn
    refine ⟨B, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    simpa only [Real.norm_eq_abs] using hB x hx
  have hfbound : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |f x| ≤ fsup :=
    ae_restrict_of_forall_mem Q.isOpen.measurableSet
      (fun x hx => le_csSup hfbdd ⟨x, subset_closure hx, rfl⟩)
  obtain ⟨U0, ns, UN, hns, hU0c, hU0r, _, hU0h, hUni, hUN⟩ :=
    hBank f fsup hf hfsup hfbound fL2 hfL2
  have hUeq : EqOn U0 U (closure (Q : Set (SpatialCoordinates d))) :=
    eqOn_closure_of_ae_eq_restrict Q.isOpen hU0c hUc (hU0r.symm.trans hUr)
  have hUh : IsHolderOn beta (closure (Q : Set (SpatialCoordinates d))) U :=
    (isHolderOn_congr hUeq).mp hU0h
  let N : ℕ → ℕ := fun n => phi (ps (ns n))
  let omN : ℕ → BilateralField d := fun n => env (ps (ns n)) omega
  let uN : ℕ → weakSobolevGraph Q := fun n =>
    ⟨(responseSolution S (cutoffPositiveCoefficient M H (omN n) (N n) Qc hQr)
      ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).val,
      killedSobolevGraph_le_weakSobolevGraph (hS ▸ (responseSolution S
        (cutoffPositiveCoefficient M H (omN n) (N n) Qc hQr)
        ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).property)⟩
  have hsolve : ∀ n, ∀ psi : killedSobolevGraph Q,
      sobolevCoefficientForm (cutoffPositiveCoefficient M H (omN n) (N n) Qc hQr)
        (uN n).val psi.val = sobolevVolumeLoad fL2 psi.val := by
    intro n psi
    exact responseSolution_spec S (cutoffPositiveCoefficient M H (omN n) (N n) Qc hQr)
      ((sobolevVolumeLoad fL2).comp S.space.subtypeL) ⟨psi.val, hS.symm ▸ psi.property⟩
  have hUNr : ∀ n, ((uN n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Q : Set (SpatialCoordinates d))] UN n := by
    intro n
    have heq := (hUN n).2
    rw [hGN] at heq
    exact heq
  have hfMem : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable fsup
      (hfbound.mono fun _ h => by simpa only [Real.norm_eq_abs] using h)
  have hUMem : MemLp U 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    (memLp_congr_ae hUr).mp (Lp.memLp (GE omega fL2))
  intro w hpad hqdQ
  have hTraceQ : frontier (centeredCube c (r / 81) (div_pos hr (by norm_num)) :
      Set (SpatialCoordinates d)) ⊆ closure (Q : Set (SpatialCoordinates d)) := by
    have hqc : closure (centeredCube c (r / 81) (div_pos hr (by norm_num)) :
        Set (SpatialCoordinates d)) ⊆ Metric.closedBall c (r / 18) :=
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
        (Metric.closedBall_subset_closedBall (by linarith only [hr]))
    exact frontier_subset_closure.trans (hqc.trans (hpad.trans (hqdQ.trans subset_closure)))
  exact candidate_harmonic_window_passage hd Sob I alpha beta s Charm E0 halpha hbeta
    hCharm hwindow M H omN N Qc Qr hQr f hfMem fL2 hfL2 uN hsolve UN U
    (fun n => (hUN n).1.continuousOn) hUNr hUMem (hUni.congr_right hUeq)
    c r hr l hrl (FiniteStopping.isHolderOn_mono hTraceQ beta U hUh) w hpad hqdQ
    (fun n => aN (ps (ns n)) omega) (a omega) (fun n => haN _ _) ha.1
    (ha.2.comp (hps.comp hns).tendsto_atTop) (err omega) epshom Ctotal fsup hfsup
    (ae_restrict_of_forall_mem measurableSet_ball
      (fun x hx => le_csSup hfbdd ⟨x, subset_closure (hqdQ hx), rfl⟩))
    (hErrAe.comp hns.tendsto_atTop) hErrSmall hErrCoeff hCtotal

end Paper
