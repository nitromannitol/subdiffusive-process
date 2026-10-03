module

public import SubdiffusiveProcess.Paper.density_good_harmonic_bank
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Combine an actual normalized Holder witness with its harmonic energy bound,
then cancel the common reference factor. All quantities here are scalar. -/
lemma aux_density_source_harmonic_realization_local
    {d : ℕ} (alpha : ℝ) (z : SpatialCoordinates d) (r : ℝ)
    (U : SpatialCoordinates d → ℝ) (bound C se sf ratio nu fsup cost : ℝ)
    (hRatio : sf / se = ratio)
    (hLocal : ∃ cq : ℝ,
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ≤ bound)
    (hCost : ∀ cq : ℝ,
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) →
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ≤ bound →
      cost ≤ C * (sf / se) * (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2)) :
    cost ≤ C * ratio * (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2) := by
  obtain ⟨cq, hh, hn⟩ := hLocal
  rw [← hRatio]
  exact hCost cq hh hn

/-- Apply one represented harmonic bank to the same source representative and
its local Holder bounds, preserving actual coefficient energies and subsequences.
Both analytic premises are supplied by actual producers in the model application. -/
theorem density_source_harmonic_realization
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (S : ResponseSpace (centeredCube Qcentre Qside hQside))
    (alpha beta etaGrid t Ctotal Ce : ℝ) (hCtotal : 0 ≤ Ctotal)
    (H1 : ℕ) (psi psiH : ℕ → ℕ)
    (hpsi : StrictMono psi) (hpsiH : StrictMono psiH)
    (Bank Cells : Type) (embed : Cells → Bank)
    (fullCentre : Bank → SpatialCoordinates d) (fullRadius : Bank → ℝ)
    (fullCube : Bank → Opens (SpatialCoordinates d)) (k : Cells → ℕ) :
    let z := fun b => fullCentre (embed b)
    let Q := centeredCube Qcentre Qside hQside
    let L : ℝ := (3 : ℝ) ^ H1
    ∀ (a : Ω → ℕ → PositiveCoefficient Q) (c : Ω → ℕ → SpatialCoordinates d → ℝ)
      (coeff : Ω → ∀ q, ℕ → PositiveCoefficient (fullCube q)),
    ∀ (Good : Cells → Fin 2 → Set Ω) (eRef : Fin 2 → ℕ → ℝ)
      (sRef : Cells → Fin 2 → Ω → ℝ)
      (GE : Ω → DomainL2 Q →L[ℝ] DomainL2 Q)
      (nu : Ω → DomainL2 Q → Measure (SpatialCoordinates d))
      (hRefPos : ∀ b omega, 0 < sRef b 0 omega)
      (hRefRatio : ∀ b omega, sRef b 1 omega / sRef b 0 omega = eRef 1 (k b) / eRef 0 (k b))
      (hSource :
      ∀ᵐ omega ∂P, ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
        ∀ (fL2 : DomainL2 Q), ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] f) →
        let u := GE omega fL2
        let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
          ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
          (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
          Lane4.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
          (∀ b : Cells, (omega ∈ Good b 0 ∧ omega ∈ Good b 1) →
            ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d (subdivisionHalfWidth H1)),
            let r : ℝ := fullRadius (embed b)
            z b = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
            Metric.closedBall (z b) (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
            Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
            ∃ cq : ℝ,
              Lane4.IsHolderOn alpha
                (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
                (fun x => U (z b + r • x) - cq) ∧
              Lane4.cAlphaNorm alpha
                (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
                (fun x => U (z b + r • x) - cq) ≤
                  Ctotal * r ^ ((2 - (d : ℝ)) / 2) * (sRef b 0 omega) ^ (-(1 : ℝ) / 2) *
                    Real.sqrt ((nu omega u) (Metric.ball zP (L * r / 2))).toReal +
                  Ctotal * r ^ (2 : ℝ) * (sRef b 0 omega)⁻¹ * fsup))
      (hBank :
∀ᵐ om ∂P,
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd Qcentre Qside hQside S
          (fun n => a om (psi (psiH (seq n))))) ∧
        aux_prop_conc_mesh_cutoff_family_AllCellBounds Qcentre Qside hQside
          (fun n => c om (psi (psiH (seq n)))) t alpha ∧
        ∀ g : SpatialCoordinates d → ℝ,
          ContinuousOn g (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) →
          IsHolderOn alpha (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) g →
    ∃ A0 Osc : ℝ, 0 ≤ A0 ∧ 0 ≤ Osc ∧
      ∃ (uN : ∀ q, ℕ → weakSobolevGraph (fullCube q))
        (VN : Bank → ℕ → SpatialCoordinates d → ℝ)
        (rho : ℕ → ℕ) (Vcell : Bank → SpatialCoordinates d → ℝ) (cost : Bank → ℝ),
      StrictMono rho ∧ (∀ q,
        (∀ n, ContinuousOn (VN q n)
            (closure (fullCube q : Set (SpatialCoordinates d))) ∧
          ((uN q n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (fullCube q : Set (SpatialCoordinates d))] VN q n ∧
          (∀ x ∈ frontier (fullCube q : Set (SpatialCoordinates d)),
            VN q n x = g x) ∧
          ∀ x ∈ closure (fullCube q : Set (SpatialCoordinates d)),
            |VN q n x - g x| ≤ Osc * fullRadius q ^ alpha) ∧
        ContinuousOn (Vcell q)
          (closure (fullCube q : Set (SpatialCoordinates d))) ∧
        TendstoUniformlyOn (VN q) (Vcell q) atTop
          (closure (fullCube q : Set (SpatialCoordinates d))) ∧
        Tendsto (fun n => sobolevCoefficientForm
          (coeff om q (psi (psiH (seq (rho n))))) (uN q n).val (uN q n).val) atTop (𝓝 (cost q)) ∧
        0 ≤ cost q ∧ cost q ≤ A0 * fullRadius q ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid) ) ∧
      ∀ b : Cells, om ∈ Good b 1 → 0 < sRef b 1 om ∧
        ∀ (Cnorm se nu fsup : ℝ), 0 ≤ Cnorm → 0 < se → 0 ≤ nu → 0 ≤ fsup →
        ∀ cq : ℝ,
        IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
          (fun x => g (fullCentre (embed b) + fullRadius (embed b) • x) - cq) →
        cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
          (fun x => g (fullCentre (embed b) + fullRadius (embed b) • x) - cq) ≤
            Cnorm * fullRadius (embed b) ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu +
              Cnorm * fullRadius (embed b) ^ (2 : ℝ) * se⁻¹ * fsup →
        cost (embed b) ≤ (2 * (Ce * 8) * ((Real.sqrt d) ^ (alpha - beta) * Cnorm) ^ 2) *
          (sRef b 1 om / se) * (nu + se⁻¹ * fullRadius (embed b) ^ ((d : ℝ) + 2) * fsup ^ 2)),
      ∀ᵐ omega ∂P, ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
        ∀ (fL2 : DomainL2 Q), ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] f) →
        let u := GE omega fL2
        let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
          ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
          (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
          Lane4.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
          ∃ tau : ℕ → ℕ, StrictMono tau ∧
            Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd Qcentre Qside hQside S
              (fun n => a omega (tau n))) ∧
            aux_prop_conc_mesh_cutoff_family_AllCellBounds Qcentre Qside hQside
              (fun n => c omega (tau n)) t alpha ∧
            ∃ A0 Osc : ℝ, 0 ≤ A0 ∧ 0 ≤ Osc ∧
            ∃ (uN : ∀ q, ℕ → weakSobolevGraph (fullCube q))
              (VN : Bank → ℕ → SpatialCoordinates d → ℝ)
              (Vcell : Bank → SpatialCoordinates d → ℝ) (cost : Bank → ℝ),
              (∀ q,
                (∀ n, ContinuousOn (VN q n) (closure (fullCube q : Set (SpatialCoordinates d))) ∧
                  ((uN q n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                    (fullCube q : Set (SpatialCoordinates d))] VN q n ∧
                  (∀ x ∈ frontier (fullCube q : Set (SpatialCoordinates d)), VN q n x = U x) ∧
                  ∀ x ∈ closure (fullCube q : Set (SpatialCoordinates d)),
                    |VN q n x - U x| ≤ Osc * fullRadius q ^ alpha) ∧
                ContinuousOn (Vcell q) (closure (fullCube q : Set (SpatialCoordinates d))) ∧
                TendstoUniformlyOn (VN q) (Vcell q) atTop (closure (fullCube q : Set (SpatialCoordinates d))) ∧
                Tendsto (fun n => sobolevCoefficientForm (coeff omega q (tau n)) (uN q n).val (uN q n).val)
                  atTop (𝓝 (cost q)) ∧
                0 ≤ cost q ∧ cost q ≤ A0 * fullRadius q ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid)) ∧
              ∀ b : Cells, (omega ∈ Good b 0 ∧ omega ∈ Good b 1) →
                ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                let r : ℝ := fullRadius (embed b)
                z b = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
                Metric.closedBall (z b) (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
                Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                cost (embed b) ≤ (2 * (Ce * 8) * ((Real.sqrt d) ^ (alpha - beta) * Ctotal) ^ 2) *
                  (eRef 1 (k b) / eRef 0 (k b)) *
                  (((nu omega u) (Metric.ball zP (L * r / 2))).toReal +
                    (sRef b 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2) := by
  intro z Q L a c coeff Good eRef sRef GE nu hRefPos hRefRatio hSource hBank
  filter_upwards [hSource, hBank] with omega hsource hbankAll
  intro f hf fL2 hfr u fsup
  have hSourceU := hsource f hf fL2 hfr
  let U := hSourceU.choose
  have hU := hSourceU.choose_spec
  have hUc := hU.1
  have hUr := hU.2.1
  have hUb := hU.2.2.1
  have hUh := hU.2.2.2.1
  have hLocal := hU.2.2.2.2
  obtain ⟨seq, hseq, ⟨A⟩, hCells, hForU⟩ := hbankAll
  have hEnergyU := hForU U hUc hUh
  obtain ⟨A0, Osc, hA0, hOsc, uN, VN, rho, Vcell, cost, hrho, hbank, hCost⟩ := hEnergyU
  let tau := fun n => psi (psiH (seq (rho n)))
  have htau : StrictMono tau := hpsi.comp (hpsiH.comp (hseq.comp hrho))
  refine ⟨U, hUc, hUr, hUb, hUh, tau, htau,
    ⟨aux_prop_conc_controlled_forms_controls_reindex A rho⟩, ?_, ?_⟩
  · intro J hJ test htest testH htestH j
    obtain ⟨E, Gr, Ho, hE, hGr, hHo, hAll⟩ := hCells J hJ test htest testH htestH j
    exact ⟨E, Gr, Ho, hE, hGr, hHo, fun n => hAll (rho n)⟩
  · refine ⟨A0, Osc, hA0, hOsc, uN, VN, Vcell, cost, hbank, ?_⟩
    intro b hb zP idx r hcentre hpad hparent
    have hLocalb := hLocal b hb zP idx hcentre hpad hparent
    have hse := hRefPos b omega
    have hfsup : 0 ≤ fsup := by
      apply Real.sSup_nonneg
      rintro v ⟨x, hx, rfl⟩
      exact abs_nonneg _
    have hRatio := hRefRatio b omega
    exact aux_density_source_harmonic_realization_local alpha (z b) r U _
      (2 * (Ce * 8) * ((Real.sqrt d) ^ (alpha - beta) * Ctotal) ^ 2)
      (sRef b 0 omega) (sRef b 1 omega) (eRef 1 (k b) / eRef 0 (k b))
      (((nu omega u) (Metric.ball zP (L * r / 2))).toReal)
      fsup (cost (embed b)) hRatio hLocalb
      (fun cq hHolder hNorm => (hCost b hb.2).2 Ctotal (sRef b 0 omega)
        (((nu omega u) (Metric.ball zP (L * r / 2))).toReal) fsup
        hCtotal hse ENNReal.toReal_nonneg hfsup cq hHolder hNorm)
end Paper
