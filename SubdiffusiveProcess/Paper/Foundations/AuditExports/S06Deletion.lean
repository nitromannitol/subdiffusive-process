module

public import SubdiffusiveProcess.Paper.Foundations.AuditExports.S09Deletion

@[expose] public section

open Filter MeasureTheory Set Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.Section9
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- Source-facing closure of the S06 deletion row. The actual model supplies its
infrared characterization, and S09 supplies the regular base form and every
deleted limit with remaining-field measurable pairings. No analytic package,
base-form regularity or finite-response measurability is assumed. -/
theorem deletion_packageClosure
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    letI : NeZero d := ⟨ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hd)⟩
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∃ (Er : (i : ℕ) → BilateralField d → _root_.SubdiffusiveProcess.DirichletForm
            (volume.restrict (determiningCube d i : Set (SpatialCoordinates d))))
        (GammaR : ∀ i omega, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Er i omega).toClosedForm)
        (Gbase : KilledInverseFamily d (BilateralField d)),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i u,
          (Er i omega).toClosedForm.energy u = limitFormEnergy (Gbase i omega) u) ∧
        (∀ i (f : DomainL2 (determiningCube d i)),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => inverseResponse (determiningResponseSpace d i)
              (cutoffPositiveCoefficient M positiveInfraredVersion omega (seq n) (rationalTriadicCenter d i)
                (rationalTriadicSide_pos d i))
              ((sobolevVolumeLoad f).comp (determiningResponseSpace d i).space.subtypeL)) atTop
            (fun omega => inner ℝ f (Gbase i omega f))) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (Er i omega).toClosedForm ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (Er i omega).toClosedForm ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra (Er i omega).toClosedForm ∧
          (∃ C : Set (DomainL2 (determiningCube d i)),
            _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (Er i omega).toClosedForm
              (determiningCube d i : Set (SpatialCoordinates d)) C) ∧
          (∀ u ∈ (Er i omega).toClosedForm.domain,
            (GammaR i omega).measure u (determiningCube d i : Set (SpatialCoordinates d))ᶜ = 0)) ∧
        ∀ i layer : ℕ,
          let Q := determiningCube d i
          let P := (chaosSampleLaw M).toMeasure
          let ell := fun (omega : BilateralField d) (x : SpatialCoordinates d) =>
            omega (-(Int.ofNat layer)) x
          ∃ Gdeleted Gversion : BilateralField d → DomainL2 Q →L[ℝ] DomainL2 Q,
            (∀ f : DomainL2 Q, TendstoInMeasure P
              (fun n omega => inverseResponse (determiningResponseSpace d i)
                (determiningDeletedCoefficient M positiveInfraredVersion i layer (seq n) omega)
                ((sobolevVolumeLoad f).comp (determiningResponseSpace d i).space.subtypeL)) atTop
              (fun omega => inner ℝ f (Gdeleted omega f))) ∧
            (∀ᵐ omega ∂P,
              (∀ f g : DomainL2 Q, inner ℝ f (Gdeleted omega g) =
                inner ℝ (Gdeleted omega f) g) ∧
              Function.Injective (Gdeleted omega) ∧
              (∀ f : DomainL2 Q, IsLUB {t : ℝ | ∃ u : DomainL2 Q,
                u ∈ (Er i omega).toClosedForm.domain ∧
                t = 2 * inner ℝ f u - ∫ x in (Q : Set (SpatialCoordinates d)),
                  Real.exp (-ell omega x) ∂(GammaR i omega).measure u}
                (inner ℝ f (Gdeleted omega f)))) ∧
            Gversion =ᵐ[P] Gdeleted ∧
            (∀ f g : DomainL2 Q, Measurable[remainingSigma layer]
              (fun omega => inner ℝ f (Gversion omega g))) ∧
            (∀ᵐ omega ∂P,
              ∃ (Edeleted : _root_.SubdiffusiveProcess.DirichletForm
                    (volume.restrict (Q : Set (SpatialCoordinates d))))
                (GammaDeleted : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Edeleted.toClosedForm),
                Edeleted.toClosedForm.domain = (Er i omega).toClosedForm.domain ∧
                (∀ u : DomainL2 Q,
                  Edeleted.toClosedForm.energy u = limitFormEnergy (Gversion omega) u) ∧
                (∀ u ∈ (Er i omega).toClosedForm.domain,
                  ∀ v ∈ (Er i omega).toClosedForm.domain,
                  Edeleted.toClosedForm.form u v =
                    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ((GammaR i omega).cross u v) Set.univ
                      (fun x => Real.exp (-ell omega x))) ∧
                _root_.SubdiffusiveProcess.DirichletForm.IsRegular Edeleted.toClosedForm ∧
                _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal Edeleted.toClosedForm ∧
                (∀ u ∈ (Er i omega).toClosedForm.domain,
                  ∀ v ∈ (Er i omega).toClosedForm.domain,
                  ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
                    GammaDeleted.cross u v B =
                      _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ((GammaR i omega).cross u v) B
                        (fun x => Real.exp (-ell omega x)))) := by
  dsimp only
  let : NeZero d := ⟨ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hd)⟩
  obtain ⟨delta0, hdelta0, hdeletion⟩ := borelWeights_deletion d hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hsmall
  obtain ⟨H, hH⟩ := exists_infraredCharacterization hd M
  exact hdeletion M positiveInfraredVersion
    (infraredCharacterization_positiveInfraredVersion M H hH) hsmall

end SubdiffusiveProcess.AuditExports
