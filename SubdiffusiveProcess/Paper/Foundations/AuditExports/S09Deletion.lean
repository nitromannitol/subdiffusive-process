module

public import SubdiffusiveProcess.Paper.Foundations.AuditExports.S09DeletedCoefficients
public import SubdiffusiveProcess.Paper.Support.OriginalBasePackage
public import SubdiffusiveProcess.Paper.Support.ActualDeletionConvergence
public import SubdiffusiveProcess.Paper.Support.DeletedInverseRemVersion
public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Section9.RepresentedComparisonDraft

@[expose] public section

open Filter MeasureTheory Set Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.Section9 _root_.SubdiffusiveProcess.WeightedLimitIdentification _root_.SubdiffusiveProcess.Paper
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- Actual deletion on a member of the paper's determining cube family. -/
abbrev determiningDeletedCoefficient {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (i layer N : ℕ)
    (omega : BilateralField d) : PositiveCoefficient (determiningCube d i) :=
  deletedPositiveCoefficient M H N layer omega (rationalTriadicCenter d i)
    (rationalTriadicSide d i) (rationalTriadicSide_pos d i)

/-- On one full event, every canonical deleted scalar response agrees with that
of the supplied characterized infrared field. -/
theorem deleted_scalar_inverse_ae_eq
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (layer : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N (f : DomainL2 (centeredCube z r hr)),
      inverseResponse S (deletedPositiveCoefficient M positiveInfraredVersion N layer omega z r hr)
        ((sobolevVolumeLoad f).comp S.space.subtypeL) =
      inverseResponse S (deletedPositiveCoefficient M H N layer omega z r hr)
        ((sobolevVolumeLoad f).comp S.space.subtypeL) := by
  filter_upwards [deletedPositiveCoefficient_ae_eq M H hH layer z r hr] with omega heq N f
  exact congrArg (fun coeff => inverseResponse S coeff
    ((sobolevVolumeLoad f).comp S.space.subtypeL)) (heq N)

/-- The deletion clause of `mfd:lem-borel-weights` on the actual model's same
regular base forms. Construction packages, regularity and finite remaining-field
measurability are produced internally. The deleted limits retain the weighted
form and energy measure, and their scalar pairings have remaining-field versions. -/
theorem borelWeights_deletion
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    letI : NeZero d := ⟨ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hd)⟩
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
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
              (cutoffPositiveCoefficient M H omega (seq n) (rationalTriadicCenter d i)
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
                (determiningDeletedCoefficient M H i layer (seq n) omega)
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
  classical
  dsimp only
  let : NeZero d := ⟨ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hd)⟩
  obtain ⟨J, Pin, X, Sob, W, Cp, _, _, _, _, Interp, _, _, _, _, _, _, _, _, _⟩ :=
    inputs_simultaneous d hd
  have ht : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith
  have htd : (d : ℝ) - 1 / 2 < d := by linarith
  obtain ⟨δB, hδB, hbaseProducer⟩ := original_limit_form_package_exists d hd Interp J Pin X W Cp
    Sob (3 / 4) (1 / 4) (5 / 8) ((d : ℝ) - 1 / 2) ht htd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨δD, hδD, hdeletion⟩ := actual_deletion_convergence hd Interp J Pin X W Cp
    Sob (3 / 4) (1 / 4) (5 / 8) ((d : ℝ) - 1 / 2) ht htd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, δR, _, hδR, hresponses⟩ := inputs_responses_witness d hd 1 le_rfl
  refine ⟨min δB (min δD δR), lt_min hδB (lt_min hδD hδR), ?_⟩
  intro M H hH hsmall
  obtain ⟨Rm, _, _⟩ := hresponses M
    (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let Sreg := inputs_regularity_witness d M
  let It := inputs_iteration_witness d hd M J
  have hHplus : InfraredCharacterization M positiveInfraredVersion :=
    infraredCharacterization_positiveInfraredVersion M H hH
  have hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, rationalTriadicCenter d i c = (q : ℝ)) ∧
      ∃ m : ℤ, rationalTriadicSide d i = (3 : ℝ) ^ m := by
    intro i
    exact ⟨fun c => ⟨(rationalTriadicEnumeration d i).1 c, rfl⟩,
      ⟨(rationalTriadicEnumeration d i).2, rfl⟩⟩
  have hS : ∀ i, (determiningResponseSpace d i).space = killedSobolevGraph (determiningCube d i) :=
    fun _ => rfl
  obtain ⟨seq, hseq, Er, GammaR, Gbase, hbase, hbaseconv, hregular⟩ :=
    hbaseProducer M Rm Sreg It positiveInfraredVersion hHplus
      (hsmall.trans (min_le_left _ _)) (rationalTriadicCenter d) (rationalTriadicSide d)
      (rationalTriadicSide_pos d) (fun i => determiningResponseSpace d i) hS hrat
      (rationalTriadicCatalogue_complete d) id strictMono_id
  refine ⟨seq, hseq, Er, GammaR, Gbase, hbase, ?_, hregular, ?_⟩
  · intro i f
    apply TendstoInMeasure.congr_left ?_ (hbaseconv i f)
    intro n
    filter_upwards [positiveInfraredVersion_ae_eq M H hH] with omega heq
    rw [Lnorm.proxy_pot_eq_coefficient M positiveInfraredVersion,
      Lnorm.proxy_pot_eq_coefficient M H]
    unfold Lnorm.proxy_pot
    rw [heq]
    rfl
  · intro i layer
    let Q := determiningCube d i
    let P := (chaosSampleLaw M).toMeasure
    let ell := fun (omega : BilateralField d) (x : SpatialCoordinates d) =>
      omega (-(Int.ofNat layer)) x
    let a := determiningDeletedCoefficient M positiveInfraredVersion i layer
    have hfinite : ∀ N, layer ≤ N → ∀ f : DomainL2 Q,
        Measurable[remainingSigma layer] (fun omega => inverseResponse (determiningResponseSpace d i)
          (a N omega) ((sobolevVolumeLoad f).comp (determiningResponseSpace d i).space.subtypeL)) :=
      fun N hN f => measurable_deleted_scalar_inverse_remaining M N layer hN
        (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
        (determiningResponseSpace d i) f
    obtain ⟨Gdeleted, hconv, hdata⟩ := hdeletion M Rm Sreg It positiveInfraredVersion hHplus
      (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (rationalTriadicCenter d) (rationalTriadicSide d) (rationalTriadicSide_pos d)
      (fun i => determiningResponseSpace d i) hS hrat (rationalTriadicCatalogue_complete d) i layer seq hseq
      a (fun N omega => deletedPositiveCoefficient_coeFn M positiveInfraredVersion N layer omega
        (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i))
      (Er i) (GammaR i) (Gbase i) (hbase.mono fun omega h => h i) (hbaseconv i)
      (hregular.mono fun omega h => h i) layer
      (fun N hN f => (hfinite N hN f).mono (remainingSigma_le layer) le_rfl)
    obtain ⟨Gversion, hversion, hmeas, hversionData⟩ := deleted_inverse_rem_version P
      (remainingSigma layer) Q (determiningResponseSpace d i) a seq hseq (Er i) (GammaR i)
      ell Gdeleted hdata hconv layer hfinite
    refine ⟨Gdeleted, Gversion, ?_, ?_, hversion, hmeas, ?_⟩
    · intro f
      apply TendstoInMeasure.congr_left ?_ (hconv f)
      intro n
      filter_upwards [deletedPositiveCoefficient_ae_eq M H hH layer
        (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)]
        with omega heq
      exact congrArg (fun coeff => inverseResponse (determiningResponseSpace d i) coeff
        ((sobolevVolumeLoad f).comp (determiningResponseSpace d i).space.subtypeL)) (heq (seq n))
    · filter_upwards [hdata] with omega hω
      obtain ⟨D, hD⟩ := hω
      rw [← hD]
      exact ⟨D.symmetric, D.injective, D.inverse⟩
    · filter_upwards [hversionData] with omega hω
      obtain ⟨D, hD⟩ := hω
      refine ⟨D.form, D.gamma, D.domain_eq, ?_, D.bilinear, D.regular, D.locality, D.cross⟩
      intro u
      rw [← hD]
      exact D.energy_eq u

end SubdiffusiveProcess.AuditExports
