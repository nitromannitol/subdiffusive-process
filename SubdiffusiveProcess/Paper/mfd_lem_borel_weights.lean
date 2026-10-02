import SubdiffusiveProcess.Paper.Support.ActualDeletionConvergence
import SubdiffusiveProcess.Paper.Support.DeletedInverseRemVersion
import SubdiffusiveProcess.Paper.Support.OriginalBasePackage

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.AuditRepairs
open scoped ENNReal NNReal Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

theorem mfd_lem_borel_weights
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (M : ℝ) (hgbdd : ∀ x : SpatialCoordinates d, |g x| ≤ M)
    (hreg : DirichletForm.IsRegular E.toClosedForm)
    (hloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (hcoreQ : ∃ C : Set (Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))),
      DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (halg : DirichletForm.IsCoreAlgebra E.toClosedForm) :
    (∃ (Eg : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
        (Gammag : DirichletForm.EnergyMeasure Eg.toClosedForm),
        Eg.toClosedForm.domain = E.toClosedForm.domain ∧
        (∀ u ∈ E.toClosedForm.domain, ∀ v ∈ E.toClosedForm.domain,
          Eg.toClosedForm.form u v =
            DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
              (fun x => Real.exp (g x))) ∧
        DirichletForm.IsRegular Eg.toClosedForm ∧
        DirichletForm.IsStronglyLocal Eg.toClosedForm ∧
        (∀ u ∈ E.toClosedForm.domain, ∀ v ∈ E.toClosedForm.domain,
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gammag.cross u v B =
              DirichletForm.signedIntegralOn (Gamma.cross u v) B
                (fun x => Real.exp (g x)))) ∧
      (∀ (hd : 2 ≤ d)
        [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (hInterp : CubeFractionalInterpolationInput d hd)
        (J : in_J d) (Pin : in_poincare d hd J) (X : in_extension d hd J)
        (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
        (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
        (ht : (d : ℝ) - 1 < t) (htd : t < d)
        (ha0 : 0 < alpha) (ha1 : alpha < 1)
        (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha)
        (hb : 1 / 2 < beta) (hba : beta < alpha),
        ∃ δ0 : ℝ, 0 < δ0 ∧
          ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
            (Rm : in_responses d model) (Sreg : in_6_16 d model)
            (It : in_iteration d model J Sreg)
            (H : BilateralField d → C(SpatialCoordinates d, ℝ))
            (hH : InfraredCharacterization model H),
            model.delta ≤ δ0 →
          ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
            (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
            (hS : ∀ i, (Sspace i).space =
              killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
            (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧
              ∃ m : ℤ, R i = (3 : ℝ) ^ m)
            (hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ),
              (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
              (∃ m : ℤ, r' = (3 : ℝ) ^ m) →
              ∃ i, Z i = z' ∧ R i = r')
            (i layer : ℕ) (seq : ℕ → ℕ) (hseq : StrictMono seq),
          let Qd := centeredCube (Z i) (R i) (hR i)
          let P := (chaosSampleLaw model).toMeasure
          let ell := fun (omega : BilateralField d) (x : SpatialCoordinates d) =>
            omega (-(Int.ofNat layer)) x
          let Rem := MeasurableSpace.comap
            (fun omega : BilateralField d =>
              fun j : {j : ℤ // j ≠ -(Int.ofNat layer)} => omega j.1)
            (inferInstance : MeasurableSpace
              ({j : ℤ // j ≠ -(Int.ofNat layer)} → C(SpatialCoordinates d, ℝ)))
          ∀ (aDeleted : ℕ → BilateralField d → PositiveCoefficient Qd)
            (hdeleted : ∀ N omega, ∀ᵐ x ∂volume.restrict (Qd : Set (SpatialCoordinates d)),
              (aDeleted N omega).val x = Real.exp (-ell omega x) *
                (Lane4.cutoffPositiveCoefficient model H omega N (Z i) (hR i)).val x)
            (Er : BilateralField d → _root_.DirichletForm
              (volume.restrict (Qd : Set (SpatialCoordinates d))))
            (GammaR : ∀ omega, DirichletForm.EnergyMeasure (Er omega).toClosedForm)
            (Gbase : BilateralField d → DomainL2 Qd →L[ℝ] DomainL2 Qd)
            (hbase : ∀ᵐ omega ∂P, ∀ u,
              (Er omega).toClosedForm.energy u = limitFormEnergy (Gbase omega) u)
            (hbaseconv : ∀ f : DomainL2 Qd, TendstoInMeasure P
              (fun n omega => inverseResponse (Sspace i)
                (Lane4.cutoffPositiveCoefficient model H omega (seq n) (Z i) (hR i))
                ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)) atTop
              (fun omega => inner ℝ f (Gbase omega f)))
            (hregular : ∀ᵐ omega ∂P,
              DirichletForm.IsRegular (Er omega).toClosedForm ∧
              DirichletForm.IsStronglyLocal (Er omega).toClosedForm ∧
              DirichletForm.IsCoreAlgebra (Er omega).toClosedForm ∧
              (∃ C : Set (DomainL2 Qd),
                DirichletForm.IsCoreOn (Er omega).toClosedForm
                  (Qd : Set (SpatialCoordinates d)) C) ∧
              (∀ u ∈ (Er omega).toClosedForm.domain,
                (GammaR omega).measure u (Qd : Set (SpatialCoordinates d))ᶜ = 0))
            (N0 : ℕ)
            (hfiniteRem : ∀ N, N0 ≤ N → ∀ f : DomainL2 Qd,
              @Measurable (BilateralField d) ℝ Rem _
                (fun omega => inverseResponse (Sspace i) (aDeleted N omega)
                  ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL))),
          ∃ Gdeleted Gversion : BilateralField d → DomainL2 Qd →L[ℝ] DomainL2 Qd,
            (∀ f : DomainL2 Qd, TendstoInMeasure P
              (fun n omega => inverseResponse (Sspace i) (aDeleted (seq n) omega)
                ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)) atTop
              (fun omega => inner ℝ f (Gdeleted omega f))) ∧
            (∀ᵐ omega ∂P,
              (∀ f g : DomainL2 Qd, inner ℝ f (Gdeleted omega g) =
                inner ℝ (Gdeleted omega f) g) ∧
              Function.Injective (Gdeleted omega) ∧
              (∀ f : DomainL2 Qd, IsLUB {t : ℝ | ∃ u : DomainL2 Qd,
                u ∈ (Er omega).toClosedForm.domain ∧
                t = 2 * inner ℝ f u - ∫ x in (Qd : Set (SpatialCoordinates d)),
                  Real.exp (-ell omega x) ∂((GammaR omega).measure u)}
                (inner ℝ f (Gdeleted omega f)))) ∧
            (Gversion =ᵐ[P] Gdeleted) ∧
            (∀ f g : DomainL2 Qd, @Measurable (BilateralField d) ℝ Rem _
              (fun omega => inner ℝ f (Gversion omega g))) ∧
            (∀ᵐ omega ∂P,
              ∃ (Edeleted : _root_.DirichletForm
                    (volume.restrict (Qd : Set (SpatialCoordinates d))))
                (GammaDeleted : DirichletForm.EnergyMeasure Edeleted.toClosedForm),
                Edeleted.toClosedForm.domain = (Er omega).toClosedForm.domain ∧
                (∀ u : DomainL2 Qd,
                  Edeleted.toClosedForm.energy u = limitFormEnergy (Gversion omega) u) ∧
                (∀ u ∈ (Er omega).toClosedForm.domain,
                  ∀ v ∈ (Er omega).toClosedForm.domain,
                  Edeleted.toClosedForm.form u v =
                    DirichletForm.signedIntegralOn ((GammaR omega).cross u v) Set.univ
                      (fun x => Real.exp (-ell omega x))) ∧
                DirichletForm.IsRegular Edeleted.toClosedForm ∧
                DirichletForm.IsStronglyLocal Edeleted.toClosedForm ∧
                (∀ u ∈ (Er omega).toClosedForm.domain,
                  ∀ v ∈ (Er omega).toClosedForm.domain,
                  ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
                    GammaDeleted.cross u v B =
                      DirichletForm.signedIntegralOn ((GammaR omega).cross u v) B
                        (fun x => Real.exp (-ell omega x))))) :=
 by
  constructor
  · obtain ⟨Eg, Gammag, hdom, hform, hregg, _, hlocg, hGamma⟩ :=
      lem_borel_weights_form E Gamma g hg M hgbdd hreg hcoreQ hloc halg
    exact ⟨Eg, Gammag, hdom, hform, hregg, hlocg, hGamma⟩
  · intro hd _ _ hInterp J Pin X W Cp Sob alpha eta beta t ht htd ha0 ha1 heta hAeta hb hba
    obtain ⟨deltaB, hdeltaB, hbaseProducer⟩ := original_limit_form_package_exists
      d hd hInterp J Pin X W Cp Sob alpha eta beta t ht htd ha0 ha1 heta hAeta hb hba
    obtain ⟨deltaD, hdeltaD, hdeletion⟩ := actual_deletion_convergence
      hd hInterp J Pin X W Cp Sob alpha eta beta t ht htd ha0 ha1 heta hAeta hb hba
    refine ⟨min deltaB deltaD, lt_min hdeltaB hdeltaD, ?_⟩
    intro model Rm Sreg It H hH hsmall Z R hR Sspace hS hrat hcomp i layer seq hseq
    dsimp only
    intro aDeleted hdeleted Er GammaR Gbase hbase hbaseconv hregular N0 hfiniteRem
    let Qd := centeredCube (Z i) (R i) (hR i)
    let P := (chaosSampleLaw model).toMeasure
    let ell : BilateralField d → SpatialCoordinates d → ℝ :=
      fun omega x => omega (-(Int.ofNat layer)) x
    let Rem := MeasurableSpace.comap
      (fun omega : BilateralField d =>
        fun j : {j : ℤ // j ≠ -(Int.ofNat layer)} => omega j.1)
      (inferInstance : MeasurableSpace
        ({j : ℤ // j ≠ -(Int.ofNat layer)} → C(SpatialCoordinates d, ℝ)))
    letI : MeasurableSpace (BilateralField d) := MeasurableSpace.pi
    have hremove : Measurable (fun omega : BilateralField d =>
        fun j : {j : ℤ // j ≠ -(Int.ofNat layer)} => omega j.1) := by
      apply measurable_pi_lambda
      intro j
      exact @measurable_pi_apply ℤ (fun _ => C(SpatialCoordinates d, ℝ))
        (fun _ => inferInstance) j.1
    have hRem : Rem ≤ (inferInstance : MeasurableSpace (BilateralField d)) :=
      hremove.comap_le
    have hfiniteMeas : ∀ N, N0 ≤ N → ∀ f : DomainL2 Qd,
        Measurable (fun omega => inverseResponse (Sspace i) (aDeleted N omega)
          ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)) :=
      fun N hn f => (hfiniteRem N hn f).mono hRem le_rfl
    obtain ⟨Gdeleted, hconv, hdata⟩ := hdeletion model Rm Sreg It H hH
      (hsmall.trans (min_le_right _ _)) Z R hR Sspace hS hrat hcomp i layer seq hseq
      aDeleted hdeleted Er GammaR Gbase hbase hbaseconv hregular N0 hfiniteMeas
    have hinverse : ∀ᵐ omega ∂P,
        (∀ f g : DomainL2 Qd, inner ℝ f (Gdeleted omega g) = inner ℝ (Gdeleted omega f) g) ∧
        Function.Injective (Gdeleted omega) ∧
        (∀ f : DomainL2 Qd, IsLUB {t : ℝ | ∃ u : DomainL2 Qd,
          u ∈ (Er omega).domain ∧ t = 2 * inner ℝ f u -
            ∫ x in (Qd : Set (SpatialCoordinates d)), Real.exp (-ell omega x)
              ∂(GammaR omega).measure u} (inner ℝ f (Gdeleted omega f))) := by
      filter_upwards [hdata] with omega hω
      obtain ⟨D, hD⟩ := hω
      rw [← hD]
      exact ⟨D.symmetric, D.injective, D.inverse⟩
    obtain ⟨Gversion, hversion, hmeas, hversionData⟩ := deleted_inverse_rem_version P Rem
      Qd (Sspace i) aDeleted seq hseq Er GammaR ell Gdeleted hdata hconv N0 hfiniteRem
    refine ⟨Gdeleted, Gversion, hconv, hinverse, hversion, hmeas, ?_⟩
    filter_upwards [hversionData] with omega hω
    obtain ⟨D, hD⟩ := hω
    refine ⟨D.form, D.gamma, D.domain_eq, ?_, D.bilinear, D.regular, D.locality, D.cross⟩
    intro u
    rw [← hD]
    exact D.energy_eq u

end Paper
