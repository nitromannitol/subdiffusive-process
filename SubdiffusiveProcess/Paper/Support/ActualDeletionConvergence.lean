module

public import SubdiffusiveProcess.Paper.Support.CoupledDeletedPath
public import SubdiffusiveProcess.Paper.Support.RepresentedFamilyRegular
public import SubdiffusiveProcess.WeightedLimitIdentification.IdentifiedPairConvergence

@[expose] public section








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.WeightedLimitIdentification
open _root_.SubdiffusiveProcess.Paper

theorem actual_deletion_convergence
    {d : ℕ} (hd : 2 ≤ d)
        [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (hInterp : CubeFractionalInterpolationInput d hd)
        (J : in_J d) (Pin : in_poincare d hd J) (X : in_extension d hd J)
        (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
        (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
        (ht : (d : ℝ) - 1 < t) (htd : t < d)
        (ha0 : 0 < alpha) (ha1 : alpha < 1)
        (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha)
        (hb : 1 / 2 < beta) (hba : beta < alpha) :
        ∃ δ0 : ℝ, 0 < δ0 ∧
          ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
            (_Rm : in_responses d model) (Sreg : in_6_16 d model)
            (_It : in_iteration d model J Sreg)
            (H : BilateralField d → C(SpatialCoordinates d, ℝ))
            (_hH : InfraredCharacterization model H),
            model.delta ≤ δ0 →
          ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
            (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
            (_hS : ∀ i, (Sspace i).space =
              killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
            (_hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧
              ∃ m : ℤ, R i = (3 : ℝ) ^ m)
            (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ),
              (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
              (∃ m : ℤ, r' = (3 : ℝ) ^ m) →
              ∃ i, Z i = z' ∧ R i = r')
            (i layer : ℕ) (seq : ℕ → ℕ) (_hseq : StrictMono seq),
          let Qd := centeredCube (Z i) (R i) (hR i)
          let P := (chaosSampleLaw model).toMeasure
          let ell := fun (omega : BilateralField d) (x : SpatialCoordinates d) =>
            omega (-(Int.ofNat layer)) x
          ∀ (aDeleted : ℕ → BilateralField d → PositiveCoefficient Qd)
            (_hdeleted : ∀ N omega, ∀ᵐ x ∂volume.restrict (Qd : Set (SpatialCoordinates d)),
              (aDeleted N omega).val x = Real.exp (-ell omega x) *
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H omega N (Z i) (hR i)).val x)
            (Er : BilateralField d → _root_.SubdiffusiveProcess.DirichletForm
              (volume.restrict (Qd : Set (SpatialCoordinates d))))
            (GammaR : ∀ omega, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Er omega).toClosedForm)
            (Gbase : BilateralField d → DomainL2 Qd →L[ℝ] DomainL2 Qd)
            (_hbase : ∀ᵐ omega ∂P, ∀ u,
              (Er omega).toClosedForm.energy u = limitFormEnergy (Gbase omega) u)
            (_hbaseconv : ∀ f : DomainL2 Qd, TendstoInMeasure P
              (fun n omega => inverseResponse (Sspace i)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H omega (seq n) (Z i) (hR i))
                ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)) atTop
              (fun omega => inner ℝ f (Gbase omega f)))
            (_hregular : ∀ᵐ omega ∂P,
              _root_.SubdiffusiveProcess.DirichletForm.IsRegular (Er omega).toClosedForm ∧
              _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (Er omega).toClosedForm ∧
              _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra (Er omega).toClosedForm ∧
              (∃ C : Set (DomainL2 Qd),
                _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (Er omega).toClosedForm
                  (Qd : Set (SpatialCoordinates d)) C) ∧
              (∀ u ∈ (Er omega).toClosedForm.domain,
                (GammaR omega).measure u (Qd : Set (SpatialCoordinates d))ᶜ = 0))
            (N0 : ℕ)
            (_hfiniteMeas : ∀ N, N0 ≤ N → ∀ f : DomainL2 Qd,
              Measurable
                (fun omega => inverseResponse (Sspace i) (aDeleted N omega)
                  ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL))),
          ∃ Gdeleted : BilateralField d → DomainL2 Qd →L[ℝ] DomainL2 Qd,
            (∀ f : DomainL2 Qd, TendstoInMeasure P
              (fun n omega => inverseResponse (Sspace i) (aDeleted (seq n) omega)
                ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)) atTop
              (fun omega => inner ℝ f (Gdeleted omega f))) ∧
            (∀ᵐ omega ∂P, ∃ D : DeletedInverseData Qd (Er omega) (GammaR omega)
              (ell omega), D.operator = Gdeleted omega) := by
  classical
  obtain ⟨delta, hdelta, hrep⟩ := conv_represented_family_extra_with_ae_descent
    d hd hInterp J Pin X W Cp Sob alpha eta beta t ht htd ha0 ha1 heta hAeta hb hba
  refine ⟨delta, hdelta, ?_⟩
  intro model Rm Sreg It H hH hsmall Z R hR Sspace hS hrat hcomp i layer seq hseq
  dsimp only
  intro aDeleted hdeleted Er GammaR Gbase hbase hbaseconv hregular N0 hfiniteMeas
  let Qd := centeredCube (Z i) (R i) (hR i)
  let P := (chaosSampleLaw model).toMeasure
  let ell : BilateralField d → SpatialCoordinates d → ℝ :=
    fun omega x => omega (-(Int.ofNat layer)) x
  have hell : ∀ omega, ContinuousOn (ell omega) (closure (Qd : Set (SpatialCoordinates d))) ∧
      ∃ K : ℝ, ∀ x ∈ (Qd : Set (SpatialCoordinates d)), |ell omega x| ≤ K := by
    intro omega
    refine ⟨(omega (-(Int.ofNat layer))).continuous.continuousOn,
      ‖(omega (-(Int.ofNat layer))).restrict (closedCube (Z i) (R i) (hR i))‖, ?_⟩
    intro x hx
    simpa only [Real.norm_eq_abs] using!
      ((omega (-(Int.ofNat layer))).restrict (closedCube (Z i) (R i) (hR i))).norm_coe_le_norm
        ⟨x, centeredCube_subset_closedCube (Z i) (hR i) hx⟩
  have hregdata : ∀ᵐ omega ∂P,
      (∃ C : Set (DomainL2 Qd), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (Er omega).toClosedForm (Qd : Set _) C) ∧
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (Er omega).toClosedForm ∧
      (∀ u ∈ (Er omega).domain, (GammaR omega).measure u (Qd : Set _)ᶜ = 0) :=
    hregular.mono fun omega h => ⟨h.2.2.2.1, h.2.1, h.2.2.2.2⟩
  obtain ⟨Gdeleted, hdata⟩ := exists_deleted_inverse_family P Qd Er GammaR Gbase
    hbase hregdata ell hell
  refine ⟨Gdeleted, ?_, hdata⟩
  intro f
  apply tendsto_in_measure_of_eventually_measurable_identified_pairs P
    (fun n omega => inverseResponse (Sspace i) (aDeleted (seq n) omega)
      ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL))
    (hseq.tendsto_atTop.eventually (eventually_ge_atTop N0) |>.mono
      fun n hn => hfiniteMeas (seq n) hn f)
    (fun omega => inner ℝ f (Gdeleted omega f))
  intro u v hu hv
  obtain ⟨sigma, hsigma, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF,
    hjoint, hbounds, hforms, hextra, hdescent⟩ :=
    hrep model Rm Sreg It H hH hsmall Z R hR Sspace hS hrat hcomp
      (seq ∘ u) (seq ∘ v) (hseq.comp hu) (hseq.comp hv)
      (fun (_ : Unit) (_ : ℕ) (_ : BilateralField d) => (0 : ℝ))
      (fun _ _ => ⟨measurable_const, measurable_const⟩)
      (fun _ rho hrho => ⟨0, fun _ => by simp⟩)
  have : IsProbabilityMeasure Ph := hPh
  obtain ⟨_, hfieldmeas, hfieldlaw, _, _, _, henv, hfieldconv, _, hfinite, hlimits⟩ := hjoint.1
  have hfield : MeasurePreserving field Ph P := ⟨hfieldmeas, hfieldlaw⟩
  have hcore : ∀ᵐ omega ∂P, ∃ C : Set (DomainL2 Qd),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (Er omega).toClosedForm (Qd : Set _) C :=
    hregular.mono fun omega h => h.2.2.2.1
  have hE := coupled_deleted_path_tendsto hd model H hH.1 (Z i) (R i) (hR i)
    (Sspace i) (hS i) seq Er GammaR Gbase Gdeleted hbase hbaseconv hcore layer hdata
    aDeleted hdeleted Ph env field (fun n => (henv n).1) hfield
    (hfieldconv.mono fun omega h => h.1) (u ∘ sigma) (hu.comp hsigma)
    (GNE i) (GE i)
    (hfinite.mono fun omega h n g => (h i n g).1)
    (hlimits.mono fun omega h => (h i).1)
    (hforms.mono fun omega h => by
      obtain ⟨LE, LF, _, _⟩ := h
      exact ⟨LE i⟩)
  have hF := coupled_deleted_path_tendsto hd model H hH.1 (Z i) (R i) (hR i)
    (Sspace i) (hS i) seq Er GammaR Gbase Gdeleted hbase hbaseconv hcore layer hdata
    aDeleted hdeleted Ph env field (fun n => (henv n).2) hfield
    (hfieldconv.mono fun omega h => h.2) (v ∘ sigma) (hv.comp hsigma)
    (GNF i) (GF i)
    (hfinite.mono fun omega h n g => (h i n g).2)
    (hlimits.mono fun omega h => (h i).2)
    (hforms.mono fun omega h => by
      obtain ⟨LE, LF, _, _⟩ := h
      exact ⟨LF i⟩)
  exact ⟨sigma, hsigma, Ωh, mΩh, Ph, hPh, env, field, (fun n => (henv n).1), hfield,
    hfieldconv.mono (fun omega h => h.1), hdescent,
    hE.mono (fun omega h => h f), hF.mono (fun omega h => h f)⟩

end SubdiffusiveProcess.WeightedLimitIdentification
