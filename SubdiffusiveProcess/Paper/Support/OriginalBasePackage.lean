module

public import SubdiffusiveProcess.Paper.Support.OriginalInverseLimits
public import SubdiffusiveProcess.Paper.Support.RepresentedFamilyRegular
public import SubdiffusiveProcess.Paper.Support.RegularBaseData
public import SubdiffusiveProcess.WeightedLimitIdentification.CoupledBaseIdentification
public import SubdiffusiveProcess.WeightedLimitIdentification.CutoffScalarMeasurability

@[expose] public section








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.WeightedLimitIdentification
open _root_.SubdiffusiveProcess.Paper

theorem original_limit_form_package_exists
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha) (hb : 1 / 2 < beta) (hba : beta < alpha) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (_hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (initial : ℕ → ℕ), StrictMono initial →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∃ (Er : (i : ℕ) → BilateralField d → _root_.SubdiffusiveProcess.DirichletForm
              (volume.restrict (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d))))
          (GammaR : ∀ i omega, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Er i omega).toClosedForm)
          (Gbase : (i : ℕ) → BilateralField d →
            DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
              DomainL2 (centeredCube (Z i) (R i) (hR i))),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i u,
            (Er i omega).toClosedForm.energy u = limitFormEnergy (Gbase i omega) u) ∧
          (∀ i (f : DomainL2 (centeredCube (Z i) (R i) (hR i))),
            TendstoInMeasure (chaosSampleLaw M).toMeasure
              (fun n omega => inverseResponse (Sspace i)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (initial (seq n)) (Z i) (hR i))
                ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)) atTop
              (fun omega => inner ℝ f (Gbase i omega f))) ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
            _root_.SubdiffusiveProcess.DirichletForm.IsRegular (Er i omega).toClosedForm ∧
            _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (Er i omega).toClosedForm ∧
            _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra (Er i omega).toClosedForm ∧
            (∃ C : Set (DomainL2 (centeredCube (Z i) (R i) (hR i))),
              _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (Er i omega).toClosedForm
                (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d)) C) ∧
            (∀ u ∈ (Er i omega).toClosedForm.domain,
              (GammaR i omega).measure u
                (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d))ᶜ = 0)) := by
  classical
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨deltaI, hdeltaI, hinverse⟩ := exists_original_inverse_limits d hd hInterp E Pin X W Cp Sob
  obtain ⟨deltaR, hdeltaR, hrep⟩ := conv_represented_family_extra_with_ae_descent
    d hd hInterp E Pin X W Cp Sob alpha eta beta t ht htd ha0 ha1 heta hAeta hb hba
  refine ⟨min deltaI deltaR, lt_min hdeltaI hdeltaR, ?_⟩
  intro M Rm Sreg It H hH hdelta Z R hR Sspace hS hrat hcomp initial hinitial
  let P := (chaosSampleLaw M).toMeasure
  obtain ⟨G, hGmeas, hGconv⟩ := hinverse M Rm Sreg It H hH
    (hdelta.trans (min_le_left _ _)) Z R hR Sspace hS hrat hcomp
  have hscalar : ∀ i (f : DomainL2 (centeredCube (Z i) (R i) (hR i))),
      TendstoInMeasure P (fun n β => inverseResponse (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (initial n) (Z i) (hR i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)) atTop
        (fun β => inner ℝ f (G i β f)) := fun i f =>
    (cutoff_scalar_inverse_tendsto_in_measure M H hH.1 (Z i) (R i) (hR i)
      (Sspace i) (G i) (hGconv i) f).comp hinitial.tendsto_atTop
  obtain ⟨sigma, hsigma, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF,
    hjoint, hbounds, hforms, hextra, hdescent⟩ :=
    hrep M Rm Sreg It H hH (hdelta.trans (min_le_right _ _)) Z R hR Sspace hS hrat hcomp
      initial initial hinitial hinitial (fun (_ : Unit) (_ : ℕ) (_ : BilateralField d) => (0 : ℝ))
      (fun _ _ => ⟨measurable_const, measurable_const⟩)
      (fun _ rho hrho => ⟨0, fun _ => by simp⟩)
  have : IsProbabilityMeasure Ph := hPh
  obtain ⟨_, hfieldmeas, hfieldlaw, _, _, _, henv, hfieldconv, _, hfinite, hlimits⟩ := hjoint.1
  have hfield : MeasurePreserving field Ph P := ⟨hfieldmeas, hfieldlaw⟩
  have hquad : ∀ i, ∀ᵐ ω ∂Ph, ∀ f : DomainL2 (centeredCube (Z i) (R i) (hR i)),
      inner ℝ f (GE i ω f) = inner ℝ f (G i (field ω) f) := by
    intro i
    apply coupled_base_quadratic_identification P Ph env field
      (fun n => (henv n).1) hfield (hfieldconv.mono fun ω h => h.1)
      (fun n β f => inverseResponse (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (initial n) (Z i) (hR i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL))
      (fun n f => (measurable_cutoff_scalar_inverse M H hH.1 (initial n)
        (Z i) (R i) (hR i) (Sspace i) f).aestronglyMeasurable)
      (G i) (hscalar i) sigma hsigma (GNE i) (GE i) ?_
      (hlimits.mono fun ω h => (h i).1)
    filter_upwards [hfinite] with ω hω n f
    rw [(hω i n f).1, inverseResponse_eq_load]
    rfl
  let good : BilateralField d → Prop := fun β => ∀ i,
    Nonempty (RegularBaseData (centeredCube (Z i) (R i) (hR i)) (G i β))
  have hgoodRep : ∀ᵐ ω ∂Ph, good (field ω) := by
    filter_upwards [hforms, ae_all_iff.mpr hquad] with ω hform hq i
    obtain ⟨LE, LF, hlocal, hnested⟩ := hform
    obtain ⟨D⟩ := regular_base_data_of_limit_side (LE i) (hlocal i).1
    exact ⟨D.ofQuadraticEq (hq i)⟩
  have hgood : ∀ᵐ β ∂P, good β := hdescent good hgoodRep
  obtain ⟨β0, hβ0⟩ := hgood.exists
  let G' : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
        DomainL2 (centeredCube (Z i) (R i) (hR i)) := fun i β =>
    if good β then G i β else G i β0
  have hdata : ∀ i β,
      Nonempty (RegularBaseData (centeredCube (Z i) (R i) (hR i)) (G' i β)) := by
    intro i β
    by_cases hβ : good β
    · simpa only [G', ite_eq_left hβ] using hβ i
    · simpa only [G', ite_eq_right hβ] using hβ0 i
  let D : ∀ i β, RegularBaseData (centeredCube (Z i) (R i) (hR i)) (G' i β) :=
    fun i β => Classical.choice (hdata i β)
  refine ⟨id, strictMono_id, (fun i β => (D i β).form),
    (fun i β => (D i β).gamma), G', ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun β i u => (D i β).energy_eq u
  · intro i f
    apply TendstoInMeasure.congr_right ?_ (hscalar i f)
    filter_upwards [hgood] with β hβ
    simp only [G', ite_eq_left hβ]
  · exact Filter.Eventually.of_forall fun β i =>
      ⟨(D i β).regular, (D i β).locality, (D i β).algebra, (D i β).core, (D i β).support⟩

end SubdiffusiveProcess.WeightedLimitIdentification
