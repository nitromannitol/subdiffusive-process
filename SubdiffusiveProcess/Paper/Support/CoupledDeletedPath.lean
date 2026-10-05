module

public import SubdiffusiveProcess.Paper.Support.DeletedResponseLimitSide
public import SubdiffusiveProcess.WeightedLimitIdentification.CoupledBaseIdentification
public import SubdiffusiveProcess.WeightedLimitIdentification.CutoffScalarMeasurability

@[expose] public section








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.WeightedLimitIdentification
open _root_.SubdiffusiveProcess.Paper

theorem coupled_deleted_path_tendsto
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (seq : ℕ → ℕ)
    (E : BilateralField d → _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (Gamma : ∀ β, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (E β).toClosedForm)
    (Gbase Gdeleted : BilateralField d → DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr))
    (hbase : ∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ u, (E β).energy u = limitFormEnergy (Gbase β) u)
    (hbaseconv : ∀ f : DomainL2 (centeredCube z r hr),
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n β => inverseResponse S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (seq n) z hr)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (fun β => inner ℝ f (Gbase β f)))
    (hcore : ∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∃ C : Set (DomainL2 (centeredCube z r hr)),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (E β).toClosedForm (centeredCube z r hr : Set _) C)
    (layer : ℕ)
    (hdata : ∀ᵐ β ∂(chaosSampleLaw M).toMeasure,
      ∃ D : DeletedInverseData (centeredCube z r hr) (E β) (Gamma β) (β (-(Int.ofNat layer))),
        D.operator = Gdeleted β)
    (b : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr))
    (hb : ∀ N β, (b N β).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => Real.exp (-β (-(Int.ofNat layer)) x) *
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr).val x)
    {Ωh : Type} [MeasurableSpace Ωh] (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
    (env : ℕ → Ωh → BilateralField d) (field : Ωh → BilateralField d)
    (henv : ∀ n, MeasurePreserving (env n) Ph (chaosSampleLaw M).toMeasure)
    (hfield : MeasurePreserving field Ph (chaosSampleLaw M).toMeasure)
    (hfieldconv : ∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (field ω)))
    (ns : ℕ → ℕ) (hns : StrictMono ns)
    (GN : ℕ → Ωh → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : Ωh → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ᵐ ω ∂Ph, ∀ n f, GN n ω f = (responseSolution S
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n ω) (seq (ns n)) z hr)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlimit : ∀ᵐ ω ∂Ph, Tendsto (fun n => GN n ω) atTop (𝓝 (G ω)))
    (hforms : ∀ᵐ ω ∂Ph, Nonempty (aux_limit_form_package_limit_side d hd z r hr S (G ω)
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n ω) (seq (ns n)) z hr))) :
    ∀ᵐ ω ∂Ph, ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto (fun n => inverseResponse S (b (seq (ns n)) (env n ω))
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (𝓝 (inner ℝ f (Gdeleted (field ω) f))) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hquad : ∀ᵐ ω ∂Ph, ∀ f, inner ℝ f (G ω f) = inner ℝ f (Gbase (field ω) f) := by
    apply coupled_base_quadratic_identification (chaosSampleLaw M).toMeasure Ph env field
      henv hfield hfieldconv
      (fun n β f => inverseResponse S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (seq n) z hr)
        ((sobolevVolumeLoad f).comp S.space.subtypeL))
      (fun n f => (measurable_cutoff_scalar_inverse M H hH (seq n) z r hr S f).aestronglyMeasurable)
      Gbase hbaseconv ns hns GN G ?_ hlimit
    filter_upwards [hGN] with ω hω n f
    rw [hω n f, inverseResponse_eq_load]
    rfl
  filter_upwards [hforms, hquad, hfieldconv,
    hfield.quasiMeasurePreserving.ae hbase, hfield.quasiMeasurePreserving.ae hcore,
    hfield.quasiMeasurePreserving.ae hdata] with ω hL hq henvω hbω hcω hdω
  obtain ⟨L⟩ := hL
  obtain ⟨D, hD⟩ := hdω
  have hbaseL : ∀ u, (E (field ω)).energy u = L.form.energy u := by
    intro u
    rw [hbω u, L.energy_eq u]
    exact (dual_energy_eq_of_quadratic_eq (G ω) (Gbase (field ω)) hq u).symm
  have hell : Tendsto (fun n => env n ω (-(Int.ofNat layer))) atTop
      (𝓝 (field ω (-(Int.ofNat layer)))) :=
    ((continuous_apply (-(Int.ofNat layer))).tendsto (field ω)).comp henvω
  have ht := deleted_response_tendsto_of_limit_side hS L (E (field ω)) (Gamma (field ω))
    hcω hbaseL (field ω (-(Int.ofNat layer))) (fun n => env n ω (-(Int.ofNat layer)))
    hell D (fun n => b (seq (ns n)) (env n ω))
    (fun n => hb (seq (ns n)) (env n ω))
  simpa only [hD] using ht

end SubdiffusiveProcess.WeightedLimitIdentification
