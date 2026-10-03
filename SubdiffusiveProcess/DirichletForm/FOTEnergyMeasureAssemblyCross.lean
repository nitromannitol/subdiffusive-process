module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblySigned
public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuous

@[expose] public section

open MeasureTheory Filter Set Topology

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

theorem EnergyFamily.cross_add_self {F : _root_.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {u v : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure (u + v) B).toReal = (Γ.measure u B).toReal +
      2 * Γ.cross u v B + (Γ.measure v B).toReal := by
  have huv := F.domain.add_mem hu hv
  rw [← Γ.cross_self (u + v) huv B hB,
    Γ.cross_symm _ huv _ huv, Γ.cross_add_right _ huv u hu v hv,
    VectorMeasure.add_apply, Γ.cross_symm (u + v) huv u hu,
    Γ.cross_symm (u + v) huv v hv,
    Γ.cross_add_right u hu u hu v hv, Γ.cross_add_right v hv u hu v hv,
    VectorMeasure.add_apply, VectorMeasure.add_apply, Γ.cross_symm v hv u hu,
    Γ.cross_self u hu B hB, Γ.cross_self v hv B hB]
  ring

theorem EnergyFamily.cross_absolutelyContinuous_left
    {F : _root_.DirichletForm m} {U : Set X} (Γ : EnergyFamily F U)
    {u v : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain) :
    (Γ.cross u v).totalVariation ≪ Γ.measure u := by
  rw [← VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure (Γ.measure u),
    ← SignedMeasure.absolutelyContinuous_ennreal_iff]
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro B hB hzero
  rw [Measure.toENNRealVectorMeasure_apply_measurable hB] at hzero
  have h := Γ.cross_le u hu v hv B hB
  rw [hzero, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at h
  exact abs_nonpos_iff.mp h

/-- The representatives also agree for both Jordan parts of a cross measure. -/
theorem RepresentativeFamily.continuous_agree_cross
    {F : _root_.DirichletForm m} {U : Set X} (Γ : EnergyFamily F U)
    (q : RepresentativeFamily Γ) {u v : Lp ℝ 2 m}
    (hu : u ∈ F.domain) (hv : v ∈ F.domain) {f : X → ℝ}
    (hf : Continuous f) (hae : ⇑u =ᵐ[m] f) :
    q.rep u hu =ᵐ[(Γ.cross u v).toJordanDecomposition.posPart] f ∧
      q.rep u hu =ᵐ[(Γ.cross u v).toJordanDecomposition.negPart] f := by
  have hc := (SignedMeasure.totalVariation_absolutelyContinuous_iff _ _).mp
    (Γ.cross_absolutelyContinuous_left hu hv)
  exact ⟨hc.1.ae_eq (q.continuous_agree u hu f hf hae u hu),
    hc.2.ae_eq (q.continuous_agree u hu f hf hae u hu)⟩

theorem EnergyFamily.cross_locality [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    {F : _root_.DirichletForm m} {U : Set X} (h : Data F U) (Γ : EnergyFamily F U)
    {u v u' v' : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    (hu' : u' ∈ F.domain) (hv' : v' ∈ F.domain) {O : Set X} (hO : IsOpen O)
    (heu : ⇑u =ᵐ[m.restrict O] ⇑u') (hev : ⇑v =ᵐ[m.restrict O] ⇑v') :
    (Γ.cross u v).restrict O = (Γ.cross u' v').restrict O := by
  have headd : ⇑(u + v) =ᵐ[m.restrict O] ⇑(u' + v') := by
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add u v),
      ae_restrict_of_ae (Lp.coeFn_add u' v'), heu, hev] with x h1 h2 h3 h4
    simp only [h1, h2, Pi.add_apply, h3, h4]
  have hru := Γ.locality h hu hu' hO heu
  have hrv := Γ.locality h hv hv' hO hev
  have hra := Γ.locality h (F.domain.add_mem hu hv) (F.domain.add_mem hu' hv') hO headd
  ext B hB
  rw [VectorMeasure.restrict_apply _ hO.measurableSet hB,
    VectorMeasure.restrict_apply _ hO.measurableSet hB]
  have hμu := congrArg (fun μ : Measure X => (μ B).toReal) hru
  have hμv := congrArg (fun μ : Measure X => (μ B).toReal) hrv
  have hμa := congrArg (fun μ : Measure X => (μ B).toReal) hra
  simp only [Measure.restrict_apply hB] at hμu hμv hμa
  rw [Γ.cross_add_self hu hv (hB.inter hO.measurableSet),
    Γ.cross_add_self hu' hv' (hB.inter hO.measurableSet)] at hμa
  linarith

end DirichletForm.FOTConstruction
