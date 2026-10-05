module

public import SubdiffusiveProcess.Paper.represented_limit_planes_null
public import SubdiffusiveProcess.Paper.conv_represented_joint_buffered

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- On one common event, both actual represented inverse limits have plane-null energy
measures on every determining cube, for every regular form representing that inverse limit. -/
theorem conv_represented_limit_planes (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (hdata : conv_represented_joint_buffered d hd model H Ω P field envE envF z r hr Sspace
      GNE GNF GE GF NE NF alpha eta)
    (hBounds : aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr
      Sspace GE GF NE NF) :
    ∀ᵐ omega ∂P, ∀ i,
      (∀ (Ef : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))))
        (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Ef.toClosedForm),
        (∀ u, Ef.toClosedForm.energy u = limitFormEnergy (GE i omega) u) →
        (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Ef.toClosedForm
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) →
        ∀ u ∈ Ef.domain, ∀ (j : Fin d) (c : ℝ),
          Gamma.measure u {x : SpatialCoordinates d | x j = c} = 0) ∧
      (∀ (Ef : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))))
        (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Ef.toClosedForm),
        (∀ u, Ef.toClosedForm.energy u = limitFormEnergy (GF i omega) u) →
        (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Ef.toClosedForm
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) →
        ∀ u ∈ Ef.domain, ∀ (j : Fin d) (c : ℝ),
          Gamma.measure u {x : SpatialCoordinates d | x j = c} = 0) := by
  classical
  rcases hdata with ⟨hjoint, hcatalogues⟩
  rcases hjoint with ⟨_, _, _, _, _, _, _, _, _, hGN, hlim⟩
  rw [ae_all_iff]
  intro i
  obtain ⟨e, he, hcat⟩ := hcatalogues i
  obtain ⟨j, hj⟩ := he i le_rfl
  obtain ⟨cR, cC, respE, respF, evE, evF, root, hunit, Dcat, hDcat, fcat, trace, traceH1,
    usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, beta, t, I,
    cK, eK, lK, sRK, sGK, sHK, cRK, cGK, cHK, origin, gridRoot, gridKey, hbuf, hcats⟩ := hcat
  have : ∀ j, Countable (Dcat j) := hDcat
  have heventE : ∀ᵐ omega ∂P, omega ∈ evE :=
    ae_iff.mpr hcats.1.2.2.2.2.2.2.2.2.2.1.2.2.1
  have heventF : ∀ᵐ omega ∂P, omega ∈ evF :=
    ae_iff.mpr hcats.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  filter_upwards [hBounds, hGN, hlim, heventE, heventF] with omega hB hG hL home homf
  rw [← hj]
  constructor
  · intro Ef Gamma hEf hcore
    exact represented_limit_planes_null d hd model H Ω P NE envE ℕ root
      (z ∘ e) (r ∘ e) (fun j => hr (e j)) (fun j => Sspace (e j)) Dcat fcat
      (fun _ => ℕ) trace traceH1 usrcE srcRepE ucellE Cext beta alpha eta t {1} I ℕ
      (fun i n omega => cR i (NE n) (envE n omega)) respE
      (fun i n omega => cC i (NE n) (envE n omega)) evE cK eK lK sRK sGK sHK cRK cGK cHK
      ℕ origin gridRoot gridKey hcats.1 omega home j
      (fun n => GNE (e j) n omega) (GE (e j) omega) (hB (e j)).1
      (fun n f => (hG (e j) n f).1) (hL (e j)).1 Ef hEf hcore Gamma
  · intro Ef Gamma hEf hcore
    exact represented_limit_planes_null d hd model H Ω P NF envF ℕ root
      (z ∘ e) (r ∘ e) (fun j => hr (e j)) (fun j => Sspace (e j)) Dcat fcat
      (fun _ => ℕ) trace traceH1 usrcF srcRepF ucellF Cext beta alpha eta t {1} I ℕ
      (fun i n omega => cR i (NF n) (envF n omega)) respF
      (fun i n omega => cC i (NF n) (envF n omega)) evF cK eK lK sRK sGK sHK cRK cGK cHK
      ℕ origin gridRoot gridKey hcats.2 omega homf j
      (fun n => GNF (e j) n omega) (GF (e j) omega) (hB (e j)).2
      (fun n f => (hG (e j) n f).2) (hL (e j)).2 Ef hEf hcore Gamma

end SubdiffusiveProcess.Paper
