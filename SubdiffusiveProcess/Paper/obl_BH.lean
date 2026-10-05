module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import SubdiffusiveProcess.Paper.obl_BH_smooth_null_cutoffs
public import SubdiffusiveProcess.Paper.obl_BH_cutoff_weak_form
public import SubdiffusiveProcess.Paper.obl_BH_compact_preimage_nullity
public import SubdiffusiveProcess.Paper.obl_BH_lipschitz_smooth_approx
public import SubdiffusiveProcess.Paper.obl_BH_energy_measure_convergence
public import SubdiffusiveProcess.Paper.obl_BH_quasi_continuous_representative
public import SubdiffusiveProcess.Paper.prop_killed_inverse

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- The image of a finite energy measure under a measurable representative that kills the
preimage of every **compact** Lebesgue-null set is absolutely continuous.  Inner regularity
of the finite Borel image measure on `ℝ` upgrades the compact case to every measurable set,
and `toMeasurable` upgrades it to every set. -/
theorem aux_obl_BH_map_absolutelyContinuous
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hv : v ∈ E.toClosedForm.domain)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    (hK : ∀ K : Set ℝ, IsCompact K → volume K = 0 → Gamma.measure v (f ⁻¹' K) = 0) :
    Measure.map f (Gamma.measure v) ≪ volume := by
  have hfin : IsFiniteMeasure (Measure.map f (Gamma.measure v)) := by
    constructor
    rw [Measure.map_apply hf MeasurableSet.univ]
    exact Gamma.measure_lt_top hv _
  intro s hs
  have hs'meas : MeasurableSet (toMeasurable volume s) := measurableSet_toMeasurable _ _
  have hs'null : volume (toMeasurable volume s) = 0 := by
    rw [measure_toMeasurable]
    exact hs
  have hzero : Measure.map f (Gamma.measure v) (toMeasurable volume s) = 0 := by
    by_contra hne
    have hpos : 0 < Measure.map f (Gamma.measure v) (toMeasurable volume s) :=
      pos_iff_ne_zero.mpr hne
    obtain ⟨K, hKs, ⟨hKc, _⟩, hKpos⟩ :=
      innerRegular_isCompact_isClosed_measurableSet_of_finite
        (Measure.map f (Gamma.measure v)) hs'meas 0 hpos
    have hKnull : volume K = 0 := le_antisymm (hs'null ▸ measure_mono hKs) (zero_le)
    have hKzero : Measure.map f (Gamma.measure v) K = 0 := by
      rw [Measure.map_apply hf hKc.measurableSet]
      exact hK K hKc hKnull
    rw [hKzero] at hKpos
    exact lt_irrefl _ hKpos
  exact le_antisymm (hzero ▸ measure_mono (subset_toMeasurable volume s)) (zero_le)

/-- Absolute continuity of the image measure kills the preimage of every Lebesgue-null set,
measurable or not. -/
theorem aux_obl_BH_preimage_null
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    (habs : Measure.map f (Gamma.measure v) ≪ volume)
    (N : Set ℝ) (hN : volume N = 0) :
    Gamma.measure v (f ⁻¹' N) = 0 := by
  have hN'meas : MeasurableSet (toMeasurable volume N) := measurableSet_toMeasurable _ _
  have hN'null : volume (toMeasurable volume N) = 0 := by
    rw [measure_toMeasurable]
    exact hN
  have hmap : Gamma.measure v (f ⁻¹' toMeasurable volume N) = 0 := by
    rw [← Measure.map_apply hf hN'meas]
    exact habs hN'null
  refine le_antisymm ?_ (zero_le)
  exact hmap ▸ measure_mono (preimage_mono (subset_toMeasurable volume N))



theorem obl_BH
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (_halg : _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra E.toClosedForm)
    (_hnc : _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions E)
    (hqc : obl_BH_quasi_continuous_representative E Gamma) :
    ∃ rep :
        ∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))),
          v ∈ E.toClosedForm.domain → SpatialCoordinates d → ℝ,
      (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
          (hv : v ∈ E.toClosedForm.domain),
        Measurable (rep v hv)) ∧
      (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
          (hv : v ∈ E.toClosedForm.domain),
        (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] rep v hv)) ∧
      (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
          (hv : v ∈ E.toClosedForm.domain),
        Measure.map (rep v hv) (Gamma.measure v) ≪ volume) ∧
      (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
          (hv : v ∈ E.toClosedForm.domain),
        ∀ N : Set ℝ, volume N = 0 →
          Gamma.measure v ((rep v hv) ⁻¹' N) = 0) ∧
      (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
          (hv : v ∈ E.toClosedForm.domain),
        ∀ T : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K T) → T 0 = 0 →
        ∀ Tderiv : ℝ → ℝ, Measurable Tderiv →
          (∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) →
          ∀ (w : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
            (_hw : w ∈ E.toClosedForm.domain),
            (⇑w =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
              (fun x => T (rep v hv x))) →
            ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
              ((Gamma.measure w B).toReal =
                ∫ x in B, (Tderiv (rep v hv x)) ^ 2 ∂(Gamma.measure v))) := by
  obtain ⟨rep, hmeas, hae, hcompact, hchain⟩ := hqc
  have habs : ∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
      (hv : v ∈ E.toClosedForm.domain),
      Measure.map (rep v hv) (Gamma.measure v) ≪ volume := fun v hv =>
    aux_obl_BH_map_absolutelyContinuous E Gamma v hv (rep v hv) (hmeas v hv)
      (hcompact v hv)
  exact ⟨rep, hmeas, hae, habs, fun v hv N hN =>
    aux_obl_BH_preimage_null E Gamma v (rep v hv) (hmeas v hv) (habs v hv) N hN,
    hchain⟩

end SubdiffusiveProcess.Paper
