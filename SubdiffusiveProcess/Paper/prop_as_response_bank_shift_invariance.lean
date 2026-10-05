module

public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/--
Docstring tick list: `model.G1.stationary` is the manuscript Assumption
`a.g1`; `chaosSampleLaw model` is the product law from the common-scale
coupling `in_common_scale_coupling`; `Shift` translates the whole bilateral
field and reanchors the infrared coordinate at the unit origin. The equality
of the shifted law with the original law is concluded here, not carried as a
hypothesis. No simultaneous uncountable event is asserted.
The statement is only the deterministic-translation law identity.
-/
theorem prop_as_response_bank_shift_invariance
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∀ w : SpatialCoordinates d,
      Measure.map
          (fun omega : BilateralField d => fun j : ℤ =>
            (omega j).comp
              (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
                C(SpatialCoordinates d, SpatialCoordinates d)))
          (chaosSampleLaw model).toMeasure =
          (chaosSampleLaw model).toMeasure := by
  intro w
  let T : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩
  let translate : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => x + w, continuous_id.add continuous_const⟩
  have hroot : ∀ z : SpatialCoordinates d, MeasurePreserving
      (fun f : C(SpatialCoordinates d, ℝ) =>
        f.comp (⟨fun x => x + z, continuous_id.add continuous_const⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d)))
      (chaosRootFieldLaw model).toMeasure (chaosRootFieldLaw model).toMeasure := by
    intro z
    simpa [chaosRootFieldLaw] using
      (gmc_zero_field_law_stationary model z)
  have hroot' : MeasurePreserving
      (fun f : C(SpatialCoordinates d, ℝ) => f.comp translate)
      (chaosRootFieldLaw model).toMeasure (chaosRootFieldLaw model).toMeasure := by
    simpa [translate] using hroot w
  have hlayer : ∀ j : ℤ, MeasurePreserving
      (fun f : C(SpatialCoordinates d, ℝ) => f.comp T)
      (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure
      (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure := by
    intro j
    let a : C(SpatialCoordinates d, SpatialCoordinates d) :=
      ⟨fun x => (3 : ℝ) ^ (-j) • x,
        by simpa using! (continuous_const : Continuous (fun _ : SpatialCoordinates d => (3 : ℝ) ^ (-j))).smul continuous_id⟩
    let z : SpatialCoordinates d := (3 : ℝ) ^ (-j) • w
    let translateZ : C(SpatialCoordinates d, SpatialCoordinates d) :=
      ⟨fun x => x + z, continuous_id.add continuous_const⟩
    have hz : MeasurePreserving
        (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ)
        (chaosRootFieldLaw model).toMeasure (chaosRootFieldLaw model).toMeasure := by
      simpa [translateZ] using hroot z
    have hcomm :
        (fun f : C(SpatialCoordinates d, ℝ) => f.comp T) ∘
            (layerScaling d j) =
          (layerScaling d j) ∘
            (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ) := by
      funext f
      ext x
      dsimp [ContinuousMap.compRightContinuousMap, layerScaling,
        ContinuousMap.comp, T, translateZ, z]
      congr 1
      ext i
      simp [cubeDilation_apply, sub_zero]
      ring
    refine ⟨by fun_prop, ?_⟩
    change Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp T)
        (Measure.map (layerScaling d j)
          (chaosRootFieldLaw model).toMeasure) =
      Measure.map (layerScaling d j) (chaosRootFieldLaw model).toMeasure
    calc
      Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp T)
          (Measure.map (layerScaling d j)
            (chaosRootFieldLaw model).toMeasure) =
          Measure.map ((fun f : C(SpatialCoordinates d, ℝ) => f.comp T) ∘
            layerScaling d j) (chaosRootFieldLaw model).toMeasure :=
        Measure.map_map (by fun_prop) (by fun_prop)
      _ = Measure.map ((layerScaling d j) ∘
            (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ))
          (chaosRootFieldLaw model).toMeasure := by rw [hcomm]
      _ = Measure.map (layerScaling d j)
          (Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ)
            (chaosRootFieldLaw model).toMeasure) := by
        exact (Measure.map_map (layerScaling d j).continuous.measurable
          (by fun_prop)).symm
      _ = Measure.map (layerScaling d j)
          (chaosRootFieldLaw model).toMeasure := by rw [hz.map_eq]
  change Measure.map
      (fun omega : BilateralField d => fun j : ℤ => (omega j).comp T)
      (Measure.infinitePi (fun j : ℤ =>
        (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure)) =
    Measure.infinitePi (fun j : ℤ =>
      (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure)
  have hprod := Measure.infinitePi_map_pi
    (μ := fun j : ℤ => (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure)
    (f := fun _ : ℤ => fun f : C(SpatialCoordinates d, ℝ) => f.comp T)
    (fun _ => by fun_prop)
  rw [hprod]
  congr 1
  funext j
  exact (hlayer j).map_eq

end SubdiffusiveProcess.Paper
