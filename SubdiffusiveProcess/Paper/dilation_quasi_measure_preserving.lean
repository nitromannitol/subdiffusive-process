module

public import SubdiffusiveProcess.EllipticRegularity.CubeDilation

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem dilation_quasi_measure_preserving :
  ∀ (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1),
    MeasureTheory.Measure.QuasiMeasurePreserving (cubeDilation z z' r)
      (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  intro d z z' r hr h1
  have hmeas : Measurable (cubeDilation z z' r) :=
    (continuous_cubeDilation z z' r).measurable
  -- Step 1: the dilation is quasi-measure-preserving for Lebesgue measure on all of space,
  -- as the composite of a translation, a nonzero dilation and a translation.
  have hglob : Measure.QuasiMeasurePreserving (cubeDilation z z' r)
      (volume : Measure (SpatialCoordinates d)) volume := by
    have hsub : Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => x - z')
        volume volume := (measurePreserving_sub_right volume z').quasiMeasurePreserving
    have hsmul : Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => r • x)
        volume volume := Measure.quasiMeasurePreserving_smul volume hr.ne'
    have hadd : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => z + y)
        volume volume := (measurePreserving_add_left volume z).quasiMeasurePreserving
    have h := hadd.comp (hsmul.comp hsub)
    have hfun : (fun y : SpatialCoordinates d => z + y) ∘
        ((fun x : SpatialCoordinates d => r • x) ∘
          (fun x : SpatialCoordinates d => x - z')) = cubeDilation z z' r := by
      funext x i
      simp [cubeDilation, Function.comp]
    rwa [hfun] at h
  -- Step 2: restrict.  A null set of `volume.restrict Q_r` meets `Q_r` in a null set; its
  -- preimage meets `Q_1` inside the preimage of that intersection, because the map carries
  -- `Q_1` into `Q_r`; and Step 1 makes that preimage null.
  refine ⟨hmeas, Measure.AbsolutelyContinuous.mk fun s hsm hs => ?_⟩
  rw [Measure.map_apply hmeas hsm, Measure.restrict_apply (hmeas hsm)]
  rw [Measure.restrict_apply hsm] at hs
  refine measure_mono_null (fun x hx => ?_) (hglob.preimage_null hs)
  exact ⟨hx.1, cubeDilation_mapsTo z z' hr h1 x hx.2⟩

end SubdiffusiveProcess.Paper
