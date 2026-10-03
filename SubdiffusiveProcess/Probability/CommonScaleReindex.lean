module

public import SubdiffusiveProcess.Main.CommonScaleLaw

@[expose] public section

open MeasureTheory
noncomputable section
namespace SubdiffusiveProcess

/-- Reversing the indices of the approved common-scale field gives exactly
the product convention used by the infrared-tail estimates. -/
theorem measurePreserving_neg_reindex_commonScaleLaw
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
    let scale : ℤ → C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
      fun j => ContinuousMap.compRightContinuousMap ℝ
        (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ j • x,
          by
            exact (continuous_const :
              Continuous (fun _ : SpatialCoordinates d => (3 : ℝ) ^ j)).smul
              (continuous_id : Continuous (fun x : SpatialCoordinates d => x))⟩ : C(SpatialCoordinates d, SpatialCoordinates d))
    let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
      fun j => (ν.map (scale j)).toMeasure
    MeasurePreserving (fun ω : ℤ → C(SpatialCoordinates d, ℝ) => fun j => ω (-j))
      (commonScaleLaw d ν).toMeasure (Measure.infinitePi laws) := by
  intro scale laws
  refine ⟨Measurable.of_eval (fun j : ℤ => measurable_pi_apply (-j)), ?_⟩
  have h := Measure.infinitePi_map_piCongrLeft laws (Equiv.neg ℤ)
  have he : (MeasurableEquiv.piCongrLeft
      (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) (Equiv.neg ℤ) :
        (ℤ → C(SpatialCoordinates d, ℝ)) → (ℤ → C(SpatialCoordinates d, ℝ))) =
      (fun ω j => ω (-j)) := by
    funext ω j
    simpa using (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ℤ => C(SpatialCoordinates d, ℝ)) (Equiv.neg ℤ) ω (-j))
  rw [he] at h
  exact h

end SubdiffusiveProcess
