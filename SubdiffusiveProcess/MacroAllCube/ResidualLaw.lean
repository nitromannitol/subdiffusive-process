module

public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.BilateralField
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

open MeasureTheory
open SubdiffusiveProcess

noncomputable section

namespace SubdiffusiveProcess.MacroAllCube

variable {d : ℕ}

def spatialDilation (d : ℕ) (r : ℝ) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨fun x => r • x, by
    simpa only [Pi.smul_apply, Function.id_def] using!
      (continuous_const.smul continuous_id :
        Continuous ((fun _ : SpatialCoordinates d => r) • (id : SpatialCoordinates d → SpatialCoordinates d)))⟩

def dilateField (d : ℕ) (r : ℝ) :
    C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
  ContinuousMap.compRightContinuousMap ℝ (spatialDilation d r)

def residualShift (r : ℝ) (k : ℕ) (om : BilateralField d) : BilateralField d :=
  fun j => dilateField d r (om (j - (k : ℤ)))

theorem residualShift_apply (r : ℝ) (k : ℕ) (om : BilateralField d)
    (j : ℤ) (x : SpatialCoordinates d) :
    residualShift r k om j x = om (j - (k : ℤ)) (r • x) := rfl

/-- Every side at most one is a negative integer triadic scale times a
bounded dilation factor in `(1,3]`. -/
theorem exists_residual_scale {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ k : ℕ, 1 < r * (3 : ℝ) ^ k ∧ r * (3 : ℝ) ^ k ≤ 3 := by
  obtain ⟨n, hn, hnext⟩ := exists_nat_pow_near
    ((one_le_inv₀ hr).2 hr1) (by norm_num : (1 : ℝ) < 3)
  refine ⟨n + 1, ?_, ?_⟩
  · have h := mul_lt_mul_of_pos_left hnext hr
    simpa only [mul_inv_cancel₀ hr.ne'] using h
  · have h := mul_le_mul_of_nonneg_left hn hr.le
    rw [mul_inv_cancel₀ hr.ne'] at h
    rw [pow_succ]
    nlinarith

theorem dilation_comp_layerScaling (r : ℝ) (k : ℕ) (j : ℤ) :
    (dilateField d r) ∘ layerScaling d (j - (k : ℤ)) =
      (layerScaling d j) ∘ dilateField d (r * (3 : ℝ) ^ k) := by
  funext f
  ext x
  simp only [Function.comp_apply, dilateField, layerScaling,
    ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
    spatialDilation, ContinuousMap.coe_mk]
  congr 1
  rw [smul_smul, smul_smul]
  congr 1
  rw [show -(j - (k : ℤ)) = -j + (k : ℤ) by ring,
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  ring

section Measure

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

def residualRootLaw (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ))
    (s : ℝ) : ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
  ν.map (dilateField d s)

theorem map_scaledLayerLaw_dilation (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ))
    (r : ℝ) (k : ℕ) (j : ℤ) :
    (scaledLayerLaw d ν (j - (k : ℤ)) : Measure C(SpatialCoordinates d, ℝ)).map
        (dilateField d r) =
      (scaledLayerLaw d (residualRootLaw ν (r * (3 : ℝ) ^ k)) j :
        Measure C(SpatialCoordinates d, ℝ)) := by
  simp only [scaledLayerLaw, residualRootLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (dilateField d r).continuous.measurable
      (layerScaling d _).continuous.measurable,
    Measure.map_map (layerScaling d j).continuous.measurable
      (dilateField d _).continuous.measurable,
    dilation_comp_layerScaling]

theorem measurePreserving_reindex_sub {X : Type*} [MeasurableSpace X]
    (laws : ℤ → Measure X) [∀ n, IsProbabilityMeasure (laws n)] (k : ℤ) :
    MeasurePreserving (fun om : ℤ → X => fun j : ℤ => om (j - k))
      (Measure.infinitePi laws) (Measure.infinitePi (fun j : ℤ => laws (j - k))) := by
  let e : ℤ ≃ ℤ := Equiv.addRight k
  have he : (MeasurableEquiv.piCongrLeft (fun _ : ℤ => X) e : (ℤ → X) → (ℤ → X)) =
      (fun om : ℤ → X => fun j : ℤ => om (j - k)) := by
    funext om j
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
      e, cast_eq]
    rfl
  have hmap := Measure.infinitePi_map_piCongrLeft
    (μ := fun j : ℤ => laws (j - k)) e
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact (MeasurableEquiv.piCongrLeft (fun _ : ℤ => X) e).measurable
  · rw [← he]
    simpa only [e, Equiv.coe_addRight, add_sub_cancel_right] using hmap

/-- Exact law transport for the arbitrary real side. The codomain root law
is the original seed dilated by the bounded residual factor, not the old
seed law itself. -/
theorem measurePreserving_residualShift
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) (r : ℝ) (k : ℕ) :
    MeasurePreserving (residualShift (d := d) r k)
      (commonScaleLaw d ν).toMeasure
      (commonScaleLaw d (residualRootLaw ν (r * (3 : ℝ) ^ k))).toMeasure := by
  change MeasurePreserving _ (Measure.infinitePi _) (Measure.infinitePi _)
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  have hre := measurePreserving_reindex_sub laws (k : ℤ)
  have hpi : MeasurePreserving
      (fun (om : BilateralField d) (j : ℤ) => dilateField d r (om j))
      (Measure.infinitePi (fun j => laws (j - (k : ℤ))))
      (Measure.infinitePi (fun j =>
        (scaledLayerLaw d (residualRootLaw ν (r * (3 : ℝ) ^ k)) j).toMeasure)) := by
    refine ⟨Measurable.of_eval fun j =>
      (dilateField d r).continuous.measurable.comp (measurable_pi_apply j), ?_⟩
    rw [Measure.infinitePi_map_pi _ (fun _ => (dilateField d r).continuous.measurable)]
    congr 1
    funext j
    exact map_scaledLayerLaw_dilation ν r k j
  exact hpi.comp hre

end Measure

end SubdiffusiveProcess.MacroAllCube


