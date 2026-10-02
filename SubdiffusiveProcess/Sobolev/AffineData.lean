import SubdiffusiveProcess.Sobolev.MeanZero

/-!
# Affine functions in the concrete Sobolev graph

The boundary slope in the finite-volume responses of Section 3.2 is an
actual affine function on the domain. Its weak gradient is proved to be the
constant vector of slopes. Boundedness supplies its L2 membership; integration
by parts uses the compact support of the test, not of the affine function.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- The literal coordinate pairing with a prescribed affine slope. -/
def affineSlope (p : Fin d → ℝ) : SpatialCoordinates d →L[ℝ] ℝ :=
  ∑ i : Fin d, p i • ContinuousLinearMap.proj i

/-- The pairing is the ordinary sum of coordinate products. -/
theorem affineSlope_apply (p : Fin d → ℝ) (x : SpatialCoordinates d) :
    affineSlope p x = ∑ i : Fin d, p i * x i := by
  simp [affineSlope]

/-- The derivative of the affine function is its slope, including nonzero offsets. -/
theorem affine_fderiv (p : Fin d → ℝ) (c : ℝ) (x : SpatialCoordinates d) :
    fderiv ℝ (fun y => affineSlope p y + c) x = affineSlope p := by
  exact ((affineSlope p).hasFDerivAt.add_const c).fderiv

/-- Each coordinate derivative is the corresponding slope component. -/
theorem affine_fderiv_coordinate (p : Fin d → ℝ) (c : ℝ)
    (x : SpatialCoordinates d) (i : Fin d) :
    fderiv ℝ (fun y => affineSlope p y + c) x (Pi.single i 1) = p i := by
  rw [affine_fderiv, affineSlope_apply]
  simp [Pi.single_apply]

variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- Bounded domains make every affine function square integrable. -/
theorem affine_memLp (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) :
    MemLp (fun x => affineSlope p x + c) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  obtain ⟨R, hR⟩ := hΩ.exists_norm_le
  apply MemLp.of_bound ((affineSlope p).continuous.add continuous_const).aestronglyMeasurable
    (‖affineSlope p‖ * R + ‖c‖)
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact (norm_add_le _ _).trans (add_le_add
    (((affineSlope p).le_opNorm x).trans
      (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _))) le_rfl)

/-- An affine function as its actual L2 equivalence class. -/
def affineL2 (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) : DomainL2 Ω :=
  (affine_memLp hΩ p c).toLp (fun x => affineSlope p x + c)

/-- The L2 representative agrees almost everywhere with the affine formula. -/
theorem affineL2_coeFn (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) :
    (affineL2 hΩ p c : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => affineSlope p x + c :=
  MemLp.coeFn_toLp _

/-- The affine function paired with its constant coordinate gradients. -/
def affineSobolevData (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) : SobolevData Ω :=
  (affineL2 hΩ p c, fun i => domainConstantL2 (p i))

/-- The specified constant gradients really are the distributional derivatives. -/
theorem affineSobolevData_mem (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) : affineSobolevData hΩ p c ∈ weakSobolevGraph Ω := by
  rw [mem_weakSobolevGraph_iff]
  intro φ i
  let v : SpatialCoordinates d := Pi.single i 1
  let b : SpatialCoordinates d → ℝ := fun x => affineSlope p x + c
  have hb : Continuous b := (affineSlope p).continuous.add continuous_const
  have hφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (φ.contDiff.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hdb : Continuous (fun x => fderiv ℝ b x v) := by
    simpa only [b, v, affine_fderiv_coordinate] using
      (continuous_const : Continuous (fun _ : SpatialCoordinates d => p i))
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (SpatialCoordinates d))) (v := v)
    ((hφ.mul hb).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.fderiv_apply ℝ v).mul_right)
    ((φ.contDiff.continuous.mul hdb).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right)
    ((φ.contDiff.continuous.mul hb).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right)
    (φ.contDiff.differentiable (by simp)) ((affineSlope p).differentiable.add_const c)
  have hleft : (∫ x in (Ω : Set (SpatialCoordinates d)),
      φ x * (domainConstantL2 (Ω := Ω) (p i)) x) = ∫ x, φ x * fderiv ℝ b x v := by
    calc
      _ = ∫ x in (Ω : Set (SpatialCoordinates d)), φ x * fderiv ℝ b x v := by
        apply integral_congr_ae
        filter_upwards [domainConstantL2_coeFn (Ω := Ω) (p i)] with x hx
        rw [hx, show fderiv ℝ b x v = p i from affine_fderiv_coordinate p c x i]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hx (φ.tsupport_subset h))
        simp only [hz, zero_mul]
  have hright : (∫ x in (Ω : Set (SpatialCoordinates d)),
      fderiv ℝ φ x v * (affineL2 hΩ p c) x) = ∫ x, fderiv ℝ φ x v * b x := by
    calc
      _ = ∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ φ x v * b x := by
        apply integral_congr_ae
        filter_upwards [affineL2_coeFn hΩ p c] with x hx
        rw [hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hz : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ
          (fun h => hx (φ.tsupport_subset h))
        simp only [hz, ContinuousLinearMap.zero_apply, zero_mul]
  change (∫ x in (Ω : Set (SpatialCoordinates d)),
    φ x * (domainConstantL2 (Ω := Ω) (p i)) x) +
    (∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ φ x v * (affineL2 hΩ p c) x) = 0
  rw [hleft, hright, hibp, neg_add_cancel]

/-- Affine boundary data as an element of the proved weak Sobolev graph. -/
def affineSobolev (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) : weakSobolevGraph Ω :=
  ⟨affineSobolevData hΩ p c, affineSobolevData_mem hΩ p c⟩

end SubdiffusiveProcess
