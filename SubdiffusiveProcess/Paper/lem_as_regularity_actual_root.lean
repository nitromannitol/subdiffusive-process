module

public import SubdiffusiveProcess.Paper.lem_as_regularity_physical_root
public import SubdiffusiveProcess.Paper.lem_as_regularity_actual_native_error
public import SubdiffusiveProcess.Analysis.DilatedCubeCoefficient
public import SubdiffusiveProcess.Geometry.DilatedFold

@[expose] public section

/-! The reflected root of an actual cutoff Neumann solution has the exact
native coefficient and energy scaling. This is a carrier construction and
contains no regularity estimate or probabilistic bound.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The unit coefficient has a positive continuous dilation with the exact pullback identity. -/
theorem aux_lem_as_regularity_actual_root_dilate {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (l : ℝ) (hl : 0 < l) :
    ∃ A : PositiveCoefficient (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl),
      ((A.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl : Set (SpatialCoordinates d))]
          fun x => cutoffCoefficient M H omega N (l⁻¹ • x)) ∧
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos).val y =
          A.val (l • y)) := by
  have hr := cutoffPositiveCoefficient_representative M H omega N (fun _ => (1 / 2 : ℝ)) one_pos
  exact exists_dilatedCubeCoefficient_of_side (fun _ : Fin d => (1 / 2 : ℝ))
    1 l l one_pos hl hl (mul_one l).symm (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos)
    (cutoffCoefficient M H omega N) hr.1 hr.2.1 hr.2.2.2

/-- A folded native coefficient representative has the required centered chart. -/
theorem aux_lem_as_regularity_actual_root_chart {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N m : ℕ) (w : SpatialCoordinates d) (I J : Finset (Fin d))
    (hR : (0 : ℝ) < 3 ^ m)
    (fc : PositiveCoefficient (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR))
    (hfc : (fc.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
        fun x => cutoffCoefficient M H omega N
          (((3 : ℝ) ^ N)⁻¹ • coordinateFold ((3 : ℝ) ^ N • w) I J x)) :
    ∀ᵐ y ∂volume.restrict (openCubeSet (originCube d (m : ℤ))),
      cutoffCoefficient M H omega N (coordinateFold w I J ((3 : ℝ) ^ (-(N : ℤ)) • y + w)) =
        fc.val (fun i => ((3 : ℝ) ^ N • w) i + y i) := by
  let coeff : SpatialCoordinates d → ℝ := fc.val
  change coeff =ᵐ[volume.restrict (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR :
    Set (SpatialCoordinates d))] _ at hfc
  rw [centeredCube_eq_translateSet_cube m _ hR] at hfc
  have hh := aux_in_deterministic_core_ae_affine (R := 1) zero_lt_one
    ((3 : ℝ) ^ N • w) (cube d (m : ℤ)) (by simpa only [one_smul] using! hfc)
  filter_upwards [hh] with y hy
  rw [one_smul, inv_smul_coordinateFold_add _ (by positivity)] at hy
  have hscale : ((3 : ℝ) ^ N)⁻¹ = (3 : ℝ) ^ (-(N : ℤ)) := by rw [zpow_neg, zpow_natCast]
  rw [hscale] at hy
  have hid : (fun i => ((3 : ℝ) ^ N • w) i + y i) = y + (3 : ℝ) ^ N • w := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [hid]
  exact hy.symm

/-- An actual cutoff Neumann solution supplies the exact reflected native root. -/
theorem lem_as_regularity_actual_root {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N m : ℕ) (hR : (0 : ℝ) < 3 ^ m)
    (f : SpatialCoordinates d → ℝ) (hfm : Measurable f) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ x, |f x| ≤ Kf)
    (hf0 : (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x) = 0)
    (u : meanZeroSobolevGraph (unitNeumannCube d))
    (hu : SolvesNeumann (cutoffPositiveCoefficient M H omega N
      (fun _ => (1 / 2 : ℝ)) one_pos) f u)
    (y : SpatialCoordinates d) (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (I : Finset (Fin d)) (Lstar Rk : ℝ) (hLstar : 10 ≤ Lstar) (hRk : 0 < Rk) (hRk3 : 3 * Rk < 1)
    (hI : ∀ i, i ∉ I → 4 * Lstar * Rk ≤ min (y i) (1 - y i))
    (hscale : (3 : ℝ) ^ m / 2 = (3 : ℝ) ^ N * (3 * Rk)) :
    ∃ (fc : PositiveCoefficient (centeredCube
        ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m) hR))
      (ut : weakSobolevGraph (centeredCube
        ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m) hR)),
      (∀ᵐ x ∂volume.restrict (openCubeSet (originCube d (m : ℤ))),
        cutoffCoefficient M H omega N
          (coordinateFold (aux_rem_resolved_meshes_center y I) I (aux_rem_resolved_meshes_faceSet y I)
            ((3 : ℝ) ^ (-(N : ℤ)) • x + aux_rem_resolved_meshes_center y I)) =
          fc.val (fun i => ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) i + x i)) ∧
      (∀ φ : killedSobolevGraph (centeredCube
          ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m) hR),
        sobolevCoefficientForm fc (ut : SobolevData _) (φ : SobolevData _) =
          ∫ x in (centeredCube ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I)
              ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)),
            (((3 : ℝ) ^ N)⁻¹ * f (((3 : ℝ) ^ N)⁻¹ • coordinateFold
              ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) I
                (aux_rem_resolved_meshes_faceSet y I) x)) * (φ : SobolevData
                  (centeredCube ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m) hR)).1 x) ∧
      (∀ (r : ℝ) (hr : 0 < r), r ≤ (3 : ℝ) ^ m →
        localGradientEnergy fc (centeredCube ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I)
            r hr).isOpen.measurableSet (sobolevGradient (ut : SobolevData _)) =
          2 ^ I.card * (((3 : ℝ) ^ N) ^ d * aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (r / (2 * (3 : ℝ) ^ N))))) := by
  obtain ⟨A, hA, ha⟩ := aux_lem_as_regularity_actual_root_dilate M H omega N
    ((3 : ℝ) ^ N) (by positivity)
  have ha' : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos).val y =
        1 * A.val ((3 : ℝ) ^ N • y) := by simpa only [one_mul] using ha
  obtain ⟨fc, ut, hfc, hut, hE⟩ := lem_as_regularity_physical_root ((3 : ℝ) ^ N)
    (by positivity) 1 zero_lt_one _ A (fun x => cutoffCoefficient M H omega N (((3 : ℝ) ^ N)⁻¹ • x))
    hA ha' f hfm Kf hKf hfb hf0 u hu y hy I Lstar Rk hLstar hRk hRk3 hI
    ((3 : ℝ) ^ m) hR hscale
  refine ⟨fc, ut, aux_lem_as_regularity_actual_root_chart M H omega N m _ I _ hR fc hfc, ?_, ?_⟩
  · simpa only [one_mul] using hut
  · simpa only [inv_one, mul_one] using hE

end SubdiffusiveProcess.Paper
