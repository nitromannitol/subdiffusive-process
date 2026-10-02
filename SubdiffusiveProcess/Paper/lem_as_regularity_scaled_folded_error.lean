import SubdiffusiveProcess.Paper.lem_as_regularity_folded_error
import SubdiffusiveProcess.Paper.in_deterministic
import SubdiffusiveProcess.Analysis.ContinuousCubeCoefficient

/-! The native error at an arbitrary integer scale of a dilated, folded
coefficient is bounded by its original physical error. This identifies the
error input of rooted iteration; it does not assert a score or stopping bound.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace Paper

/-- A physical coefficient representative gives the native error under arbitrary positive dilation. -/
theorem aux_lem_as_regularity_scaled_folded_error_chart {d : ℕ}
    (E : in_J d) (z : SpatialCoordinates d) (r mu : ℝ) (hr : 0 < r) (hmu : 0 < mu)
    (k : ℤ) (hscale : r * ((3 : ℝ) ^ k)⁻¹ = mu)
    (A : PositiveCoefficient (centeredCube z r hr)) (f : Vec d → ℝ)
    (hrep : (A.val : Vec d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (Vec d))] f)
    (data : ScalarTriadicCoeffData (fun y => f (mu • (y + 0) + z)))
    (a0 s : ℝ) (ha0 : 0 < a0) (hs : s ∈ Ioc (0 : ℝ) 1) :
    E.err z r hr A z r a0 s 2 =
      (paperHomogenizationError (originCube d k) k s
        Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0).toReal ∧
      paperHomogenizationError (originCube d k) k s
        Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0 ≠ ⊤ := by
  have hset : translateSet z (mu • openCubeSet (originCube d k)) =
      (centeredCube z r hr : Set (Vec d)) := by
    rw [show openCubeSet (originCube d k) = cube d k from rfl,
      aux_in_deterministic_core_cube_eq_ball, aux_in_deterministic_core_affine_ball hmu,
      smul_zero, zero_add]
    change Metric.ball z (mu * ((3 : ℝ) ^ k / 2)) = Metric.ball z (r / 2)
    congr 1
    rw [← hscale]
    field_simp
  have hrep' : (A.val : Vec d → ℝ) =ᵐ[
      volume.restrict (translateSet z (mu • openCubeSet (originCube d k)))] f := by
    rw [hset]
    exact hrep
  have hpull := aux_in_deterministic_core_ae_affine hmu z (openCubeSet (originCube d k)) hrep'
  apply aux_in_deterministic_core_err_scaled E z r hr k A (fun y => f (mu • y + z)) 0
    _ data a0 ha0 s hs
  filter_upwards [hpull] with y hy
  have hid : (fun i => z i + r * ((3 : ℝ) ^ k)⁻¹ * y i) = mu • y + z := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hscale]
    ring
  simpa only [add_zero, hid] using hy.symm

/-- The canonical continuous cube coefficients have the required folded almost-everywhere identity. -/
theorem aux_lem_as_regularity_scaled_folded_error_fold {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (I P : Finset (Fin d))
    (A : PositiveCoefficient (centeredCube z r hr)) (f : Vec d → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (hrep : (A.val : Vec d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (Vec d))] f) :
    ((continuousCubeCoefficient z r hr (fun x => f (coordinateFold z I P x))
      (hf.comp (coordinateFold_continuous z I P)) (fun x => hpos _)).val : Vec d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (Vec d))] fun x => A.val (coordinateFold z I P x) := by
  have hmaps : MapsTo (coordinateFold z I P) (centeredCube z r hr : Set (Vec d))
      (centeredCube z r hr : Set (Vec d)) := by
    intro x hx
    change dist (coordinateFold z I P x) z < r / 2
    rw [coordinateFold_dist_center]
    exact hx
  have hcomp := ((aux_lem_repair_err_fold_carrier_bridge_fold_qmp z I P).restrict hmaps).ae_eq_comp hrep
  exact (continuousCubeCoefficient_ae z r hr _ _ _).trans hcomp.symm

/-- Dilating the folded native coefficient preserves the original reference and costs only the fold factor. -/
theorem lem_as_regularity_scaled_folded_error (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (z : SpatialCoordinates d) (r mu : ℝ) (hr : 0 < r) (hmu : 0 < mu)
    (k : ℤ) (hscale : r * ((3 : ℝ) ^ k)⁻¹ = mu) (I P : Finset (Fin d))
    (A : PositiveCoefficient (centeredCube z r hr)) (f : Vec d → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (hrep : (A.val : Vec d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (Vec d))] f)
    (data : ScalarTriadicCoeffData (fun y => f (coordinateFold z I P (mu • (y + 0) + z))))
    (a0 s : ℝ) (ha0 : 0 < a0) (hs : 0 < s) (hs1 : s < 1 / 2) :
    paperHomogenizationError (originCube d k) k s
      Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal
        ((1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s) - 1)) * E.err z r hr A z r a0 s 2) := by
  let Af := continuousCubeCoefficient z r hr (fun x => f (coordinateFold z I P x))
    (hf.comp (coordinateFold_continuous z I P)) (fun x => hpos _)
  obtain ⟨heq, hfin⟩ := aux_lem_as_regularity_scaled_folded_error_chart E z r mu hr hmu k hscale
    Af (fun x => f (coordinateFold z I P x)) (continuousCubeCoefficient_ae z r hr _ _ _)
    data a0 s ha0 ⟨hs, by linarith only [hs1]⟩
  rw [← ENNReal.ofReal_toReal hfin, ← heq]
  apply ENNReal.ofReal_le_ofReal
  exact lem_as_regularity_folded_error d hd E z r r hr hr le_rfl I P A Af f hf hpos hrep
    (aux_lem_as_regularity_scaled_folded_error_fold z r hr I P A f hf hpos hrep) s a0 hs hs1 ha0

end Paper
