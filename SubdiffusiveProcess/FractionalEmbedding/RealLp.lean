module

public import SubdiffusiveProcess.FractionalEmbedding.Normalization
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open MeasureTheory Set
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.FractionalEmbedding

theorem scalarGagliardoEnergy_congr_ae {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    {f g : SpatialCoordinates d → ℝ}
    (hfg : f =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g) :
    scalarGagliardoEnergy z r hr s f = scalarGagliardoEnergy z r hr s g := by
  unfold scalarGagliardoEnergy
  apply lintegral_congr_ae
  filter_upwards [hfg] with x hx
  apply lintegral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hx, hy]

theorem scalarGagliardoEnergy_abs_le {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (f : SpatialCoordinates d → ℝ) :
    scalarGagliardoEnergy z r hr s (fun x => |f x|) ≤ scalarGagliardoEnergy z r hr s f := by
  unfold scalarGagliardoEnergy
  apply lintegral_mono
  intro x
  apply lintegral_mono
  intro y
  apply ENNReal.div_le_div_right
  apply ENNReal.ofReal_le_ofReal
  have h := abs_abs_sub_abs_le_abs_sub (f x) (f y)
  have hsq := mul_self_le_mul_self (abs_nonneg (|f x| - |f y|)) h
  simpa only [← sq, sq_abs] using hsq

theorem squaredMoment_eq_L2 {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : DomainL2 (centeredCube z r hr)) :
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((v x) ^ 2)) = ENNReal.ofReal (‖v‖ ^ 2) := by
  let μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  have hpoint (x : SpatialCoordinates d) :
      ENNReal.ofReal ((v x) ^ 2) = ‖v x‖ₑ ^ (2 : ℝ) := by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  calc
    _ = ∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂μ := by simp_rw [hpoint]; rfl
    _ = (eLpNorm v (2 : ℝ≥0∞) μ) ^ (2 : ℝ) := by
      symm
      exact eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (f := (v : SpatialCoordinates d → ℝ)) (μ := μ) (by norm_num) (Lp.aestronglyMeasurable v)
    _ = _ := by
      rw [← Lp.enorm_def v, ← ofReal_norm, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (norm_nonneg v)]

theorem memLp_of_abs_moment {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 0 < q)
    (hfinite : (∫⁻ x, ENNReal.ofReal (|f x| ^ q) ∂μ) < ⊤) :
    MemLp f (ENNReal.ofReal q) μ := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0
    ENNReal.ofReal_ne_top hf).mpr ?_
  rw [ENNReal.toReal_ofReal hq.le]
  simpa only [Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq.le] using hfinite

theorem absMoment_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hf : AEStronglyMeasurable f μ) (q : ℝ) :
    (∫ x, |f x| ^ q ∂μ) = (∫⁻ x, ENNReal.ofReal (|f x| ^ q) ∂μ).toReal := by
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (f x)) q)
    (by simpa only [Real.norm_eq_abs] using
      (hf.norm.aemeasurable.pow_const q).aestronglyMeasurable)

end SubdiffusiveProcess.FractionalEmbedding
