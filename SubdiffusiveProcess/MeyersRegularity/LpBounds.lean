module

public import SubdiffusiveProcess.MeyersRegularity.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

/-! Finite-measure norm bounds used in the interior iteration. -/

open MeasureTheory Filter Set Homogenization
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]

/-- The outer balls carry finite Lebesgue measure. -/
theorem unitBall_volume_lt_top (d : ℕ) {r : ℝ} (hr : 0 < r) :
    volume (unitBall d r) < ⊤ := by
  exact ((Metric.isBounded_ball (x := (0 : Vec d)) (r := r)).subset
    (Meyers.eBall_subset_ball 0 hr)).measure_lt_top

/-- Downgrade a finite exponent to two with its explicit volume factor. -/
theorem two_norm_le_lp_norm {μ : Measure α} [IsFiniteMeasure μ] {f : α → E} {p : ℝ}
    (hp : 2 ≤ p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm f 2 μ).toReal ≤ (eLpNorm f (ENNReal.ofReal p) μ).toReal *
      (μ univ ^ (1/2 - 1/p)).toReal := by
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hp)
  have hexp : 0 ≤ 1/2 - 1/p := by
    have hp0 : 0 < p := by linarith
    have hi := (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp)
    linarith
  have hnorm := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp2 hf.aestronglyMeasurable
  have hm : μ univ ^ (1/2 - 1/p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ univ)
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] at hnorm
  have htop := ENNReal.mul_ne_top hf.eLpNorm_ne_top hm
  have ht := ENNReal.toReal_mono htop hnorm
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ p),
    ENNReal.toReal_ofNat] using ht

/-- The real squared L2 norm is the squared-norm integral. -/
theorem two_norm_sq_eq_integral {μ : Measure α} {f : α → E}
    [MeasurableSpace E] [BorelSpace E] (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal^2 = ∫ x, ‖f x‖^2 ∂μ := by
  have hnorm := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hnonneg : 0 ≤ ∫ x, ‖f x‖^(2 : ℝ) ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [hnorm]
  norm_num only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
  congr 1 with x
  rw [Real.rpow_two]

/-- Squared energy of a zero extension is the energy on the original set. -/
theorem indicator_energy_eq {μ : Measure α} {U : Set α} {f : α → E}
    [MeasurableSpace E] [BorelSpace E] (hU : MeasurableSet U) (hf : MemLp f 2 (μ.restrict U)) :
    (∫ x, ‖U.indicator f x‖^2 ∂μ) = (eLpNorm f 2 (μ.restrict U)).toReal^2 := by
  have hfi : MemLp (U.indicator f) 2 μ :=
    (MeasureTheory.memLp_indicator_iff_restrict hU).mpr hf
  rw [← two_norm_sq_eq_integral hfi, eLpNorm_indicator_eq_eLpNorm_restrict hU]

/-- Pass from a Hilbert-valued local L2 witness to the raw-vector witness. -/
theorem memVectorL2_of_hilbert_memLp {d : ℕ} {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (volume.restrict U)) :
    MemVectorL2 U F := by
  let T : HilbertVec d →L[ℝ] Vec d :=
    (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap
  simpa [MemVectorL2, volumeMeasureOn, hilbertifyVecField, Function.comp_def, T] using
    T.comp_memLp' hF

/-- A pointwise coefficient error gives the expected L2 triangle estimate. -/
theorem two_norm_le_of_norm_bound {μ : Measure α} {f g H : α → E} {δ : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hH : MemLp H 2 μ) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ δ*‖f x‖ + ‖H x‖) :
    (eLpNorm g 2 μ).toReal ≤ δ*(eLpNorm f 2 μ).toReal + (eLpNorm H 2 μ).toReal := by
  have hmono := eLpNorm_mono_ae_real (p := (2 : ℝ≥0∞)) hg.aestronglyMeasurable hbound
  change eLpNorm g 2 μ ≤ eLpNorm
    ((δ • (fun x => ‖f x‖)) + (fun x => ‖H x‖)) 2 μ at hmono
  have htriangle := eLpNorm_add_le
    (f := δ • (fun x => ‖f x‖)) (g := fun x => ‖H x‖) (μ := μ)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hh := hmono.trans htriangle
  simp only [eLpNorm_const_smul, eLpNorm_norm _ hf.aestronglyMeasurable,
    eLpNorm_norm _ hH.aestronglyMeasurable, ← ofReal_norm,
    Real.norm_eq_abs, abs_of_nonneg hδ] at hh
  have ht := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by finiteness) hf.eLpNorm_ne_top, hH.eLpNorm_ne_top⟩) hh
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by finiteness) hf.eLpNorm_ne_top) hH.eLpNorm_ne_top,
    ENNReal.toReal_mul] at ht
  simpa only [ENNReal.toReal_ofReal hδ] using ht

end SubdiffusiveProcess.MeyersRegularity
