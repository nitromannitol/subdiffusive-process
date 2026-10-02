import SubdiffusiveProcess.MeyersRegularity.LayerCake

/-! Interior Meyers regularity: TailIntegration. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

open CubeCalderonZygmund

variable {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem clipped_tail_set_eq {f : α → E} {a T t : ℝ} (ha : 0 < a) (hcut : a*t < T) :
    {x | t < min ‖f x‖ T / a} = {x | a*t < ‖f x‖} := by
  ext x
  simp only [mem_setOf_eq, lt_div_iff₀ ha, lt_min_iff, mul_comm t a,
    and_iff_left hcut]

theorem truncatedMoment_le_of_tail {μ ν : Measure α} {f : α → E} {g : α → F}
    {p M eps lambda0 T : ℝ} {κ : ℝ≥0∞}
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hμν : μ ≤ ν) (hp : 2 < p) (hM : 1 ≤ M) (heps : 0 < eps)
    (heps1 : eps ≤ 1) (hlambda0 : 0 < lambda0) (hT : 0 ≤ T)
    (htail : ∀ t : ℝ, lambda0 ≤ t →
      sqWeightedMeasure f μ {x | M*t < ‖f x‖} ≤ κ *
        (sqWeightedMeasure f ν {x | t/2 < ‖f x‖} + ENNReal.ofReal (eps⁻¹^2) *
          sqWeightedMeasure g ν {x | eps*t/2 < ‖g x‖})) :
    truncatedMoment μ f p T ≤
      ENNReal.ofReal ((M*lambda0)^(p-2)) * sqWeightedMeasure f μ univ +
        ENNReal.ofReal ((2*M)^(p-2)) * κ * truncatedMoment ν f p T +
        ENNReal.ofReal ((2*M/eps)^(p-2) * eps⁻¹^2) * κ *
          truncatedMoment ν g p T := by
  have hMpos : 0 < M := by linarith
  have hepshalf : 0 < eps/2 := by positivity
  let μf := sqWeightedMeasure f μ
  let νf := sqWeightedMeasure f ν
  let νg := sqWeightedMeasure g ν
  let u : α → ℝ := fun x => min ‖f x‖ T / M
  let v : α → ℝ := fun x => min ‖f x‖ T / (1/2)
  let w : α → ℝ := fun x => min ‖g x‖ T / (eps/2)
  have hu : AEMeasurable u μf :=
    (((hf.mono_measure hμν).norm.aemeasurable.min aemeasurable_const).div_const M).mono'
      (withDensity_absolutelyContinuous μ _)
  have hv : AEMeasurable v νf :=
    ((hf.norm.aemeasurable.min aemeasurable_const).div_const (1/2)).mono'
      (withDensity_absolutelyContinuous ν _)
  have hw : AEMeasurable w νg :=
    ((hg.norm.aemeasurable.min aemeasurable_const).div_const (eps/2)).mono'
      (withDensity_absolutelyContinuous ν _)
  have htail' : ∀ t : ℝ, 0 < t → μf {x | t < u x} ≤
      μf {x | t < lambda0} + κ * (νf {x | t < v x} +
        ENNReal.ofReal (eps⁻¹^2) * νg {x | t < w x}) := by
    intro t ht
    by_cases hlo : t < lambda0
    · have hset : {x : α | t < lambda0} = univ := by ext x; simp [hlo]
      rw [hset]
      exact (measure_mono (subset_univ _)).trans (le_add_right le_rfl)
    · have hl : lambda0 ≤ t := le_of_not_gt hlo
      by_cases hcut : M*t < T
      · have hfcut : (1/2 : ℝ)*t < T := by nlinarith
        have hgcut : (eps/2)*t < T := by nlinarith
        have hfst : {x | (1/2 : ℝ)*t < ‖f x‖} = {x | t/2 < ‖f x‖} := by
          have hn : (1/2 : ℝ)*t = t/2 := by ring
          simp only [hn]
        have hgst : {x | (eps/2)*t < ‖g x‖} = {x | eps*t/2 < ‖g x‖} := by
          have hn : (eps/2)*t = eps*t/2 := by ring
          simp only [hn]
        dsimp only [u, v, w]
        rw [clipped_tail_set_eq hMpos hcut,
          clipped_tail_set_eq (by norm_num : (0 : ℝ) < 1/2) hfcut,
          clipped_tail_set_eq hepshalf hgcut, hfst, hgst]
        exact (htail t hl).trans (le_add_left le_rfl)
      · have hset : {x | t < u x} = ∅ := by
          ext x
          simp only [u, mem_setOf_eq, mem_empty_iff_false, iff_false]
          rw [lt_div_iff₀ hMpos]
          exact not_lt_of_ge ((min_le_right _ _).trans (by nlinarith : T ≤ t*M))
        rw [hset, measure_empty]
        exact bot_le
  have hh := rpow_moment_le_of_tail hu hv hw
    (ae_of_all _ (fun x => div_nonneg (le_min (norm_nonneg _) hT) hMpos.le))
    (ae_of_all _ (fun x => div_nonneg (le_min (norm_nonneg _) hT) (by norm_num)))
    (ae_of_all _ (fun x => div_nonneg (le_min (norm_nonneg _) hT) hepshalf.le))
    (by linarith : 0 < p-2) hlambda0.le htail'
  change (∫⁻ x, ENNReal.ofReal ((min ‖f x‖ T/M)^(p-2)) ∂μf) ≤
    μf univ * ENNReal.ofReal (lambda0^(p-2)) + κ *
      ((∫⁻ x, ENNReal.ofReal ((min ‖f x‖ T/(1/2))^(p-2)) ∂νf) +
        ENNReal.ofReal (eps⁻¹^2) *
          ∫⁻ x, ENNReal.ofReal ((min ‖g x‖ T/(eps/2))^(p-2)) ∂νg) at hh
  dsimp only [μf, νf, νg] at hh
  rw [clipped_rpow_moment_eq (hf.mono_measure hμν) hp hT hMpos,
    clipped_rpow_moment_eq hf hp hT (by norm_num : (0 : ℝ) < 1/2),
    clipped_rpow_moment_eq hg hp hT hepshalf] at hh
  rw [ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hMpos _),
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) _),
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hepshalf _)] at hh
  let A := ENNReal.ofReal (M^(p-2))
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hMpos _)).ne'
  have hAtop : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmult := mul_le_mul_right hh A
  have hcancel : A * (A⁻¹ * truncatedMoment μ f p T) = truncatedMoment μ f p T := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hA0 hAtop, one_mul]
  have hcancel' : A * ((ENNReal.ofReal (M^(p-2)))⁻¹ * truncatedMoment μ f p T) =
      truncatedMoment μ f p T := by simpa only [A] using hcancel
  rw [hcancel'] at hmult
  have hlow : A * ENNReal.ofReal (lambda0^(p-2)) =
      ENNReal.ofReal ((M*lambda0)^(p-2)) := by
    rw [Real.mul_rpow hMpos.le hlambda0.le, ENNReal.ofReal_mul (Real.rpow_nonneg hMpos.le _)]
  have hself : A * (ENNReal.ofReal ((1/2 : ℝ)^(p-2)))⁻¹ =
      ENNReal.ofReal ((2*M)^(p-2)) := by
    rw [show 2*M = M/(1/2) by ring, Real.div_rpow hMpos.le (by norm_num),
      ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) _)]
    simp only [A, div_eq_mul_inv]
  have hdata : A * (ENNReal.ofReal ((eps/2)^(p-2)))⁻¹ =
      ENNReal.ofReal ((2*M/eps)^(p-2)) := by
    rw [show 2*M/eps = M/(eps/2) by ring, Real.div_rpow hMpos.le hepshalf.le,
      ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hepshalf _)]
    simp only [A, div_eq_mul_inv]
  calc
    truncatedMoment μ f p T ≤ A *
      (sqWeightedMeasure f μ univ * ENNReal.ofReal (lambda0^(p-2)) + κ *
        ((ENNReal.ofReal ((1/2 : ℝ)^(p-2)))⁻¹ * truncatedMoment ν f p T +
          ENNReal.ofReal (eps⁻¹^2) * (ENNReal.ofReal ((eps/2)^(p-2)))⁻¹ *
            truncatedMoment ν g p T)) := by simpa only [mul_assoc] using hmult
    _ = (A * ENNReal.ofReal (lambda0^(p-2))) * sqWeightedMeasure f μ univ +
        (A * (ENNReal.ofReal ((1/2 : ℝ)^(p-2)))⁻¹) * κ * truncatedMoment ν f p T +
        ((A * (ENNReal.ofReal ((eps/2)^(p-2)))⁻¹) * ENNReal.ofReal (eps⁻¹^2)) * κ *
          truncatedMoment ν g p T := by ring
    _ = _ := by
      rw [hlow, hself, hdata, ← ENNReal.ofReal_mul
        (Real.rpow_nonneg (by positivity : 0 ≤ 2*M/eps) _)]


end SubdiffusiveProcess.MeyersRegularity
