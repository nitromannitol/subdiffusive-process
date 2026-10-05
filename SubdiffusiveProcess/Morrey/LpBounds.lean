module

public import SubdiffusiveProcess.Analysis.NormalizedMeanMinimizer
public import SubdiffusiveProcess.Sobolev.CampanatoRepresentative
public import Homogenization.Sobolev.MatchedPair.ScaledPoincare
public import Homogenization.Ambient.Euclidean
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import SubdiffusiveProcess.MultiplicativeChaos.ChaosBasic

@[expose] public section

/-!
# Local oscillation bounds for Morrey's inequality

Scaled cube Poincaré and the finite-measure comparison of Lᵖ and L² norms give
oscillation bounds using the Euclidean magnitude of an H¹ weak gradient.
The spatial metric remains the product supremum norm.
-/

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab (normalizedL2On)
open scoped ENNReal NNReal Topology Pointwise

noncomputable section
namespace SubdiffusiveProcess.Morrey

theorem normalizedL2_eq {d : ℕ} (S : Set (Vec d)) (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume.restrict S)) :
    normalizedL2On S f = (eLpNorm f 2 (volume.restrict S)).toReal /
      Real.sqrt (volume.real S) := by
  have hnorm : (eLpNorm f 2 (volume.restrict S)).toReal =
      Real.sqrt (∫ x in S, f x ^ 2) := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
    norm_num only [ENNReal.toReal_ofNat]
    simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg
      (integral_nonneg fun x => sq_nonneg _) _)]
    rw [← Real.sqrt_eq_rpow]
  rw [hnorm]
  change Real.sqrt ((volume.real S)⁻¹ * ∫ x in S, f x ^ 2) = _
  rw [Real.sqrt_mul (inv_nonneg.mpr measureReal_nonneg), Real.sqrt_inv]
  ring

theorem local_lp_two {d : ℕ} {Ω S : Set (Vec d)} (hS : S ⊆ Ω)
    (hSfin : volume S ≠ ⊤) {p : ℝ} (hp : 2 ≤ p)
    {f : Vec d → ℝ} (hf : MemLp f (ENNReal.ofReal p) (volume.restrict Ω)) :
    (eLpNorm f 2 (volume.restrict S)).toReal ≤
      (eLpNorm f (ENNReal.ofReal p) (volume.restrict Ω)).toReal *
        (volume.real S) ^ (1 / 2 - 1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hpE : (2 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hpow : 0 ≤ (1 / 2 : ℝ) - 1 / p := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
    linarith
  have hμ : volume.restrict S ≤ volume.restrict Ω := Measure.restrict_mono hS le_rfl
  have hfS : MemLp f (ENNReal.ofReal p) (volume.restrict S) := hf.mono_measure hμ
  have hbase := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpE hfS.aestronglyMeasurable
  simp only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hp0.le] at hbase
  have hle := hbase.trans (mul_le_mul_left
    (eLpNorm_mono_measure f hμ) ((volume S) ^ ((1 / 2 : ℝ) - 1 / p)))
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hf.eLpNorm_ne_top (ENNReal.rpow_ne_top_of_nonneg hpow hSfin)) hle
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Measure.real] using ht

theorem oscillation_subset {d : ℕ} {B S : Set (Vec d)} (hS : S ⊆ B)
    (hBfin : volume B ≠ ⊤) (hSpos : 0 < volume.real S)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict B)) :
    normalizedL2On S (fun y => f y - (volume.real S)⁻¹ * ∫ t in S, f t) ≤
      Real.sqrt (volume.real B / volume.real S) *
        normalizedL2On B (fun y => f y - (volume.real B)⁻¹ * ∫ t in B, f t) := by
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hBfin (measure_mono hS)
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSfin
  have hfS : MemLp f 2 (volume.restrict S) := hf.mono_measure (Measure.restrict_mono hS le_rfl)
  let A : ℝ := (volume.real B)⁻¹ * ∫ t in B, f t
  have hmin := integral_sq_sub_average_le_integral_sq_sub_const S hSfin f hfS A
  have hmono : ∫ y in S, (f y - A) ^ 2 ≤ ∫ y in B, (f y - A) ^ 2 :=
    setIntegral_mono_set ((hf.sub (memLp_const A)).integrable_sq)
      (Filter.Eventually.of_forall fun y => sq_nonneg _) hS.eventuallyLE
  have hBpos : 0 < volume.real B := hSpos.trans_le (measureReal_mono hS hBfin)
  have heq : (volume.real B / volume.real S) *
      ((volume.real B)⁻¹ * ∫ y in B, (f y - A) ^ 2) =
      (volume.real S)⁻¹ * ∫ y in B, (f y - A) ^ 2 := by
    field_simp
  change Real.sqrt ((volume.real S)⁻¹ *
      ∫ y in S, (f y - (volume.real S)⁻¹ * ∫ t in S, f t) ^ 2) ≤
    Real.sqrt (volume.real B / volume.real S) *
      Real.sqrt ((volume.real B)⁻¹ * ∫ y in B, (f y - A) ^ 2)
  rw [← Real.sqrt_mul (div_nonneg hBpos.le hSpos.le), heq]
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (hmin.trans hmono) (inv_nonneg.mpr hSpos.le))

theorem axisCube_eq_ball {d : ℕ} (x : Vec d) {r : ℝ} (hr : 0 < r) :
    axisCube (fun i => x i - r) (2 * r) = Metric.ball x r := by
  ext y
  simp only [axisCube, mem_pi, mem_univ, forall_const, mem_Ioo, Metric.mem_ball,
    dist_eq_norm]
  rw [pi_norm_lt_iff hr]
  constructor
  · intro hy i
    rw [Real.norm_eq_abs, abs_lt]
    have h := hy i
    change -r < y i - x i ∧ y i - x i < r
    constructor <;> linarith [h.1, h.2]
  · intro hy i
    have h := hy i
    rw [Real.norm_eq_abs, abs_lt] at h
    change -r < y i - x i ∧ y i - x i < r at h
    change x i - r < y i ∧ y i < x i - r + 2 * r
    constructor <;> linarith [h.1, h.2]

theorem poincare_ball {d : ℕ} (x : Vec d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (Metric.ball x r)) :
    (eLpNorm (fun y => u.toFun y - integralAverage (Metric.ball x r) u.toFun)
      2 (volume.restrict (Metric.ball x r))).toReal ≤
      unitMeanZeroPoincareConst d * (2 * r) * (d : ℝ) *
        (eLpNorm (fun y => euclideanNorm (u.grad y)) 2
          (volume.restrict (Metric.ball x r))).toReal := by
  have hEq := axisCube_eq_ball x hr
  have hs := @scaled_meanZero_poincare d (fun i => x i - r) (2 * r)
    (mul_pos (by norm_num) hr)
  change ∀ v : H1Function (axisCube (fun i => x i - r) (2 * r)),
    (eLpNorm (fun y => v.toFun y - integralAverage
      (axisCube (fun i => x i - r) (2 * r)) v.toFun) 2
      (volume.restrict (axisCube (fun i => x i - r) (2 * r)))).toReal ≤
    unitMeanZeroPoincareConst d * (2 * r) * ∑ i : Fin d,
      (eLpNorm (fun y => v.grad y i) 2
        (volume.restrict (axisCube (fun i => x i - r) (2 * r)))).toReal at hs
  rw [hEq] at hs
  have hPi := hs u
  have hg : MemLp (fun y => euclideanNorm (u.grad y)) 2
      (volume.restrict (Metric.ball x r)) := by
    simpa only [euclideanNorm_eq_norm_ofVec, hilbertifyVecField, volumeMeasureOn] using
      (memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2).norm
  have hcoord : ∀ i : Fin d,
      (eLpNorm (fun y => u.grad y i) 2 (volume.restrict (Metric.ball x r))).toReal ≤
        (eLpNorm (fun y => euclideanNorm (u.grad y)) 2
          (volume.restrict (Metric.ball x r))).toReal := by
    intro i
    apply ENNReal.toReal_mono hg.eLpNorm_ne_top
    apply eLpNorm_mono_ae (u.grad_memL2 i).aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (euclideanNorm_nonneg _),
      euclideanNorm_eq_norm_ofVec]
    exact HilbertVec.abs_apply_le_norm (HilbertVec.ofVec (u.grad y)) i
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hC : 0 ≤ unitMeanZeroPoincareConst d * (2 * r) :=
    mul_nonneg (unitMeanZeroPoincareConst_nonneg d) (by positivity)
  have hfinal := hPi.trans (mul_le_mul_of_nonneg_left hsum hC)
  simpa only [H1Function.subAverage_apply, volumeMeasureOn, mul_assoc] using hfinal

theorem ball_oscillation_lp {d : ℕ} {Ω : Set (Vec d)} (u : H1Function Ω)
    {p : ℝ} (hp : 2 ≤ p)
    (hg : MemLp (fun y => euclideanNorm (u.grad y)) (ENNReal.ofReal p)
      (volume.restrict Ω)) (x : Vec d) {r : ℝ} (hr : 0 < r)
    (hB : Metric.ball x r ⊆ Ω) :
    normalizedL2On (Metric.ball x r)
      (fun y => u.toFun y - integralAverage (Metric.ball x r) u.toFun) ≤
      (2 * unitMeanZeroPoincareConst d * (d : ℝ)) * r *
        (volume.real (Metric.ball x r)) ^ (-(1 / p)) *
        (eLpNorm (fun y => euclideanNorm (u.grad y)) (ENNReal.ofReal p)
          (volume.restrict Ω)).toReal := by
  let B : Set (Vec d) := Metric.ball x r
  have hBfin : volume B ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  have hvol : 0 < volume.real B := by
    rw [Measure.real, volume_ball_spatial x hr, ENNReal.toReal_ofReal (by positivity)]
    positivity
  let v : H1Function B := u.restrict Metric.isOpen_ball hB
  have hf : MemLp u.toFun 2 (volume.restrict B) :=
    u.memL2.mono_measure (Measure.restrict_mono hB le_rfl)
  have hres : MemLp (fun y => u.toFun y - integralAverage B u.toFun) 2
      (volume.restrict B) := hf.sub (memLp_const _)
  have hP := poincare_ball x hr v
  have hLp := local_lp_two hB hBfin hp hg
  have hC : 0 ≤ unitMeanZeroPoincareConst d * (2 * r) * (d : ℝ) := by
    exact mul_nonneg (mul_nonneg (unitMeanZeroPoincareConst_nonneg d)
      (by positivity)) (Nat.cast_nonneg d)
  have hpow : (volume.real B) ^ (1 / 2 - 1 / p) / Real.sqrt (volume.real B) =
      (volume.real B) ^ (-(1 / p)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hvol]
    congr 1
    ring
  rw [normalizedL2_eq B _ hres]
  calc
    (eLpNorm (fun y => u.toFun y - integralAverage B u.toFun) 2
        (volume.restrict B)).toReal / Real.sqrt (volume.real B) ≤
      (unitMeanZeroPoincareConst d * (2 * r) * (d : ℝ) *
        ((eLpNorm (fun y => euclideanNorm (u.grad y)) (ENNReal.ofReal p)
          (volume.restrict Ω)).toReal * (volume.real B) ^ (1 / 2 - 1 / p))) /
        Real.sqrt (volume.real B) :=
      div_le_div_of_nonneg_right (hP.trans (mul_le_mul_of_nonneg_left hLp hC))
        (Real.sqrt_nonneg _)
    _ = (2 * unitMeanZeroPoincareConst d * (d : ℝ)) * r *
        (volume.real B) ^ (-(1 / p)) *
        (eLpNorm (fun y => euclideanNorm (u.grad y)) (ENNReal.ofReal p)
          (volume.restrict Ω)).toReal := by
      calc
        _ = (unitMeanZeroPoincareConst d * (2 * r) * (d : ℝ) *
          (eLpNorm (fun y => euclideanNorm (u.grad y)) (ENNReal.ofReal p)
            (volume.restrict Ω)).toReal) *
          ((volume.real B) ^ (1 / 2 - 1 / p) / Real.sqrt (volume.real B)) := by ring
        _ = _ := by rw [hpow]; ring

end SubdiffusiveProcess.Morrey
