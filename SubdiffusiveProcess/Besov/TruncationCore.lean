module

public import SubdiffusiveProcess.Besov.SpatialPairing
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- Symmetric truncation of a real number. -/
def clip (M t : ℝ) : ℝ := max (-M) (min t M)

theorem clip_lipschitz (M : ℝ) : LipschitzWith 1 (clip M) :=
  (LipschitzWith.id.min_const M).const_max (-M)

theorem clip_zero {M : ℝ} (hM : 0 ≤ M) : clip M 0 = 0 := by
  simp [clip, hM, neg_nonpos.mpr hM]

theorem clip_sub_le (M a b : ℝ) : |clip M a - clip M b| ≤ |a - b| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using (clip_lipschitz M).dist_le_mul a b

theorem clip_abs_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : |clip M t| ≤ |t| := by
  simpa only [clip_zero hM, sub_zero] using clip_sub_le M t 0

theorem clip_abs_le_bound {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : |clip M t| ≤ M := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem clip_eq_self {M t : ℝ} (h : |t| ≤ M) : clip M t = t := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  rw [clip, min_eq_left hu, max_eq_right hl]

theorem tendsto_clip (t : ℝ) :
    Filter.Tendsto (fun n : ℕ => clip (n + 1) t) Filter.atTop (𝓝 t) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |t|
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  apply Filter.eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  symm
  apply clip_eq_self
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

instance normalizedCubeMeasure_isProbability {d : ℕ} (R : TriadicCube d) :
    IsProbabilityMeasure (normalizedCubeMeasure R) := ⟨normalizedCubeMeasure_apply_univ R⟩

/-- On a probability space, subtracting the mean costs at most twice the L1 distance to any constant. -/
theorem eLpNorm_sub_integral_le_two {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (h : α → ℝ) (hh : Integrable h μ) (c : ℝ) :
    eLpNorm (fun x => h x - ∫ y, h y ∂μ) 1 μ ≤
      2 * eLpNorm (fun x => h x - c) 1 μ := by
  let v : α → ℝ := fun x => h x - c
  have hv : Integrable v μ := hh.sub (integrable_const c)
  have hmean : (∫ y, v y ∂μ) = (∫ y, h y ∂μ) - c := by
    rw [integral_sub hh (integrable_const c)]
    simp
  have heq : (fun x => h x - ∫ y, h y ∂μ) = (v - fun _ => ∫ y, v y ∂μ) := by
    funext x
    dsimp only [v, Pi.sub_apply]
    rw [hmean]
    ring
  rw [heq]
  have hconst : eLpNorm (fun _ : α => ∫ y, v y ∂μ) 1 μ ≤ eLpNorm v 1 μ := by
    rw [eLpNorm_const (∫ y, v y ∂μ) one_ne_zero (NeZero.ne μ)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    rw [eLpNorm_one_eq_lintegral_enorm hv.aestronglyMeasurable]
    exact enorm_integral_le_lintegral_enorm v
  calc
    _ ≤ eLpNorm v 1 μ + eLpNorm (fun _ : α => ∫ y, v y ∂μ) 1 μ :=
      eLpNorm_sub_le (f := v) (g := fun _ => ∫ y, v y ∂μ) le_rfl
    _ ≤ eLpNorm v 1 μ + eLpNorm v 1 μ := add_le_add le_rfl hconst
    _ = _ := by rw [two_mul]

/-- Integrability of the clipped function follows from its contraction bound. -/
theorem integrable_clip {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {h : α → ℝ} (hh : Integrable h μ) {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun x => clip M (h x)) μ := by
  apply hh.norm.mono' ((clip_lipschitz M).continuous.comp_aestronglyMeasurable hh.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using clip_abs_le hM (h x)

/-- The centered oscillation of a clipped function is bounded by twice the original oscillation. -/
theorem clipped_oscillation_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (g : α → ℝ) (hg : Integrable g μ) (a M : ℝ) (hM : 0 ≤ M) :
    eLpNorm (fun x => clip M (g x - a) - ∫ y, clip M (g y - a) ∂μ) 1 μ ≤
      2 * eLpNorm (fun x => g x - ∫ y, g y ∂μ) 1 μ := by
  have ht := integrable_clip μ (hg.sub (integrable_const a)) hM
  have h := eLpNorm_sub_integral_le_two μ _ ht (clip M ((∫ y, g y ∂μ) - a))
  refine h.trans (mul_le_mul_right ?_ 2)
  apply eLpNorm_mono_ae (ht.aestronglyMeasurable.sub aestronglyMeasurable_const)
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Pi.sub_apply, Real.norm_eq_abs, sub_sub_sub_cancel_right] using!
      clip_sub_le M (g x - a) ((∫ y, g y ∂μ) - a)

end SubdiffusiveProcess.Besov
