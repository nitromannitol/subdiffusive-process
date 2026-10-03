module

public import Mathlib
public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.Path.ExitTime
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal
noncomputable section
namespace Paper
def aux_lim_nonbrownian_scalePath {d : ℕ} (a : ℝ) (c : ℝ≥0)
    (w : DiffusionPath d) : DiffusionPath d :=
  ⟨fun t => a • (w (c * t) - w 0), by fun_prop⟩


/-- Section 10, limiting-process.tex L:122–169 or L:319–354; independently harvested flash leaf. -/

theorem aux_lim_nonbrownian_scalePath_ball
    {d : ℕ} (a : ℝ) (ha : 0 < a) (c t : ℝ≥0)
    (r : ℝ) (w : DiffusionPath d) :
    aux_lim_nonbrownian_scalePath a c w t ∈ Metric.ball 0 r ↔
      w (c * t) ∈ Metric.ball (w 0) (r / a) := by
  change dist (a • (w (c * t) - w 0)) 0 < r ↔ dist (w (c * t)) (w 0) < r / a
  rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos ha, lt_div_iff₀ ha]
  rw [dist_eq_norm, mul_comm a]


/-- Section 10, limiting-process.tex L:122–169 or L:319–354; independently harvested flash leaf. -/

theorem aux_lim_nonbrownian_scalePath_measurable
    {d : ℕ} (a : ℝ) (c : ℝ≥0) :
    Measurable (aux_lim_nonbrownian_scalePath (d := d) a c) := by
  have hg : Continuous fun t : ℝ≥0 => c * t := continuous_const.mul continuous_id
  let g : C(ℝ≥0, ℝ≥0) := ⟨fun t => c * t, hg⟩
  have hpre : Continuous fun w : C(ℝ≥0, SpatialCoordinates d) => w.comp g :=
    ContinuousMap.continuous_precomp g
  have hev : Continuous fun w : C(ℝ≥0, SpatialCoordinates d) => w 0 :=
    ContinuousEvalConst.continuous_eval_const (0 : ℝ≥0)
  have hconst : Continuous fun w : C(ℝ≥0, SpatialCoordinates d) =>
      ContinuousMap.const ℝ≥0 (w 0) := ContinuousMap.continuous_const'.comp hev
  have hsub : Continuous fun w : C(ℝ≥0, SpatialCoordinates d) =>
      w.comp g - ContinuousMap.const ℝ≥0 (w 0) := hpre.sub hconst
  have hsmul : Continuous fun w : C(ℝ≥0, SpatialCoordinates d) =>
      a • (w.comp g - ContinuousMap.const ℝ≥0 (w 0)) := hsub.const_smul a
  have heq : aux_lim_nonbrownian_scalePath a c =
      (fun w : C(ℝ≥0, SpatialCoordinates d) =>
        a • (w.comp g - ContinuousMap.const ℝ≥0 (w 0))) := by
    funext w
    apply ContinuousMap.ext
    intro t
    rfl
  rw [heq]
  exact hsmul.measurable


/-- Section 10, limiting-process.tex L:122–169 or L:319–354; independently harvested flash leaf. -/

theorem aux_lim_nonbrownian_scalePath_exit_le
    {d : ℕ} (a : ℝ) (ha : 0 < a) (c : ℝ≥0) (hc : 0 < c)
    (t : ℝ≥0) (r : ℝ) (w : DiffusionPath d) :
    ContinuousPath.exitTime (Metric.ball 0 r) (aux_lim_nonbrownian_scalePath a c w) ≤ t ↔
      ContinuousPath.exitTime (Metric.ball (w 0) (r / a)) w ≤ c * t := by
  rw [ContinuousPath.exitTime_le_iff_mem_hitsSetBy (Metric.ball 0 r) Metric.isOpen_ball t,
      ← ENNReal.coe_mul,
      ContinuousPath.exitTime_le_iff_mem_hitsSetBy (Metric.ball (w 0) (r / a))
        Metric.isOpen_ball (c * t) w]
  simp only [ContinuousPath.hitsSetBy, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨⟨c * s.1, ?_⟩, ?_⟩
    · show c * s.1 ≤ c * t
      exact mul_le_mul_of_nonneg_left s.2 c.property
    · intro h
      exact hs ((aux_lim_nonbrownian_scalePath_ball a ha c s.1 r w).mpr h)
  · rintro ⟨s, hs⟩
    refine ⟨⟨s.1 / c, ?_⟩, ?_⟩
    · show s.1 / c ≤ t
      rw [div_le_iff₀ hc]
      calc s.1 ≤ c * t := s.2
        _ = t * c := mul_comm c t
    · intro h
      have hcw : c * (s.1 / c) = s.1 := mul_div_cancel₀ s.1 (ne_of_gt hc)
      exact hs (hcw ▸ (aux_lim_nonbrownian_scalePath_ball a ha c (s.1 / c) r w).mp h)


/-- Section 10, limiting-process.tex L:122–169 or L:319–354; independently harvested flash leaf. -/

theorem aux_lim_nonbrownian_scalePath_exit
    {d : ℕ} (a : ℝ) (ha : 0 < a) (c : ℝ≥0) (hc : 0 < c)
    (r : ℝ) (w : DiffusionPath d) :
    ContinuousPath.exitTime (Metric.ball 0 r) (aux_lim_nonbrownian_scalePath a c w) =
      (c : ℝ≥0∞)⁻¹ * ContinuousPath.exitTime (Metric.ball (w 0) (r / a)) w := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  refine (aux_lim_nonbrownian_scalePath_exit_le a ha c hc t r w).trans ?_
  exact (ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr (ne_of_gt hc)) ENNReal.coe_ne_top).symm


/-- Section 10, limiting-process.tex L:122–169 or L:319–354; independently harvested flash leaf. -/

theorem aux_lim_nonbrownian_centered_exit_sup_bound
    {d : ℕ} (P : Measure (DiffusionPath d)) (x : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (hstart : ∀ᵐ w ∂P, w 0 = x)
    (K : SpatialCoordinates d → Measure (DiffusionPath d)) (hP : P = K x) :
    (∫⁻ w, ContinuousPath.exitTime (Metric.ball (w 0) r) w ∂P) ≤
      ⨆ y ∈ Metric.ball x r, ∫⁻ w, ContinuousPath.exitTime (Metric.ball x r) w ∂K y := by
  rw [hP] at hstart ⊢
  have hx_mem : x ∈ Metric.ball x r := by
    rw [Metric.mem_ball]
    simpa using hr
  have hae : (fun w => ContinuousPath.exitTime (Metric.ball (w 0) r) w)
      =ᵐ[K x] (fun w => ContinuousPath.exitTime (Metric.ball x r) w) := by
    filter_upwards [hstart] with w hw
    rw [hw]
  rw [MeasureTheory.lintegral_congr_ae hae]
  exact le_iSup_of_le x (le_iSup_of_le hx_mem le_rfl)


/-- Section 10, limiting-process.tex L:122–169 or L:319–354; independently harvested flash leaf. -/

theorem aux_lim_nonbrownian_exit_scale_algebra
    (C eta : ℝ) (k : ℕ) :
    (3 : ℝ) ^ (2 * (-(k : ℤ))) * (C * (3 : ℝ) ^ (-(eta * (k : ℝ)))) =
      C * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ))) := by
  have h3 : (0:ℝ) < 3 := by norm_num
  have hcast : ((2 * (-(k:ℤ)) : ℤ) : ℝ) = -2 * (k:ℝ) := by
    push_cast
    ring
  rw [← Real.rpow_intCast (3:ℝ) (2 * (-(k:ℤ))), hcast]
  rw [show -((2 + eta) * (k:ℝ)) = -2 * (k:ℝ) + -(eta * (k:ℝ)) by ring]
  rw [Real.rpow_add h3]
  ring


end Paper
