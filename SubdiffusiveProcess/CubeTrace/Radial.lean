import Mathlib

/-!
# Radial integrals for the sup norm on `ℝ^d`

`(Fin d → ℝ) = Fin d → ℝ` carries the sup norm, so `integral_fun_norm_addHaar` applies
verbatim.  These are the two integrals behind the fractional seminorm estimate: the integral of
`‖z‖^{γ-d}` over a ball (γ > 0) and of `‖z‖^{-d-a}` outside a ball (a > 0).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace SubdiffusiveProcess.CubeTrace

variable {d : ℕ}

/-- The dimensional constant `d · vol(B(0,1))` (sup-norm unit ball, i.e. `d · 2^d`). -/
def ctCd (d : ℕ) : ℝ := (d : ℝ) * (volume (Metric.ball (0 : (Fin d → ℝ)) 1)).toReal

theorem ctCd_nonneg (d : ℕ) : 0 ≤ ctCd d := by
  unfold ctCd; positivity

/-- `∫_{B(0,ρ)} ‖z‖^{γ-d} dz ≤ C_d ρ^γ/γ`. -/
theorem lintegral_ball_norm_rpow_le [NeZero d] {γ ρ : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) :
    ∫⁻ z in Metric.ball (0 : (Fin d → ℝ)) ρ, ENNReal.ofReal (‖z‖ ^ (γ - (d : ℝ))) ≤
      ENNReal.ofReal (ctCd d * ρ ^ γ / γ) := by
  haveI : Nontrivial (Fin d → ℝ) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_neZero d⟩⟩
    infer_instance
  have hd1 : 1 ≤ d := Nat.pos_of_neZero d
  let g : ℝ → ℝ := fun r => if 0 ≤ r ∧ r < ρ then r ^ (γ - (d : ℝ)) else 0
  have hg0 : ∀ r, 0 ≤ g r := by
    intro r; simp only [g]; split_ifs with h
    · exact Real.rpow_nonneg h.1 _
    · exact le_rfl
  have hfin : Module.finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
  -- the one-dimensional integrand
  let h : ℝ → ℝ := fun y => y ^ (γ - 1)
  have h1D : ∀ y ∈ Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Fin d → ℝ) - 1) • g y =
      (Ioo (0 : ℝ) ρ).indicator h y := by
    intro y hy
    have hy0 : 0 < y := hy
    rw [hfin]
    by_cases hyρ : y < ρ
    · have hmem : y ∈ Ioo (0 : ℝ) ρ := ⟨hy0, hyρ⟩
      rw [Set.indicator_of_mem hmem]
      simp only [g, if_pos (And.intro hy0.le hyρ), smul_eq_mul, h]
      rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
      congr 1
      rw [Nat.cast_sub hd1]; push_cast; ring
    · have hnm : y ∉ Ioo (0 : ℝ) ρ := fun hh => hyρ hh.2
      rw [Set.indicator_of_notMem hnm]
      simp only [g, smul_eq_mul]
      rw [if_neg (fun hh => hyρ hh.2), mul_zero]
  have hint_h : IntegrableOn h (Ioo (0 : ℝ) ρ) volume := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ρ) (r := γ - 1)
      (by linarith))
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hρ.le] at this
    exact this
  have hint1 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ (Fin d → ℝ) - 1) • g y) (Ioi 0)
      volume := by
    have : IntegrableOn ((Ioo (0 : ℝ) ρ).indicator h) (Ioi 0) volume :=
      (hint_h.integrable_indicator measurableSet_Ioo).integrableOn
    exact this.congr_fun (fun y hy => (h1D y hy).symm) measurableSet_Ioi
  have hint : Integrable (fun z : Fin d → ℝ => g ‖z‖) volume :=
    (integrable_fun_norm_addHaar volume).2 hint1
  have hval : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Fin d → ℝ) - 1) • g y = ρ ^ γ / γ := by
    have hI : Ioi (0 : ℝ) ∩ Ioo 0 ρ = Ioo 0 ρ := Set.inter_eq_right.2 (fun y hy => hy.1)
    rw [setIntegral_congr_fun measurableSet_Ioi h1D, setIntegral_indicator measurableSet_Ioo, hI]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le]
    simp only [h]
    rw [integral_rpow (Or.inl (by linarith))]
    rw [show γ - 1 + 1 = γ by ring, Real.zero_rpow hγ.ne']
    ring
  calc ∫⁻ z in Metric.ball (0 : Fin d → ℝ) ρ, ENNReal.ofReal (‖z‖ ^ (γ - (d : ℝ)))
      = ∫⁻ z : Fin d → ℝ, ENNReal.ofReal (g ‖z‖) := by
        rw [← lintegral_indicator measurableSet_ball]
        congr 1
        funext z
        by_cases hz : z ∈ Metric.ball (0 : Fin d → ℝ) ρ
        · rw [Set.indicator_of_mem hz]
          simp only [g, mem_ball_zero_iff.1 hz, norm_nonneg, and_self, if_true]
        · rw [Set.indicator_of_notMem hz]
          have : ¬ (‖z‖ < ρ) := fun hh => hz (mem_ball_zero_iff.2 hh)
          simp only [g, this, and_false, if_false, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (∫ z : Fin d → ℝ, g ‖z‖) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun z => hg0 _))).symm
    _ = ENNReal.ofReal (ctCd d * ρ ^ γ / γ) := by
        rw [integral_fun_norm_addHaar volume g, hval, hfin]
        simp only [smul_eq_mul, nsmul_eq_mul, Measure.real, ctCd]
        congr 1
        ring
    _ ≤ _ := le_rfl

/-- `∫_{‖z‖ ≥ ρ} ‖z‖^{-d-a} dz ≤ C_d ρ^{-a}/a`. -/
theorem lintegral_compl_ball_norm_rpow_le [NeZero d] {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    ∫⁻ z in (Metric.ball (0 : (Fin d → ℝ)) ρ)ᶜ, ENNReal.ofReal (‖z‖ ^ (-((d : ℝ) + a))) ≤
      ENNReal.ofReal (ctCd d * ρ ^ (-a) / a) := by
  haveI : Nontrivial (Fin d → ℝ) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_neZero d⟩⟩
    infer_instance
  have hd1 : 1 ≤ d := Nat.pos_of_neZero d
  let g : ℝ → ℝ := fun r => if ρ ≤ r then r ^ (-((d : ℝ) + a)) else 0
  have hg0 : ∀ r, 0 ≤ g r := by
    intro r; simp only [g]; split_ifs with h
    · exact Real.rpow_nonneg (le_trans hρ.le h) _
    · exact le_rfl
  have hfin : Module.finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
  let h : ℝ → ℝ := fun y => y ^ (-a - 1)
  have h1D : ∀ y ∈ Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Fin d → ℝ) - 1) • g y =
      (Ici ρ).indicator h y := by
    intro y hy
    have hy0 : 0 < y := hy
    rw [hfin]
    by_cases hyρ : ρ ≤ y
    · rw [Set.indicator_of_mem (show y ∈ Ici ρ from hyρ)]
      simp only [g, if_pos hyρ, smul_eq_mul, h]
      rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
      congr 1
      rw [Nat.cast_sub hd1]; push_cast; ring
    · rw [Set.indicator_of_notMem (show y ∉ Ici ρ from hyρ)]
      simp only [g, smul_eq_mul]
      rw [if_neg hyρ, mul_zero]
  have hint_h : IntegrableOn h (Ioi ρ) volume :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hρ
  have hint1 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ (Fin d → ℝ) - 1) • g y) (Ioi 0)
      volume := by
    have h2 : IntegrableOn h (Ici ρ) volume := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact hint_h
    have : IntegrableOn ((Ici ρ).indicator h) (Ioi 0) volume :=
      (h2.integrable_indicator measurableSet_Ici).integrableOn
    exact this.congr_fun (fun y hy => (h1D y hy).symm) measurableSet_Ioi
  have hint : Integrable (fun z : Fin d → ℝ => g ‖z‖) volume :=
    (integrable_fun_norm_addHaar volume).2 hint1
  have hval : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Fin d → ℝ) - 1) • g y =
      ρ ^ (-a) / a := by
    have hI : Ioi (0 : ℝ) ∩ Ici ρ = Ici ρ := Set.inter_eq_right.2 (fun y hy => lt_of_lt_of_le hρ hy)
    rw [setIntegral_congr_fun measurableSet_Ioi h1D, setIntegral_indicator measurableSet_Ici, hI,
      integral_Ici_eq_integral_Ioi]
    simp only [h]
    rw [integral_Ioi_rpow_of_lt (by linarith) hρ]
    rw [show -a - 1 + 1 = -a by ring]
    field_simp
  calc ∫⁻ z in (Metric.ball (0 : Fin d → ℝ) ρ)ᶜ, ENNReal.ofReal (‖z‖ ^ (-((d : ℝ) + a)))
      = ∫⁻ z : Fin d → ℝ, ENNReal.ofReal (g ‖z‖) := by
        rw [← lintegral_indicator (measurableSet_ball.compl)]
        congr 1
        funext z
        by_cases hz : z ∈ (Metric.ball (0 : Fin d → ℝ) ρ)ᶜ
        · rw [Set.indicator_of_mem hz]
          have : ρ ≤ ‖z‖ := by
            simpa [mem_ball_zero_iff, not_lt] using hz
          simp only [g, this, if_true]
        · rw [Set.indicator_of_notMem hz]
          have : ¬ (ρ ≤ ‖z‖) := by
            intro hh; exact hz (by simpa [mem_ball_zero_iff, not_lt] using hh)
          simp only [g, this, if_false, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (∫ z : Fin d → ℝ, g ‖z‖) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun z => hg0 _))).symm
    _ = ENNReal.ofReal (ctCd d * ρ ^ (-a) / a) := by
        rw [integral_fun_norm_addHaar volume g, hval, hfin]
        simp only [smul_eq_mul, nsmul_eq_mul, Measure.real, ctCd]
        congr 1
        ring
    _ ≤ _ := le_rfl

/-- Translation to a ball about `x`. -/
theorem lintegral_ball_center (x : (Fin d → ℝ)) (ρ : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y in Metric.ball x ρ, g ‖y - x‖ = ∫⁻ z in Metric.ball (0 : (Fin d → ℝ)) ρ, g ‖z‖ := by
  have h1 : ∫⁻ y in Metric.ball x ρ, g ‖y - x‖ =
      ∫⁻ y, (Metric.ball (0 : Fin d → ℝ) ρ).indicator (fun z => g ‖z‖) (y - x) := by
    rw [← lintegral_indicator measurableSet_ball]
    congr 1
    funext y
    by_cases hy : y ∈ Metric.ball x ρ
    · have : y - x ∈ Metric.ball (0 : Fin d → ℝ) ρ := by
        simpa [mem_ball_iff_norm] using hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : y - x ∉ Metric.ball (0 : Fin d → ℝ) ρ := by
        simpa [mem_ball_iff_norm] using hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [h1, lintegral_sub_right_eq_self (fun y => (Metric.ball (0 : Fin d → ℝ) ρ).indicator (fun z => g ‖z‖) y) x,
    lintegral_indicator measurableSet_ball]

theorem lintegral_compl_ball_center (x : (Fin d → ℝ)) (ρ : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y in (Metric.ball x ρ)ᶜ, g ‖y - x‖ =
      ∫⁻ z in (Metric.ball (0 : (Fin d → ℝ)) ρ)ᶜ, g ‖z‖ := by
  have h1 : ∫⁻ y in (Metric.ball x ρ)ᶜ, g ‖y - x‖ =
      ∫⁻ y, ((Metric.ball (0 : Fin d → ℝ) ρ)ᶜ).indicator (fun z => g ‖z‖) (y - x) := by
    rw [← lintegral_indicator measurableSet_ball.compl]
    congr 1
    funext y
    by_cases hy : y ∈ (Metric.ball x ρ)ᶜ
    · have : y - x ∈ (Metric.ball (0 : Fin d → ℝ) ρ)ᶜ := by
        simpa [mem_ball_iff_norm] using hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : y - x ∉ (Metric.ball (0 : Fin d → ℝ) ρ)ᶜ := by
        simpa [mem_ball_iff_norm] using hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [h1, lintegral_sub_right_eq_self (fun y => ((Metric.ball (0 : Fin d → ℝ) ρ)ᶜ).indicator (fun z => g ‖z‖) y) x,
    lintegral_indicator measurableSet_ball.compl]

end SubdiffusiveProcess.CubeTrace
