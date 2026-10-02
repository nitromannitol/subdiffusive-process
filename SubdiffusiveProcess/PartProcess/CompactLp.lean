import SubdiffusiveProcess.PartProcess.CoreDensity
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

def compactToLp (m : Measure (Fin d → ℝ)) [IsLocallyFiniteMeasure m]
    (g : CompactlySupportedContinuousMap (Fin d → ℝ) ℝ) : Lp ℝ 2 m :=
  (g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport).toLp g

theorem compactToLp_coe [IsLocallyFiniteMeasure m] (g : CompactlySupportedContinuousMap (Fin d → ℝ) ℝ) :
    ⇑(compactToLp m g) =ᵐ[m] ⇑g := MemLp.coeFn_toLp _

theorem exists_nonneg_compactToLp_seq [IsLocallyFiniteMeasure m]
    (f : (Fin d → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfL : MemLp f 2 m) :
    ∃ g : ℕ → CompactlySupportedContinuousMap (Fin d → ℝ) ℝ, (∀ n x, 0 ≤ g n x) ∧
      Tendsto (fun n => compactToLp m (g n)) atTop (𝓝 (hfL.toLp f)) := by
  have happ : ∀ n : ℕ, ∃ g : (Fin d → ℝ) → ℝ,
      HasCompactSupport g ∧ eLpNorm (f - g) 2 m ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧
        Continuous g ∧ MemLp g 2 m := by
    intro n
    exact hfL.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
  choose k hk herr hc hL using happ
  let g : ℕ → CompactlySupportedContinuousMap (Fin d → ℝ) ℝ :=
    fun n => (⟨⟨k n, hc n⟩, hk n⟩ : CompactlySupportedContinuousMap (Fin d → ℝ) ℝ) ⊔ 0
  have hg0 : ∀ n x, 0 ≤ g n x := fun n x => le_max_right _ _
  have hb : ∀ n, ‖compactToLp m (g n) - hfL.toLp f‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have he : eLpNorm (f - ⇑(g n)) 2 m ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      refine (eLpNorm_mono (fun x => ?_)).trans (herr n)
      change ‖f x - max (k n x) 0‖ ≤ ‖f x - k n x‖
      simp only [Real.norm_eq_abs]
      by_cases hx : 0 ≤ k n x
      · rw [max_eq_left hx]
      · rw [max_eq_right (le_of_not_ge hx), sub_zero, abs_of_nonneg (hf0 x),
          abs_of_nonneg (by linarith [hf0 x] : 0 ≤ f x - k n x)]
        linarith
    rw [norm_sub_rev, compactToLp, ← hfL.toLp_sub, Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  refine ⟨g, hg0, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hb tendsto_one_div_add_atTop_nhds_zero_nat

theorem nonneg_of_tendsto_Lp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : ℕ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ}
    (hu : ∀ n, ∀ᵐ x ∂μ, 0 ≤ u n x) (hv : Tendsto u atTop (𝓝 v)) :
    ∀ᵐ x ∂μ, 0 ≤ v x := by
  obtain ⟨ns, _, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  filter_upwards [hlim, ae_all_iff.2 hu] with x hx hpos
  exact isClosed_Ici.mem_of_tendsto hx (Eventually.of_forall fun n => hpos (ns n))

theorem isLocallyFiniteMeasure_withDensity_Lp [IsLocallyFiniteMeasure m] (u : Lp ℝ 2 m) :
    IsLocallyFiniteMeasure (m.withDensity (fun x => ENNReal.ofReal (u x))) := by
  haveI : IsFiniteMeasureOnCompacts (m.withDensity (fun x => ENNReal.ofReal (u x))) := by
    constructor
    intro K hK
    rw [withDensity_apply _ hK.measurableSet]
    have hi := (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      |>.integrableOn_isCompact hK
    apply (lintegral_mono (fun x => ?_)).trans_lt hi.2
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  infer_instance

theorem measure_ext_of_lintegral_nonneg_compact
    (μ ν : Measure (Fin d → ℝ)) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (heq : ∀ g : CompactlySupportedContinuousMap (Fin d → ℝ) ℝ, (∀ x, 0 ≤ g x) →
      (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∫⁻ x, ENNReal.ofReal (g x) ∂ν) :
    μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  let gp := g ⊔ 0
  let gn := (-g) ⊔ 0
  have hp := heq gp (fun x => le_max_right _ _)
  have hn := heq gn (fun x => le_max_right _ _)
  have hreal : ∀ h : CompactlySupportedContinuousMap (Fin d → ℝ) ℝ,
      (∀ x, 0 ≤ h x) → (∫ x, h x ∂μ) = ∫ x, h x ∂ν := by
    intro h hh
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hh) h.continuous.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hh) h.continuous.aestronglyMeasurable,
      heq h hh]
  have hs : ⇑g = (fun x => gp x - gn x) := by
    funext x
    exact (max_zero_sub_max_neg_zero_eq_self (g x)).symm
  have hpμ : Integrable (fun x => gp x) μ := gp.continuous.integrable_of_hasCompactSupport gp.hasCompactSupport
  have hnμ : Integrable (fun x => gn x) μ := gn.continuous.integrable_of_hasCompactSupport gn.hasCompactSupport
  have hpν : Integrable (fun x => gp x) ν := gp.continuous.integrable_of_hasCompactSupport gp.hasCompactSupport
  have hnν : Integrable (fun x => gn x) ν := gn.continuous.integrable_of_hasCompactSupport gn.hasCompactSupport
  rw [hs, integral_sub hpμ hnμ, integral_sub hpν hnν,
    hreal gp (fun x => le_max_right _ _), hreal gn (fun x => le_max_right _ _)]

end SubdiffusiveProcess.PartProcess
