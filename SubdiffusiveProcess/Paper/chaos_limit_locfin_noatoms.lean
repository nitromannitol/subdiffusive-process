import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.WeightedChaosCutoff
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.MeasuresConvergeLocally
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.ContinuousMap.CompactlySupported

open Filter MeasureTheory ProbabilityTheory Topology
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Part of G-2 of Proposition `mfd:prop-chaos-growth` (paper 4803-4816): a
measure obeying the growth bound `eq:mfd-39` on every bounded region is
locally finite and has no atoms.

Both are read off the bound and nothing else.  Local finiteness is the bound
at radius one; the absence of atoms is the bound as `r -> 0`, which forces
`mu {y} = 0` because the exponent `d - epsilon` is POSITIVE -- the one place
`epsilon < 1` and `d ≥ 2` are used, and the reason the growth exponent may not
be allowed to reach `d`. -/
theorem chaos_limit_locfin_noatoms
    {d : ℕ} (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo 0 1)
    (mu : Measure (SpatialCoordinates d))
    (hgrowth : ∀ Rset : Set (SpatialCoordinates d), Bornology.IsBounded Rset →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Rset, ∀ r : ℝ, 0 < r → r ≤ 1 →
        mu (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - epsilon))) :
    IsLocallyFiniteMeasure mu ∧ NoAtoms mu := by
  obtain ⟨hep0, hep1⟩ := hepsilon
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdeps : 0 < (d : ℝ) - epsilon := by linarith
  constructor
  · refine ⟨fun x => ?_⟩
    obtain ⟨K, hK, hb⟩ := hgrowth (Metric.ball x 2) Metric.isBounded_ball
    refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
    have hx : x ∈ Metric.ball x 2 := Metric.mem_ball_self (by norm_num)
    exact lt_of_le_of_lt (hb x hx 1 one_pos le_rfl) ENNReal.ofReal_lt_top
  · refine ⟨fun y => ?_⟩
    obtain ⟨K, hK, hb⟩ := hgrowth (Metric.ball y 2) Metric.isBounded_ball
    have hy : y ∈ Metric.ball y 2 := Metric.mem_ball_self (by norm_num)
    have hle : ∀ r : ℝ, 0 < r → r ≤ 1 →
        mu {y} ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - epsilon)) := by
      intro r hr hr1
      refine le_trans (measure_mono ?_) (hb y hy r hr hr1)
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Metric.mem_ball_self hr
    have hc : ContinuousAt (fun r : ℝ => r ^ ((d : ℝ) - epsilon)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr hdeps.le)
    have h1 : Filter.Tendsto (fun r : ℝ => K * r ^ ((d : ℝ) - epsilon))
        (nhds 0) (nhds 0) := by
      have h0 := hc.tendsto
      rw [Real.zero_rpow (ne_of_gt hdeps)] at h0
      have := h0.const_mul K
      rwa [mul_zero] at this
    have htend : Filter.Tendsto
        (fun r : ℝ => ENNReal.ofReal (K * r ^ ((d : ℝ) - epsilon)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h1' : Filter.Tendsto (fun r : ℝ => K * r ^ ((d : ℝ) - epsilon))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
        h1.mono_left nhdsWithin_le_nhds
      have h2 := ENNReal.tendsto_ofReal h1'
      simpa using h2
    have hev : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        mu {y} ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - epsilon)) := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
      exact hle r hr.1 hr.2.le
    exact le_antisymm (ge_of_tendsto htend hev) (zero_le _)

end Paper
