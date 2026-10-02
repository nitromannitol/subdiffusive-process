import SubdiffusiveProcess.Section10.EndpointPaths
import SubdiffusiveProcess.Section10.ExitLawPassage

/-! Powered exit passage consumes actual weak convergence and a prelimit
moment bound. The physical clock/random-bank producer supplies that bound;
this module does not close the source exit-moment corollary. -/
open Filter MeasureTheory ProbabilityTheory MarkovProcess Set Topology SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.ExitMomentPassage

/-- ENNReal powers preserve lower semicontinuity for every real p > 0. -/
lemma smallExit_rpow_lsc {d : ℕ} (k : ℕ) (p : ℝ) (hp : 0 < p) :
    LowerSemicontinuous (fun w : DiffusionPath d => EndpointPaths.smallExit k w ^ p) := by
  exact (ENNReal.continuous_rpow_const (y := p)).comp_lowerSemicontinuous
    (Paper.aux_lim_nonbrownian_centered_exit_lsc ((3 : ℝ) ^ (-(k : ℤ)) / 2))
    (ENNReal.monotone_rpow_of_nonneg hp.le)

/-- Consume the existing real-valued Portmanteau supplier on finite truncations
of a lower-semicontinuous extended functional, then its monotone limit. -/
theorem lintegral_le_of_weak_limit_lsc {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (P : ProbabilityMeasure X) (PN : ℕ → ProbabilityMeasure X)
    (hconv : Tendsto PN atTop (𝓝 P)) (f : X → ℝ≥0∞)
    (hf : LowerSemicontinuous f) (b : ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, (∫⁻ x, f x ∂(PN n : Measure X)) ≤ b) :
    (∫⁻ x, f x ∂(P : Measure X)) ≤ b := by
  have htrunc : ∀ T : ℝ≥0∞, T ≠ ⊤ →
      (∫⁻ x, ENNReal.ofReal (T.truncateToReal (f x)) ∂(P : Measure X)) ≤ b := by
    intro T hT
    have hL := (ENNReal.continuous_truncateToReal hT).comp_lowerSemicontinuous hf
      (ENNReal.monotone_truncateToReal hT)
    have hPort := Paper.aux_lim_transition_domination_portmanteau_lsc
      (P : Measure X) (fun n => (PN n : Measure X))
      (fun x => T.truncateToReal (f x)) hL (fun _ => ENNReal.truncateToReal_nonneg)
      (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hG)
    refine hPort.trans (Filter.liminf_le_of_frequently_le'
      (hbound.mono (fun n hn => (lintegral_mono (fun x => ?_)).trans hn)).frequently)
    change ENNReal.ofReal ((min T (f x)).toReal) ≤ f x
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top hT (min_le_left _ _))]
    exact min_le_right _ _
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (μ := (P : Measure X)) (f := fun n x => min (n : ℝ≥0∞) (f x))
    (fun n => (measurable_const.min hf.measurable).aemeasurable)
    (ae_of_all _ (fun x i j hij => min_le_min_right _ (by exact_mod_cast hij)))
    (ae_of_all _ (fun x => by simpa only [min_top_left] using
      ENNReal.tendsto_nat_nhds_top.min (tendsto_const_nhds (x := f x))))
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  have h := htrunc n (ENNReal.natCast_ne_top n)
  simpa only [ENNReal.truncateToReal,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_left _ _))] using h

/-- Literal powered centred-cube exit passage at each fixed scale. -/
theorem smallExit_moment_passage {d : ℕ}
    (P : ProbabilityMeasure (DiffusionPath d)) (PN : ℕ → ProbabilityMeasure (DiffusionPath d))
    (hconv : Tendsto PN atTop (𝓝 P)) (k : ℕ) (p : ℝ) (hp : 0 < p) (b : ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, (∫⁻ w, EndpointPaths.smallExit k w ^ p
      ∂(PN n : Measure (DiffusionPath d))) ≤ b) :
    (∫⁻ w, EndpointPaths.smallExit k w ^ p ∂(P : Measure (DiffusionPath d))) ≤ b :=
  lintegral_le_of_weak_limit_lsc P PN hconv _ (smallExit_rpow_lsc k p hp) b hbound

/-- Consumer boundary: Cp is one fixed finite real constant, independent of
scale and cutoff; eta is exactly the strict-decay exponent of the producer. -/
theorem smallExit_moment_decay_of_prelimit {d : ℕ}
    (P : ProbabilityMeasure (DiffusionPath d)) (PN : ℕ → ProbabilityMeasure (DiffusionPath d))
    (hconv : Tendsto PN atTop (𝓝 P)) (Cp eta p : ℝ) (hp : 0 < p)
    (hbound : ∀ k : ℕ, ∀ᶠ n in atTop, (∫⁻ w, EndpointPaths.smallExit k w ^ p
      ∂(PN n : Measure (DiffusionPath d))) ≤
      ENNReal.ofReal (Cp * (3 : ℝ) ^ (-(p * (2 + eta) * k)))) :
    ∀ k : ℕ, (∫⁻ w, EndpointPaths.smallExit k w ^ p
      ∂(P : Measure (DiffusionPath d))) ≤
      ENNReal.ofReal (Cp * (3 : ℝ) ^ (-(p * (2 + eta) * k))) := by
  intro k
  exact smallExit_moment_passage P PN hconv k p hp _ (hbound k)

end SubdiffusiveProcess.Section10.ExitMomentPassage
