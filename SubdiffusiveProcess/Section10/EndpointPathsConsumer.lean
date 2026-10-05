module

public import SubdiffusiveProcess.Section10.EndpointPathsConsequences

@[expose] public section

open Filter MeasureTheory Topology Set SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.EndpointPaths

/-- Application of the existing Markov/Borel–Cantelli supplier, with the same
`eta` and `epsilon`. Index zero is omitted because its literal threshold is
zero; the deterministic consequence already tolerates finite initial scales.
The summability and measurability inputs are discharged by the eventual final
source assembly, not asserted here as a source theorem. -/
theorem ae_endpoint_consequences {d : ℕ} (P : Measure (DiffusionPath d))
    (eta epsilon : ℝ) (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hmeas : ∀ n : ℕ, Measurable (smallExit (d := d) (n + 1)))
    (hsum : (∑' n : ℕ,
      (∫⁻ w, smallExit (n + 1) w ∂P) /
        ENNReal.ofReal (endpoint eta epsilon (n + 1))) ≠ ⊤) :
    ∀ᵐ w ∂P,
      (∀ᶠ t : ℝ≥0 in 𝓝[>] 0,
        oscillationConstant eta epsilon *
          ((t : ℝ) / Real.log (1 / (t : ℝ)) ^ (1 + epsilon)) ^
            (1 / (2 + eta)) ≤ maximum t w) ∧
      Tendsto (fun t : ℝ≥0 => maximum t w / Real.sqrt t) (𝓝[>] 0) atTop ∧
      (∀ gamma : ℝ, 0 ≤ gamma →
        (fun t : ℝ≥0 => euclideanNorm (w t - w 0))
          =O[𝓝[>] 0] (fun t : ℝ≥0 => (t : ℝ) ^ gamma) →
        gamma ≤ 1 / (2 + eta)) ∧
      (∀ᶠ k : ℕ in atTop,
        smallExit k w ≤ ENNReal.ofReal (endpoint eta epsilon k)) := by
  have hsup := _root_.SubdiffusiveProcess.Paper.aux_lim_paths_markov_bc P
    (fun n => smallExit (n + 1)) hmeas
    (fun n => ENNReal.ofReal (endpoint eta epsilon (n + 1)))
    (fun n => ne_of_gt (ENNReal.ofReal_pos.mpr (endpoint_pos eta epsilon (by omega))))
    (fun _ => ENNReal.ofReal_ne_top) hsum
  filter_upwards [hsup] with w hw
  obtain ⟨N, hN⟩ := eventually_atTop.mp hw
  have hexit : ∀ᶠ k : ℕ in atTop,
      smallExit k w ≤ ENNReal.ofReal (endpoint eta epsilon k) := by
    apply eventually_atTop.mpr
    refine ⟨N + 1, ?_⟩
    intro k hk
    have h := (hN (k - 1) (by omega)).le
    simpa only [Nat.sub_add_cancel (show 1 ≤ k by omega)] using h
  exact ⟨oscillation_of_eventual_exits eta epsilon heta hepsilon w hexit,
    maximum_div_sqrt_tendsto eta epsilon heta hepsilon w hexit,
    fun gamma hgamma hholder =>
      holder_exponent_le_of_eventual_exits eta epsilon heta hepsilon w hexit
        gamma hgamma hholder,
    hexit⟩





end SubdiffusiveProcess.Section10.EndpointPaths
