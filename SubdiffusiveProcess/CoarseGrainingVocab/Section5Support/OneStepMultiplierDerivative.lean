import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryOrbitRigidity

/-!
# Spatial derivative of the one-step suffix multiplier

The one-step multiplier is the exponential of a finite centered shell block.
This file records its literal Fréchet derivative on the GMC sample carrier.
It is the pointwise generator input for the stationary Hodge trace argument.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Spatial derivative of the uncentered shell block in a cutoff ratio. -/
def oneStepShellDerivative {d : ℕ} (n h : ℕ)
    (omega : Sample d) (x : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ k ∈ cutoffShellIndices (n + h) (n : ℤ),
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega k) x

/-- The finite one-step shell sum has the sum of the stored shell
derivatives as its Fréchet derivative. -/
theorem hasFDerivAt_cutoffShellSum_oneStep {d : ℕ}
    (n h : ℕ) (omega : Sample d) (x : Vec d) :
    HasFDerivAt
      (fun y => cutoffShellSum (n + h) (n : ℤ) y omega)
      (oneStepShellDerivative n h omega x) x := by
  unfold cutoffShellSum oneStepShellDerivative
  exact HasFDerivAt.fun_sum
    (u := cutoffShellIndices (n + h) (n : ℤ)) fun k _ =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.hasFDerivAt (omega k) x

/-- Exact pointwise derivative of the one-step centered suffix multiplier. -/
theorem hasFDerivAt_oneStepMultiplierAt {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (x : Vec d) (hh : 0 < h) :
    HasFDerivAt
      (fun y => oneStepMultiplierAt M n h y omega)
      (Real.exp
          (cutoffShellSum (n + h) (n : ℤ) x omega -
            (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) •
        oneStepShellDerivative n h omega x) x := by
  have hn : (-1 : ℤ) ≤ (n : ℤ) := by omega
  have hnm : (n : ℤ) < ((n + h : ℕ) : ℤ) := by
    exact_mod_cast Nat.lt_add_of_pos_right hh
  have hdiff : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
    push_cast
    ring
  have hshell := hasFDerivAt_cutoffShellSum_oneStep n h omega x
  have hcentered : HasFDerivAt
      (fun y => cutoffShellSum (n + h) (n : ℤ) y omega -
        (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
      (oneStepShellDerivative n h omega x) x :=
    hshell.sub_const _
  have hexp := hcentered.exp
  have hfinal := hexp.sub_const (1 : ℝ)
  convert hfinal using 1
  · funext y
    rw [oneStepMultiplierAt, cutoffRatioMinusOne_eq_exp_shell
      M (n + h) (n : ℤ) omega y hn hnm, hdiff]

/-- Directional derivative along a coordinate axis. -/
theorem hasDerivAt_oneStepMultiplierAt_coord {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (x : Vec d) (i : Fin d) (hh : 0 < h) :
    HasDerivAt
      (fun t : ℝ => oneStepMultiplierAt M n h
        (x + t • (Pi.single i 1 : Vec d)) omega)
      (Real.exp
          (cutoffShellSum (n + h) (n : ℤ) x omega -
            (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        oneStepShellDerivative n h omega x (Pi.single i 1)) 0 := by
  have hline : HasDerivAt
      (fun t : ℝ => x + t • (Pi.single i 1 : Vec d))
      (Pi.single i 1 : Vec d) 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).smul_const
      (Pi.single i 1 : Vec d) |>.const_add x
  simpa using
    (hasFDerivAt_oneStepMultiplierAt M n h omega
      (x + (0 : ℝ) • (Pi.single i 1 : Vec d)) hh).comp_hasDerivAt 0 hline

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
