module

public import SubdiffusiveProcess.Model.ShellLawPrefix
public import SubdiffusiveProcess.Model.ShellLawG1
public import SubdiffusiveProcess.Model.ShellLawG2
public import SubdiffusiveProcess.Model.ShellLawG3
public import SubdiffusiveProcess.Model.ShellLawG4

@[expose] public section

/-!
# The standing random environment

`GMCModel d` contains a positive disorder strength, a probability law on
sequences of locally `C¹ˑ¹` scalar potential layers, and the standing layer
assumptions. `shellPrefix` includes dimension `d ≥ 2`, disorder in `(0,1/2]`,
independence and exact marginal scaling. `G1`--`G4` supply the remaining
stationarity, concentration, finite-range and positive-strength assumptions.
Every element of the potential carrier has the stated regularity; this is
stronger than merely saying regularity holds almost surely for an arbitrary
raw field. The headline theorems are conditional on this model data.

Explicit dimension and positive-disorder premises in some public wrappers
repeat `shellPrefix.dimension` and `shellPrefix.delta_pos`. They retain the
source-facing interfaces and do not impose a further model restriction.
`NeZero d` is likewise implied by `d ≥ 2`.
-/

open MeasureTheory

/-- The complete standing environment model for the finite-cutoff
development in `a.g1` and `a.g2` and `a.g3` and `a.g4`. -/

structure SubdiffusiveProcess.Model.GMCModel (d : ℕ) where
  delta : ℝ
  P : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d)
  shellPrefix : _root_.SubdiffusiveProcess.Model.ShellLawPrefix d delta P
  G1 : _root_.SubdiffusiveProcess.Model.ShellLawG1 d P
  G2 : _root_.SubdiffusiveProcess.Model.ShellLawG2 d delta P
  G3 : _root_.SubdiffusiveProcess.Model.ShellLawG3 d P
  G4 : _root_.SubdiffusiveProcess.Model.ShellLawG4 d P

