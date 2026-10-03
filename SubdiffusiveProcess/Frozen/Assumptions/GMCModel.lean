module

public import SubdiffusiveProcess.Frozen.Assumptions.ShellLawPrefix
public import SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1
public import SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2
public import SubdiffusiveProcess.Frozen.Assumptions.ShellLawG3
public import SubdiffusiveProcess.Frozen.Assumptions.ShellLawG4

@[expose] public section

/-!
# The standing GMC model
-/

open MeasureTheory




structure SubdiffusiveProcess.Frozen.Assumptions.GMCModel (d : ℕ) where
  delta : ℝ
  P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
  shellPrefix : SubdiffusiveProcess.Frozen.Assumptions.ShellLawPrefix d delta P
  G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d P
  G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta P
  G3 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG3 d P
  G4 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG4 d P

