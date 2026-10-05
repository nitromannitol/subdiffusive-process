module

public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Assumptions.AnchoredCoefficient
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
public import SubdiffusiveProcess.Assumptions.CoefficientPackaging
public import SubdiffusiveProcess.Assumptions.Cutoff
public import SubdiffusiveProcess.Assumptions.Observables
public import SubdiffusiveProcess.Assumptions.OGammaBridge
public import SubdiffusiveProcess.Assumptions.PotentialField
public import SubdiffusiveProcess.Assumptions.Sample
public import SubdiffusiveProcess.Model.ACutoff
public import SubdiffusiveProcess.Model.AAnchored
public import SubdiffusiveProcess.Model.AnchoredC11GoodSet
public import SubdiffusiveProcess.Model.AnchoredC11Sample
public import SubdiffusiveProcess.Model.AnchoredLog
public import SubdiffusiveProcess.Model.G2Observable
public import SubdiffusiveProcess.Model.GMCModel
public import SubdiffusiveProcess.Model.LocalSigma
public import SubdiffusiveProcess.Model.IsAnchoredC11Limit
public import SubdiffusiveProcess.Model.OGammaLE
public import SubdiffusiveProcess.Model.PotentialField
public import SubdiffusiveProcess.Model.PotentialMarginalLaw
public import SubdiffusiveProcess.Model.PotentialSample
public import SubdiffusiveProcess.Model.ShellLawG1
public import SubdiffusiveProcess.Model.ShellLawG2
public import SubdiffusiveProcess.Model.ShellLawG3
public import SubdiffusiveProcess.Model.ShellLawG4
public import SubdiffusiveProcess.Model.ShellLawPrefix
public import SubdiffusiveProcess.Model.TauSq
public import SubdiffusiveProcess.Model.UnitCubeDerivLipschitzSeminorm
public import SubdiffusiveProcess.Model.UnitCubeDerivNorm
public import SubdiffusiveProcess.Model.UnitCubeValueNorm
public import SubdiffusiveProcess.Model.ZeroPotentialLaw

@[expose] public section

/-!
# Standing assumptions for Gaussian multiplicative chaos

This facade exposes the source-level model together with its proved analytic and measurable support.
-/
