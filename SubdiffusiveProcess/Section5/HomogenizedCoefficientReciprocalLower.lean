module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
public import SubdiffusiveProcess.Providers.Section5.ReciprocalLower

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab


theorem SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤ ahom M m

:= SubdiffusiveProcess.Providers.Section5.homogenized_coefficient_reciprocal_lower M m
