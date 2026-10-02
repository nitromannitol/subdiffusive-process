import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
import SubdiffusiveProcess.Providers.Section5.ReciprocalLower

open SubdiffusiveProcess.CoarseGrainingVocab


theorem SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤ ahom M m

:= SubdiffusiveProcess.Providers.Section5.homogenized_coefficient_reciprocal_lower M m
