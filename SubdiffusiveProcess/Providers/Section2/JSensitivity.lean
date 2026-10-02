import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity




set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory
noncomputable section


-- carries the manuscript's standing `d ≥ 2` convention.
set_option linter.unusedVariables false in

theorem SubdiffusiveProcess.Providers.Section2.j_sensitivity {d : ℕ} (hd : 2 ≤ d)
    (U : Ch02.Domain d) (a b : Vec d → ℝ)
    (ha : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (hb : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U b)
    (lambda delta : ℝ) (hlambda : 0 < lambda) (hdelta : 0 < delta)
    (hdelta_one : delta ≤ 1) (p q : Vec d) :
    SubdiffusiveProcess.CoarseGrainingVocab.J U hb.toCoeffOn
        ((Real.sqrt lambda)⁻¹ • p) (Real.sqrt lambda • q) ≤
      (1 + delta) * SubdiffusiveProcess.CoarseGrainingVocab.J U ha.toCoeffOn p q +
        3 / delta *
          (SubdiffusiveProcess.CoarseGrainingVocab.scalarRatioLInf U (fun x => lambda * a x) b ^ 2 +
            SubdiffusiveProcess.CoarseGrainingVocab.scalarRatioLInf U (fun x => lambda⁻¹ * b x) a ^ 2) *
          (SubdiffusiveProcess.CoarseGrainingVocab.J U ha.toCoeffOn p q + vecDot p q)

:= SubdiffusiveProcess.CoarseGrainingVocab.responseJ_sensitivity ha hb hlambda hdelta hdelta_one p q
