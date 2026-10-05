module

public import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity
public import SubdiffusiveProcess.Providers.Section2.JSensitivity
@[expose] public section

set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory
noncomputable section

theorem SubdiffusiveProcess.Section2.j_sensitivity {d : ℕ} (hd : 2 ≤ d)
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
:= SubdiffusiveProcess.Providers.Section2.j_sensitivity hd U a b ha hb lambda delta hlambda hdelta hdelta_one p q
