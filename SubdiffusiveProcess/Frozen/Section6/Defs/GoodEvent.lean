module

public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodFieldOne
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodFieldTwo
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodResponse

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The translated good event `G_{m,y}(epsilon,s)`. -/

def SubdiffusiveProcess.CoarseGrainingVocab.goodEvent {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (cutoff : Option ℕ) (m : ℕ) (y : Vec d) (epsilon s : ℝ) :
    Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  {ω | GoodFieldOne m y epsilon s ω ∧ GoodFieldTwo m y s ω ∧
    GoodResponse M cutoff m y epsilon s ω}

