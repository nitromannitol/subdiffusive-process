module

public import SubdiffusiveProcess.Section6.Defs.GoodFieldOne
public import SubdiffusiveProcess.Section6.Defs.GoodFieldTwo
public import SubdiffusiveProcess.Section6.Defs.GoodResponse

@[expose] public section

/-!
# Good events for finite and uncut response fields

`goodEvent M cutoff m y epsilon s` is a set of potential-layer sequences,
defined by the conjunction `GoodFieldOne`, `GoodFieldTwo` and `GoodResponse`.
A finite optional cutoff is represented by `some L`; `none` uses the uncut
response convention. The paper's uses impose positive small error parameters
and `0 < s ≤ 1/4`; the definition remains total for other real values.
Layer-gradient terms explicitly use the Euclidean norm where it is written.
Convergence and moment estimates belong to the accompanying supplier theorems,
not to the existence of the set definition itself.
-/

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The translated good event `G_{m,y}(epsilon,s)`. -/

def SubdiffusiveProcess.CoarseGrainingVocab.goodEvent {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (cutoff : Option ℕ) (m : ℕ) (y : Vec d) (epsilon s : ℝ) :
    Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  {ω | GoodFieldOne m y epsilon s ω ∧ GoodFieldTwo m y s ω ∧
    GoodResponse M cutoff m y epsilon s ω}

