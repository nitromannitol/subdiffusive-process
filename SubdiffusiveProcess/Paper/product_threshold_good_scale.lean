module

public import SubdiffusiveProcess.Section6.Defs.GoodEvent
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

namespace SubdiffusiveProcess.Paper

/--
- Raw original-layer field and response tests of primitive_scores, with the product endpoint B written explicitly.
- B=6 is M's GoodFieldTwo; B=12 is the upper endpoint consumed by paper obl_ramp, lines2653–2684.
- The same cutoff enters the response test; field tests are unchanged.
- This definition proves no regularity estimate. The 6-to-12 deterministic extension remains obl_ramp's theorem obligation.

The product endpoint `B` is kept general and positive: it is a free real
parameter of the event, written in the mathematical notation `B`, so that the
same definition serves the field endpoint `B = 6` and the ramp endpoint
`B = 12`; the `B`-parameter convention is recorded in paper label `mfd:in-deterministic`. Event
membership opens with the valid score parameter regime `0 < B`, `0 < s`,
`s ≤ 1`, `0 < epsilon`, `epsilon ≤ 1`, and is then followed by the stored field
event `GoodFieldOne`, the product bound and the stored response event
`GoodResponse`. For every `j` the product clause additionally carries the finite
product-bound interpretation using actual convergence and boundedness: the
infinite exponential factor is `Multipliable` at every point of the physical
cube `translatedCube d (m + 1 + j) y`, the absolute-value image of the
pointwise sum of the finite and infinite products is `BddAbove` on that cube,
and the existing `supNormOn` of that pointwise sum is bounded by
`B * 3^(s*j/8)`. No totalized real `tprod` or `sSup` is used to let a divergent
product pass, and neither the field test nor the response test is dropped.
`B = 12` is the deterministic event consumed by `obl_ramp`; `B = 6` is its
manuscript predecessor; both share the same physical cutoff.
-/
def product_threshold_good_scale
    (d : ℕ) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (B : ℝ)
    (cutoff : Option ℕ) (m : ℕ) (y : Vec d) (epsilon s : ℝ) :
    Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  {omega | 0 < B ∧ 0 < s ∧ s ≤ 1 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
    GoodFieldOne m y epsilon s omega ∧
    (∀ j : ℕ,
      (∀ x ∈ translatedCube d (m + 1 + j) y,
        Multipliable (fun i : ℕ =>
          if m + j ≤ i then Real.exp (4 * |omega i x - omega i y|) else 1)) ∧
      BddAbove ((fun x : Vec d =>
        |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |omega i x - omega i y|) else 1|) ''
        translatedCube d (m + 1 + j) y) ∧
      supNormOn (translatedCube d (m + 1 + j) y) (fun x ↦
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |omega i x - omega i y|) else 1) ≤
        B * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)) ∧
    GoodResponse M cutoff m y epsilon s omega}

end SubdiffusiveProcess.Paper
