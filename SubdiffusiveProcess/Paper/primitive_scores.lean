import SubdiffusiveProcess.Frozen.Section6.Defs.AccumulatedError
import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.Lane3.Forms
import Mathlib.Tactic

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.Lane3
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



def primitive_scores (d : ℕ) [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s eps : ℝ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop) : Prop :=
  let normOn : Set (Vec d) → (Vec d → ℝ) → ENNReal :=
    fun W f => sSup {v : ENNReal | ∃ x : Vec d, x ∈ W ∧ v = ENNReal.ofReal |f x|}
  let J : ℕ → Vec d → ENNReal :=
    fun n z => sSup {v : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
      v = ENNReal.ofReal (section6Response M n n omega z e)}
  let eramp : ℝ → ℝ → ENNReal → ℝ :=
    fun a b X =>
      (min (1 : ENNReal) ((X - ENNReal.ofReal a) / ENNReal.ofReal (b - a))).toReal
  0 < s ∧ s ≤ 1 ∧ 0 < eps ∧ eps < 1 ∧
    -- (2) `Fsc`: extended-valued discounted supremum of the raw field tests.
    (∀ (m : ℕ) (z : Vec d),
      Fsc m z = sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ∑ i ∈ Finset.Icc (m - j) (m + j),
            normOn (translatedCube d (m + 1 + j) z)
              (fun x : Vec d => |omega i x| + (3 : ℝ) ^ (i : ℝ) *
                Homogenization.euclideanNorm (shellGradient (omega i) x))}) ∧
    -- (3) `Psc`: extended-valued discounted supremum of the pointwise product sum.
    (∀ (m : ℕ) (z : Vec d),
      Psc m z = sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
            w = (∏ i ∈ Finset.Icc (m - j) (m + j),
                  ENNReal.ofReal (Real.exp |omega i x|)) +
                sSup {u : ENNReal | ∃ K : ℕ,
                  u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                    ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}}}) ∧
    -- (4) `Rsc`: extended-valued discounted supremum over annular cells and
    -- directions of the exact matched response.
    (∀ (m : ℕ) (z : Vec d),
      Rsc m z = sSup {v : ENNReal | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧ ∃ x : Vec d,
        OnTriadicGrid n (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) * J n x}) ∧
    -- (5) `Dsc`: the complete `e.def.bfG.mhq`, all four terms, extended-valued.
    (∀ (k : ℕ) (z : Vec d),
      Dsc k z =
        sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
          OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
            (min (J l x) 1) ^ (1 / 2 : ℝ)} +
        sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
            normOn (translatedCube d k z) (shellBlock k j omega)} +
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
          normOn (translatedCube d k z) (omega 0) +
        ∑' j : ℕ, if k ≤ j then
          ENNReal.ofReal ((3 : ℝ) ^ k) *
            normOn (translatedCube d k z)
              (fun x : Vec d =>
                Homogenization.euclideanNorm (shellGradient (omega j) x))
          else 0) ∧
    -- (6) the good event of Definition `d.good.events`.
    (∀ (m : ℕ) (z : Vec d),
      (goodEvt m z ↔
        (Fsc m z ≤ ENNReal.ofReal eps ∧ Psc m z ≤ 6 ∧
          Rsc m z ≤ ENNReal.ofReal (eps ^ 2)))) ∧
    -- (7) the bad score through `eramp`, with `0 ≤ Z ≤ 3`.
    (∀ (m : ℕ) (z : Vec d),
      Zsc m z = eramp (eps / 2) eps (Fsc m z) + eramp 6 12 (Psc m z) +
          eramp (eps ^ 2 / 4) (eps ^ 2) (Rsc m z) ∧
        0 ≤ Zsc m z ∧ Zsc m z ≤ 3) ∧
    -- (8) the conditional zero-disorder baseline.
    ((SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P = 0 ∧
        (∀ n : ℕ, ahom M n = 1) ∧
        (∀ (i : ℕ) (x : Vec d), omega i x = 0)) →
      ∀ (m : ℕ) (z : Vec d),
        Fsc m z = 0 ∧ Psc m z = 2 ∧ Rsc m z = 0 ∧ Dsc m z = 0)

end Paper
