import SubdiffusiveProcess.FiniteStopping.ZeroDisorderScores

/-! Canonical extended-valued primitive scores on a potential sample.
These definitions retain every term in the original field, product, response,
and accumulated-error tests. They assert no almost-sure finiteness or moment
bound. The zero-disorder identities use the existing finite-stopping library.
-/
open Set SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- The extended supremum of the absolute value on a set. -/
def primitiveNormOn {d : ℕ} (S : Set (Vec d)) (f : Vec d → ℝ) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ x ∈ S, v = ENNReal.ofReal |f x|}

/-- The maximal matched diagonal response at one scale and centre. -/
def primitiveResponseDefect {d : ℕ} [NeZero d] (M : GMCModel d)
    (omega : PotentialSample d) (n : ℕ) (z : Vec d) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ e : Vec d, vecNormSq e = 1 ∧
    v = ENNReal.ofReal (section6Response M n n omega z e)}

/-- The discounted raw field and gradient test. -/
def primitiveFieldScore {d : ℕ} (s : ℝ) (omega : PotentialSample d)
    (m : ℕ) (z : Vec d) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ j : ℕ,
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        primitiveNormOn (translatedCube d (m + 1 + j) z)
          (fun x => |omega i x| + (3 : ℝ) ^ (i : ℝ) *
            euclideanNorm (shellGradient (omega i) x))}

/-- The discounted product test, including the full partial-product supremum. -/
def primitiveProductScore {d : ℕ} (s : ℝ) (omega : PotentialSample d)
    (m : ℕ) (z : Vec d) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ j : ℕ,
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (m + 1 + j) z,
        w = (∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |omega i x|)) +
          sSup {u : ℝ≥0∞ | ∃ K : ℕ,
            u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
              ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}}}

/-- The discounted supremum of matched response defects over the original annular cells. -/
def primitiveResponseScore {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ)
    (omega : PotentialSample d) (m : ℕ) (z : Vec d) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧ ∃ x : Vec d,
    OnTriadicGrid n (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
      primitiveResponseDefect M omega n x}

/-- The complete accumulated error, with all four original terms. -/
def primitiveErrorScore {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ)
    (omega : PotentialSample d) (k : ℕ) (z : Vec d) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
    OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
      (min (primitiveResponseDefect M omega l x) 1) ^ (1 / 2 : ℝ)} +
  sSup {v : ℝ≥0∞ | ∃ j : ℕ, j ≤ k ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
      primitiveNormOn (translatedCube d k z) (shellBlock k j omega)} +
  ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
    primitiveNormOn (translatedCube d k z) (omega 0) +
  ∑' j : ℕ, if k ≤ j then
    ENNReal.ofReal ((3 : ℝ) ^ k) * primitiveNormOn (translatedCube d k z)
      (fun x => euclideanNorm (shellGradient (omega j) x)) else 0

/-- The bounded ramp on an extended nonnegative argument. -/
def extendedPrimitiveRamp (lo hi : ℝ) (X : ℝ≥0∞) : ℝ :=
  (min (1 : ℝ≥0∞) ((X - ENNReal.ofReal lo) / ENNReal.ofReal (hi - lo))).toReal

/-- The extended ramp always lies between zero and one, including at infinity. -/
theorem extendedPrimitiveRamp_bounds (lo hi : ℝ) (X : ℝ≥0∞) :
    0 ≤ extendedPrimitiveRamp lo hi X ∧ extendedPrimitiveRamp lo hi X ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h := ENNReal.toReal_mono ENNReal.one_ne_top
    (min_le_left (1 : ℝ≥0∞) ((X - ENNReal.ofReal lo) / ENNReal.ofReal (hi - lo)))
  exact h.trans_eq ENNReal.toReal_one

/-- The three original bad-score ramps. -/
def primitiveBadScore {d : ℕ} [NeZero d] (M : GMCModel d) (s eps : ℝ)
    (omega : PotentialSample d) (m : ℕ) (z : Vec d) : ℝ :=
  extendedPrimitiveRamp (eps / 2) eps (primitiveFieldScore s omega m z) +
    extendedPrimitiveRamp 6 12 (primitiveProductScore s omega m z) +
    extendedPrimitiveRamp (eps ^ 2 / 4) (eps ^ 2) (primitiveResponseScore M s omega m z)

/-- The canonical raw good event uses the original three thresholds. -/
def primitiveGoodEvent {d : ℕ} [NeZero d] (M : GMCModel d) (s eps : ℝ)
    (omega : PotentialSample d) (m : ℕ) (z : Vec d) : Prop :=
  primitiveFieldScore s omega m z ≤ ENNReal.ofReal eps ∧
    primitiveProductScore s omega m z ≤ 6 ∧
    primitiveResponseScore M s omega m z ≤ ENNReal.ofReal (eps ^ 2)

/-- The bad score lies between zero and three for every potential sample. -/
theorem primitiveBadScore_bounds {d : ℕ} [NeZero d] (M : GMCModel d) (s eps : ℝ)
    (omega : PotentialSample d) (m : ℕ) (z : Vec d) :
    0 ≤ primitiveBadScore M s eps omega m z ∧ primitiveBadScore M s eps omega m z ≤ 3 := by
  have hF := extendedPrimitiveRamp_bounds (eps / 2) eps (primitiveFieldScore s omega m z)
  have hP := extendedPrimitiveRamp_bounds 6 12 (primitiveProductScore s omega m z)
  have hR := extendedPrimitiveRamp_bounds (eps ^ 2 / 4) (eps ^ 2)
    (primitiveResponseScore M s omega m z)
  unfold primitiveBadScore
  constructor <;> linarith only [hF.1, hF.2, hP.1, hP.2, hR.1, hR.2]

/-- The canonical scores have the exact zero-disorder baseline. -/
theorem primitiveScores_zero {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (omega : PotentialSample d) (htau : tauSq M.P = 0)
    (hahom : ∀ n : ℕ, ahom M n = 1) (hz : ∀ (i : ℕ) (x : Vec d), omega i x = 0)
    (m : ℕ) (z : Vec d) :
    primitiveFieldScore s omega m z = 0 ∧ primitiveProductScore s omega m z = 2 ∧
      primitiveResponseScore M s omega m z = 0 ∧ primitiveErrorScore M s omega m z = 0 := by
  have hJ := fun n x e he => FiniteStopping.ps_section6Response_nonpos M n omega
    htau (hahom n) hz x e he
  exact ⟨FiniteStopping.ps_F_zero s omega hz m z, FiniteStopping.ps_P_two s hs omega hz m z,
    FiniteStopping.ps_R_zero M s omega hJ m z, FiniteStopping.ps_D_zero M s omega hJ hz m z⟩

end SubdiffusiveProcess
