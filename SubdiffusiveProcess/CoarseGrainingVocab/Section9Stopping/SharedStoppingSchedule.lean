module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section




set_option autoImplicit false
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

/-- The budget `H_{a+1,j}` of a single collection of tests. -/
def stoppingTestHeight (h a j : ℕ) : ℕ := (a + 1) ^ 2 * h + j

/-- The largest native scale tested in that collection. -/
def stoppingTestScale (m h a j : ℕ) : ℕ := m + (a + 1) * h + j

/-- Its physical search radius at native scale `n`. -/
def stoppingTestRadius (m h a j n : ℕ) : ℝ :=
  ((m : ℝ) + 2) ^ (a + 1) *
    Real.exp (((a + 1 : ℕ) : ℝ) * h + j) * (3 : ℝ) ^ n

/-- The logarithmic counting budget `V_{a+1,j}`. -/
def stoppingTestEntropy (m h a j : ℕ) : ℝ :=
  ((a + 1 : ℕ) : ℝ) * ((h : ℝ) + 1 + Real.log ((m : ℝ) + 2)) + j

theorem stoppingTestRadius_pos (m h a j n : ℕ) :
    0 < stoppingTestRadius m h a j n := by
  unfold stoppingTestRadius
  positivity

theorem stoppingTestScale_mono {m m' h a j : ℕ} (hmm : m ≤ m') :
    stoppingTestScale m h a j ≤ stoppingTestScale m' h a j := by
  exact Nat.add_le_add_right (Nat.add_le_add_right hmm _) _

theorem stoppingTestRadius_mono {m m' : ℕ} (hmm : m ≤ m') (h a j n : ℕ) :
    stoppingTestRadius m h a j n ≤ stoppingTestRadius m' h a j n := by
  unfold stoppingTestRadius
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply pow_le_pow_left₀ (by positivity)
  exact add_le_add (Nat.cast_le.mpr hmm) le_rfl

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
