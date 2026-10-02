import SubdiffusiveProcess.Frozen.Section6.Defs.CoefficientAt
import SubdiffusiveProcess.Assumptions.Cutoff
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

/-! # The exact local normalization

The finite coefficient splits into the cutoff at the domain scale and
the anchored oscillations of the remaining shells. Above the cutoff,
the normalization factor is exactly one.
-/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Cutoff index used for the time scale of the physical cube. -/
def localIndex (L : WithTop ℕ) (m : ℕ) : ℕ :=
  match L with
  | ⊤ => m
  | (n : ℕ) => min m n

/-- Speed density in the locally anchored coordinates of a physical cube. -/
def localDensity {d : ℕ} (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) (z : Vec d)
    (ω : AnchoredC11Sample d) (x : Vec d) : ℝ :=
  (coefficientAt M L ω z / aCutoff M (localIndex L m) ω.1 z)⁻¹ *
    coefficientAt M L ω (z + (3 : ℝ) ^ m • x)

/-- Energy coefficient with the local homogenized time scale. -/
def localCoefficient {d : ℕ} (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) (z : Vec d)
    (ω : AnchoredC11Sample d) (x : Vec d) : ℝ :=
  (ahom M (localIndex L m))⁻¹ * localDensity M L m z ω x

theorem coefficientAt_pos {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (ω : AnchoredC11Sample d) (x : Vec d) : 0 < coefficientAt M L ω x := by
  cases L using WithTop.recTopCoe
  · exact aAnchored_pos M ω x
  · exact aCutoff_pos M _ ω.1 x

theorem localDensity_pos {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (m : ℕ) (z : Vec d) (ω : AnchoredC11Sample d) (x : Vec d) :
    0 < localDensity M L m z ω x :=
  mul_pos (inv_pos.mpr (div_pos (coefficientAt_pos M L ω z)
    (aCutoff_pos M _ ω.1 z))) (coefficientAt_pos M L ω _)

theorem localCoefficient_pos {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (m : ℕ) (z : Vec d) (ω : AnchoredC11Sample d) (x : Vec d) :
    0 < localCoefficient M L m z ω x :=
  mul_pos (inv_pos.mpr (ahom_pos M _)) (localDensity_pos M L m z ω x)

theorem continuous_coefficientAt {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (ω : AnchoredC11Sample d) : Continuous (coefficientAt M L ω) := by
  cases L using WithTop.recTopCoe
  · exact continuous_aAnchored M ω
  · exact continuous_aCutoff M _ ω.1

theorem continuous_localDensity {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (m : ℕ) (z : Vec d) (ω : AnchoredC11Sample d) :
    Continuous (localDensity M L m z ω) :=
  continuous_const.mul ((continuous_coefficientAt M L ω).comp
    (continuous_const.add (continuous_const.smul continuous_id)))

theorem localDensity_origin {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (m : ℕ) (z : Vec d) (ω : AnchoredC11Sample d) :
    localDensity M L m z ω 0 = aCutoff M (localIndex L m) ω.1 z := by
  unfold localDensity
  simp only [smul_zero, add_zero]
  field_simp [(coefficientAt_pos M L ω z).ne']

/-- Above the finite cutoff the constant removed at the centre is one. -/
theorem localDensity_finite_of_le {d : ℕ} (M : GMCModel d) {L m : ℕ}
    (hLm : L ≤ m) (z : Vec d) (ω : AnchoredC11Sample d) (x : Vec d) :
    localDensity M (L : WithTop ℕ) m z ω x = aCutoff M L ω.1 (z + (3 : ℝ) ^ m • x) := by
  change (aCutoff M L ω.1 z / aCutoff M (min m L) ω.1 z)⁻¹ *
    aCutoff M L ω.1 (z + (3 : ℝ) ^ m • x) = _
  rw [min_eq_right hLm, div_self (aCutoff_pos M L ω.1 z).ne', inv_one, one_mul]

/-- Exact finite-shell oscillation left by anchoring at the domain centre. -/
theorem localDensity_finite_factorization {d : ℕ} (M : GMCModel d) {L m : ℕ}
    (hmL : m ≤ L) (z : Vec d) (ω : AnchoredC11Sample d) (x : Vec d) :
    localDensity M (L : WithTop ℕ) m z ω x =
      aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) *
        Real.exp (∑ i ∈ Finset.Ico (m + 1) (L + 1),
          (ω.1 i (z + (3 : ℝ) ^ m • x) - ω.1 i z)) := by
  let y := z + (3 : ℝ) ^ m • x
  have hsplit : ∀ w : Vec d,
      (∑ i ∈ Finset.range (L + 1), (ω.1 i w - tauSq M.P)) =
        (∑ i ∈ Finset.range (m + 1), (ω.1 i w - tauSq M.P)) +
          ∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω.1 i w - tauSq M.P) :=
    fun w => (Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right hmL 1)).symm
  change (aCutoff M L ω.1 z / aCutoff M (min m L) ω.1 z)⁻¹ *
    aCutoff M L ω.1 y = _
  rw [min_eq_left hmL]
  unfold aCutoff
  rw [inv_div, ← Real.exp_sub, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [hsplit z, hsplit y]
  have htail : (∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω.1 i y - tauSq M.P)) -
      (∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω.1 i z - tauSq M.P)) =
        ∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω.1 i y - ω.1 i z) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  dsimp only [y] at htail
  linarith

end SubdiffusiveProcess.Static
