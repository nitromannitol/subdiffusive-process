module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5RobustTests
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5TailContrast

@[expose] public section

/-!
# Replacement for the law-guarded anchored transfer

The shell tolerance is calibrated against the multiplier tolerance before
the raw local event is used.  The
conclusion consists of unconditional tests for the actual anchored coefficient.
The law of that coefficient is used only by the subsequent analytic readout.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- An explicit shell tolerance can always be chosen after a positive multiplier tolerance. -/
theorem exists_goodCubeV5_shell_tolerance {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eps1 : ℝ, 0 < eps1 ∧
      goodCubeV5TailBudget eps1 ≤ Real.log (1 + epsilon) := by
  have hlog : 0 < Real.log (1 + epsilon) := Real.log_pos (by linarith)
  have hq := goodCubeV5ShellRatio_pos
  have h1q : 0 < 1 - goodCubeV5ShellRatio := sub_pos.mpr goodCubeV5ShellRatio_lt_one
  refine ⟨Real.log (1 + epsilon) * (1 - goodCubeV5ShellRatio) /
    goodCubeV5ShellRatio, div_pos (mul_pos hlog h1q) hq, ?_⟩
  unfold goodCubeV5TailBudget
  field_simp
  rfl

/-- O's selected value `eps1 = 1` does not satisfy the corrected small-multiplier
budget.  This refutes that calibration, not the original transfer proposition. -/
theorem not_goodCubeV5_unit_shell_budget {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    ¬ goodCubeV5TailBudget 1 ≤ Real.log (1 + epsilon) := by
  have hq : (1 / 3 : ℝ) ≤ goodCubeV5ShellRatio := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by norm_num : (-1 : ℝ) ≤ -(1 : ℝ) / 4)
    norm_num only [Real.rpow_neg_one] at h
    simpa only [goodCubeV5ShellRatio, neg_div] using h
  have h1q : 0 < 1 - goodCubeV5ShellRatio := sub_pos.mpr goodCubeV5ShellRatio_lt_one
  have hbudget : (1 / 2 : ℝ) ≤ goodCubeV5TailBudget 1 := by
    simp only [goodCubeV5TailBudget, one_mul]
    apply (le_div_iff₀ h1q).mpr
    linarith
  have hlog : Real.log (1 + epsilon) ≤ epsilon := by
    simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + epsilon)
  intro h
  linarith

/-- The exact ratio of anchored and cutoff coefficients is admissible on the
native cube.  Its normalization is its value at the cube centre. -/
theorem goodCubeV5_anchored_ratio_admissible {d : ℕ} (M : GMCModel d)
    (omega : AnchoredC11Sample d) (n : ℕ) (z : Lattice d)
    {eps1 epsilon : ℝ} (heps1 : 0 ≤ eps1) (hepsilon : 0 < epsilon)
    (hbudget : goodCubeV5TailBudget eps1 ≤ Real.log (1 + epsilon))
    (E0 : Lattice d → Set (PotentialSample d))
    (hgood : omega.1 ∈ goodCubeEvent (goodCubeEventField n 1 eps1 E0) z) :
    GoodCubeV5AdmissibleMultiplier (nativeBox n 1 z) epsilon
      (fun x => aAnchored M omega x / aCutoff M n omega.1 x) := by
  let theta : Vec d → ℝ := fun x => aAnchored M omega x / aCutoff M n omega.1 x
  have htheta (x : Vec d) : 0 < theta x :=
    div_pos (aAnchored_pos M omega x) (aCutoff_pos M n omega.1 x)
  have hc : goodCubeCentre n z ∈ nativeBox n 1 z := by
    refine mem_centeredAxisCube.mpr fun i => ?_
    simp only [sub_self, abs_zero]
    positivity
  refine ⟨((continuous_aAnchored M omega).div (continuous_aCutoff M n omega.1)
    (fun x => (aCutoff_pos M n omega.1 x).ne')).continuousOn,
    fun x _ => htheta x, theta (goodCubeCentre n z), htheta _, ?_⟩
  intro x hx
  have hlog := goodCubeV5_log_ratio_sub_le M omega n z heps1 E0 hgood hx hc
  change |Real.log (theta x) - Real.log (theta (goodCubeCentre n z))| ≤ _ at hlog
  let t := Real.log (theta x) - Real.log (theta (goodCubeCentre n z))
  have ht : |t| ≤ Real.log (1 + epsilon) := hlog.trans hbudget
  have heq : (theta (goodCubeCentre n z))⁻¹ * theta x = Real.exp t := by
    dsimp only [t]
    rw [Real.exp_sub, Real.exp_log (htheta x), Real.exp_log (htheta _)]
    ring
  rw [heq]
  have hupper : Real.exp t ≤ 1 + epsilon := by
    simpa only [Real.exp_log (by linarith : 0 < 1 + epsilon)] using
      Real.exp_le_exp.mpr (abs_le.mp ht).2
  have hlogle : Real.log (1 + epsilon) ≤ epsilon := by
    simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + epsilon)
  have hlow := Real.add_one_le_exp t
  exact abs_le.mpr ⟨by linarith [(abs_le.mp ht).1], by linarith⟩

/-- The replacement transfer consumes unconditional robust tests and returns
unconditional tests.  No cutoff-law existence or process transformation occurs. -/
def GoodCubeAnchoredTestTransferAll (d : ℕ) : Prop :=
  ∀ (eps1 epsilon : ℝ), 0 < eps1 → 0 < epsilon → epsilon < 1 / 2 →
    goodCubeV5TailBudget eps1 ≤ Real.log (1 + epsilon) →
  ∀ (M : GMCModel d) (n : ℕ) (z : Lattice d) (omega : AnchoredC11Sample d)
    (E0 : Lattice d → Set (PotentialSample d)),
    omega.1 ∈ goodCubeEvent (goodCubeEventField n 1 eps1 E0) z →
  ∀ (p A sigma eps epsH massFraction eps0 : ℝ) (clock : ℝ → ℝ)
    (G : Finset (ℤ × Vec d)) (Pairs Pfam : Set (Cube d × Cube d)),
    (∀ q ∈ G, cubeSet (q.2, (3 : ℝ)^q.1) ⊆ nativeBox n 1 z) →
    (∀ q ∈ Pairs, cubeSet q.2 ⊆ nativeBox n 1 z) →
    (∀ q ∈ Pfam, cubeSet q.2 ⊆ nativeBox n 1 z) →
    GoodCubeV5RobustFiniteLocalTests (aCutoff M n omega.1) (nativeBox n 1 z)
      epsilon p A sigma eps epsH massFraction clock G Pairs →
    GoodCubeV5RobustHarmonicOscillation (aCutoff M n omega.1) (nativeBox n 1 z)
      epsilon eps0 Pfam →
    GoodCubeFiniteLocalTests (aAnchored M omega)
      p A sigma eps epsH massFraction clock G Pairs ∧
      LocalHarmonicOscillation (aAnchored M omega) eps0 Pfam

/-- The complete deterministic replacement transfer. -/
theorem goodCubeAnchoredTestTransferAll (d : ℕ) : GoodCubeAnchoredTestTransferAll d := by
  intro eps1 epsilon heps1 hepsilon _hhalf hbudget M n z omega E0 hgood
    p A sigma eps epsH massFraction eps0 clock G Pairs Pfam hinside hpairs hpfam htests hosc
  have htheta := goodCubeV5_anchored_ratio_admissible M omega n z heps1.le hepsilon
    hbudget E0 hgood
  have hab : EqOn (fun x => aCutoff M n omega.1 x *
      (aAnchored M omega x / aCutoff M n omega.1 x)) (aAnchored M omega)
      (nativeBox n 1 z) := by
    intro x _
    field_simp [(aCutoff_pos M n omega.1 x).ne']
  exact ⟨goodCubeV5RobustFiniteLocalTests_of_eqOn htests htheta hab hinside hpairs,
    goodCubeV5RobustHarmonicOscillation_of_eqOn hosc htheta hab hpfam⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
