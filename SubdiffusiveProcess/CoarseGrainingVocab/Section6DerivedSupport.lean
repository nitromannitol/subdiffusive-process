module

public import SubdiffusiveProcess.Section6.Defs.AffineMinimizers
public import SubdiffusiveProcess.Section6.Defs.AnchoredCutoff
public import SubdiffusiveProcess.Section6.Defs.CoefficientAt
public import SubdiffusiveProcess.Section6.Defs.CoefficientSigma
public import SubdiffusiveProcess.Section6.Defs.Excess
public import SubdiffusiveProcess.Section6.Defs.FractionalInfinityNormOn
public import SubdiffusiveProcess.Section6.Defs.FractionalSeminormOn
public import SubdiffusiveProcess.Section6.Defs.GammaReg
public import SubdiffusiveProcess.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Section6.Defs.H2DatumNorm
public import SubdiffusiveProcess.Section6.Defs.HolderRegularityConclusions
public import SubdiffusiveProcess.Section6.Defs.OrdinaryVectorHMinusOne
public import SubdiffusiveProcess.Section6.Defs.RegularityMinimalScale
public import SubdiffusiveProcess.Section6.Defs.RescaledCutoffCoefficient
public import SubdiffusiveProcess.Section6.Defs.TruncatedCube

@[expose] public section

/-!
# Derived mechanical support for the section 6 frozen surface
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Literal `σ(A)`-measurability, without ambient completion. -/
def CoefficientMeasurable {d : ℕ} {Ω : Type*} (A : Ω → Vec d → ℝ)
    (X : Ω → ℝ) : Prop :=
  @Measurable Ω ℝ (coefficientSigma A) (borel ℝ) X

/-- Finiteness of the normalized fractional seminorm on a window. -/
def MemFractionalOn {d : ℕ} (W : Set (Vec d)) (s : ℝ)
    (f : Vec d → Vec d) : Prop :=
  fractionalSeminormOn W s f ≠ ⊤

/-- A scale-`m-j` cube lying in the concentric middle half. -/
def IsMiddleHalfSubcube {d : ℕ} (m : ℤ) (z : Vec d) (j : ℕ)
    (B' : Set (Vec d)) : Prop :=
  ∃ z' : Vec d, B' = translatedCube d (m - j) z' ∧
    ∀ x ∈ B', ‖x - z‖ ≤ (3 : ℝ) ^ m / 4

/-! ## Density assembly for intersections of good events -/

/-- Empirical density of a family of events on the integer interval
`{m₀, …, m₀ + K}`. -/
def eventIndicator {Ω : Type*} (E : Set Ω) (ω : Ω) : ℝ :=
  if ω ∈ E then 1 else 0

noncomputable def intervalEventDensity {Ω : Type*} (E : ℕ → Set Ω)
    (m0 K : ℕ) (ω : Ω) : ℝ :=
  (∑ m ∈ Finset.Icc m0 (m0 + K), eventIndicator (E m) ω) / (K + 1)

/-- If an intersection of three event families has density at most `1-θ`,
then one of the three complementary families has density at least `θ/3`.
This is the deterministic union-bound assembly in the printed proof of
`p.density.of.good.scales`. -/
theorem le_one_sub_of_inter_three_imp_bad_density
    {Ω : Type*} (A B C : ℕ → Set Ω) (m0 K : ℕ) (theta : ℝ) (ω : Ω)
    (hgood : intervalEventDensity (fun m => A m ∩ B m ∩ C m) m0 K ω ≤ 1 - theta) :
    theta / 3 ≤ intervalEventDensity (fun m => (A m)ᶜ) m0 K ω ∨
      theta / 3 ≤ intervalEventDensity (fun m => (B m)ᶜ) m0 K ω ∨
      theta / 3 ≤ intervalEventDensity (fun m => (C m)ᶜ) m0 K ω := by
  classical
  let I := Finset.Icc m0 (m0 + K)
  let g : ℕ → ℝ := fun m => eventIndicator (A m ∩ B m ∩ C m) ω
  let ba : ℕ → ℝ := fun m => eventIndicator (A m)ᶜ ω
  let bb : ℕ → ℝ := fun m => eventIndicator (B m)ᶜ ω
  let bc : ℕ → ℝ := fun m => eventIndicator (C m)ᶜ ω
  have hpoint (m : ℕ) : 1 ≤ g m + ba m + bb m + bc m := by
    by_cases hA : ω ∈ A m <;> by_cases hB : ω ∈ B m <;>
      by_cases hC : ω ∈ C m <;>
      simp [g, ba, bb, bc, eventIndicator, hA, hB, hC]
  have hsum : (I.card : ℝ) ≤
      ∑ m ∈ I, g m + ∑ m ∈ I, ba m + ∑ m ∈ I, bb m + ∑ m ∈ I, bc m := by
    calc
      (I.card : ℝ) = ∑ _m ∈ I, (1 : ℝ) := by simp
      _ ≤ ∑ m ∈ I, (g m + ba m + bb m + bc m) :=
        Finset.sum_le_sum fun m _ => hpoint m
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hcard : (I.card : ℝ) = (K : ℝ) + 1 := by
    dsimp [I]
    rw [Nat.card_Icc]
    norm_cast
    omega
  have hden : 0 < (K : ℝ) + 1 := by positivity
  have hnormalized : 1 ≤
      (∑ m ∈ I, g m) / ((K : ℝ) + 1) +
      (∑ m ∈ I, ba m) / ((K : ℝ) + 1) +
      (∑ m ∈ I, bb m) / ((K : ℝ) + 1) +
      (∑ m ∈ I, bc m) / ((K : ℝ) + 1) := by
    calc
      1 = (I.card : ℝ) / ((K : ℝ) + 1) := by rw [hcard]; field_simp
      _ ≤ (∑ m ∈ I, g m + ∑ m ∈ I, ba m +
          ∑ m ∈ I, bb m + ∑ m ∈ I, bc m) / ((K : ℝ) + 1) :=
        (div_le_div_iff_of_pos_right hden).2 hsum
      _ = _ := by ring
  have hgood' : (∑ m ∈ I, g m) / ((K : ℝ) + 1) ≤ 1 - theta := by
    simpa only [intervalEventDensity, I, g, Nat.cast_add, Nat.cast_one] using hgood
  have hbad : theta ≤
      (∑ m ∈ I, ba m) / ((K : ℝ) + 1) +
      (∑ m ∈ I, bb m) / ((K : ℝ) + 1) +
      (∑ m ∈ I, bc m) / ((K : ℝ) + 1) := by
    linarith only [hnormalized, hgood']
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨hba, hbb, hbc⟩
  have hba' : (∑ m ∈ I, ba m) / ((K : ℝ) + 1) < theta / 3 := by
    simpa only [intervalEventDensity, I, ba, Nat.cast_add, Nat.cast_one] using hba
  have hbb' : (∑ m ∈ I, bb m) / ((K : ℝ) + 1) < theta / 3 := by
    simpa only [intervalEventDensity, I, bb, Nat.cast_add, Nat.cast_one] using hbb
  have hbc' : (∑ m ∈ I, bc m) / ((K : ℝ) + 1) < theta / 3 := by
    simpa only [intervalEventDensity, I, bc, Nat.cast_add, Nat.cast_one] using hbc
  linarith only [hbad, hba', hbb', hbc']

/-- Measure-level union bound corresponding to
`le_one_sub_of_inter_three_imp_bad_density`. -/
theorem measure_inter_three_density_failure_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B C : ℕ → Set Ω) (m0 K : ℕ) (theta : ℝ) :
    μ {ω | intervalEventDensity (fun m => A m ∩ B m ∩ C m) m0 K ω ≤ 1 - theta} ≤
      μ {ω | theta / 3 ≤ intervalEventDensity (fun m => (A m)ᶜ) m0 K ω} +
      μ {ω | theta / 3 ≤ intervalEventDensity (fun m => (B m)ᶜ) m0 K ω} +
      μ {ω | theta / 3 ≤ intervalEventDensity (fun m => (C m)ᶜ) m0 K ω} := by
  let EA := {ω | theta / 3 ≤ intervalEventDensity (fun m => (A m)ᶜ) m0 K ω}
  let EB := {ω | theta / 3 ≤ intervalEventDensity (fun m => (B m)ᶜ) m0 K ω}
  let EC := {ω | theta / 3 ≤ intervalEventDensity (fun m => (C m)ᶜ) m0 K ω}
  calc
    μ {ω | intervalEventDensity (fun m => A m ∩ B m ∩ C m) m0 K ω ≤ 1 - theta} ≤
        μ (EA ∪ EB ∪ EC) := by
      apply measure_mono
      intro ω hω
      rcases le_one_sub_of_inter_three_imp_bad_density A B C m0 K theta ω hω with
        hA | hB | hC
      · exact Or.inl (Or.inl hA)
      · exact Or.inl (Or.inr hB)
      · exact Or.inr hC
    _ ≤ μ EA + μ EB + μ EC := by
      exact (measure_union_le (EA ∪ EB) EC).trans
        (add_le_add (measure_union_le EA EB) le_rfl)

end

end SubdiffusiveProcess.CoarseGrainingVocab
