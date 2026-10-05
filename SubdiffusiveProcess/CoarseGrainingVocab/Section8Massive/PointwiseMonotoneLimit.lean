module

public import Mathlib.MeasureTheory.Function.AEMeasurableSequence
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-!
# Pointwise monotone representatives of an a.e. monotone sequence

Sobolev solutions carry arbitrary representatives.  This file turns an a.e.
nonnegative, bounded, monotone real sequence into pointwise monotone bounded
representatives by clipping and recursive finite maxima.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Clip a real-valued function to `[0,C]`. -/
def clipToNonnegativeInterval (C : ℝ) (f : X → ℝ) : X → ℝ :=
  fun x ↦ max 0 (min C (f x))

/-- Recursive finite maxima of clipped representatives. -/
def monotoneModification (C : ℝ) (f : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => clipToNonnegativeInterval C (f 0)
  | n + 1 => fun x ↦ max (monotoneModification C f n x)
      (clipToNonnegativeInterval C (f (n + 1)) x)

omit [MeasurableSpace X] in
theorem monotone_monotoneModification (C : ℝ) (f : ℕ → X → ℝ) (x : X) :
    Monotone fun n ↦ monotoneModification C f n x := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

omit [MeasurableSpace X] in
theorem monotoneModification_nonneg {C : ℝ} (_hC : 0 ≤ C)
    (f : ℕ → X → ℝ) (n : ℕ) (x : X) :
    0 ≤ monotoneModification C f n x := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih => exact ih.trans (le_max_left _ _)

omit [MeasurableSpace X] in
theorem monotoneModification_le {C : ℝ} (hC : 0 ≤ C)
    (f : ℕ → X → ℝ) (n : ℕ) (x : X) :
    monotoneModification C f n x ≤ C := by
  induction n with
  | zero =>
      exact max_le hC (min_le_left _ _)
  | succ n ih =>
      exact max_le ih (max_le hC (min_le_left _ _))

/-- The recursive finite-max modification agrees a.e. with every member of an
a.e. nonnegative, bounded, monotone sequence. -/
theorem monotoneModification_ae_eq
    (μ : Measure X) {C : ℝ} (_hC : 0 ≤ C) (f : ℕ → X → ℝ)
    (hnonneg : ∀ n, 0 ≤ᵐ[μ] f n)
    (hle : ∀ n, f n ≤ᵐ[μ] fun _ ↦ C)
    (hmono : ∀ n, f n ≤ᵐ[μ] f (n + 1)) :
    ∀ n, monotoneModification C f n =ᵐ[μ] f n := by
  intro n
  induction n with
  | zero =>
      filter_upwards [hnonneg 0, hle 0] with x hx0 hxC
      have hx0' : (0 : ℝ) ≤ f 0 x := by simpa using hx0
      simp only [monotoneModification, clipToNonnegativeInterval]
      rw [min_eq_right hxC, max_eq_right hx0']
  | succ n ih =>
      filter_upwards [ih, hnonneg (n + 1), hle (n + 1), hmono n]
        with x hprev hx0 hxC hstep
      have hx0' : (0 : ℝ) ≤ f (n + 1) x := by simpa using hx0
      simp only [monotoneModification, clipToNonnegativeInterval]
      rw [hprev, min_eq_right hxC, max_eq_right hx0', max_eq_right hstep]

/-- Pointwise monotone representatives with their pointwise supremum and
convergence to it. -/
theorem exists_pointwise_monotone_limit
    (μ : Measure X) {C : ℝ} (hC : 0 ≤ C) (f : ℕ → X → ℝ)
    (hnonneg : ∀ n, 0 ≤ᵐ[μ] f n)
    (hle : ∀ n, f n ≤ᵐ[μ] fun _ ↦ C)
    (hmono : ∀ n, f n ≤ᵐ[μ] f (n + 1)) :
    ∃ v : ℕ → X → ℝ, ∃ u : X → ℝ,
      (∀ n, v n =ᵐ[μ] f n) ∧
      (∀ x, Monotone fun n ↦ v n x) ∧
      (∀ n x, 0 ≤ v n x ∧ v n x ≤ C) ∧
      (∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x))) := by
  let v := monotoneModification C f
  let u : X → ℝ := fun x ↦ ⨆ n, v n x
  refine ⟨v, u, monotoneModification_ae_eq μ hC f hnonneg hle hmono,
    fun x ↦ monotone_monotoneModification C f x, ?_, ?_⟩
  · intro n x
    exact ⟨monotoneModification_nonneg hC f n x,
      monotoneModification_le hC f n x⟩
  · intro x
    apply tendsto_atTop_ciSup (monotone_monotoneModification C f x)
    exact ⟨C, fun _ ⟨n, hn⟩ ↦ hn ▸ monotoneModification_le hC f n x⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
