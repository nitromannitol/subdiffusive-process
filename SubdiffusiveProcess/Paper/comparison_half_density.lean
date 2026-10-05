module

public import SubdiffusiveProcess.ResponseMoments.UpperDensity
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set _root_.SubdiffusiveProcess.ResponseMoments
open scoped Topology BigOperators

namespace SubdiffusiveProcess.Paper



theorem comparison_half_density
    (V : Type) [AddCommGroup V] [Module ℝ V]
    (LE LF : ℕ → QuadraticForm ℝ V)
    (affine : Submodule ℝ V)
    (m M : ℝ) (_hmM : m ≤ M)
    (H1 : ℕ) (_hH1 : 0 < H1)
    (ck : ℕ → ℝ) (hck : ∀ k, m ≤ ck k ∧ ck k ≤ M)
    (good : ℕ → Prop)
    (hLE : ∀ k b, 0 ≤ LE k b)
    (horder : ∀ k b, m * LE k b ≤ LF k b ∧ LF k b ≤ M * LE k b)
    (hsaving : ∀ k, good k → ∀ ell ∈ affine,
      |LF k ell - ck k * LE k ell| ≤ (1/8 : ℝ) * (M-m) * LE k ell) :
    let U := fun n => ck (H1*n) ≤ (m+M)/2
    let Vlevels := fun n => ¬ U n
    let Delta := M-m
    let B := fun k b => M * LE k b - LF k b
    ((1/2 : ℝ) ≤ upperDensity U ∨ (1/2 : ℝ) ≤ upperDensity Vlevels) ∧
    (∀ n, U n → good (H1*n) → ∀ ell ∈ affine,
      (M - ck (H1*n) - (1/8 : ℝ)*Delta) * LE (H1*n) ell ≤ B (H1*n) ell ∧
      (3/8 : ℝ)*Delta*LE (H1*n) ell ≤
        (M - ck (H1*n) - (1/8 : ℝ)*Delta) * LE (H1*n) ell) ∧
    (∀ k b, 0 ≤ B k b ∧ B k b ≤ Delta * LE k b) := by
  classical
  dsimp
  constructor
  · by_cases hU : (1 / 2 : ℝ) ≤
        upperDensity (fun n => ck (H1 * n) ≤ (m + M) / 2)
    · exact Or.inl hU
    · right
      by_contra hV
      have hU_lt : upperDensity (fun n => ck (H1 * n) ≤ (m + M) / 2) <
          (1 / 2 : ℝ) := lt_of_not_ge hU
      have hV_lt : upperDensity (fun n => ¬ ck (H1 * n) ≤ (m + M) / 2) <
          (1 / 2 : ℝ) := lt_of_not_ge hV
      have hU_ev : ∀ᶠ J : ℕ in atTop,
          (levelCount (fun n => ck (H1 * n) ≤ (m + M) / 2) J : ℝ) / (J : ℝ) <
            (1 / 2 : ℝ) :=
        eventually_lt_of_limsup_lt hU_lt
          (upperDensity_bddUnder (fun n => ck (H1 * n) ≤ (m + M) / 2))
      have hV_ev : ∀ᶠ J : ℕ in atTop,
          (levelCount (fun n => ¬ ck (H1 * n) ≤ (m + M) / 2) J : ℝ) / (J : ℝ) <
            (1 / 2 : ℝ) :=
        eventually_lt_of_limsup_lt hV_lt
          (upperDensity_bddUnder (fun n => ¬ ck (H1 * n) ≤ (m + M) / 2))
      have hJ_ev : ∀ᶠ J : ℕ in atTop, 1 ≤ J :=
        eventually_atTop.2 ⟨1, fun J hJ => hJ⟩
      rcases eventually_atTop.1 hU_ev with ⟨JU, hU_ev'⟩
      rcases eventually_atTop.1 hV_ev with ⟨JV, hV_ev'⟩
      rcases eventually_atTop.1 hJ_ev with ⟨J1, hJ_ev'⟩
      let J := max JU (max JV J1)
      have hJUJ : JU ≤ J := le_max_left _ _
      have hJVJ : JV ≤ J :=
        (le_max_left _ _).trans (le_max_right _ _)
      have hJ1J : J1 ≤ J :=
        (le_max_right _ _).trans (le_max_right _ _)
      have hUJ := hU_ev' J hJUJ
      have hVJ := hV_ev' J hJVJ
      have hJ1 := hJ_ev' J hJ1J
      have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ1
      have hcovNat : J ≤
          levelCount (fun n => ck (H1 * n) ≤ (m + M) / 2) J +
            levelCount (fun n => ¬ ck (H1 * n) ≤ (m + M) / 2) J := by
        have hcover := levelCount_cover
          (fun n => ck (H1 * n) ≤ (m + M) / 2)
          (fun n => ¬ ck (H1 * n) ≤ (m + M) / 2)
          (fun _ : ℕ => False)
          (by
            intro n hnU hnV
            exact hnV hnU)
          J
        simpa [levelCount] using hcover
      have hcov : (J : ℝ) ≤
          (levelCount (fun n => ck (H1 * n) ≤ (m + M) / 2) J : ℝ) +
            (levelCount (fun n => ¬ ck (H1 * n) ≤ (m + M) / 2) J : ℝ) := by
        exact_mod_cast hcovNat
      have hU_count :
          (levelCount (fun n => ck (H1 * n) ≤ (m + M) / 2) J : ℝ) <
            (1 / 2 : ℝ) * (J : ℝ) := by
        exact (div_lt_iff₀ hJpos).mp hUJ
      have hV_count :
          (levelCount (fun n => ¬ ck (H1 * n) ≤ (m + M) / 2) J : ℝ) <
            (1 / 2 : ℝ) * (J : ℝ) := by
        exact (div_lt_iff₀ hJpos).mp hVJ
      nlinarith
  constructor
  · intro n hnU hgood ell hell
    have hsave := hsaving (H1 * n) hgood ell hell
    have hsave' : LF (H1 * n) ell - ck (H1 * n) * LE (H1 * n) ell ≤
        (1 / 8 : ℝ) * (M - m) * LE (H1 * n) ell :=
      (abs_le.mp hsave).2
    constructor
    · nlinarith
    · have hcoef :
          (3 / 8 : ℝ) * (M - m) ≤
            M - ck (H1 * n) - (1 / 8 : ℝ) * (M - m) := by
        have hck' := (hck (H1 * n)).2
        nlinarith
      exact mul_le_mul_of_nonneg_right hcoef (hLE (H1 * n) ell)
  · intro k b
    constructor <;> nlinarith [horder k b]

end SubdiffusiveProcess.Paper
