module

public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Lane3.Forms
public import SubdiffusiveProcess.Lane3.DiffCauchySchwarz
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

namespace Paper

lemma aux_neumann_load_sup_difference_reverse_triangle
    (V : Type) [AddCommGroup V] [Module ℝ V]
    (S : Submodule ℝ V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y : V, x ∈ S → y ∈ S → B x y = B y x)
    (hnonneg : ∀ x : V, x ∈ S → 0 ≤ B x x)
    (a b : V) (ha : a ∈ S) (hb : b ∈ S) :
    |Real.sqrt (B a a) - Real.sqrt (B b b)| ≤
      Real.sqrt (B (a - b) (a - b)) := by
  let B' : S → S → ℝ := fun x y => B x.1 y.1
  have hsymm' : ∀ x y : S, B' x y = B' y x := by
    intro x y
    change B x.1 y.1 = B y.1 x.1
    exact hsymm x.1 y.1 x.2 y.2
  have hadd' : ∀ x y z : S, B' (x + y) z = B' x z + B' y z := by
    intro x y z
    change B (x.1 + y.1) z.1 = B x.1 z.1 + B y.1 z.1
    simp only [map_add, LinearMap.add_apply]
  have hsmul' : ∀ (c : ℝ) (x y : S), B' (c • x) y = c * B' x y := by
    intro c x y
    change B (c • x.1) y.1 = c * B x.1 y.1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hnonneg' : ∀ x : S, 0 ≤ B' x x := by
    intro x
    change 0 ≤ B x.1 x.1
    exact hnonneg x.1 x.2
  have hcs :
      |B a b| ≤ Real.sqrt (B a a * B b b) := by
    have h := SubdiffusiveProcess.Lane3.abs_bilin_le_sqrt
      (B := B') hsymm' hadd' hsmul' hnonneg'
      (⟨a, ha⟩ : S) (⟨b, hb⟩ : S)
    simpa [B'] using h
  have hcross : B a b ≤ Real.sqrt (B a a * B b b) :=
    (abs_le.mp hcs).2
  have hrootmul :
      Real.sqrt (B a a * B b b) =
        Real.sqrt (B a a) * Real.sqrt (B b b) :=
    Real.sqrt_mul (hnonneg a ha) _
  rw [hrootmul] at hcross
  have hdiff :
      B (a - b) (a - b) = B a a - 2 * B a b + B b b := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hsymm b a hb ha]
    ring
  have henergy : 0 ≤ B (a - b) (a - b) :=
    hnonneg (a - b) (S.sub_mem ha hb)
  have hA : 0 ≤ B a a := hnonneg a ha
  have hB : 0 ≤ B b b := hnonneg b hb
  have hsqA : (Real.sqrt (B a a)) ^ 2 = B a a := Real.sq_sqrt hA
  have hsqB : (Real.sqrt (B b b)) ^ 2 = B b b := Real.sq_sqrt hB
  have hsquares :
      (Real.sqrt (B a a) - Real.sqrt (B b b)) ^ 2 ≤
        B (a - b) (a - b) := by
    rw [hdiff]
    nlinarith [hcross, hsqA, hsqB]
  have hsqroot :
      (Real.sqrt (B (a - b) (a - b))) ^ 2 = B (a - b) (a - b) :=
    Real.sq_sqrt henergy
  have hsqabs :
      |Real.sqrt (B a a) - Real.sqrt (B b b)| ^ 2 =
        (Real.sqrt (B a a) - Real.sqrt (B b b)) ^ 2 :=
    sq_abs _
  have hqnonneg :
      0 ≤ |Real.sqrt (B a a) - Real.sqrt (B b b)| := abs_nonneg _
  have hsnonneg : 0 ≤ Real.sqrt (B (a - b) (a - b)) := Real.sqrt_nonneg _
  by_contra hnot
  have hgt : Real.sqrt (B (a - b) (a - b)) <
      |Real.sqrt (B a a) - Real.sqrt (B b b)| := lt_of_not_ge hnot
  have hqpos : 0 < |Real.sqrt (B a a) - Real.sqrt (B b b)| :=
    lt_of_le_of_lt hsnonneg hgt
  have hprod : 0 <
      (|Real.sqrt (B a a) - Real.sqrt (B b b)| -
          Real.sqrt (B (a - b) (a - b))) *
        (|Real.sqrt (B a a) - Real.sqrt (B b b)| +
          Real.sqrt (B (a - b) (a - b))) := by
    exact mul_pos (sub_pos.mpr hgt)
      (add_pos_of_pos_of_nonneg hqpos hsnonneg)
  nlinarith [hsquares, hsqroot, hsqabs, hprod]



theorem neumann_load_sup_difference
    (Om Qs Vt : Type) [AddCommGroup Vt] [Module ℝ Vt]
    (meanZero : Qs → Submodule ℝ Vt)
    (E : ℕ → Qs → Om → Vt →ₗ[ℝ] Vt →ₗ[ℝ] ℝ)
    (hsymm : ∀ (N : ℕ) (Q : Qs) (omega : Om) (u v : Vt),
      u ∈ meanZero Q → v ∈ meanZero Q → E N Q omega u v = E N Q omega v u)
    (hnonneg : ∀ (N : ℕ) (Q : Qs) (omega : Om) (v : Vt),
      v ∈ meanZero Q → 0 ≤ E N Q omega v v)
    (load : Qs → Vt →ₗ[ℝ] ℝ) (loadSm : Qs → ℝ → Vt →ₗ[ℝ] ℝ)
    (u : ℕ → Qs → Om → Vt) (uh : ℕ → Qs → Om → ℝ → Vt)
    (hu : ∀ (N : ℕ) (Q : Qs) (omega : Om), u N Q omega ∈ meanZero Q)
    (huh : ∀ (N : ℕ) (Q : Qs) (omega : Om) (h : ℝ),
      0 < h → h < 1 / 8 → uh N Q omega h ∈ meanZero Q)
    (hRiesz : ∀ (N : ℕ) (Q : Qs) (omega : Om) (v : Vt),
      v ∈ meanZero Q → E N Q omega (u N Q omega) v = load Q v)
    (hRieszh : ∀ (N : ℕ) (Q : Qs) (omega : Om) (h : ℝ),
      0 < h → h < 1 / 8 → ∀ v ∈ meanZero Q,
        E N Q omega (uh N Q omega h) v = loadSm Q h v)
    (YN : ℕ → Qs → Om → ℝ) (YNh : ℕ → Qs → Om → ℝ → ℝ)
    (hYN : ∀ (N : ℕ) (Q : Qs) (omega : Om),
      YN N Q omega = E N Q omega (u N Q omega) (u N Q omega))
    (hYNh : ∀ (N : ℕ) (Q : Qs) (omega : Om) (h : ℝ),
      0 < h → h < 1 / 8 →
        YNh N Q omega h = E N Q omega (uh N Q omega h) (uh N Q omega h))
    (KN : ℕ → Qs → Om → ℝ)
    (hKN : ∀ (N : ℕ) (Q : Qs) (omega : Om), 0 < KN N Q omega)
    (Cc : ℝ) (hCc : 0 < Cc)
    (hsmooth : ∀ (N : ℕ) (Q : Qs) (omega : Om) (h : ℝ),
      0 < h → h < 1 / 8 → ∀ v ∈ meanZero Q,
        |load Q v - loadSm Q h v| ≤
          Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) *
            Real.sqrt (E N Q omega v v)) :
    ∀ (N : ℕ) (Q : Qs) (omega : Om) (h : ℝ), 0 < h → h < 1 / 8 →
      |YN N Q omega - YNh N Q omega h| ≤
        Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) *
          (Real.sqrt (YN N Q omega) + Real.sqrt (YNh N Q omega h)) := by
  intro N Q omega h hh0 hh8
  let a : Vt := u N Q omega
  let b : Vt := uh N Q omega h
  have ha : a ∈ meanZero Q := by
    simpa [a] using hu N Q omega
  have hb : b ∈ meanZero Q := by
    simpa [b] using huh N Q omega h hh0 hh8
  have hw : a - b ∈ meanZero Q := (meanZero Q).sub_mem ha hb
  have hR1 : E N Q omega a (a - b) = load Q (a - b) := by
    simpa [a] using hRiesz N Q omega (a - b) hw
  have hR2 : E N Q omega b (a - b) = loadSm Q h (a - b) := by
    simpa [b] using hRieszh N Q omega h hh0 hh8 (a - b) hw
  have henergy_eq :
      E N Q omega (a - b) (a - b) =
        load Q (a - b) - loadSm Q h (a - b) := by
    calc
      E N Q omega (a - b) (a - b) =
          (E N Q omega a - E N Q omega b) (a - b) := by
            exact congrArg (fun f : Vt →ₗ[ℝ] ℝ => f (a - b))
              ((E N Q omega).map_sub a b)
      _ = E N Q omega a (a - b) - E N Q omega b (a - b) := by
            rw [LinearMap.sub_apply]
      _ = load Q (a - b) - loadSm Q h (a - b) := by rw [hR1, hR2]
  have henergy_nonneg : 0 ≤ E N Q omega (a - b) (a - b) :=
    hnonneg N Q omega (a - b) hw
  have hload_energy :
      E N Q omega (a - b) (a - b) ≤
        Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) *
          Real.sqrt (E N Q omega (a - b) (a - b)) := by
    calc
      E N Q omega (a - b) (a - b) =
          |E N Q omega (a - b) (a - b)| :=
            (abs_of_nonneg henergy_nonneg).symm
      _ = |load Q (a - b) - loadSm Q h (a - b)| := by rw [henergy_eq]
      _ ≤ Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) *
          Real.sqrt (E N Q omega (a - b) (a - b)) :=
        hsmooth N Q omega h hh0 hh8 (a - b) hw
  have hfactor_nonneg :
      0 ≤ Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) := by
    positivity
  have hsqrt_energy :
      Real.sqrt (E N Q omega (a - b) (a - b)) ≤
        Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) := by
    by_cases hz : Real.sqrt (E N Q omega (a - b) (a - b)) = 0
    · rw [hz]
      exact hfactor_nonneg
    · have hzpos : 0 < Real.sqrt (E N Q omega (a - b) (a - b)) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      have hquad :
          Real.sqrt (E N Q omega (a - b) (a - b)) *
              Real.sqrt (E N Q omega (a - b) (a - b)) ≤
            (Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega)) *
              Real.sqrt (E N Q omega (a - b) (a - b)) := by
        nlinarith [hload_energy,
          Real.sq_sqrt henergy_nonneg]
      exact le_of_mul_le_mul_right hquad hzpos
  have hrootdiff :
      |Real.sqrt (E N Q omega a a) - Real.sqrt (E N Q omega b b)| ≤
        Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) := by
    have htri := aux_neumann_load_sup_difference_reverse_triangle Vt
      (meanZero Q) (E N Q omega)
      (fun x y hx hy => hsymm N Q omega x y hx hy)
      (fun x hx => hnonneg N Q omega x hx) a b ha hb
    exact htri.trans hsqrt_energy
  have hresponse_diff :
      |Real.sqrt (YN N Q omega) - Real.sqrt (YNh N Q omega h)| ≤
        Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) := by
    simpa [a, b, hYN N Q omega, hYNh N Q omega h hh0 hh8] using hrootdiff
  have hsum_nonneg :
      0 ≤ Real.sqrt (YN N Q omega) + Real.sqrt (YNh N Q omega h) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hresponse_diff hsum_nonneg
  have hYN_nonneg : 0 ≤ YN N Q omega := by
    rw [hYN N Q omega]
    exact hnonneg N Q omega a ha
  have hYNh_nonneg : 0 ≤ YNh N Q omega h := by
    rw [hYNh N Q omega h hh0 hh8]
    exact hnonneg N Q omega b hb
  have hfactor :
      |YN N Q omega - YNh N Q omega h| =
        |Real.sqrt (YN N Q omega) - Real.sqrt (YNh N Q omega h)| *
          (Real.sqrt (YN N Q omega) + Real.sqrt (YNh N Q omega h)) := by
    have hprod :
        (Real.sqrt (YN N Q omega) - Real.sqrt (YNh N Q omega h)) *
            (Real.sqrt (YN N Q omega) + Real.sqrt (YNh N Q omega h)) =
          YN N Q omega - YNh N Q omega h := by
      nlinarith [Real.sq_sqrt hYN_nonneg, Real.sq_sqrt hYNh_nonneg]
    rw [← hprod, abs_mul, abs_of_nonneg hsum_nonneg]
  rw [hfactor]
  exact hmul

end Paper
