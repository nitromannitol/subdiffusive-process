module

public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.ResponseMoments.Forms
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.neumann_load_sup_difference

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

/--
- Form domain: meanZero Q; symmetry and positivity are restricted to that domain, not all L2.
- Riesz representatives: hRiesz and hRieszh pin the solutions to the two loads; hYN and hYNh pin the responses to their energies. The source is the definitions in lem_neumann_error.
- Load estimate: hsmooth is lem_load, eq:mfd-7, composed with lem_coercivity, eq:mfd-1; the factor sqrt(KN) is in this estimate.
- Energy at the maximizer equals its response by the Riesz definition; no unsupported energy ≤ KN times response assumption is used.
- Constants: Cc precedes N, Q, omega, h in the conclusion; h lies in the paper's 0<h<1/8 range.
- Conclusion: the two-term pointwise load estimate; neumann_load_sup_difference supplies the symmetric estimate to absorb; no conclusion is a hypothesis.
-/
theorem neumann_load_pointwise
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
          (4 * Cc + Cc ^ 2) * Real.sqrt (KN N Q omega) * h ^ ((1 : ℝ) / 4) *
          Real.sqrt (YN N Q omega) +
        (4 * Cc + Cc ^ 2) * KN N Q omega * h ^ ((1 : ℝ) / 2) := by
  intro N Q omega h hh0 hh8
  have hY : 0 ≤ YN N Q omega := by
    rw [hYN N Q omega]
    exact hnonneg N Q omega _ (hu N Q omega)
  have hZh : 0 ≤ YNh N Q omega h := by
    rw [hYNh N Q omega h hh0 hh8]
    exact hnonneg N Q omega _ (huh N Q omega h hh0 hh8)
  have hDnn : 0 ≤ |YN N Q omega - YNh N Q omega h| := abs_nonneg _
  have hsup := neumann_load_sup_difference Om Qs Vt meanZero E hsymm hnonneg load loadSm u uh
    hu huh hRiesz hRieszh YN YNh hYN hYNh KN hKN Cc hCc hsmooth N Q omega h hh0 hh8
  have hZh_le : YNh N Q omega h ≤ YN N Q omega + |YN N Q omega - YNh N Q omega h| := by
    have h1 : YNh N Q omega h - YN N Q omega ≤ |YNh N Q omega h - YN N Q omega| := le_abs_self _
    rw [abs_sub_comm] at h1
    linarith
  have hsqrtZh : Real.sqrt (YNh N Q omega h) ≤
      Real.sqrt (YN N Q omega) + Real.sqrt (|YN N Q omega - YNh N Q omega h|) := by
    have hle : YN N Q omega + |YN N Q omega - YNh N Q omega h| ≤
        (Real.sqrt (YN N Q omega) + Real.sqrt (|YN N Q omega - YNh N Q omega h|)) ^ 2 := by
      rw [add_sq, Real.sq_sqrt hY, Real.sq_sqrt hDnn]
      nlinarith [Real.sqrt_nonneg (YN N Q omega),
        Real.sqrt_nonneg (|YN N Q omega - YNh N Q omega h|)]
    calc Real.sqrt (YNh N Q omega h)
        ≤ Real.sqrt (YN N Q omega + |YN N Q omega - YNh N Q omega h|) := Real.sqrt_le_sqrt hZh_le
      _ ≤ Real.sqrt ((Real.sqrt (YN N Q omega) + Real.sqrt (|YN N Q omega - YNh N Q omega h|)) ^ 2) :=
            Real.sqrt_le_sqrt hle
      _ = Real.sqrt (YN N Q omega) + Real.sqrt (|YN N Q omega - YNh N Q omega h|) := by
          rw [Real.sqrt_sq_eq_abs,
            abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hA : 0 ≤ Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) := by positivity
  have hstep1 : |YN N Q omega - YNh N Q omega h| ≤
      Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) *
        (2 * Real.sqrt (YN N Q omega) + Real.sqrt (|YN N Q omega - YNh N Q omega h|)) := by
    have h1 := mul_le_mul_of_nonneg_left
      (add_le_add_left hsqrtZh (Real.sqrt (YN N Q omega))) hA
    nlinarith [hsup, h1]
  have hAMGM : Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega) *
        Real.sqrt (|YN N Q omega - YNh N Q omega h|) ≤
      |YN N Q omega - YNh N Q omega h| / 2 +
        (Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega)) ^ 2 / 2 := by
    have hsq := Real.sq_sqrt hDnn
    nlinarith [sq_nonneg (Real.sqrt (|YN N Q omega - YNh N Q omega h|) -
      Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega)), hsq]
  have hD_final : |YN N Q omega - YNh N Q omega h| ≤
      4 * (Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega)) * Real.sqrt (YN N Q omega) +
        (Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega)) ^ 2 := by
    nlinarith [hstep1, hAMGM]
  have hpow : (h ^ ((1 : ℝ) / 4)) ^ 2 = h ^ ((1 : ℝ) / 2) := by
    rw [sq, ← Real.rpow_add hh0]
    norm_num
  have hsqKN : Real.sqrt (KN N Q omega) ^ 2 = KN N Q omega :=
    Real.sq_sqrt (hKN N Q omega).le
  have ha : 0 ≤ h ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hh0.le _
  have hb : 0 ≤ Real.sqrt (KN N Q omega) := Real.sqrt_nonneg _
  have hc : 0 ≤ h ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hh0.le _
  have hd : 0 ≤ KN N Q omega := (hKN N Q omega).le
  have he : 0 ≤ Real.sqrt (YN N Q omega) := Real.sqrt_nonneg _
  have hs1 : 0 ≤ Cc ^ 2 * Real.sqrt (KN N Q omega) * h ^ ((1 : ℝ) / 4) *
      Real.sqrt (YN N Q omega) := by
    have hh := mul_nonneg (sq_nonneg Cc) (mul_nonneg hb (mul_nonneg ha he))
    linarith [hh]
  have hs2 : 0 ≤ 4 * Cc * KN N Q omega * h ^ ((1 : ℝ) / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCc.le) hd) hc
  have hs3 : 0 ≤ Cc ^ 2 * KN N Q omega * h ^ ((1 : ℝ) / 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg Cc) hd) hc
  have hsquare :
      (Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega)) ^ 2 =
        Cc ^ 2 * KN N Q omega * h ^ ((1 : ℝ) / 2) := by
    calc
      (Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega)) ^ 2 =
          Cc ^ 2 * (h ^ ((1 : ℝ) / 4)) ^ 2 * (Real.sqrt (KN N Q omega)) ^ 2 := by ring
      _ = Cc ^ 2 * KN N Q omega * h ^ ((1 : ℝ) / 2) := by rw [hpow, hsqKN]; ring
  have hmain : |YN N Q omega - YNh N Q omega h| ≤
      4 * Cc * Real.sqrt (KN N Q omega) * h ^ ((1 : ℝ) / 4) *
          Real.sqrt (YN N Q omega) +
        Cc ^ 2 * KN N Q omega * h ^ ((1 : ℝ) / 2) := by
    calc
      |YN N Q omega - YNh N Q omega h| ≤
          4 * (Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega)) *
              Real.sqrt (YN N Q omega) +
            (Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (KN N Q omega)) ^ 2 := hD_final
      _ = 4 * Cc * Real.sqrt (KN N Q omega) * h ^ ((1 : ℝ) / 4) *
            Real.sqrt (YN N Q omega) +
          Cc ^ 2 * KN N Q omega * h ^ ((1 : ℝ) / 2) := by rw [hsquare]; ring
  nlinarith [hmain, hs1, hs2, hs3]

end SubdiffusiveProcess.Paper
