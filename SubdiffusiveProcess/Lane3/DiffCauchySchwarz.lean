module

public import SubdiffusiveProcess.Lane3.BilinearCS
public import Mathlib.Tactic

@[expose] public section

/-!
# The relative form of two candidate energies, Lemma `mfd:lem-diff`

`mfd:lem-diff`: with
`m Γ_E ≤ Γ_F ≤ M Γ_E` and `c ∈ [m, M]`, the relative measure
`Γ_D = Γ_F - c Γ_E` satisfies
`|Γ_D(u,v)|(B) ≤ Δ √(Γ_E(u)(B) Γ_E(v)(B))` with `Δ = M - m`.
The proof is matrix Cauchy--Schwarz applied to the two nonnegative
combinations `Δ Γ_E ± Γ_D`, exactly as in paper lines 3292-3297.
-/

open Real

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- From the squared Cauchy--Schwarz inequality to the absolute value. -/
theorem abs_bilin_le_sqrt {B : V → V → ℝ} (hsymm : ∀ u v, B u v = B v u)
    (hadd : ∀ u v w, B (u + v) w = B u w + B v w)
    (hsmul : ∀ (c : ℝ) (u v : V), B (c • u) v = c * B u v)
    (hnonneg : ∀ u, 0 ≤ B u u) (u v : V) :
    |B u v| ≤ Real.sqrt (B u u * B v v) := by
  have hsq := bilin_sq_le hsymm hadd hsmul hnonneg u v
  have hy : (0 : ℝ) ≤ B u u * B v v := mul_nonneg (hnonneg u) (hnonneg v)
  refine (Real.le_sqrt (abs_nonneg _) hy).mpr ?_
  rwa [sq_abs]

variable {X : Type*} [MeasurableSpace X]

theorem diff_measure_cauchy_schwarz (E F : LocalEnergy V X) (m M c : ℝ)
    (hmc : m ≤ c) (hcM : c ≤ M)
    (hlower : ∀ (w : V) (s : Set X), MeasurableSet s → m * E.gam w w s ≤ F.gam w w s)
    (hupper : ∀ (w : V) (s : Set X), MeasurableSet s → F.gam w w s ≤ M * E.gam w w s)
    (u v : V) (s : Set X) (hs : MeasurableSet s) :
    |LocalEnergy.diffGam c E F u v s| ≤
      (M - m) * Real.sqrt (E.gam u u s * E.gam v v s) := by
  classical
  set Del : ℝ := M - m with hDel
  set P : V → V → ℝ := fun w w' =>
    Del * E.gam w w' s + (F.gam w w' s - c * E.gam w w' s) with hP
  set N : V → V → ℝ := fun w w' =>
    Del * E.gam w w' s - (F.gam w w' s - c * E.gam w w' s) with hN
  have hEnn : ∀ w : V, 0 ≤ E.gam w w s := fun w => E.gam_nonneg w s
  have hPsymm : ∀ a b, P a b = P b a := by
    intro a b; simp only [hP, E.gam_symm a b s, F.gam_symm a b s]
  have hNsymm : ∀ a b, N a b = N b a := by
    intro a b; simp only [hN, E.gam_symm a b s, F.gam_symm a b s]
  have hPadd : ∀ a b w, P (a + b) w = P a w + P b w := by
    intro a b w; simp only [hP, E.gam_add_left, F.gam_add_left]; ring
  have hNadd : ∀ a b w, N (a + b) w = N a w + N b w := by
    intro a b w; simp only [hN, E.gam_add_left, F.gam_add_left]; ring
  have hPsmul : ∀ (r : ℝ) a b, P (r • a) b = r * P a b := by
    intro r a b; simp only [hP, E.gam_smul_left, F.gam_smul_left]; ring
  have hNsmul : ∀ (r : ℝ) a b, N (r • a) b = r * N a b := by
    intro r a b; simp only [hN, E.gam_smul_left, F.gam_smul_left]; ring
  have hPnn : ∀ w : V, 0 ≤ P w w := by
    intro w
    have h1 := hlower w s hs
    have h2 := hEnn w
    simp only [hP, hDel]
    nlinarith
  have hNnn : ∀ w : V, 0 ≤ N w w := by
    intro w
    have h1 := hupper w s hs
    have h2 := hEnn w
    simp only [hN, hDel]
    nlinarith
  have hPle : ∀ w : V, P w w ≤ 2 * Del * E.gam w w s := by
    intro w
    have h1 := hupper w s hs
    have h2 := hEnn w
    simp only [hP, hDel]
    nlinarith
  have hNle : ∀ w : V, N w w ≤ 2 * Del * E.gam w w s := by
    intro w
    have h1 := hlower w s hs
    have h2 := hEnn w
    simp only [hN, hDel]
    nlinarith
  have hPcs := abs_bilin_le_sqrt hPsymm hPadd hPsmul hPnn u v
  have hNcs := abs_bilin_le_sqrt hNsymm hNadd hNsmul hNnn u v
  have hd : 0 ≤ Del := by simp only [hDel]; linarith
  have hPNu : P u u + N u u = 2 * Del * E.gam u u s := by simp only [hP, hN]; ring
  have hPNv : P v v + N v v = 2 * Del * E.gam v v s := by simp only [hP, hN]; ring
  have hcs2 := sqrt_mul_add_sqrt_mul_le (hPnn u) (hNnn u) (hPnn v) (hNnn v)
  rw [hPNu, hPNv] at hcs2
  have hkey : Real.sqrt ((2 * Del * E.gam u u s) * (2 * Del * E.gam v v s)) =
      2 * Del * Real.sqrt (E.gam u u s * E.gam v v s) := by
    have hrw : (2 * Del * E.gam u u s) * (2 * Del * E.gam v v s) =
        (2 * Del) ^ 2 * (E.gam u u s * E.gam v v s) := by ring
    rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hkey] at hcs2
  have hsum : |P u v| + |N u v| ≤
      2 * Del * Real.sqrt (E.gam u u s * E.gam v v s) := by
    linarith [hPcs, hNcs, hcs2]
  have hDeq : LocalEnergy.diffGam c E F u v s = (P u v - N u v) / 2 := by
    simp only [hP, hN, LocalEnergy.diffGam]
    ring
  have habs : |P u v - N u v| ≤ |P u v| + |N u v| := by
    rcases abs_cases (P u v - N u v) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] <;> [skip; skip] <;>
      · rcases abs_cases (P u v) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          rcases abs_cases (N u v) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
          rw [h1, h2] <;> linarith
  rw [hDeq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hDel' : Del = M - m := hDel
  nlinarith [habs, hsum, Real.sqrt_nonneg (E.gam u u s * E.gam v v s)]


/-- The energy of the difference of the two minimizers, Lemma `mfd:lem-diff`,
`eq:mfd-27`, paper lines 3283-3285. -/
theorem minimizer_difference_energy_le (E F : LocalEnergy V X) (m M c : ℝ)
    (hm : 0 < m) (hmc : m ≤ c) (hcM : c ≤ M) (uE w : V)
    (hcoercive : m * E.form w w ≤ F.form w w)
    (heuler : F.form w w = -(F.form uE w - c * E.form uE w))
    (hCS : |F.form uE w - c * E.form uE w| ≤
      (M - m) * Real.sqrt (E.form uE uE * E.form w w)) :
    E.form w w ≤ ((M - m) / m) ^ 2 * E.form uE uE := by
  have hEu : 0 ≤ E.form uE uE := E.form_nonneg uE
  have hEw : 0 ≤ E.form w w := E.form_nonneg w
  have hsplit : Real.sqrt (E.form uE uE * E.form w w) =
      Real.sqrt (E.form uE uE) * Real.sqrt (E.form w w) := Real.sqrt_mul hEu _
  have hneg : -(F.form uE w - c * E.form uE w) ≤
      |F.form uE w - c * E.form uE w| := neg_le_abs _
  have hkey : m * E.form w w ≤
      (M - m) * (Real.sqrt (E.form uE uE) * Real.sqrt (E.form w w)) := by
    rw [← hsplit]
    calc m * E.form w w ≤ F.form w w := hcoercive
      _ = -(F.form uE w - c * E.form uE w) := heuler
      _ ≤ |F.form uE w - c * E.form uE w| := hneg
      _ ≤ (M - m) * Real.sqrt (E.form uE uE * E.form w w) := hCS
  have hy : Real.sqrt (E.form w w) ^ 2 = E.form w w := Real.sq_sqrt hEw
  have hx : Real.sqrt (E.form uE uE) ^ 2 = E.form uE uE := Real.sq_sqrt hEu
  have hynn : 0 ≤ Real.sqrt (E.form w w) := Real.sqrt_nonneg _
  have hxnn : 0 ≤ Real.sqrt (E.form uE uE) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hynn with hy0 | hy0
  · have : E.form w w = 0 := by rw [← hy, ← hy0]; ring
    rw [this]
    positivity
  · have hstep : m * Real.sqrt (E.form w w) ≤ (M - m) * Real.sqrt (E.form uE uE) := by
      have := hkey
      rw [← hy] at this
      nlinarith [this, hy0]
    have hdiv : Real.sqrt (E.form w w) ≤ (M - m) / m * Real.sqrt (E.form uE uE) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm]
      nlinarith [hstep]
    have hsq := mul_self_le_mul_self hynn hdiv
    rw [← hy, ← hx]
    nlinarith [hsq, hxnn]

/-- Harmonic replacement error, Lemma `mfd:lem-replace`, paper lines 3674-3702. -/
theorem harmonic_replacement_error_le (E : LocalEnergy V X) (u pr : V)
    (f2 nrm Kp hmesh s : ℝ) (hs : 0 < s) (hh : 0 < hmesh) (hK : 0 ≤ Kp)
    (hf2 : 0 ≤ f2) (hnrm : 0 ≤ nrm)
    (hload : E.form u pr = E.form pr pr)
    (hCS : E.form u pr ≤ f2 * nrm)
    (hpoin : nrm ^ 2 ≤ Kp * hmesh ^ (2 * s) * E.form pr pr) :
    E.form pr pr ≤ Kp * hmesh ^ (2 * s) * f2 ^ 2 := by
  have hA : 0 ≤ E.form pr pr := E.form_nonneg pr
  have hpow : 0 < hmesh ^ (2 * s) := Real.rpow_pos_of_pos hh _
  have h1 : E.form pr pr ≤ f2 * nrm := by rw [← hload]; exact hCS
  rcases eq_or_lt_of_le hA with hA0 | hA0
  · rw [← hA0]
    positivity
  · have h2 : E.form pr pr ^ 2 ≤ f2 ^ 2 * nrm ^ 2 := by
      have := mul_self_le_mul_self hA h1
      nlinarith [this, hnrm, hf2]
    nlinarith [h2, hpoin, hA0, hpow, hK, sq_nonneg f2]

end Lane3
end SubdiffusiveProcess
