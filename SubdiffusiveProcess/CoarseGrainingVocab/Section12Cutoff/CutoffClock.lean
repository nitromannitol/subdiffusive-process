module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.Frozen.Section7.Defs.IntrinsicOffDiagonalRate

@[expose] public section




set_option autoImplicit false

open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Process

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section12Cutoff

variable {d : ℕ}

/-- The finite-cutoff clock `Tr_L`. -/
def cutoffTimeScale (ahom : ℕ → ℝ) (L : ℕ) (r : ℝ) : ℝ :=
  if r ≤ (3 : ℝ) ^ L then timeScale ahom r else r ^ 2 / ahom L

/-- The normalized rescaled clock `Theta_L(r) = Tr_L(3^L r) / Tr(3^L)`. -/
def rescaledCutoffClock (ahom : ℕ → ℝ) (L : ℕ) (r : ℝ) : ℝ :=
  cutoffTimeScale ahom L ((3 : ℝ) ^ L * r) / timeScale ahom ((3 : ℝ) ^ L)

/-- The rescaled coefficient `A_L(z) = a_L(3^L z)`. -/
def rescaledCoefficient (aL : Vec d → ℝ) (L : ℕ) (z : Vec d) : ℝ :=
  aL (fun i => (3 : ℝ) ^ L * z i)

/-- The rescaled kernel `k^{(L)}_t(z,w) = 3^{dL} p^{(L)}_{Tr(3^L) t}(3^L z, 3^L w)`. -/
def rescaledKernel (d : ℕ) (ahom : ℕ → ℝ) (L : ℕ)
    (p : ℝ → Vec d → Vec d → ℝ) (t : ℝ) (z w : Vec d) : ℝ :=
  (3 : ℝ) ^ (d * L) *
    p (timeScale ahom ((3 : ℝ) ^ L) * t)
      (fun i => (3 : ℝ) ^ L * z i) (fun i => (3 : ℝ) ^ L * w i)

/-- Below the cutoff radius the cutoff clock is the ambient one. -/
theorem cutoffTimeScale_of_le (ahom : ℕ → ℝ) (L : ℕ) {r : ℝ} (hr : r ≤ (3 : ℝ) ^ L) :
    cutoffTimeScale ahom L r = timeScale ahom r := by
  rw [cutoffTimeScale, if_pos hr]

/-- Above it the cutoff clock is exactly quadratic. -/
theorem cutoffTimeScale_of_gt (ahom : ℕ → ℝ) (L : ℕ) {r : ℝ} (hr : (3 : ℝ) ^ L < r) :
    cutoffTimeScale ahom L r = r ^ 2 / ahom L := by
  rw [cutoffTimeScale, if_neg (not_le.mpr hr)]

/-- The normalization `Theta_L(1) = 1`, whenever the ambient clock does not vanish at the
cutoff radius. -/
theorem rescaledCutoffClock_one (ahom : ℕ → ℝ) (L : ℕ)
    (h : timeScale ahom ((3 : ℝ) ^ L) ≠ 0) :
    rescaledCutoffClock ahom L 1 = 1 := by
  unfold rescaledCutoffClock
  rw [mul_one, cutoffTimeScale_of_le ahom L le_rfl, div_self h]

end SubdiffusiveProcess.CoarseGrainingVocab.Section12Cutoff
