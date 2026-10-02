/-
# Resolvents and the dual (variational) form of the energy
-/
import SubdiffusiveProcess.DirichletForm.Energy

/-!
# Resolvents and the dual energy

A closed form `E` determines, for `α > 0`, the resolvent `G_α = (α + A)⁻¹` of its
associated nonnegative self-adjoint operator `A`, characterized by
`α⟪G_α f, v⟫ + E(G_α f, v) = ⟪f, v⟫` for all `v ∈ D(E)`
(`DirichletForm.IsResolvent`).  Conversely the energy is recovered from the
resolvent by the variational (dual) formula

`E_α(u) = sup_f (2⟪f, u⟫ - ⟪f, G_α f⟫)`,

which is `DirichletForm.dualEnergy`.  This file fixes both notions and proves
the elementary facts that do not need the spectral theorem: a resolvent is
symmetric and positive, and the dual energy is nonnegative and is `⊤` exactly
off its domain.

## References

* Fukushima–Oshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  §1.3–§1.4.
-/

open MeasureTheory Filter Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

namespace DirichletForm

/-- `G` is the resolvent of `E` at `α`: `G f ∈ D(E)` and
`α⟪G f, v⟫ + E(G f, v) = ⟪f, v⟫` for every `v ∈ D(E)`. -/
def IsResolvent (E : ClosedForm m) (α : ℝ) (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) : Prop :=
  ∀ f : Lp ℝ 2 m, G f ∈ E.domain ∧
    ∀ v ∈ E.domain, α * (inner ℝ (G f) v : ℝ) + E.form (G f) v = (inner ℝ f v : ℝ)

namespace IsResolvent

variable {E : ClosedForm m} {α : ℝ} {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}

theorem mem_domain (h : IsResolvent E α G) (f : Lp ℝ 2 m) : G f ∈ E.domain := (h f).1

theorem eq (h : IsResolvent E α G) (f : Lp ℝ 2 m) {v : Lp ℝ 2 m} (hv : v ∈ E.domain) :
    α * (inner ℝ (G f) v : ℝ) + E.form (G f) v = (inner ℝ f v : ℝ) := (h f).2 v hv

/-- A resolvent is symmetric. -/
theorem inner_comm (h : IsResolvent E α G) (f g : Lp ℝ 2 m) :
    (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ) := by
  have h₁ := h.eq f (h.mem_domain g)
  have h₂ := h.eq g (h.mem_domain f)
  have hE := E.form_symm _ (h.mem_domain f) _ (h.mem_domain g)
  have hi : (inner ℝ (G f) (G g) : ℝ) = (inner ℝ (G g) (G f) : ℝ) := real_inner_comm _ _
  rw [hi, hE] at h₁
  linarith

/-- A resolvent with nonnegative parameter is a positive operator. -/
theorem inner_self_nonneg (h : IsResolvent E α G) (hα : 0 ≤ α) (f : Lp ℝ 2 m) :
    0 ≤ (inner ℝ f (G f) : ℝ) := by
  have h₁ := h.eq f (h.mem_domain f)
  have h₂ : (inner ℝ f (G f) : ℝ) = (inner ℝ (G f) f : ℝ) := real_inner_comm _ _
  have h₃ : (0 : ℝ) ≤ (inner ℝ (G f) (G f) : ℝ) := real_inner_self_nonneg
  have h₄ := E.form_nonneg _ (h.mem_domain f)
  nlinarith [h₁, h₂, h₃, h₄, mul_nonneg hα h₃]

end IsResolvent

/-- The dual (variational) energy of a bounded operator `G`:
`E_G(u) = sup_f (2⟪f, u⟫ - ⟪f, G f⟫)`. -/
def dualEnergy (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (u : Lp ℝ 2 m) : EReal :=
  ⨆ f : Lp ℝ 2 m, ((2 * (inner ℝ f u : ℝ) - (inner ℝ f (G f) : ℝ) : ℝ) : EReal)

/-- The domain of the dual energy. -/
def dualEnergyDomain (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) : Set (Lp ℝ 2 m) :=
  {u : Lp ℝ 2 m | dualEnergy G u < (⊤ : EReal)}

/-- The polarization of the dual energy. -/
def dualEnergyBilinear (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (u v : Lp ℝ 2 m) : EReal :=
  (dualEnergy G (u + v) - dualEnergy G (u - v)) / 4

/-- The dual energy is nonnegative. -/
theorem dualEnergy_nonneg (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (u : Lp ℝ 2 m) :
    0 ≤ dualEnergy G u := by
  refine le_iSup_of_le 0 ?_
  simp

/-- The dual energy of `0` vanishes when `G` is positive. -/
theorem dualEnergy_zero_of_nonneg {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hG : ∀ f : Lp ℝ 2 m, 0 ≤ (inner ℝ f (G f) : ℝ)) : dualEnergy G 0 = 0 := by
  refine le_antisymm ?_ (dualEnergy_nonneg G 0)
  refine iSup_le fun f => ?_
  have := hG f
  simp only [inner_zero_right, mul_zero, zero_sub]
  exact_mod_cast neg_nonpos.mpr this

/-- The polarization identity behind the parallelogram law for a dual energy.
Writing `A(f, w) = 2⟪f, w⟫ - ⟪f, G f⟫` for the affine functional whose supremum
is the dual energy, a symmetric `G` gives
`A(p+r, u+v) + A(p-r, u-v) = 2 A(p, u) + 2 A(r, v)`. -/
theorem dualEnergy_pairing_add {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hsymm : ∀ f g : Lp ℝ 2 m, (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ))
    (u v p r : Lp ℝ 2 m) :
    (2 * (inner ℝ (p + r) (u + v) : ℝ) - (inner ℝ (p + r) (G (p + r)) : ℝ)) +
        (2 * (inner ℝ (p - r) (u - v) : ℝ) - (inner ℝ (p - r) (G (p - r)) : ℝ)) =
      2 * (2 * (inner ℝ p u : ℝ) - (inner ℝ p (G p) : ℝ)) +
        2 * (2 * (inner ℝ r v : ℝ) - (inner ℝ r (G r) : ℝ)) := by
  have hpr := hsymm p r
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right]
  linarith [hpr]

/-- Each affine functional is below the dual energy. -/
theorem le_dualEnergy (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f w : Lp ℝ 2 m) :
    ((2 * (inner ℝ f w : ℝ) - (inner ℝ f (G f) : ℝ) : ℝ) : EReal) ≤ dualEnergy G w :=
  le_iSup (fun g : Lp ℝ 2 m =>
    ((2 * (inner ℝ g w : ℝ) - (inner ℝ g (G g) : ℝ) : ℝ) : EReal)) f

/-- Approximation from below of a finite dual energy. -/
theorem exists_lt_dualEnergy {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} {w : Lp ℝ 2 m} {c : ℝ}
    (h : ((c : ℝ) : EReal) < dualEnergy G w) :
    ∃ f : Lp ℝ 2 m, c < 2 * (inner ℝ f w : ℝ) - (inner ℝ f (G f) : ℝ) := by
  have h' : ((c : ℝ) : EReal) < ⨆ f : Lp ℝ 2 m,
      ((2 * (inner ℝ f w : ℝ) - (inner ℝ f (G f) : ℝ) : ℝ) : EReal) := h
  rw [lt_iSup_iff] at h'
  obtain ⟨f, hf⟩ := h'
  exact ⟨f, by exact_mod_cast hf⟩

/-- **Parallelogram inequality for a dual energy.**  For a symmetric `G`,
`2E(u) + 2E(v) ≤ E(u+v) + E(u-v)`; combined with the reverse inequality coming
from a recovery sequence with vanishing cross energy, it forces
`E(u+v) = E(u-v)`, which is the vanishing of the polarized form. -/
theorem dualEnergy_add_eq_sub_of_le {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hsymm : ∀ f g : Lp ℝ 2 m, (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ))
    {u v : Lp ℝ 2 m} {Eu Ev : ℝ}
    (hu : dualEnergy G u = (Eu : EReal)) (hv : dualEnergy G v = (Ev : EReal))
    (h1 : dualEnergy G (u + v) ≤ ((Eu + Ev : ℝ) : EReal))
    (h2 : dualEnergy G (u - v) ≤ ((Eu + Ev : ℝ) : EReal)) :
    dualEnergy G (u + v) = dualEnergy G (u - v) := by
  have hbot : ∀ w : Lp ℝ 2 m, dualEnergy G w ≠ ⊥ := by
    intro w
    have h0 : (⊥ : EReal) < dualEnergy G w :=
      lt_of_lt_of_le (by simpa using EReal.bot_lt_coe (0 : ℝ)) (dualEnergy_nonneg G w)
    exact h0.ne'
  obtain ⟨A, hA⟩ : ∃ A : ℝ, dualEnergy G (u + v) = (A : EReal) :=
    ⟨(dualEnergy G (u + v)).toReal,
      (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) h1) (hbot _)).symm⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, dualEnergy G (u - v) = (B : EReal) :=
    ⟨(dualEnergy G (u - v)).toReal,
      (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) h2) (hbot _)).symm⟩
  rw [hA] at h1
  rw [hB] at h2
  have hAle : A ≤ Eu + Ev := by exact_mod_cast h1
  have hBle : B ≤ Eu + Ev := by exact_mod_cast h2
  have hlow : ∀ ε : ℝ, 0 < ε → 2 * Eu + 2 * Ev - 4 * ε ≤ A + B := by
    intro ε hε
    obtain ⟨p, hp⟩ : ∃ p : Lp ℝ 2 m,
        Eu - ε < 2 * (inner ℝ p u : ℝ) - (inner ℝ p (G p) : ℝ) := by
      refine exists_lt_dualEnergy ?_
      rw [hu]
      exact_mod_cast (by linarith : Eu - ε < Eu)
    obtain ⟨r, hr⟩ : ∃ r : Lp ℝ 2 m,
        Ev - ε < 2 * (inner ℝ r v : ℝ) - (inner ℝ r (G r) : ℝ) := by
      refine exists_lt_dualEnergy ?_
      rw [hv]
      exact_mod_cast (by linarith : Ev - ε < Ev)
    have hsum := dualEnergy_pairing_add hsymm u v p r
    have hr1 : 2 * (inner ℝ (p + r) (u + v) : ℝ) -
        (inner ℝ (p + r) (G (p + r)) : ℝ) ≤ A := by
      have := le_dualEnergy G (p + r) (u + v)
      rw [hA] at this
      exact_mod_cast this
    have hr2 : 2 * (inner ℝ (p - r) (u - v) : ℝ) -
        (inner ℝ (p - r) (G (p - r)) : ℝ) ≤ B := by
      have := le_dualEnergy G (p - r) (u - v)
      rw [hB] at this
      exact_mod_cast this
    linarith [hsum, hr1, hr2, hp, hr]
  have hAeq : A = Eu + Ev := by
    refine le_antisymm hAle (le_of_forall_pos_le_add fun δ hδ => ?_)
    have := hlow (δ / 4) (by positivity)
    linarith [hBle]
  have hBeq : B = Eu + Ev := by
    refine le_antisymm hBle (le_of_forall_pos_le_add fun δ hδ => ?_)
    have := hlow (δ / 4) (by positivity)
    linarith [hAle]
  rw [hA, hB, hAeq, hBeq]

/-- `u` lies in the dual-energy domain exactly when the dual energy is finite. -/
theorem mem_dualEnergyDomain_iff (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (u : Lp ℝ 2 m) :
    u ∈ dualEnergyDomain G ↔ dualEnergy G u < (⊤ : EReal) := Iff.rfl

end DirichletForm
