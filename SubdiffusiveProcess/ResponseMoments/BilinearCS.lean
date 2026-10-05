module

public import SubdiffusiveProcess.ResponseMoments.FormAlgebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# Cauchy--Schwarz for a nonnegative symmetric bilinear form

Used by Lemma `mfd:lem-diff` : the relative form `Γ_D = Γ_F - c Γ_E` obeys
`|Γ_D(u,v)|(B) ≤ Δ √(Γ_E(u)(B) Γ_E(v)(B))`, which is matrix
Cauchy--Schwarz applied to the two nonnegative combinations `Δ Γ_E ± Γ_D`.

The statements are for a bare bilinear function `B : V → V → ℝ`, so that they
apply to `Δ Γ_E ± Γ_D` without constructing a `LocalEnergy` for it.
-/

open Real

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

omit [Module ℝ V] in
theorem bilin_add_right {V : Type*} [AddCommGroup V] [_module : Module ℝ V]
    {B : V → V → ℝ} (hsymm : ∀ u v, B u v = B v u)
    (hadd : ∀ u v w, B (u + v) w = B u w + B v w) (u v w : V) :
    B u (v + w) = B u v + B u w := by
  rw [hsymm, hadd, hsymm w u, hsymm v u]

theorem bilin_smul_right {B : V → V → ℝ} (hsymm : ∀ u v, B u v = B v u)
    (hsmul : ∀ (c : ℝ) (u v : V), B (c • u) v = c * B u v) (c : ℝ) (u v : V) :
    B u (c • v) = c * B u v := by
  rw [hsymm, hsmul, hsymm v u]

theorem bilin_expand {B : V → V → ℝ} (hsymm : ∀ u v, B u v = B v u)
    (hadd : ∀ u v w, B (u + v) w = B u w + B v w)
    (hsmul : ∀ (c : ℝ) (u v : V), B (c • u) v = c * B u v)
    (t : ℝ) (u v : V) :
    B (u + t • v) (u + t • v) = B u u + 2 * t * B u v + t ^ 2 * B v v := by
  have h1 : B (u + t • v) (u + t • v) = B u (u + t • v) + B (t • v) (u + t • v) :=
    hadd _ _ _
  have h2 : B u (u + t • v) = B u u + t * B u v := by
    rw [bilin_add_right hsymm hadd, bilin_smul_right hsymm hsmul]
  have h3 : B (t • v) (u + t • v) = t * B v u + t * (t * B v v) := by
    rw [bilin_add_right hsymm hadd, hsmul, hsmul, bilin_smul_right hsymm hsmul]
  rw [h1, h2, h3, hsymm v u]
  ring

theorem bilin_apply_eq_zero_of_diag_zero {B : V → V → ℝ}
    (hsymm : ∀ u v, B u v = B v u)
    (hadd : ∀ u v w, B (u + v) w = B u w + B v w)
    (hsmul : ∀ (c : ℝ) (u v : V), B (c • u) v = c * B u v)
    (hnonneg : ∀ u, 0 ≤ B u u) (u v : V) (hv : B v v = 0) :
    B u v = 0 := by
  by_contra hne
  set t : ℝ := -(B u u + 1) / (2 * B u v) with ht
  have h := hnonneg (u + t • v)
  rw [bilin_expand hsymm hadd hsmul, hv] at h
  have h2 : 2 * t * B u v = -(B u u + 1) := by
    rw [ht]
    field_simp
  rw [h2] at h
  linarith

theorem bilin_sq_le {B : V → V → ℝ} (hsymm : ∀ u v, B u v = B v u)
    (hadd : ∀ u v w, B (u + v) w = B u w + B v w)
    (hsmul : ∀ (c : ℝ) (u v : V), B (c • u) v = c * B u v)
    (hnonneg : ∀ u, 0 ≤ B u u) (u v : V) :
    B u v ^ 2 ≤ B u u * B v v := by
  rcases eq_or_lt_of_le (hnonneg v) with hv | hv
  · have hz := bilin_apply_eq_zero_of_diag_zero hsymm hadd hsmul hnonneg u v hv.symm
    rw [hz, ← hv]
    norm_num
  · have h := hnonneg (B v v • u + (-(B u v)) • v)
    rw [bilin_expand hsymm hadd hsmul, hsmul, bilin_smul_right hsymm hsmul,
      hsmul] at h
    nlinarith [h, hv]

/-- Cauchy--Schwarz in `ℝ²`: `√(ac) + √(be) ≤ √((a+b)(c+e))`. -/
theorem sqrt_mul_add_sqrt_mul_le {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) :
    Real.sqrt (a * c) + Real.sqrt (b * e) ≤ Real.sqrt ((a + b) * (c + e)) := by
  have hac : (0 : ℝ) ≤ a * c := mul_nonneg ha hc
  have hbe : (0 : ℝ) ≤ b * e := mul_nonneg hb he
  have hae : (0 : ℝ) ≤ a * e := mul_nonneg ha he
  have hbc : (0 : ℝ) ≤ b * c := mul_nonneg hb hc
  have hprod : (0 : ℝ) ≤ (a + b) * (c + e) :=
    mul_nonneg (add_nonneg ha hb) (add_nonneg hc he)
  have h1 : (0 : ℝ) ≤ Real.sqrt (a * c) + Real.sqrt (b * e) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine (Real.le_sqrt h1 hprod).mpr ?_
  have e1 : Real.sqrt (a * c) ^ 2 = a * c := Real.sq_sqrt hac
  have e2 : Real.sqrt (b * e) ^ 2 = b * e := Real.sq_sqrt hbe
  have e4 : Real.sqrt (a * e) ^ 2 = a * e := Real.sq_sqrt hae
  have e5 : Real.sqrt (b * c) ^ 2 = b * c := Real.sq_sqrt hbc
  have e3 : Real.sqrt (a * c) * Real.sqrt (b * e) =
      Real.sqrt (a * e) * Real.sqrt (b * c) := by
    rw [← Real.sqrt_mul hac, ← Real.sqrt_mul hae]
    congr 1
    ring
  nlinarith [e1, e2, e3, e4, e5, sq_nonneg (Real.sqrt (a * e) - Real.sqrt (b * c))]

/-- Cauchy--Schwarz for the energy measure of a candidate local energy. -/
theorem gam_sq_le {X : Type*} [MeasurableSpace X] (E : LocalEnergy V X)
    (u v : V) (s : Set X) :
    E.gam u v s ^ 2 ≤ E.gam u u s * E.gam v v s :=
  bilin_sq_le (fun a b => E.gam_symm a b s) (fun a b c => E.gam_add_left a b c s)
    (fun c a b => E.gam_smul_left c a b s) (fun a => E.gam_nonneg a s) u v

end ResponseMoments
end SubdiffusiveProcess
