import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DilationWeakEquation
import SubdiffusiveProcess.Section10.PhysicalTightnessEarlyExit
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicWeakScaling
import Homogenization.Sobolev.H1.Translation
import Homogenization.Book.Ch01.Theorems.NormScaling

/-! Actual Sobolev carriers, weak subsolutions and energy under the positive
spatial chart used in the physical/local coupling. These are deterministic
transports, independent of the existence of the random static bank. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open scoped Pointwise ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

private theorem inverse_smul_domain {d : ℕ} {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) : r⁻¹ • (r • U) = U := by
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

private theorem castH10_fun {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (u : H10Function U) (x : Vec d) : (h ▸ u).toFun x = u.toFun x := by
  cases h
  rfl

private theorem castH10_gradient {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (u : H10Function U) (x : Vec d) :
    (h ▸ u).toH1Function.grad x = u.toH1Function.grad x := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.aux_dedup_d213_castH10Function_grad (d := d) (U := U) (V := V) (hUV := h) (phi := u) (x := x)

/-- Pullback of the actual physical Sobolev witness, with no amplitude factor. -/
def affineH1Pullback {d : ℕ} {U : Set (Vec d)} {r : ℝ} (hr : 0 < r)
    (z : Vec d) (u : H1Function (translateSet z (r • U))) : H1Function U :=
  (H1Function.untranslate z u).unscale hr

@[simp] theorem affineH1Pullback_toFun {d : ℕ} {U : Set (Vec d)} {r : ℝ}
    (hr : 0 < r) (z : Vec d) (u : H1Function (translateSet z (r • U))) (x : Vec d) :
    (affineH1Pullback hr z u).toFun x = u.toFun (r • x + z) := rfl

@[simp] theorem affineH1Pullback_grad {d : ℕ} {U : Set (Vec d)} {r : ℝ}
    (hr : 0 < r) (z : Vec d) (u : H1Function (translateSet z (r • U))) (x : Vec d) :
    (affineH1Pullback hr z u).grad x = r • u.grad (r • x + z) := rfl

/-- Push a genuine zero-trace cutoff to the physical chart. Inverse `unscale`
preserves zero trace and its approximation certificate. -/
def affineH10Pushforward {d : ℕ} {U : Set (Vec d)} {r : ℝ} (hr : 0 < r)
    (z : Vec d) (u : H10Function U) : H10Function (translateSet z (r • U)) :=
  ((inverse_smul_domain hr U).symm ▸ u).unscale (inv_pos.mpr hr) |>.translate z

@[simp] theorem affineH10Pushforward_toFun {d : ℕ} {U : Set (Vec d)} {r : ℝ}
    (hr : 0 < r) (z : Vec d) (u : H10Function U) (y : Vec d) :
    (affineH10Pushforward hr z u).toFun y = u.toFun (r⁻¹ • (y - z)) := by
  simp only [affineH10Pushforward, H10Function.translate_toH1Function,
    H1Function.translate_toFun, H10Function.unscale_toH1Function,
    H1Function.unscale_toFun, castH10_fun]

@[simp] theorem affineH10Pushforward_grad {d : ℕ} {U : Set (Vec d)} {r : ℝ}
    (hr : 0 < r) (z : Vec d) (u : H10Function U) (y : Vec d) :
    (affineH10Pushforward hr z u).toH1Function.grad y =
      r⁻¹ • u.toH1Function.grad (r⁻¹ • (y - z)) := by
  simp only [affineH10Pushforward, H10Function.translate_toH1Function,
    H1Function.translate_grad, H10Function.unscale_toH1Function,
    H1Function.unscale_grad, castH10_gradient]

/-- The chart maps Lebesgue a.e. assertions in either direction. -/
theorem affine_ae_iff {d : ℕ} {U : Set (Vec d)} {r : ℝ} (hr : 0 < r)
    (z : Vec d) (P : Vec d → Prop) :
    (∀ᵐ y ∂volume.restrict (translateSet z (r • U)), P y) ↔
      ∀ᵐ x ∂volume.restrict U, P (r • x + z) := by
  constructor
  · intro h
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.harmonic_ae_smul hr
      ((measurePreserving_addRight_restrict_translateSet z (r • U)).quasiMeasurePreserving.ae h)
  · intro h
    have hs : ∀ᵐ y ∂volume.restrict (r • U), P (y + z) := by
      have h' : ∀ᵐ x ∂volume.restrict (r⁻¹ • (r • U)), P (r • x + z) := by
        rwa [inverse_smul_domain hr U]
      have h'' := SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.harmonic_ae_smul
        (inv_pos.mpr hr) h'
      simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using h''
    have ht := (measurePreserving_subRight_restrict_translateSet z (r • U)).quasiMeasurePreserving.ae hs
    simpa only [sub_add_cancel] using ht

/-- Exact Jacobian formula for lower integrals, with no integrand measurability
premise: the spatial chart is a measurable equivalence. -/
theorem affine_lintegral {d : ℕ} {r : ℝ} (hr : 0 < r) (z : Vec d)
    (U : Set (Vec d)) (f : Vec d → ℝ≥0∞) :
    (∫⁻ y in translateSet z (r • U), f y) =
      ENNReal.ofReal (r ^ d) * ∫⁻ x in U, f (r • x + z) := by
  have ht := (measurePreserving_addRight_restrict_translateSet z (r • U)).lintegral_comp_emb
    (Homeomorph.addRight z).measurableEmbedding f
  have hs := lintegral_map_equiv (μ := volume.restrict U)
    (fun y => f (y + z)) (Homeomorph.smulOfNeZero r hr.ne').toMeasurableEquiv
  change (∫⁻ y, f (y + z) ∂Measure.map (fun x : Vec d => r • x) (volume.restrict U)) =
    ∫⁻ x in U, f (r • x + z) at hs
  rw [map_smul_volume_restrict hr, lintegral_smul_measure, smul_eq_mul] at hs
  rw [← ht, ← hs, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr.le d),
    mul_inv_cancel₀ (pow_pos hr d).ne', ENNReal.ofReal_one, one_mul]

/-- Pulling back a weak subsolution and dividing its coefficient by a positive
constant preserves the inequality, including the genuine nonnegative H10 tests. -/
theorem subsolution_affine_pullback {d : ℕ} {U : Set (Vec d)} {r gamma : ℝ}
    (hr : 0 < r) (hgamma : 0 < gamma) (z : Vec d) {c a : Vec d → ℝ}
    (hc : ∀ x, c (r • x + z) = gamma * a x)
    (u : H1Function (translateSet z (r • U)))
    (hu : IsWeakSubSolutionOn c (translateSet z (r • U)) u) :
    IsWeakSubSolutionOn a U (affineH1Pullback hr z u) := by
  intro phi hphi
  let psi := affineH10Pushforward hr z phi
  have hpsi : ∀ y, 0 ≤ psi.toFun y := by
    intro y
    simpa only [psi, affineH10Pushforward_toFun] using hphi (r⁻¹ • (y - z))
  have hp := hu psi hpsi
  have heq : (∫ y in translateSet z (r • U),
      vecDot (c y • u.grad y) (psi.toH1Function.grad y)) =
      (r ^ d * gamma * r⁻¹ * r⁻¹) *
        ∫ x in U, vecDot (a x • (affineH1Pullback hr z u).grad x)
          (phi.toH1Function.grad x) := by
    rw [Homogenization.Book.Ch01.setIntegral_translateSet_smul_set_eq_comp_affine_of_pos hr,
      smul_eq_mul]
    simp_rw [psi, affineH10Pushforward_grad, add_sub_cancel_right, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul, hc, affineH1Pullback_grad,
      vecDot_smul_left, vecDot_smul_right]
    simp only [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    field_simp
  rw [heq] at hp
  exact nonpos_of_mul_nonpos_right hp (by positivity)

/-- Exact physical cutoff energy. The common scalar is retained here; it will
cancel against the speed-density scalar in the exit probability. -/
theorem energy_affine_pushforward {d : ℕ} {U : Set (Vec d)} {r gamma : ℝ}
    (hr : 0 < r) (z : Vec d) {c a : Vec d → ℝ}
    (hc : ∀ x, c (r • x + z) = gamma * a x) (chi : H10Function U) :
    energy c (translateSet z (r • U)) (affineH10Pushforward hr z chi).toH1Function =
      (r ^ d * gamma * r⁻¹ * r⁻¹) * energy a U chi.toH1Function := by
  unfold energy
  rw [Homogenization.Book.Ch01.setIntegral_translateSet_smul_set_eq_comp_affine_of_pos hr,
    smul_eq_mul]
  simp_rw [affineH10Pushforward_grad, add_sub_cancel_right, smul_smul,
    inv_mul_cancel₀ hr.ne', one_smul, hc, vecDot_smul_left, vecDot_smul_right]
  simp only [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end SubdiffusiveProcess.Section10.PhysicalTightness
