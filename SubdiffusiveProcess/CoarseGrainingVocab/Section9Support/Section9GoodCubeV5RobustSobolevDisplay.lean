module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5RobustSobolev
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeExitTransfer

@[expose] public section

/-!
# Step S of the robust good-cube event, assembled: the transferred Sobolev display

 §5 Step S, final assembly.

`Section9GoodCubeV5RobustSobolev.lean` proved the two perturbation halves —
`lpSq_mul_le` (the `L^p` seminorm pays `u^{1/p}` squared) and `energy_mul_ge` (the Dirichlet
energy gains the scalar lower bound) — and `Section9GoodCubeV5RobustMass.lean` proved C2
(`weightedMeasure_mul_le`).  What was still missing is the **negative** power of the weighted
mass that `GoodCubeSobolevDisplay` carries: `x ↦ x^{-(1-2/p)}` is antitone, so a two-sided
comparison of the masses transfers in the opposite direction.

* `ennreal_rpow_le_rpow_of_nonpos` — antitonicity of a nonpositive real power on `ℝ≥0∞`.  No
  positivity or finiteness side condition: the negative power is the inverse of a nonnegative
  one, and `ENNReal.inv_le_inv` is unconditional.
* `rpow_le_const_mul_rpow_of_nonpos` — the quantitative form: from `W' ≤ L · W` with `L`
  positive and finite and `W` finite, `W^c ≤ L^{-c} · W'^c` for `c ≤ 0`.
* `goodCubeSobolevDisplay_mul_of_admissible` — the display itself, with constant
  `CC · (1+ε)/(1-ε)`.

The plan's central bookkeeping claim is verified here in Lean: the multiplier's **scale** `k`
cancels.  The `L^p` factor contributes `(k(1+ε))^{2/p}`, the negative power of the weighted
measure contributes `(k(1+ε))^{1-2/p}`, and the energy contributes `(k(1-ε))^{-1}`; the exponent
identity is `2/p + (1 - 2/p) - 1 = 0`, so the transferred constant depends on neither `p` nor `k`.
`2 < p0` is what makes the exponent `-(1 - 2/p0)` nonpositive.

Two side conditions the plan's pointwise argument hides are carried explicitly rather than
assumed away: `energy` is a **Bochner** integral, so the energy comparison needs both integrands
integrable on the cube, and the mass transfer needs the unmultiplied weighted mass finite.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-- Antitonicity of a nonpositive real power on `ℝ≥0∞`.  No finiteness or positivity side
condition is needed: the negative power is the inverse of a nonnegative one. -/
theorem ennreal_rpow_le_rpow_of_nonpos {x y : ℝ≥0∞} (hxy : x ≤ y) {c : ℝ} (hc : c ≤ 0) :
    y ^ c ≤ x ^ c := by
  have hnc : (0:ℝ) ≤ -c := by linarith
  have hx : x ^ (-c) ≤ y ^ (-c) := ENNReal.rpow_le_rpow hxy hnc
  have hinv : (y ^ (-c))⁻¹ ≤ (x ^ (-c))⁻¹ := ENNReal.inv_le_inv.mpr hx
  rw [← ENNReal.rpow_neg, ← ENNReal.rpow_neg, neg_neg] at hinv
  exact hinv

/-- Transferring a nonpositive power across a scalar upper bound. -/
theorem rpow_le_const_mul_rpow_of_nonpos {W W' L : ℝ≥0∞} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hW : W ≠ ⊤) (hle : W' ≤ L * W) {c : ℝ} (hc : c ≤ 0) :
    W ^ c ≤ L ^ (-c) * W' ^ c := by
  have hsplit : (L * W) ^ c = L ^ c * W ^ c := ENNReal.mul_rpow_of_ne_top hLtop hW c
  have hstep : L ^ c * W ^ c ≤ W' ^ c := by
    rw [← hsplit]
    exact ennreal_rpow_le_rpow_of_nonpos hle hc
  have hmul := mul_le_mul_right hstep (L ^ (-c))
  have hcancel : L ^ (-c) * (L ^ c * W ^ c) = W ^ c := by
    rw [← mul_assoc, ← ENNReal.rpow_add _ _ hL0 hLtop]
    simp
  rwa [hcancel] at hmul

/-- **Step S, assembled.**  The good-cube Sobolev display survives multiplication by an
admissible multiplier, with the constant `CC · (1+ε)/(1-ε)`: the `L^p` factor contributes
`(k(1+ε))^{2/p}`, the negative power of the weighted measure contributes `(k(1+ε))^{1-2/p}`, and
the energy contributes `(k(1-ε))⁻¹`, so the multiplier's scale `k` cancels and the exponent of
`k(1+ε)` is `2/p + (1 - 2/p) = 1`. -/
theorem goodCubeSobolevDisplay_mul_of_admissible {S : Set (Vec d)} {Q : Cube d}
    (hQm : MeasurableSet (cubeSet Q)) (hQS : cubeSet Q ⊆ S)
    {a theta : Vec d → ℝ} {p0 CC epsilon : ℝ} {clock : ℝ → ℝ}
    (hp0 : 2 < p0) (hCC : 0 ≤ CC) (hclock : 0 ≤ clock Q.2)
    (heps0 : 0 ≤ epsilon) (heps1 : epsilon < 1)
    (ha : ∀ x ∈ S, 0 ≤ a x)
    (hadm : GoodCubeV5AdmissibleMultiplier S epsilon theta)
    (hWfin : weightedMeasure a (cubeSet Q) ≠ ⊤)
    (hint1 : ∀ f : H10Function (cubeSet Q), IntegrableOn
      (fun x => a x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x)) (cubeSet Q))
    (hint2 : ∀ f : H10Function (cubeSet Q), IntegrableOn
      (fun x => a x * theta x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
      (cubeSet Q))
    (hdisp : GoodCubeSobolevDisplay a p0 CC clock Q) :
    GoodCubeSobolevDisplay (fun x => a x * theta x) p0
      (CC * (1 + epsilon) / (1 - epsilon)) clock Q := by
  classical
  obtain ⟨k, hk, hkb⟩ := admissibleMultiplier_bounds hadm
  have hp0pos : 0 < p0 := by linarith
  have hu : 0 < k * (1 + epsilon) := by nlinarith
  have hl : 0 < k * (1 - epsilon) := by nlinarith
  set L : ℝ≥0∞ := ENNReal.ofReal (k * (1 + epsilon)) with hLdef
  have hL0 : L ≠ 0 := by rw [hLdef]; simpa using hu
  have hLtop : L ≠ ⊤ := by rw [hLdef]; exact ENNReal.ofReal_ne_top
  set c : ℝ := -(1 - 2 / p0) with hcdef
  have hc : c ≤ 0 := by
    rw [hcdef]
    have : 2 / p0 < 1 := by rw [div_lt_one hp0pos]; linarith
    linarith
  intro f
  -- the three transfers
  have h1 := lpSq_mul_le (p := p0) hQm hQS hu ha (fun x hx => (hkb x hx).2) f.toH1Function.toFun
  have h3 : weightedMeasure a (cubeSet Q) ^ c ≤
      L ^ (-c) * weightedMeasure (fun x => a x * theta x) (cubeSet Q) ^ c :=
    rpow_le_const_mul_rpow_of_nonpos hL0 hLtop hWfin
      (weightedMeasure_mul_le hQm hQS hu.le ha (fun x hx => (hkb x hx).2)) hc
  have h4 : k * (1 - epsilon) * energy a (cubeSet Q) f.toH1Function ≤
      energy (fun x => a x * theta x) (cubeSet Q) f.toH1Function :=
    energy_mul_ge hQm hQS ha (fun x hx => (hkb x hx).1) f.toH1Function (hint1 f) (hint2 f)
  -- the exponent identity
  have hexp : (L ^ (1 / ENNReal.ofReal p0).toReal) ^ (2 : ℕ) * L ^ (-c) = L := by
    have htoreal : (1 / ENNReal.ofReal p0).toReal = 1 / p0 := by
      rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0pos.le, one_div]
    rw [htoreal, ← ENNReal.rpow_natCast (L ^ (1 / p0)) 2, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add _ _ hL0 hLtop]
    have : 1 / p0 * (2 : ℕ) + -c = 1 := by
      rw [hcdef]
      push_cast
      field_simp
      ring
    rw [this, ENNReal.rpow_one]
  -- the real-side energy comparison
  have hEt : clock Q.2 * (k * (1 + epsilon) * energy a (cubeSet Q) f.toH1Function) ≤
      (1 + epsilon) / (1 - epsilon) *
        (clock Q.2 * energy (fun x => a x * theta x) (cubeSet Q) f.toH1Function) := by
    have hkey : k * (1 + epsilon) * energy a (cubeSet Q) f.toH1Function ≤
        (1 + epsilon) / (1 - epsilon) *
          energy (fun x => a x * theta x) (cubeSet Q) f.toH1Function := by
      have hkne : k ≠ 0 := ne_of_gt hk
      have hene : (1 : ℝ) - epsilon ≠ 0 := by linarith
      rw [← sub_nonneg] at h4 ⊢
      have hfac : (1 + epsilon) / (1 - epsilon) *
            energy (fun x => a x * theta x) (cubeSet Q) f.toH1Function -
          k * (1 + epsilon) * energy a (cubeSet Q) f.toH1Function =
          ((1 + epsilon) / (1 - epsilon)) *
            (energy (fun x => a x * theta x) (cubeSet Q) f.toH1Function -
              k * (1 - epsilon) * energy a (cubeSet Q) f.toH1Function) := by
        field_simp
      rw [hfac]
      exact mul_nonneg (div_nonneg (by linarith) (by linarith)) h4
    nlinarith [hkey, hclock]
  calc lpSq (fun x => a x * theta x) (cubeSet Q) p0 f.toH1Function.toFun
      ≤ (L ^ (1 / ENNReal.ofReal p0).toReal) ^ (2 : ℕ) *
          lpSq a (cubeSet Q) p0 f.toH1Function.toFun := h1
    _ ≤ (L ^ (1 / ENNReal.ofReal p0).toReal) ^ (2 : ℕ) *
          (ENNReal.ofReal CC * weightedMeasure a (cubeSet Q) ^ c *
            ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function)) :=
        mul_le_mul_right (hdisp f) _
    _ ≤ (L ^ (1 / ENNReal.ofReal p0).toReal) ^ (2 : ℕ) *
          (ENNReal.ofReal CC *
            (L ^ (-c) * weightedMeasure (fun x => a x * theta x) (cubeSet Q) ^ c) *
            ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function)) := by
        gcongr
    _ = ((L ^ (1 / ENNReal.ofReal p0).toReal) ^ (2 : ℕ) * L ^ (-c)) *
          (ENNReal.ofReal CC *
            weightedMeasure (fun x => a x * theta x) (cubeSet Q) ^ c *
            ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function)) := by
        ring
    _ = ENNReal.ofReal CC *
          weightedMeasure (fun x => a x * theta x) (cubeSet Q) ^ c *
          (L * ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function)) := by
        rw [hexp]; ring
    _ ≤ ENNReal.ofReal CC *
          weightedMeasure (fun x => a x * theta x) (cubeSet Q) ^ c *
          ENNReal.ofReal ((1 + epsilon) / (1 - epsilon) *
            (clock Q.2 * energy (fun x => a x * theta x) (cubeSet Q) f.toH1Function)) := by
        gcongr
        rw [hLdef, ← ENNReal.ofReal_mul hu.le]
        exact ENNReal.ofReal_le_ofReal (by linarith [hEt])
    _ = ENNReal.ofReal (CC * (1 + epsilon) / (1 - epsilon)) *
          weightedMeasure (fun x => a x * theta x) (cubeSet Q) ^ c *
          ENNReal.ofReal (clock Q.2 *
            energy (fun x => a x * theta x) (cubeSet Q) f.toH1Function) := by
        have hfrac : (0:ℝ) ≤ (1 + epsilon) / (1 - epsilon) :=
          div_nonneg (by linarith) (by linarith)
        rw [show CC * (1 + epsilon) / (1 - epsilon) = CC * ((1 + epsilon) / (1 - epsilon)) by
            ring, ENNReal.ofReal_mul hCC, ENNReal.ofReal_mul hfrac]
        ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
