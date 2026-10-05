module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimum
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Sobolev.H1.Translation
public import Homogenization.Book.Ch02.Dilation

@[expose] public section

/-!
# Dilation and translation covariance of the continuum Dirichlet minimum

Step 3 of the strict-decay proof (paper label `p.homogenized.coefficient.strict.decay`) runs its
induction between the generations `spx_{NR}` and `spx_{(N-1)R}`, and compares
the outer weight `B_{NR}` with the *unit-scale* constant `q_R`.  Both moves are
changes of variables in the continuum minimum

```text
min_{u in linear_p + H_0^1(U)} int_U B |nabla u|^2 .
```

This file proves the two covariances, for an arbitrary open (indeed arbitrary
measurable) domain, which is what the simplex mesh needs -- the library's
`Ch02.aCoarse_dilate` is stated for `IsCubeDilation` on **cube** domains and a
`TriadicCoeffFamily`, and `Sobolev/H1/Translation.lean` transports only the
`H^1_0` carrier.

* `dirichletEnergyOn'_comp_smul` / `dirichletEnergyOn'_comp_add_right` -- the
  change of variables at the level of one competitor's energy;
* `dirichletInfOn_comp_smul` -- **the dilation covariance**

  ```text
  dirichletInfOn (B (a .)) U p = (a ^ d)⁻¹ * dirichletInfOn B (a • U) p ;
  ```

* `dirichletInfOn_comp_add_right` -- the translation covariance;
* `dirichletInfOn_dilateVec` -- the same statement for the triadic dilation
  `Ch02.dilateVec k` and the preimage domain `phi ⁻¹' U`;
* `normalized_dirichletInfOn_dilateVec` -- the *normalized* form actually
  consumed by the induction,

  ```text
  (vol (phi ⁻¹' U))⁻¹ * dirichletInfOn (B ∘ phi) (phi ⁻¹' U) p
    = (vol U)⁻¹ * dirichletInfOn B U p ,
  ```

  which holds with no finiteness or nondegeneracy hypothesis on `U`.

## Mechanism

The `H^1_0` carrier transports by composition.  The library already has the
pullback `H10Function.unscale : H10Function (a • U) → H10Function U` with
`grad x = a • grad (a x)`; rescaling it by `a⁻¹` gives the *energy-natural*
correspondence `w'(y) = a⁻¹ w(a y)`, whose gradient is exactly `grad w (a y)`,
and the correspondence is bijective because the inverse dilation gives the
inverse map.  The energy then transforms by
`MeasureTheory.Measure.setIntegral_comp_smul_of_pos`, which carries no
integrability hypothesis, so the two energy sets differ exactly by the positive
factor `(a ^ d)⁻¹` and the infima follow.  Translation is the same argument
with `H10Function.translate` / `H10Function.untranslate`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book MeasureTheory Set

open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-! ## Elementary transport of the carrier -/

private def castH10 {U V : Set (Vec d)} (h : U = V) (u : H10Function U) : H10Function V :=
  h ▸ u

private theorem castH10_grad {U V : Set (Vec d)} (h : U = V) (u : H10Function U) :
    (castH10 h u).toH1Function.grad = u.toH1Function.grad := by
  subst h
  rfl

private theorem smul_set_eq_preimage {a : ℝ} (ha : a ≠ 0) (U : Set (Vec d)) :
    a • U = (fun x : Vec d => a⁻¹ • x) ⁻¹' U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_smul, ha] using hy
  · intro hx
    exact ⟨a⁻¹ • x, hx, by simp [smul_smul, ha]⟩

private theorem measurableSet_smul_set {a : ℝ} (ha : a ≠ 0) {U : Set (Vec d)}
    (hU : MeasurableSet U) : MeasurableSet (a • U) := by
  rw [smul_set_eq_preimage ha]
  exact (measurable_const_smul (a⁻¹ : ℝ)) hU

private theorem inv_smul_smul_set {a : ℝ} (ha : a ≠ 0) (U : Set (Vec d)) :
    a⁻¹ • (a • U) = U := by
  rw [smul_set_eq_preimage (inv_ne_zero ha), smul_set_eq_preimage ha]
  ext x
  simp [smul_smul, ha]

private theorem smul_inv_smul_set {a : ℝ} (ha : a ≠ 0) (U : Set (Vec d)) :
    a • (a⁻¹ • U) = U := by
  simpa using inv_smul_smul_set (inv_ne_zero ha) U

/-! ## The two dilation transports of a competitor -/

/-- The competitor on `U` induced by a competitor on `a • U`: `w'(x) = a⁻¹ w(a x)`,
whose weak gradient is `grad w (a x)`. -/
private def dilationPullback {U : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (u : H10Function (a • U)) : H10Function U :=
  a⁻¹ • H10Function.unscale ha u

private theorem dilationPullback_grad {U : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (u : H10Function (a • U)) (x : Vec d) :
    (dilationPullback ha u).toH1Function.grad x = u.toH1Function.grad (a • x) := by
  show a⁻¹ • ((H10Function.unscale ha u).toH1Function.grad x) = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_grad, smul_smul,
    inv_mul_cancel₀ ha.ne', one_smul]

/-- The competitor on `a • U` induced by a competitor on `U`: `u(y) = a w(a⁻¹ y)`,
whose weak gradient is `grad w (a⁻¹ y)`. -/
private def dilationPushforward {U : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (w : H10Function U) : H10Function (a • U) :=
  a • H10Function.unscale (inv_pos.mpr ha)
    (castH10 (inv_smul_smul_set ha.ne' U).symm w)

private theorem dilationPushforward_grad {U : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (w : H10Function U) (x : Vec d) :
    (dilationPushforward ha w).toH1Function.grad (a • x) = w.toH1Function.grad x := by
  show a • ((H10Function.unscale (inv_pos.mpr ha)
    (castH10 (inv_smul_smul_set ha.ne' U).symm w)).toH1Function.grad (a • x)) = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_grad, castH10_grad,
    smul_smul, mul_inv_cancel₀ ha.ne', one_smul, smul_smul, inv_mul_cancel₀ ha.ne',
    one_smul]

/-! ## Change of variables in one competitor's energy -/

/-- **The dilation change of variables.**  With `w'(x) = a⁻¹ w(a x)` the energy
of `w'` against the pulled-back weight is `(a ^ d)⁻¹` times the energy of `w`
against `B`.  No integrability hypothesis is needed: the identity is the
measure-theoretic scaling of a set integral. -/
theorem dirichletEnergyOn'_comp_smul {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d}
    {G : Vec d → Vec d} {a : ℝ} (ha : 0 < a) :
    dirichletEnergyOn' (fun y => B (a • y)) U p (fun x => G (a • x)) =
      (a ^ d)⁻¹ * dirichletEnergyOn' B (a • U) p G := by
  have h := MeasureTheory.Measure.setIntegral_comp_smul_of_pos
    (μ := (volume : Measure (Vec d))) (f := fun y => B y * vecNormSq (p + G y)) U ha
  simpa [dirichletEnergyOn', smul_eq_mul] using h

/-- **The translation change of variables.** -/
theorem dirichletEnergyOn'_comp_add_right {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d}
    {G : Vec d → Vec d} (z : Vec d) :
    dirichletEnergyOn' (fun y => B (y + z)) U p (fun x => G (x + z)) =
      dirichletEnergyOn' B (translateSet z U) p G := by
  simpa [dirichletEnergyOn'] using
    setIntegral_comp_addRight_translateSet (d := d) z U
      (fun y => B y * vecNormSq (p + G y))

/-! ## Covariance of the infimum -/

/-- **Dilation covariance of the continuum Dirichlet minimum.**  For every
positive `a`,

```text
dirichletInfOn (fun y => B (a • y)) U p = (a ^ d)⁻¹ * dirichletInfOn B (a • U) p .
```

Both sides are infima over the whole of `linear_p + H_0^1`, and the dilation is
a bijection between the two competitor sets that multiplies every energy by the
same positive constant. -/
theorem dirichletInfOn_comp_smul {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d} {a : ℝ}
    (ha : 0 < a) (hU : MeasurableSet U) (hB : ∀ x, 0 ≤ B x) :
    dirichletInfOn (fun y => B (a • y)) U p =
      (a ^ d)⁻¹ * dirichletInfOn B (a • U) p := by
  have haU : MeasurableSet (a • U) := measurableSet_smul_set ha.ne' hU
  have hBa : ∀ x, 0 ≤ B (a • x) := fun x => hB _
  have hapow : (0 : ℝ) < a ^ d := pow_pos ha d
  refine le_antisymm ?_ ?_
  · have hstep : a ^ d * dirichletInfOn (fun y => B (a • y)) U p ≤
        dirichletInfOn B (a • U) p := by
      refine le_csInf (dirichletEnergySet_nonempty B (a • U) p) ?_
      rintro E ⟨u, rfl⟩
      have hle := dirichletInfOn_le (B := fun y => B (a • y)) (U := U) (p := p) hU hBa
        (dilationPullback ha u)
      have hfun : (dilationPullback ha u).toH1Function.grad =
          fun x => u.toH1Function.grad (a • x) :=
        funext (dilationPullback_grad ha u)
      rw [hfun, dirichletEnergyOn'_comp_smul (B := B) (U := U) (p := p)
        (G := u.toH1Function.grad) ha] at hle
      calc a ^ d * dirichletInfOn (fun y => B (a • y)) U p
          ≤ a ^ d * ((a ^ d)⁻¹ *
              dirichletEnergyOn' B (a • U) p u.toH1Function.grad) :=
            mul_le_mul_of_nonneg_left hle hapow.le
        _ = dirichletEnergyOn' B (a • U) p u.toH1Function.grad := by
            field_simp
    have h2 := mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hapow.le)
    rw [← mul_assoc, inv_mul_cancel₀ hapow.ne', one_mul] at h2
    exact h2
  · refine le_csInf (dirichletEnergySet_nonempty (fun y => B (a • y)) U p) ?_
    rintro E ⟨w, rfl⟩
    have hfun : w.toH1Function.grad =
        fun x => (dilationPushforward ha w).toH1Function.grad (a • x) :=
      (funext (dilationPushforward_grad ha w)).symm
    rw [hfun, dirichletEnergyOn'_comp_smul (B := B) (U := U) (p := p)
      (G := (dilationPushforward ha w).toH1Function.grad) ha]
    exact mul_le_mul_of_nonneg_left
      (dirichletInfOn_le haU hB (dilationPushforward ha w)) (inv_nonneg.mpr hapow.le)

/-- **Translation covariance of the continuum Dirichlet minimum.** -/
theorem dirichletInfOn_comp_add_right {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d}
    (z : Vec d) (hU : MeasurableSet U) (hB : ∀ x, 0 ≤ B x) :
    dirichletInfOn (fun y => B (y + z)) U p = dirichletInfOn B (translateSet z U) p := by
  have hzU : MeasurableSet (translateSet z U) := by
    have hset : translateSet z U = (fun x : Vec d => x - z) ⁻¹' U := by
      ext x
      exact mem_translateSet_iff_sub_mem
    rw [hset]
    exact (measurable_id.sub_const z) hU
  have hBz : ∀ x, 0 ≤ B (x + z) := fun x => hB _
  refine le_antisymm ?_ ?_
  · refine le_csInf (dirichletEnergySet_nonempty B (translateSet z U) p) ?_
    rintro E ⟨u, rfl⟩
    have hle := dirichletInfOn_le (B := fun y => B (y + z)) (U := U) (p := p) hU hBz
      (H10Function.untranslate z u)
    have hfun : (H10Function.untranslate z u).toH1Function.grad =
        fun x => u.toH1Function.grad (x + z) := rfl
    rw [hfun, dirichletEnergyOn'_comp_add_right (B := B) (U := U) (p := p)
      (G := u.toH1Function.grad) z] at hle
    exact hle
  · refine le_csInf (dirichletEnergySet_nonempty (fun y => B (y + z)) U p) ?_
    rintro E ⟨w, rfl⟩
    have hfun : w.toH1Function.grad =
        fun x => (w.translate z).toH1Function.grad (x + z) := by
      funext x
      show _ = w.toH1Function.grad (x + z - z)
      rw [add_sub_cancel_right]
    rw [hfun, dirichletEnergyOn'_comp_add_right (B := B) (U := U) (p := p)
      (G := (w.translate z).toH1Function.grad) z]
    exact dirichletInfOn_le hzU hB (w.translate z)

/-! ## The triadic dilation -/

/-- The preimage of a set under the triadic dilation is its inverse dilate. -/
theorem preimage_dilateVec (k : ℤ) (U : Set (Vec d)) :
    Ch02.dilateVec (d := d) k ⁻¹' U = (Ch02.triadicDilationFactor k)⁻¹ • U := by
  rw [smul_set_eq_preimage (inv_ne_zero (Ch02.triadicDilationFactor_ne_zero k))]
  ext x
  simp [Ch02.dilateVec]

/-- **The dilation covariance of `dirichletInfOn` for the triadic dilation.**
With `phi = Ch02.dilateVec k` and `lambda = 3 ^ k`,

```text
dirichletInfOn (B ∘ phi) (phi ⁻¹' U) p = (lambda ^ d)⁻¹ * dirichletInfOn B U p .
```
-/
theorem dirichletInfOn_dilateVec {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d} (k : ℤ)
    (hU : MeasurableSet U) (hB : ∀ x, 0 ≤ B x) :
    dirichletInfOn (fun x => B (Ch02.dilateVec k x)) (Ch02.dilateVec (d := d) k ⁻¹' U) p =
      (Ch02.triadicDilationFactor k ^ d)⁻¹ * dirichletInfOn B U p := by
  have hlam : (0 : ℝ) < Ch02.triadicDilationFactor k := Ch02.triadicDilationFactor_pos k
  have hpre := preimage_dilateVec (d := d) k U
  have hmeas : MeasurableSet ((Ch02.triadicDilationFactor k)⁻¹ • U) :=
    measurableSet_smul_set (inv_ne_zero hlam.ne') hU
  rw [hpre]
  have h := dirichletInfOn_comp_smul (B := B)
    (U := (Ch02.triadicDilationFactor k)⁻¹ • U) (p := p) hlam hmeas hB
  rw [smul_inv_smul_set hlam.ne' U] at h
  simpa [Ch02.dilateVec] using h

/-- **The normalized dilation covariance**, in the form Step 3 consumes: the
volume-averaged Dirichlet minimum is invariant under the triadic dilation.  No
finiteness or nondegeneracy hypothesis on `U` is needed. -/
theorem normalized_dirichletInfOn_dilateVec {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d}
    (k : ℤ) (hU : MeasurableSet U) (hB : ∀ x, 0 ≤ B x) :
    (volume (Ch02.dilateVec (d := d) k ⁻¹' U)).toReal⁻¹ *
        dirichletInfOn (fun x => B (Ch02.dilateVec k x))
          (Ch02.dilateVec (d := d) k ⁻¹' U) p =
      (volume U).toReal⁻¹ * dirichletInfOn B U p := by
  have hlam : (0 : ℝ) < Ch02.triadicDilationFactor k := Ch02.triadicDilationFactor_pos k
  have hpow : (0 : ℝ) < Ch02.triadicDilationFactor k ^ d := pow_pos hlam d
  have hvol : (volume (Ch02.dilateVec (d := d) k ⁻¹' U)).toReal =
      (Ch02.triadicDilationFactor k ^ d)⁻¹ * (volume U).toReal := by
    rw [preimage_dilateVec, MeasureTheory.Measure.addHaar_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    congr 1
    rw [Module.finrank_fin_fun, abs_pow, abs_of_pos (inv_pos.mpr hlam), inv_pow]
  rw [hvol, dirichletInfOn_dilateVec k hU hB, mul_inv, inv_inv]
  field_simp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
