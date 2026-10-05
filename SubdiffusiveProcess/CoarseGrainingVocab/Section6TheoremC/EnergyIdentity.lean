module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SeminormLimits

@[expose] public section

/-!
# The energy identity for `u_N - u`

Step S5 of Theorem C's proof, paper label `l.finite.cutoff.coefficient.convergence`:

> Lemma `l.finite.cutoff.coefficient.convergence` and the energy identity for
> `u_N - u` give `‖∇u_N-∇u‖_{L²(𝔠_m)} ⟶ 0`.

The tex names the energy identity but does not display it.  It is the standard
comparison for two weak solutions of *different* coefficients sharing boundary
data: with `u` being `a`-harmonic, `u_N` being `b`-harmonic (`b = ã_N`), and
`w := u_N - u ∈ H¹₀(𝔠_m)`, testing each equation against `w` and subtracting
gives

```
∫ b |∇w|²  =  ∫ (a-b) ∇u·∇w .
```

Ellipticity on the left and Cauchy--Schwarz on the right then give

```
‖∇w‖_{L²}  ≤  λ⁻¹ · sup|a-b| · ‖∇u‖_{L²} ,
```

so `∇u_N → ∇u` in `L²(𝔠_m)` as soon as `ã_N → a` uniformly on `𝔠_m` -- which is
exactly what the proved anchor `l.finite.cutoff.coefficient.convergence`
(paper label `l.finite.cutoff.coefficient.convergence`) supplies on compact sets.

This file proves the identity and the pointwise Cauchy--Schwarz ingredient.
The `L²` plumbing that converts the identity into the displayed convergence is
carried as explicit integrability hypotheses, in the style of
`Section6Iteration.NormalizedL2`.

Note on scope: the coefficient here is a *scalar* field, and the two
normalizations in play (`coefficientAt` versus `anchoredCutoff`) are reconciled
by `PositiveRescaling` from this package, so no normalization bookkeeping is
needed below.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### Pointwise algebra of the comparison -/

/-- The pointwise integrand identity behind the energy identity.  With
`∇v = ∇u + ∇w`, the difference of the two tested equations collapses to the
energy of `w` plus the coefficient defect against `∇u`. -/
theorem energy_integrand_eq {a b : Vec d → ℝ} {gu gv gw : Vec d → Vec d}
    (hgrad : ∀ x, gv x = gu x + gw x) (x : Vec d) :
    vecDot (b x • gv x) (gw x) - vecDot (a x • gu x) (gw x) =
      b x * vecNormSq (gw x) - (a x - b x) * vecDot (gu x) (gw x) := by
  rw [hgrad x, smul_add, vecDot_add_left, vecDot_smul_left, vecDot_smul_left,
    vecDot_smul_left, vecNormSq]
  ring

/-! ### The energy identity -/

/-- **The energy identity for `u_N - u`**.  If `u` is
`a`-harmonic, `v` is `b`-harmonic, and `v - u` is represented by the zero-trace
function `w`, then the `b`-energy of `w` is balanced by the coefficient defect
tested against `∇u`.

Stated in the combined form, which needs only the integrability of the two
tested products actually appearing in the weak formulations. -/
theorem integral_energy_combination_eq_zero {W : Set (Vec d)}
    {a b : Vec d → ℝ} {u v : H1Function W} {w : H10Function W}
    (hu : IsWeaklyHarmonicOn a W u) (hv : IsWeaklyHarmonicOn b W v)
    (hgrad : ∀ x, v.grad x = u.grad x + w.toH1Function.grad x)
    (hintv : IntegrableOn
      (fun x ↦ vecDot (b x • v.grad x) (w.toH1Function.grad x)) W)
    (hintu : IntegrableOn
      (fun x ↦ vecDot (a x • u.grad x) (w.toH1Function.grad x)) W) :
    ∫ x in W, (b x * vecNormSq (w.toH1Function.grad x) -
        (a x - b x) * vecDot (u.grad x) (w.toH1Function.grad x)) ∂volume = 0 := by
  have hvw := hv w
  have huw := hu w
  have hsub : ∫ x in W, (vecDot (b x • v.grad x) (w.toH1Function.grad x) -
      vecDot (a x • u.grad x) (w.toH1Function.grad x)) ∂volume = 0 := by
    rw [integral_sub hintv hintu, hvw, huw, sub_zero]
  rw [← hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  exact (energy_integrand_eq hgrad x).symm

/-- The energy identity in split form: the `b`-energy of `w` equals the
coefficient defect tested against `∇u`. -/
theorem integral_energy_eq {W : Set (Vec d)}
    {a b : Vec d → ℝ} {u v : H1Function W} {w : H10Function W}
    (hu : IsWeaklyHarmonicOn a W u) (hv : IsWeaklyHarmonicOn b W v)
    (hgrad : ∀ x, v.grad x = u.grad x + w.toH1Function.grad x)
    (hintv : IntegrableOn
      (fun x ↦ vecDot (b x • v.grad x) (w.toH1Function.grad x)) W)
    (hintu : IntegrableOn
      (fun x ↦ vecDot (a x • u.grad x) (w.toH1Function.grad x)) W)
    (hE : IntegrableOn
      (fun x ↦ b x * vecNormSq (w.toH1Function.grad x)) W)
    (hD : IntegrableOn
      (fun x ↦ (a x - b x) * vecDot (u.grad x) (w.toH1Function.grad x)) W) :
    ∫ x in W, b x * vecNormSq (w.toH1Function.grad x) ∂volume =
      ∫ x in W, (a x - b x) *
        vecDot (u.grad x) (w.toH1Function.grad x) ∂volume := by
  have h := integral_energy_combination_eq_zero hu hv hgrad hintv hintu
  rw [integral_sub hE hD, sub_eq_zero] at h
  exact h

/-! ### The two sides of the identity -/

/-- Ellipticity bounds the left-hand side from below. -/
theorem lower_bound_energy {W : Set (Vec d)} {b : Vec d → ℝ} {lam : ℝ}
    (hlam : ∀ x, lam ≤ b x) {gw : Vec d → Vec d}
    (hint1 : IntegrableOn (fun x ↦ lam * vecNormSq (gw x)) W)
    (hint2 : IntegrableOn (fun x ↦ b x * vecNormSq (gw x)) W) :
    ∫ x in W, lam * vecNormSq (gw x) ∂volume ≤
      ∫ x in W, b x * vecNormSq (gw x) ∂volume := by
  refine integral_mono hint1 hint2 fun x ↦ ?_
  exact mul_le_mul_of_nonneg_right (hlam x) (vecNormSq_nonneg _)

/-- **Pointwise Cauchy--Schwarz** for the right-hand side: the coefficient
defect is controlled by its supremum times the product of the magnitudes. -/
theorem defect_le {a b : Vec d → ℝ} {K : ℝ}
    (hK : ∀ x, |a x - b x| ≤ K) (gu gw : Vec d → Vec d) (x : Vec d) :
    (a x - b x) * vecDot (gu x) (gw x) ≤
      K * (euclideanNorm (gu x) * euclideanNorm (gw x)) := by
  have hprod : euclideanNorm (gu x) * euclideanNorm (gw x) =
      Real.sqrt (vecNormSq (gu x) * vecNormSq (gw x)) := by
    rw [euclideanNorm, euclideanNorm, ← Real.sqrt_mul (vecNormSq_nonneg _)]
  have habs_cs : |vecDot (gu x) (gw x)| ≤
      euclideanNorm (gu x) * euclideanNorm (gw x) := by
    rw [hprod, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (sq_vecDot_le_vecNormSq_mul_vecNormSq _ _)
  have hKnn : 0 ≤ K := le_trans (abs_nonneg _) (hK x)
  calc (a x - b x) * vecDot (gu x) (gw x)
      ≤ |(a x - b x) * vecDot (gu x) (gw x)| := le_abs_self _
    _ = |a x - b x| * |vecDot (gu x) (gw x)| := abs_mul _ _
    _ ≤ K * (euclideanNorm (gu x) * euclideanNorm (gw x)) :=
        mul_le_mul (hK x) habs_cs (abs_nonneg _) hKnn

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
