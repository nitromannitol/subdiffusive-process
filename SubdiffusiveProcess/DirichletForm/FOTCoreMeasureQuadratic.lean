module

public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasureAlgebra

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal CompactlySupported BoundedContinuousFunction

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
variable [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
variable {F : _root_.DirichletForm m} {U : Set X}

namespace CoreMeasure
variable (Γ : CoreMeasure F U)

/-- Real linear relations are transferred by separating positive and negative coefficients. -/
theorem linear_relation {ι : Type*} (h : Data F U) (s : Finset ι)
    (v : ι → coreDomain F U) (c : ι → ℝ)
    (he : ∀ φ : CoreRiesz.tests F U, ∑ i ∈ s, c i * coreBilinear φ (v i) (v i) = 0)
    (B : Set X) : ∑ i ∈ s, c i * (Γ.measure (v i).1 B).toReal = 0 := by
  let cp := fun i => Real.toNNReal (c i)
  let cn := fun i => Real.toNNReal (-c i)
  have hc (i : ι) : (cp i : ℝ) - (cn i : ℝ) = c i := by
    simp only [cp, cn, Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]
  have hm := Γ.measureSum_eq h s s v v cp cn (by
    intro φ
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul, hc]
    exact he φ)
  have hb := congrArg (fun μ : Measure X => (μ B).toReal) hm
  rw [Γ.toReal_measureSum, Γ.toReal_measureSum] at hb
  have hz := sub_eq_zero.mpr hb
  rw [← Finset.sum_sub_distrib] at hz
  simpa only [← sub_mul, hc] using hz

/-- Evaluation on any set is a nonnegative quadratic form on the continuous core. -/
def quadratic (h : Data F U) (B : Set X) : QuadraticForm ℝ (coreDomain F U) :=
  QuadraticMap.ofPolar (fun u => (Γ.measure u.1 B).toReal)
    (by intro c u; simpa [smul_eq_mul, sq] using Γ.quadratic_smul h c u B)
    (by
      intro u v w
      have he := Γ.quadratic_three h u v w B
      simp only [QuadraticMap.polar, Submodule.coe_add]
      linarith)
    (by
      intro c u v
      let vs : Fin 6 → coreDomain F U := ![c • u + v, c • u, v, u + v, u, v]
      let cs : Fin 6 → ℝ := ![1, -1, -1, -c, c, c]
      have he := Γ.linear_relation h Finset.univ vs cs (by
        intro φ
        simp [Fin.sum_univ_succ, vs, cs, map_add, map_smul, LinearMap.add_apply,
          LinearMap.smul_apply, smul_eq_mul]
        ring) B
      simp [Fin.sum_univ_succ, vs, cs] at he
      simp only [QuadraticMap.polar, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
      linarith)

@[simp] theorem quadratic_apply (h : Data F U) (B : Set X) (u : coreDomain F U) :
    Γ.quadratic h B u = (Γ.measure u.1 B).toReal := rfl

theorem quadratic_le_energy (h : Data F U) (B : Set X) (u : coreDomain F U) :
    Γ.quadratic h B u ≤ F.form u.1 u.1 := by
  rw [quadratic_apply, ← Γ.mass u.1 u.property]
  exact ENNReal.toReal_mono (Γ.finite u.1 u.property).ne (measure_mono (subset_univ B))

end CoreMeasure

/-- Cauchy--Schwarz for a nonnegative real quadratic form. -/
theorem abs_associated_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : ∀ u, 0 ≤ Q u) (u v : V) :
    |Q.associated u v| ≤ Real.sqrt (Q u) * Real.sqrt (Q v) := by
  let B := Q.associated
  have hd (w : V) : B w w = Q w := QuadraticMap.associated_eq_self_apply ℝ Q w
  have hs (w z : V) : B w z = B z w := QuadraticMap.associated_isSymm ℝ Q w z
  have hp (t : ℝ) : 0 ≤ Q v * (t * t) + 2 * B u v * t + Q u := by
    have he := hQ (u + t • v)
    rw [← hd] at he
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at he
    rw [hd u, hd v, hs v u] at he
    nlinarith
  have hdisc := discrim_le_zero hp
  rw [discrim] at hdisc
  have hsq : B u v ^ 2 ≤ Q u * Q v := by nlinarith
  rw [← Real.sqrt_mul_self (abs_nonneg (B u v)), ← Real.sqrt_mul (hQ u)]
  apply Real.sqrt_le_sqrt
  rwa [abs_mul_abs_self, ← sq]

namespace CoreMeasure
variable (Γ : CoreMeasure F U)

theorem quadratic_difference_bound (h : Data F U) (u v : coreDomain F U) (B : Set X) :
    |(Γ.measure u.1 B).toReal - (Γ.measure v.1 B).toReal| ≤
      Real.sqrt (F.form (u.1 - v.1) (u.1 - v.1)) *
        (Real.sqrt (F.form u.1 u.1) + Real.sqrt (F.form v.1 v.1)) := by
  let Q := Γ.quadratic h B
  let β := Q.associated
  have hQ (w : coreDomain F U) : 0 ≤ Q w := ENNReal.toReal_nonneg
  have hd (w : coreDomain F U) : β w w = Q w := QuadraticMap.associated_eq_self_apply ℝ Q w
  have hs (w z : coreDomain F U) : β w z = β z w := QuadraticMap.associated_isSymm ℝ Q w z
  have he : Q u - Q v = β (u - v) u + β (u - v) v := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hd u, hd v, hs v u]
    ring
  have hβ1 := abs_associated_le Q hQ (u - v) u
  have hβ2 := abs_associated_le Q hQ (u - v) v
  have hsum : |Q u - Q v| ≤ Real.sqrt (Q (u - v)) *
      (Real.sqrt (Q u) + Real.sqrt (Q v)) := by
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add hβ1 hβ2).trans_eq (mul_add _ _ _).symm)
  have hmon : Real.sqrt (Q (u - v)) * (Real.sqrt (Q u) + Real.sqrt (Q v)) ≤
      Real.sqrt (F.form (u.1 - v.1) (u.1 - v.1)) *
        (Real.sqrt (F.form u.1 u.1) + Real.sqrt (F.form v.1 v.1)) := by
    apply mul_le_mul
    · exact Real.sqrt_le_sqrt (Γ.quadratic_le_energy h B (u - v))
    · exact add_le_add (Real.sqrt_le_sqrt (Γ.quadratic_le_energy h B u))
        (Real.sqrt_le_sqrt (Γ.quadratic_le_energy h B v))
    · positivity
    · positivity
  exact hsum.trans hmon

end CoreMeasure
end DirichletForm.FOTConstruction
