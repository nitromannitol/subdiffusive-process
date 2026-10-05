
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCoarseCellRow

@[expose] public section

/-!
# Integrability of the mesoscopic cross term

The per-cell contraction of `WholeSpaceRowsCoarseCellRow.lean` consumes the
integrability of the cross integrand

`x ↦ a x * chi x * u x * (∇u x · ∇chi x)`

on the contraction cube.  This module discharges it from data the frozen
whole-space carrier already carries, with no new analysis: Young's inequality
for the scalar-weighted dot product gives the pointwise bound

`|a chi u (∇u · ∇chi)| ≤ a |∇u|² / 2 + (Λ K / 2) u²`,

whose right-hand side is integrable because `u ∈ L²` and `a |∇u|² ∈ L¹`.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## 1. The scalar representative of an elliptic scalar field -/

/-- The scalar representative of an elliptic scalar coefficient field is
measurable once extended by zero off the domain.  This is the converse of
`isEllipticFieldOn_scalarCoeffField_of_bounds`'s measurability hypothesis, and
the only place where `d ≠ 0` is used (for `d = 0` a coefficient field carries no
entries at all). -/
theorem measurable_indicator_of_isEllipticFieldOn [NeZero d]
    {a : Vec d → ℝ} {lam Lam : ℝ} {W : Set (Vec d)}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a)) :
    Measurable (fun x : Vec d => if x ∈ W then a x else 0) := by
  classical
  set i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ with hi0
  have h1 : Measurable (fun x : Fin d → Fin d → ℝ => x i0 i0) :=
    (measurable_pi_apply i0).comp (measurable_pi_apply i0)
  have h2 : Measurable
      (fun x : Vec d => if x ∈ W then scalarCoeffField a x i0 i0 else 0) :=
    h1.comp hEll.1
  have h3 : (fun x : Vec d => if x ∈ W then scalarCoeffField a x i0 i0 else 0) =
      fun x : Vec d => if x ∈ W then a x else 0 := by
    funext x
    by_cases hx : x ∈ W <;>
      simp [hx, scalarCoeffField, Homogenization.scalarMatrix]
  rw [← h3]
  exact h2

/-- The scalar representative is measurable after restriction to the domain. -/
theorem aestronglyMeasurable_of_isEllipticFieldOn [NeZero d]
    {a : Vec d → ℝ} {lam Lam : ℝ} {W : Set (Vec d)} (hW : MeasurableSet W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a)) :
    AEStronglyMeasurable a (volume.restrict W) := by
  classical
  refine ((measurable_indicator_of_isEllipticFieldOn
    hEll).aestronglyMeasurable).congr ?_
  filter_upwards [ae_restrict_mem hW] with x hx
  simp [hx]

/-- The scalar representative is bounded above by the ellipticity constant on
the domain. -/
theorem le_of_isEllipticFieldOn_scalarCoeffField [NeZero d]
    {a : Vec d → ℝ} {lam Lam : ℝ} {W : Set (Vec d)}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    {x : Vec d} (hx : x ∈ W) : a x ≤ Lam := by
  classical
  set i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ with hi0
  have h := abs_apply_le_of_isEllipticFieldOn hEll hx i0 i0
  have hentry : scalarCoeffField a x i0 i0 = a x := by
    simp [scalarCoeffField, Homogenization.scalarMatrix]
  rw [hentry] at h
  exact (abs_le.1 h).2

/-! ## 2. The pointwise Young bound and the integrability -/

/-- **Young's inequality for the mesoscopic cross integrand.**

`|a chi w (G · ∇chi)| ≤ a |G|² / 2 + (Λ K / 2) w²` at every point of the
domain, from `abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq` with the
weights `√a` and `√a chi w`. -/
theorem abs_cross_le_of_ellipticity [NeZero d]
    {a chi : Vec d → ℝ} {lam Lam K : ℝ} {W : Set (Vec d)}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (hchi_le : ∀ x, |chi x| ≤ 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    {w : Vec d → ℝ} {G : Vec d → Vec d} {x : Vec d} (hx : x ∈ W) :
    |a x * chi x * w x *
        vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i))| ≤
      a x * vecNormSq (G x) / 2 + Lam * K / 2 * w x ^ 2 := by
  have hax : 0 ≤ a x := haNonneg x
  have haLam : a x ≤ Lam := le_of_isEllipticFieldOn_scalarCoeffField hEll hx
  have hsq : Real.sqrt (a x) * Real.sqrt (a x) = a x := Real.mul_self_sqrt hax
  have h := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    (Real.sqrt (a x)) (Real.sqrt (a x) * chi x * w x) (G x)
    (fun i ↦ (fderiv ℝ chi x) (basisVec i))
  have hL : Real.sqrt (a x) * (Real.sqrt (a x) * chi x * w x) =
      a x * chi x * w x := by
    have hexp : Real.sqrt (a x) * (Real.sqrt (a x) * chi x * w x) =
        Real.sqrt (a x) * Real.sqrt (a x) * (chi x * w x) := by ring
    rw [hexp, hsq]; ring
  have hA : Real.sqrt (a x) ^ 2 = a x := by
    rw [pow_two, hsq]
  have hB : (Real.sqrt (a x) * chi x * w x) ^ 2 =
      a x * (chi x ^ 2 * w x ^ 2) := by
    have hexp : (Real.sqrt (a x) * chi x * w x) ^ 2 =
        Real.sqrt (a x) * Real.sqrt (a x) * (chi x ^ 2 * w x ^ 2) := by ring
    rw [hexp, hsq]
  rw [hL, hA, hB] at h
  refine h.trans ?_
  set NC := vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) with hNCdef
  have hNC : (0 : ℝ) ≤ NC := vecNormSq_nonneg _
  have hNCK : NC ≤ K := hK x
  have hchisq : chi x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (chi x), hchi_le x]
  have hw0 : (0 : ℝ) ≤ w x ^ 2 := sq_nonneg _
  have hLam0 : (0 : ℝ) ≤ Lam := le_trans hax haLam
  have hstep : a x * chi x ^ 2 ≤ Lam := by nlinarith
  have key : a x * (chi x ^ 2 * w x ^ 2) * NC ≤ Lam * K * w x ^ 2 := by
    calc a x * (chi x ^ 2 * w x ^ 2) * NC
        = a x * chi x ^ 2 * w x ^ 2 * NC := by ring
      _ ≤ Lam * w x ^ 2 * NC :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hstep hw0) hNC
      _ ≤ Lam * w x ^ 2 * K :=
          mul_le_mul_of_nonneg_left hNCK (by positivity)
      _ = Lam * K * w x ^ 2 := by ring
  linarith

/-- **Integrability of the mesoscopic cross integrand.**

The `hcrossInt` hypothesis of
`massive_local_l2_translatedCube_coarse_contraction_of_cells`, for an arbitrary
pair of fields with the two integrabilities the frozen carrier supplies. -/
theorem integrableOn_cross_of_ellipticity [NeZero d]
    {a chi : Vec d → ℝ} {lam Lam K : ℝ} {W : Set (Vec d)}
    (hW : MeasurableSet W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x)
    (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hchi_le : ∀ x, |chi x| ≤ 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hwmeas : AEStronglyMeasurable w (volume.restrict W))
    (hGmeas : ∀ i : Fin d, AEStronglyMeasurable (fun x ↦ G x i)
      (volume.restrict W))
    (hmass : IntegrableOn (fun x ↦ w x ^ 2) W volume)
    (henergy : IntegrableOn (fun x ↦ a x * vecNormSq (G x)) W volume) :
    IntegrableOn (fun x ↦ a x * chi x * w x *
      vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i))) W volume := by
  classical
  have hfd : Continuous (fderiv ℝ chi) :=
    hchi.continuous_fderiv (by simp)
  have hcomp : ∀ i : Fin d,
      Continuous (fun x : Vec d ↦ (fderiv ℝ chi x) (basisVec i)) :=
    fun i ↦ hfd.clm_apply continuous_const
  have hdot : AEStronglyMeasurable
      (fun x ↦ vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (volume.restrict W) := by
    have : AEStronglyMeasurable
        (fun x ↦ ∑ i : Fin d, G x i * (fderiv ℝ chi x) (basisVec i))
        (volume.restrict W) :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
        (hGmeas i).mul (hcomp i).aestronglyMeasurable
    simpa [vecDot] using this
  have hameas : AEStronglyMeasurable a (volume.restrict W) :=
    aestronglyMeasurable_of_isEllipticFieldOn hW hEll
  have hmeasCross : AEStronglyMeasurable
      (fun x ↦ a x * chi x * w x *
        vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (volume.restrict W) :=
    ((hameas.mul hchi.continuous.aestronglyMeasurable).mul hwmeas).mul hdot
  have hg : Integrable
      (fun x ↦ a x * vecNormSq (G x) / 2 + Lam * K / 2 * w x ^ 2)
      (volume.restrict W) :=
    (henergy.div_const 2).add (hmass.const_mul (Lam * K / 2))
  refine Integrable.mono' hg hmeasCross ?_
  filter_upwards [ae_restrict_mem hW] with x hx
  simpa [Real.norm_eq_abs] using
    abs_cross_le_of_ellipticity (w := w) (G := G) hEll haNonneg hchi_le hK hx

/-! ## 3. The carrier's own cross term -/

/-- **The carrier's gradient is measurable on every open bounded convex
domain.**  The local `H¹` solution the carrier promises there has `L²`
components and agrees with the carrier almost everywhere on the domain, and the
carrier's own fields carry no measurability of their own. -/
theorem aestronglyMeasurable_grad_wholeSpaceSolution
    {a f : Vec d → ℝ} {t : ℝ} (u : WholeSpaceDivergenceResolventSolution a t f)
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W) (i : Fin d) :
    AEStronglyMeasurable (fun x ↦ u.grad x i) (volume.restrict W) := by
  obtain ⟨v, _, hgrad, _⟩ := u.locally_weak_solution W hW
  refine ((v.gradMemL2 i).aestronglyMeasurable).congr ?_
  filter_upwards [hgrad] with x hx
  rw [hx]

/-- **The `hcrossInt` hypothesis, discharged for the frozen carrier.**

Every input is data the carrier already carries: `memL2_toFun` for the mass,
`integrable_energy` for the Dirichlet energy, and `locally_weak_solution` for
the measurability of the gradient. -/
theorem integrableOn_cross_wholeSpaceSolution [NeZero d]
    {a f chi : Vec d → ℝ} {t lam Lam K : ℝ} {W : Set (Vec d)}
    (hWdom : IsOpenBoundedConvexDomain W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x)
    (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hchi_le : ∀ x, |chi x| ≤ 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (u : WholeSpaceDivergenceResolventSolution a t f) :
    IntegrableOn (fun x ↦ a x * chi x * u.toFun x *
      vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i))) W volume :=
  integrableOn_cross_of_ellipticity hWdom.isOpen.measurableSet hEll haNonneg
    hchi hchi_le hK u.memL2_toFun.aestronglyMeasurable.restrict
    (fun i ↦ aestronglyMeasurable_grad_wholeSpaceSolution u hWdom i)
    u.memL2_toFun.integrable_sq.restrict u.integrable_energy.restrict

/-- The contraction-cube form of `integrableOn_cross_wholeSpaceSolution`: this
is verbatim the `hcrossInt` hypothesis of
`wholeSpaceSolution_translatedCube_coarse_mass_contraction_of_cells`. -/
theorem integrableOn_cross_wholeSpaceSolution_translatedCube [NeZero d]
    {a f chi : Vec d → ℝ} {t lam Lam K : ℝ} {n : ℤ} {c : Vec d}
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) c)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x)
    (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hchi_le : ∀ x, |chi x| ≤ 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (u : WholeSpaceDivergenceResolventSolution a t f) :
    IntegrableOn (fun x ↦ a x * chi x * u.toFun x *
      vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (translatedCube d (n + 1) c) volume :=
  integrableOn_cross_wholeSpaceSolution
    (isOpenBoundedConvexDomain_translatedCube (n + 1) c) hEll haNonneg hchi
    hchi_le hK u

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
