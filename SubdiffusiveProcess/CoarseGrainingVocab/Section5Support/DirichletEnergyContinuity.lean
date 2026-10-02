import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimum
import Homogenization.CoarseGraining.QuadraticStability.Integral




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## Pointwise algebra -/

/-- **`|s|^2 - |t|^2 = (s - t) . (s + t)`**, the elementary identity behind every
`L^2` continuity statement for a quadratic energy. -/
theorem vecNormSq_sub_vecNormSq (s t : Vec d) :
    vecNormSq s - vecNormSq t = vecDot (s - t) (s + t) := by
  simp only [vecNormSq, vecDot, Pi.sub_apply, Pi.add_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Cauchy-Schwarz in `R^d`, in square-root form. -/
theorem abs_vecDot_le_sqrt_mul_sqrt (u v : Vec d) :
    |vecDot u v| ≤ Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq v) := by
  have h : Real.sqrt (vecDot u v ^ 2) ≤ Real.sqrt (vecNormSq u * vecNormSq v) :=
    Real.sqrt_le_sqrt (sq_vecDot_le_vecNormSq_mul_vecNormSq u v)
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_mul (vecNormSq_nonneg u)] at h

/-! ## The `L^2` norm of a vector field on a set -/

/-- **`||F||_{L^2(U)}`** for a vector field, as a real number. -/
def l2NormOn (U : Set (Vec d)) (F : Vec d → Vec d) : ℝ :=
  Real.sqrt (∫ x in U, vecNormSq (F x))

theorem l2NormOn_nonneg (U : Set (Vec d)) (F : Vec d → Vec d) : 0 ≤ l2NormOn U F :=
  Real.sqrt_nonneg _

theorem sq_l2NormOn {U : Set (Vec d)} {F : Vec d → Vec d} (hU : MeasurableSet U) :
    l2NormOn U F ^ 2 = ∫ x in U, vecNormSq (F x) :=
  Real.sq_sqrt (setIntegral_nonneg hU fun _ _ => vecNormSq_nonneg _)

/-! ## Integrability of the square of a vector field -/

/-- A vector field whose coordinates are in `L^2(U)` has integrable square. -/
theorem integrableOn_vecNormSq_of_memLp {U : Set (Vec d)} {F : Vec d → Vec d}
    (h : ∀ i : Fin d, MemLp (fun x => F x i) 2 (volume.restrict U)) :
    IntegrableOn (fun x => vecNormSq (F x)) U volume := by
  have hsum := integrable_finset_sum (μ := volume.restrict U) Finset.univ
    (f := fun (i : Fin d) (x : Vec d) => F x i ^ 2) fun i _ => (h i).integrable_sq
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [vecNormSq, vecDot, pow_two]

/-- The square of `p + Dw` is integrable for an `H^1` gradient on a finite-measure
domain. -/
theorem integrableOn_vecNormSq_add_grad {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)] (w : H1Function U) (p : Vec d) :
    IntegrableOn (fun x => vecNormSq (p + w.grad x)) U volume :=
  integrableOn_vecNormSq_of_memLp fun i => (memLp_const (p i)).add (w.gradMemL2 i)

/-- The square of a difference of two `H^1` gradients is integrable. -/
theorem integrableOn_vecNormSq_sub_grad {U : Set (Vec d)} (v w : H1Function U) :
    IntegrableOn (fun x => vecNormSq (v.grad x - w.grad x)) U volume :=
  integrableOn_vecNormSq_of_memLp fun i => (v.gradMemL2 i).sub (w.gradMemL2 i)

/-! ## The integral Cauchy-Schwarz step -/

/-- The product of the two pointwise norms is integrable, by `AM-GM`. -/
theorem integrableOn_sqrt_vecNormSq_mul {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : IntegrableOn (fun x => vecNormSq (F x)) U volume)
    (hG : IntegrableOn (fun x => vecNormSq (G x)) U volume) :
    IntegrableOn
      (fun x => Real.sqrt (vecNormSq (F x)) * Real.sqrt (vecNormSq (G x))) U volume := by
  refine Integrable.mono' ((hF.add hG).div_const 2) ?_ ?_
  · exact (Real.continuous_sqrt.comp_aestronglyMeasurable hF.1).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hG.1)
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact sqrt_mul_sqrt_le_half_add (vecNormSq_nonneg _) (vecNormSq_nonneg _)

/-- **The integral Cauchy-Schwarz step** for two vector fields on `U`. -/
theorem integral_sqrt_vecNormSq_mul_le {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : IntegrableOn (fun x => vecNormSq (F x)) U volume)
    (hG : IntegrableOn (fun x => vecNormSq (G x)) U volume) :
    (∫ x in U, Real.sqrt (vecNormSq (F x)) * Real.sqrt (vecNormSq (G x))) ≤
      l2NormOn U F * l2NormOn U G :=
  integral_sqrt_mul_sqrt_le hF hG
    (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)
    (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)

/-! ## Continuity of the energy in the gradient -/



theorem abs_dirichletEnergyOn'_sub_le {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d}
    {a b : Vec d → Vec d} {C : ℝ} (hU : MeasurableSet U) (hC : 0 ≤ C)
    (hBbd : ∀ x ∈ U, |B x| ≤ C)
    (ha : IntegrableOn (fun x => B x * vecNormSq (p + a x)) U volume)
    (hb : IntegrableOn (fun x => B x * vecNormSq (p + b x)) U volume)
    (hdiff : IntegrableOn (fun x => vecNormSq (a x - b x)) U volume)
    (hsum : IntegrableOn (fun x => vecNormSq (p + a x + (p + b x))) U volume) :
    |dirichletEnergyOn' B U p a - dirichletEnergyOn' B U p b| ≤
      C * (l2NormOn U (fun x => a x - b x) *
        l2NormOn U (fun x => p + a x + (p + b x))) := by
  have hsub : dirichletEnergyOn' B U p a - dirichletEnergyOn' B U p b =
      ∫ x in U, (B x * vecNormSq (p + a x) - B x * vecNormSq (p + b x)) :=
    (integral_sub ha hb).symm
  have hpt : ∀ x ∈ U,
      |B x * vecNormSq (p + a x) - B x * vecNormSq (p + b x)| ≤
        C * (Real.sqrt (vecNormSq (a x - b x)) *
          Real.sqrt (vecNormSq (p + a x + (p + b x)))) := by
    intro x hxU
    have hd : p + a x - (p + b x) = a x - b x := by
      funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
    have hid : B x * vecNormSq (p + a x) - B x * vecNormSq (p + b x) =
        B x * vecDot (a x - b x) (p + a x + (p + b x)) := by
      rw [← mul_sub, vecNormSq_sub_vecNormSq, hd]
    rw [hid, abs_mul]
    exact mul_le_mul (hBbd x hxU) (abs_vecDot_le_sqrt_mul_sqrt _ _) (abs_nonneg _) hC
  calc |dirichletEnergyOn' B U p a - dirichletEnergyOn' B U p b|
      = |∫ x in U, (B x * vecNormSq (p + a x) - B x * vecNormSq (p + b x))| := by
        rw [hsub]
    _ ≤ ∫ x in U, |B x * vecNormSq (p + a x) - B x * vecNormSq (p + b x)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in U, C * (Real.sqrt (vecNormSq (a x - b x)) *
          Real.sqrt (vecNormSq (p + a x + (p + b x)))) :=
        setIntegral_mono_on (ha.sub hb).abs
          ((integrableOn_sqrt_vecNormSq_mul hdiff hsum).const_mul C) hU hpt
    _ = C * ∫ x in U, Real.sqrt (vecNormSq (a x - b x)) *
          Real.sqrt (vecNormSq (p + a x + (p + b x))) := integral_const_mul _ _
    _ ≤ C * (l2NormOn U (fun x => a x - b x) *
          l2NormOn U (fun x => p + a x + (p + b x))) :=
        mul_le_mul_of_nonneg_left (integral_sqrt_vecNormSq_mul_le hdiff hsum) hC

/-! ## Continuity of the energy in the coefficient -/



theorem abs_dirichletEnergyOn'_sub_le_of_weight_close {B B' : Vec d → ℝ}
    {U : Set (Vec d)} {p : Vec d} {Dw : Vec d → Vec d} {eta : ℝ}
    (hU : MeasurableSet U)
    (hint : IntegrableOn (fun x => B x * vecNormSq (p + Dw x)) U volume)
    (hint' : IntegrableOn (fun x => B' x * vecNormSq (p + Dw x)) U volume)
    (hnorm : IntegrableOn (fun x => vecNormSq (p + Dw x)) U volume)
    (hclose : ∀ x ∈ U, |B' x - B x| ≤ eta) :
    |dirichletEnergyOn' B' U p Dw - dirichletEnergyOn' B U p Dw| ≤
      eta * ∫ x in U, vecNormSq (p + Dw x) := by
  have hsub : dirichletEnergyOn' B' U p Dw - dirichletEnergyOn' B U p Dw =
      ∫ x in U, (B' x * vecNormSq (p + Dw x) - B x * vecNormSq (p + Dw x)) :=
    (integral_sub hint' hint).symm
  have hpt : ∀ x ∈ U,
      |B' x * vecNormSq (p + Dw x) - B x * vecNormSq (p + Dw x)| ≤
        eta * vecNormSq (p + Dw x) := by
    intro x hx
    rw [← sub_mul, abs_mul, abs_of_nonneg (vecNormSq_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hclose x hx) (vecNormSq_nonneg _)
  calc |dirichletEnergyOn' B' U p Dw - dirichletEnergyOn' B U p Dw|
      = |∫ x in U, (B' x * vecNormSq (p + Dw x) - B x * vecNormSq (p + Dw x))| := by
        rw [hsub]
    _ ≤ ∫ x in U, |B' x * vecNormSq (p + Dw x) - B x * vecNormSq (p + Dw x)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in U, eta * vecNormSq (p + Dw x) :=
        setIntegral_mono_on (hint'.sub hint).abs (hnorm.const_mul eta) hU hpt
    _ = eta * ∫ x in U, vecNormSq (p + Dw x) := integral_const_mul _ _

/-! ## Crude quadratic bookkeeping -/

/-- `int |F + G|^2 <= 2 (int |F|^2 + int |G|^2)`.  Used twice downstream to keep
the right-hand factor of `abs_dirichletEnergyOn'_sub_le` bounded along an
approximating sequence, which is what makes a Minkowski inequality unnecessary. -/
theorem integral_vecNormSq_add_le {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hU : MeasurableSet U)
    (hF : IntegrableOn (fun x => vecNormSq (F x)) U volume)
    (hG : IntegrableOn (fun x => vecNormSq (G x)) U volume)
    (hFG : IntegrableOn (fun x => vecNormSq (F x + G x)) U volume) :
    (∫ x in U, vecNormSq (F x + G x)) ≤
      2 * ((∫ x in U, vecNormSq (F x)) + ∫ x in U, vecNormSq (G x)) := by
  have hbound : (∫ x in U, vecNormSq (F x + G x)) ≤
      ∫ x in U, 2 * (vecNormSq (F x) + vecNormSq (G x)) :=
    setIntegral_mono_on hFG ((hF.add hG).const_mul 2) hU
      fun x _ => vecNormSq_add_le (F x) (G x)
  rw [integral_const_mul, integral_add hF hG] at hbound
  exact hbound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
