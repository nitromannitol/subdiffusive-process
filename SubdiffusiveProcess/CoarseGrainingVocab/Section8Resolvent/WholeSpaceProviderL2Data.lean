import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderApprox




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped BigOperators

noncomputable section

variable {d : ℕ} {a : Vec d → ℝ} {t : ℝ} {f : Vec d → ℝ}

/-! ### Local certificates in terms of the global fields -/

/-- The global value and gradient of a whole-space carrier are a weak
derivative pair on every bounded open convex domain. -/
theorem hasWeakPartialDerivOn_of_wholeSpaceSolution
    (u : WholeSpaceDivergenceResolventSolution a t f) {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) (i : Fin d) :
    HasWeakPartialDerivOn W i u.toFun (fun x ↦ u.grad x i) := by
  obtain ⟨uW, hvalue, hgrad, _⟩ := u.locally_weak_solution W hW
  intro φ hsmooth hcompact hsupport
  have hbase := uW.hasWeakGradient i φ hsmooth hcompact hsupport
  have hleft : ∫ x in W, u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume =
      ∫ x in W, uW.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
    refine setIntegral_congr_fun hW.isOpen.measurableSet fun x hx ↦ ?_
    rw [hvalue x hx]
  have hright : ∫ x in W, u.grad x i * φ x ∂volume =
      ∫ x in W, uW.grad x i * φ x ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  rw [hleft, hright]
  exact hbase

/-- The massive weak equation of a whole-space carrier, read off in terms of
its global value and gradient. -/
theorem massive_identity_of_wholeSpaceSolution
    (u : WholeSpaceDivergenceResolventSolution a t f) {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) (φ : H10Function W) :
    t⁻¹ * ∫ x in W, u.toFun x * φ.toH1Function.toFun x ∂volume +
        ∫ x in W, vecDot (a x • u.grad x) (φ.toH1Function.grad x) ∂volume =
      ∫ x in W, t⁻¹ * f x * φ.toH1Function.toFun x ∂volume := by
  obtain ⟨uW, hvalue, hgrad, hsol⟩ := u.locally_weak_solution W hW
  have hbase := hsol φ
  have hmass : ∫ x in W, (1 : ℝ) * uW.toFun x * φ.toH1Function.toFun x ∂volume =
      ∫ x in W, u.toFun x * φ.toH1Function.toFun x ∂volume := by
    refine setIntegral_congr_fun hW.isOpen.measurableSet fun x hx ↦ ?_
    rw [one_mul, hvalue x hx]
  have henergy :
      ∫ x in W, vecDot (a x • uW.grad x) (φ.toH1Function.grad x) ∂volume =
        ∫ x in W, vecDot (a x • u.grad x) (φ.toH1Function.grad x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  have hforce :
      ∫ x in W, (1 : ℝ) * (t⁻¹ * f x) * φ.toH1Function.toFun x ∂volume =
        ∫ x in W, t⁻¹ * f x * φ.toH1Function.toFun x ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [one_mul]
  rw [hmass, henergy, hforce] at hbase
  exact hbase

/-! ### The coefficient-weighted gradient norm -/

/-- Each weighted gradient coordinate of a whole-space carrier is square
integrable. -/
theorem memLp_sqrt_mul_grad (hcont : Continuous a) (hnonneg : ∀ x, 0 ≤ a x)
    (u : WholeSpaceDivergenceResolventSolution a t f) (i : Fin d) :
    MemLp (fun x ↦ Real.sqrt (a x) * u.grad x i) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (fun x ↦ Real.sqrt (a x) * u.grad x i) volume :=
    (Real.continuous_sqrt.comp hcont).aestronglyMeasurable.mul
      (WholeSpaceDivergenceResolventSolution.aestronglyMeasurable_grad_apply
        u i)
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  refine Integrable.mono' u.integrable_energy (hmeas.pow 2) ?_
  refine Filter.Eventually.of_forall fun x ↦ ?_
  have hsq : (Real.sqrt (a x) * u.grad x i) ^ 2 = a x * u.grad x i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hnonneg x)]
  have hle : u.grad x i ^ 2 ≤ vecNormSq (u.grad x) := by
    have : vecNormSq (u.grad x) = ∑ j, u.grad x j * u.grad x j := rfl
    rw [this, sq]
    refine Finset.single_le_sum (f := fun j ↦ u.grad x j * u.grad x j)
      (fun j _ ↦ mul_self_nonneg _) (Finset.mem_univ i)
  rw [Real.norm_eq_abs, hsq,
    abs_of_nonneg (mul_nonneg (hnonneg x) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left hle (hnonneg x)

/-- The coefficient-weighted energy is the sum of the squared weighted
gradient coordinates. -/
theorem integral_weighted_energy_eq_sum (hnonneg : ∀ x, 0 ≤ a x)
    {g : Vec d → Vec d}
    (hi : ∀ i, Integrable (fun x ↦ (Real.sqrt (a x) * g x i) ^ 2) volume) :
    ∫ x, a x * vecNormSq (g x) ∂volume =
      ∑ i, ∫ x, (Real.sqrt (a x) * g x i) ^ 2 ∂volume := by
  rw [← integral_finset_sum Finset.univ fun i _ ↦ hi i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  have hpt : ∀ i : Fin d, (Real.sqrt (a x) * g x i) ^ 2 = a x * (g x i * g x i) := by
    intro i
    rw [mul_pow, Real.sq_sqrt (hnonneg x), sq]
  simp only [hpt]
  rw [← Finset.mul_sum]
  rfl

/-- The coefficient-weighted energy pairing splits into the coordinate
pairings of the square-root-weighted gradients. -/
theorem integral_vecDot_smul_eq_sum (hnonneg : ∀ x, 0 ≤ a x)
    {W : Set (Vec d)} {g h : Vec d → Vec d}
    (hint : ∀ i, Integrable
      (fun x ↦ Real.sqrt (a x) * g x i * (Real.sqrt (a x) * h x i))
      (volume.restrict W)) :
    ∫ x in W, vecDot (a x • g x) (h x) ∂volume =
      ∑ i, ∫ x in W,
        Real.sqrt (a x) * g x i * (Real.sqrt (a x) * h x i) ∂volume := by
  rw [← integral_finset_sum Finset.univ fun i _ ↦ hint i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  have hpt : ∀ i : Fin d,
      Real.sqrt (a x) * g x i * (Real.sqrt (a x) * h x i) =
        a x * g x i * h x i := by
    intro i
    have : Real.sqrt (a x) * Real.sqrt (a x) = a x :=
      Real.mul_self_sqrt (hnonneg x)
    calc Real.sqrt (a x) * g x i * (Real.sqrt (a x) * h x i)
        = (Real.sqrt (a x) * Real.sqrt (a x)) * (g x i * h x i) := by ring
      _ = a x * g x i * h x i := by rw [this]; ring
  simp only [hpt]
  simp only [vecDot, Pi.smul_apply, smul_eq_mul]

/-- A square-root-weighted `L²` function on a set with a coefficient upper
bound is again square integrable there. -/
theorem memLp_sqrt_mul_of_le_on (hcont : Continuous a)
    {W : Set (Vec d)} (hWmeas : MeasurableSet W) {Lam : ℝ}
    (hLam : ∀ x ∈ W, a x ≤ Lam)
    {g : Vec d → ℝ} (hg : MemLp g 2 (volume.restrict W)) :
    MemLp (fun x ↦ Real.sqrt (a x) * g x) 2 (volume.restrict W) := by
  have hmeas : AEStronglyMeasurable (fun x ↦ Real.sqrt (a x) * g x)
      (volume.restrict W) :=
    (Real.continuous_sqrt.comp hcont).aestronglyMeasurable.mul hg.1
  refine hg.of_le_mul (c := Real.sqrt Lam) hmeas ?_
  filter_upwards [ae_restrict_mem hWmeas] with x hx
  have hsqrt : Real.sqrt (a x) ≤ Real.sqrt Lam :=
    Real.sqrt_le_sqrt (hLam x hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right hsqrt (abs_nonneg _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
