import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveMaximumPrinciple
import Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-!
# The zero-trace order ideal needed for domain monotonicity

The comparison of zero-Dirichlet massive solutions on nested domains uses the
fact that `(u - v)₊` has zero trace when `u` has zero trace and `v` is
nonnegative.  This is obtained without a separate trace theorem from the
matched-trace truncation lemma: apply it to `u - v` and `-v`, whose difference
is `u`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization

noncomputable section

variable {d : ℕ}

/-- The weak equation is invariant under changing the value and gradient
representatives almost everywhere. -/
theorem IsMassiveWeakSolutionOn.congr {W : Set (Vec d)}
    {c rho : Vec d → ℝ} {mu : ℝ} {u v : H1Function W} {f : Vec d → ℝ}
    (hfun : u.toFun =ᵐ[volume.restrict W] v.toFun)
    (hgrad : u.grad =ᵐ[volume.restrict W] v.grad)
    (hu : IsMassiveWeakSolutionOn c rho mu W u f) :
    IsMassiveWeakSolutionOn c rho mu W v f := by
  intro φ
  have hEq := hu φ
  have hmass :
      (∫ x in W, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume) =
        ∫ x in W, rho x * v.toFun x * φ.toH1Function.toFun x ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hfun] with x hx
    rw [hx]
  have henergy :
      (∫ x in W, vecDot (c x • u.grad x) (φ.toH1Function.grad x) ∂volume) =
        ∫ x in W, vecDot (c x • v.grad x) (φ.toH1Function.grad x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  rwa [hmass, henergy] at hEq

/-- A weak massive equation restricts to an open subdomain.  Tests are
extended by zero to the original domain. -/
theorem IsMassiveWeakSolutionOn.restrict {W V : Set (Vec d)}
    (hWopen : IsOpen W) (hVopen : IsOpen V) (hWV : W ⊆ V)
    {c rho : Vec d → ℝ} {mu : ℝ} {u : H1Function V} {f : Vec d → ℝ}
    (hu : IsMassiveWeakSolutionOn c rho mu V u f) :
    IsMassiveWeakSolutionOn c rho mu W (u.restrict hWopen hWV) f := by
  intro φ
  have hWmeas := hWopen.measurableSet
  let ψ : H10Function V := φ.extendByZeroToOpenSuperset hWmeas hVopen hWV
  have hEq := hu ψ
  have hmass :
      (∫ x in V, rho x * u.toFun x * ψ.toH1Function.toFun x ∂volume) =
        ∫ x in W, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume := by
    calc
      _ = ∫ x in W, rho x * u.toFun x * ψ.toH1Function.toFun x ∂volume :=
        setIntegral_eq_of_subset_of_forall_diff_eq_zero hVopen.measurableSet hWV
          (fun x hx ↦ by
            rw [show ψ.toH1Function.toFun x = 0 by
              exact φ.zeroExtension_apply_of_not_mem hx.2]
            ring)
      _ = _ := integral_congr_ae (by
        filter_upwards [ae_restrict_mem hWmeas] with x hx
        rw [show ψ.toH1Function.toFun x = φ.toH1Function.toFun x by
          exact φ.zeroExtension_apply_of_mem hx])
  have henergy :
      (∫ x in V, vecDot (c x • u.grad x) (ψ.toH1Function.grad x) ∂volume) =
        ∫ x in W, vecDot (c x • u.grad x) (φ.toH1Function.grad x) ∂volume := by
    calc
      _ = ∫ x in W, vecDot (c x • u.grad x) (ψ.toH1Function.grad x) ∂volume :=
        setIntegral_eq_of_subset_of_forall_diff_eq_zero hVopen.measurableSet hWV
          (fun x hx ↦ by
            rw [show ψ.toH1Function.grad x = 0 by
              exact φ.zeroExtensionGrad_apply_of_not_mem hx.2]
            exact vecDot_zero_right _)
      _ = _ := integral_congr_ae (by
        filter_upwards [ae_restrict_mem hWmeas] with x hx
        rw [show ψ.toH1Function.grad x = φ.toH1Function.grad x by
          exact φ.zeroExtensionGrad_apply_of_mem hx])
  have hrhs :
      (∫ x in V, rho x * f x * ψ.toH1Function.toFun x ∂volume) =
        ∫ x in W, rho x * f x * φ.toH1Function.toFun x ∂volume := by
    calc
      _ = ∫ x in W, rho x * f x * ψ.toH1Function.toFun x ∂volume :=
        setIntegral_eq_of_subset_of_forall_diff_eq_zero hVopen.measurableSet hWV
          (fun x hx ↦ by
            rw [show ψ.toH1Function.toFun x = 0 by
              exact φ.zeroExtension_apply_of_not_mem hx.2]
            ring)
      _ = _ := integral_congr_ae (by
        filter_upwards [ae_restrict_mem hWmeas] with x hx
        rw [show ψ.toH1Function.toFun x = φ.toH1Function.toFun x by
          exact φ.zeroExtension_apply_of_mem hx])
  rw [hmass, henergy, hrhs] at hEq
  exact hEq

/-- If `u` has zero trace and `v` is pointwise nonnegative, then `(u-v)₊`
has zero trace.  The returned gradient is the usual truncated gradient. -/
theorem exists_h10_positivePart_sub_of_nonneg {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) (u : H10Function W) (v : H1Function W)
    (hv : ∀ x, 0 ≤ v.toFun x) :
    ∃ w : H10Function W,
      (∀ x, w.toH1Function.toFun x = max (u.toH1Function.toFun x - v.toFun x) 0) ∧
        w.toH1Function.grad =ᵐ[volume.restrict W]
          fun x ↦ {y | v.toFun y < u.toH1Function.toFun y}.indicator
            (u.toH1Function.grad - v.grad) x := by
  let w₁ : H1Function W := u.toH1Function - v
  let w₂ : H1Function W := -v
  have hmatch : MemH10 W (fun x ↦ w₁.toFun x - w₂.toFun x) := by
    refine ⟨u, ?_⟩
    funext x
    simp only [w₁, w₂, H1Function.sub_toFun, H1Function.neg_toFun]
    ring
  have hmem := memH10_max_sub_matched hW w₁ w₂ hmatch 0
  have hzero : ∀ x, max (w₂.toFun x - 0) 0 = 0 := by
    intro x
    simp only [w₂, H1Function.neg_toFun, sub_zero]
    exact max_eq_right (neg_nonpos.mpr (hv x))
  have hmem' : MemH10 W
      (fun x ↦ max (u.toH1Function.toFun x - v.toFun x) 0) := by
    refine hmem.imp fun z hz ↦ ?_
    rw [hz]
    funext x
    rw [hzero x, sub_zero]
    simp only [w₁, H1Function.sub_toFun, sub_zero]
  obtain ⟨w, hwf⟩ := hmem'
  obtain ⟨z, hzf, hzg⟩ := exists_h1_max_sub_const hW w₁ 0
  have hwfx : ∀ x,
      w.toH1Function.toFun x = max (u.toH1Function.toFun x - v.toFun x) 0 := by
    intro x
    rw [hwf]
  have heq : w.toH1Function.toFun =ᵐ[volume.restrict W] z.toFun := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [hwfx x, hzf]
    simp only [w₁, H1Function.sub_toFun, sub_zero]
  refine ⟨w, hwfx, ?_⟩
  have hgrad := Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
    hW.isOpen heq
  refine hgrad.trans ?_
  filter_upwards [hzg] with x hx
  rw [hx]
  congr 1
  · ext y
    simp only [Set.mem_setOf_eq, w₁, H1Function.sub_toFun]
    exact sub_pos
  · exact H1Function.sub_grad u.toH1Function v

/-- Comparison on one domain when only the upper competitor is known to be
nonnegative on the boundary: a zero-trace solution cannot exceed it. -/
theorem ae_le_of_massiveWeakSolutions_of_nonneg_comparison
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {c rho : Vec d → ℝ} {mu lam Lam rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hc : ∀ x ∈ W, lam ≤ c x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {u : H10Function W} {v : H1Function W} {f : Vec d → ℝ}
    (hvnonneg : ∀ x, 0 ≤ v.toFun x)
    (hu : IsMassiveWeakSolutionOn c rho mu W u.toH1Function f)
    (hv : IsMassiveWeakSolutionOn c rho mu W v f) :
    u.toH1Function.toFun ≤ᵐ[volume.restrict W] v.toFun := by
  have hWmeas := hW.isOpen.measurableSet
  obtain ⟨w, hwf, hwg⟩ := exists_h10_positivePart_sub_of_nonneg hW u v hvnonneg
  have hEqU := hu w
  have hEqV := hv w
  have hmassU : IntegrableOn
      (fun x ↦ rho x * u.toH1Function.toFun x * w.toH1Function.toFun x) W :=
    integrableOn_mass_term hrhoMeas hrhoBdd u.toH1Function.memL2 w.toH1Function.memL2
  have hmassV : IntegrableOn
      (fun x ↦ rho x * v.toFun x * w.toH1Function.toFun x) W :=
    integrableOn_mass_term hrhoMeas hrhoBdd v.memL2 w.toH1Function.memL2
  have hmassSplit :
      (∫ x in W, rho x * u.toH1Function.toFun x * w.toH1Function.toFun x ∂volume) -
          ∫ x in W, rho x * v.toFun x * w.toH1Function.toFun x ∂volume =
        ∫ x in W, rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume := by
    rw [← integral_sub hmassU hmassV]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    change rho x * u.toH1Function.toFun x * w.toH1Function.toFun x -
        rho x * v.toFun x * w.toH1Function.toFun x =
      rho x * w.toH1Function.toFun x * w.toH1Function.toFun x
    rw [hwf x]
    rcases le_or_gt (u.toH1Function.toFun x) (v.toFun x) with hle | hgt
    · rw [max_eq_right (sub_nonpos.mpr hle)]
      ring
    · rw [max_eq_left (sub_nonneg.mpr hgt.le)]
      ring
  have henU : IntegrableOn
      (fun x ↦ vecDot (c x • u.toH1Function.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_energy_term hEll u.toH1Function.grad_memVectorL2
      w.toH1Function.grad_memVectorL2
  have henV : IntegrableOn
      (fun x ↦ vecDot (c x • v.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_energy_term hEll v.grad_memVectorL2 w.toH1Function.grad_memVectorL2
  have henSplit :
      (∫ x in W, vecDot (c x • u.toH1Function.grad x) (w.toH1Function.grad x) ∂volume) -
          ∫ x in W, vecDot (c x • v.grad x) (w.toH1Function.grad x) ∂volume =
        ∫ x in W, c x * vecNormSq (w.toH1Function.grad x) ∂volume := by
    rw [← integral_sub henU henV]
    refine integral_congr_ae ?_
    filter_upwards [hwg] with x hx
    rw [hx]
    have vecDotSubLeft (a b z : Vec d) :
        vecDot (a - b) z = vecDot a z - vecDot b z := by
      simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
    by_cases hpos : x ∈ {y | v.toFun y < u.toH1Function.toFun y}
    · rw [Set.indicator_of_mem hpos]
      rw [← vecDotSubLeft, ← smul_sub, vecDot_smul_left]
      rfl
    · rw [Set.indicator_of_notMem hpos]
      simp [vecNormSq, vecDot_zero_right]
  have hid :
      mu * ∫ x in W, rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume +
          ∫ x in W, c x * vecNormSq (w.toH1Function.grad x) ∂volume = 0 := by
    have hkey :
        mu * ((∫ x in W, rho x * u.toH1Function.toFun x * w.toH1Function.toFun x ∂volume) -
          ∫ x in W, rho x * v.toFun x * w.toH1Function.toFun x ∂volume) +
          ((∫ x in W, vecDot (c x • u.toH1Function.grad x) (w.toH1Function.grad x) ∂volume) -
            ∫ x in W, vecDot (c x • v.grad x) (w.toH1Function.grad x) ∂volume) = 0 := by
      linarith [hEqU, hEqV]
    rwa [hmassSplit, henSplit] at hkey
  have hmassNonneg : 0 ≤ ∫ x in W,
      rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume := by
    refine setIntegral_nonneg hWmeas fun x hx ↦ ?_
    have := mul_nonneg (le_trans hrhoMin.le (hrhoLow x hx))
      (mul_self_nonneg (w.toH1Function.toFun x))
    simpa [mul_assoc] using this
  have henergyNonneg : 0 ≤ ∫ x in W,
      c x * vecNormSq (w.toH1Function.grad x) ∂volume := by
    refine setIntegral_nonneg hWmeas fun x hx ↦ ?_
    exact mul_nonneg (le_trans hlam.le (hc x hx)) (vecNormSq_nonneg _)
  have hmassZero : ∫ x in W,
      rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume = 0 := by
    have : mu * ∫ x in W,
        rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume = 0 := by
      apply le_antisymm
      · linarith [hid, henergyNonneg]
      · exact mul_nonneg hmu.le hmassNonneg
    exact (mul_eq_zero.1 this).resolve_left hmu.ne'
  have hmassInt : IntegrableOn
      (fun x ↦ rho x * w.toH1Function.toFun x * w.toH1Function.toFun x) W :=
    integrableOn_mass_term hrhoMeas hrhoBdd w.toH1Function.memL2 w.toH1Function.memL2
  have hmassAe : (fun x ↦ rho x * w.toH1Function.toFun x * w.toH1Function.toFun x)
      =ᵐ[volume.restrict W] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ hmassInt.integrable).1 hmassZero
    filter_upwards [ae_restrict_mem hWmeas] with x hx
    have := mul_nonneg (le_trans hrhoMin.le (hrhoLow x hx))
      (mul_self_nonneg (w.toH1Function.toFun x))
    simpa [mul_assoc] using this
  filter_upwards [hmassAe, ae_restrict_mem hWmeas] with x hx hxW
  have hrhoPos : 0 < rho x := lt_of_lt_of_le hrhoMin (hrhoLow x hxW)
  have hwzero : w.toH1Function.toFun x = 0 := by
    apply mul_self_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hrhoPos.ne'
    simpa [mul_assoc] using hx
  rw [hwf x] at hwzero
  exact sub_nonpos.mp (max_eq_right_iff.mp hwzero)

/-- **Domain monotonicity for the massive Dirichlet problem.**  For a
nonnegative source, the zero-boundary solution on a smaller domain is bounded
above by the zero-boundary solution on a larger domain. -/
theorem ae_le_of_massiveWeakSolutionsOn_nestedDomains
    {W V : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    (hV : IsOpenBoundedConvexDomain V) (hWV : W ⊆ V)
    {c rho : Vec d → ℝ} {mu lamW LamW lamV rhoMinW rhoMinV rhoMaxW rhoMaxV : ℝ}
    (hmu : 0 < mu) (hrhoMinW : 0 < rhoMinW) (hrhoMinV : 0 < rhoMinV)
    (hlamW : 0 < lamW) (hlamV : 0 < lamV)
    (hEllW : IsEllipticFieldOn lamW LamW W (scalarCoeffField c))
    (hcW : ∀ x ∈ W, lamW ≤ c x) (hcV : ∀ x ∈ V, lamV ≤ c x)
    (hrhoMeasW : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoMeasV : AEStronglyMeasurable rho (volume.restrict V))
    (hrhoLowW : ∀ x ∈ W, rhoMinW ≤ rho x)
    (hrhoLowV : ∀ x ∈ V, rhoMinV ≤ rho x)
    (hrhoBddW : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMaxW)
    (hrhoBddV : ∀ᵐ x ∂(volume.restrict V), |rho x| ≤ rhoMaxV)
    {u : H10Function W} {v : H10Function V} {f : Vec d → ℝ}
    (hfL2V : MemL2On V f) (hf : ∀ x ∈ V, 0 ≤ f x)
    (hu : IsMassiveWeakSolutionOn c rho mu W u.toH1Function f)
    (hv : IsMassiveWeakSolutionOn c rho mu V v.toH1Function f) :
    u.toH1Function.toFun ≤ᵐ[volume.restrict W] v.toH1Function.toFun := by
  have hvNonneg := ae_nonneg_of_isMassiveWeakSolutionOn hV hmu hrhoMinV hlamV hcV
    hrhoMeasV hrhoLowV hrhoBddV hfL2V hf hv
  obtain ⟨vpos, hvposFun, _⟩ := exists_h1_max_sub_const hV v.toH1Function 0
  have hvposEq : vpos.toFun =ᵐ[volume.restrict V] v.toH1Function.toFun := by
    filter_upwards [hvNonneg] with x hx
    rw [hvposFun]
    simpa using max_eq_left hx
  have hvposGrad : vpos.grad =ᵐ[volume.restrict V] v.toH1Function.grad :=
    Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hV.isOpen hvposEq
  have hvposSol : IsMassiveWeakSolutionOn c rho mu V vpos f :=
    hv.congr hvposEq.symm hvposGrad.symm
  let vW : H1Function W := vpos.restrict hW.isOpen hWV
  have hvWSol : IsMassiveWeakSolutionOn c rho mu W vW f :=
    hvposSol.restrict hW.isOpen hV.isOpen hWV
  have hvWNonneg : ∀ x, 0 ≤ vW.toFun x := by
    intro x
    change 0 ≤ vpos.toFun x
    rw [hvposFun]
    exact le_max_right _ _
  have hcomp := ae_le_of_massiveWeakSolutions_of_nonneg_comparison hW hmu hrhoMinW
    hlamW hEllW hcW hrhoMeasW hrhoLowW hrhoBddW hvWNonneg hu hvWSol
  have hvposEqW : vpos.toFun =ᵐ[volume.restrict W] v.toH1Function.toFun :=
    ae_restrict_of_ae_restrict_of_subset hWV hvposEq
  filter_upwards [hcomp, hvposEqW] with x hx hxeq
  exact hx.trans_eq hxeq

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
