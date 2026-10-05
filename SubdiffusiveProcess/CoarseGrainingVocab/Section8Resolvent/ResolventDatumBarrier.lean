module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSmoothSolution

@[expose] public section

/-!
# Comparison of a zero-boundary massive solution with a smooth supersolution

The whole-space maximum principle of `ResolventDatumUniqueness.lean` compares a
solution with a *constant* level, which is enough for the sup-norm contraction
but says nothing at infinity.  This module upgrades the comparison level from a
constant to an arbitrary smooth nonnegative **supersolution** `b`, i.e. a smooth
`b ≥ 0` whose classical massive forcing dominates the datum:

  `f ≤ μ b − ρ⁻¹ ∇·(c ∇b)`   pointwise on `W`.

For a zero-boundary solution `u ∈ H¹₀(W)` the conclusion is `u ≤ b` almost
everywhere on `W`, *with no constant depending on `W`*.  Applied to the centred
cube exhaustion of `Section8Massive/CompactSupportCubeFamily.lean` this is the
only mechanism by which a decay rate at infinity can be transferred to the
minimal whole-space solution: the barrier is chosen once, and each cube solution
is trapped under it.

The proof is Stampacchia's, with the level `k` of
`MassiveMaximumPrinciple.ae_le_of_isMassiveWeakSolutionOn` replaced by `b`:

* `b` is itself a massive weak solution on `W` with its classical forcing
  (`isMassiveWeakSolutionOn_ofContDiffOnBounded`, P-195), so `v := u − b` solves
  the equation with the nonpositive forcing `f − (μ b − ρ⁻¹∇·(c∇b))`;
* `v₊ ∈ H¹₀(W)`, because `v − (−b) = u ∈ H¹₀(W)` and `(−b)₊ = 0`, by the
  matched-trace truncation `Homogenization.memH10_max_sub_matched`;
* testing against `v₊` makes the energy and mass terms nonnegative and the
  right-hand side nonpositive, so `v₊ = 0`.

## Main declarations

* `exists_h10_positivePart_of_memH10` — the positive part with its weak gradient.
* `ae_nonpos_of_isMassiveWeakSolutionOn_of_memH10_posPart` — the abstract
  one-sided principle for an `H¹` solution with `H¹₀` positive part.
* `ae_le_barrier_of_isMassiveWeakSolutionOn` — the comparison with a smooth
  supersolution.

## References

* `s.fixed.coefficient` and `mfd:sec-speed` (the massive equation).
* `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### The positive part of an `H¹` function with `H¹₀` positive part -/

/-- The positive part of an `H¹` function, once it is known to lie in `H¹₀`,
comes with the expected weak gradient `1_{v>0} ∇v`. -/
theorem exists_h10_positivePart_of_memH10 {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) (v : H1Function W)
    (hmem : MemH10 W fun x ↦ max (v.toFun x) 0) :
    ∃ w : H10Function W,
      (∀ x, w.toH1Function.toFun x = max (v.toFun x) 0) ∧
        w.toH1Function.grad =ᵐ[volume.restrict W]
          fun x ↦ {y | (0 : ℝ) < v.toFun y}.indicator v.grad x := by
  obtain ⟨w, hwf⟩ := hmem
  obtain ⟨V, hVf, hVg⟩ := exists_h1_max_sub_const hW v 0
  have hwfx : ∀ x, w.toH1Function.toFun x = max (v.toFun x) 0 := by
    intro x
    rw [hwf]
  have hEq : w.toH1Function.toFun =ᵐ[volume.restrict W] V.toFun := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [hwfx x, hVf]
    show max (v.toFun x) 0 = max (v.toFun x - 0) 0
    rw [sub_zero]
  refine ⟨w, hwfx, ?_⟩
  have hgrad := Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
    hW.isOpen hEq
  refine hgrad.trans (hVg.mono fun x hx ↦ ?_)
  rw [hx]

/-! ### The one-sided principle for a nonpositive forcing -/

/-- **Stampacchia with a nonpositive forcing.**  If `v` solves the massive
equation on `W` with a forcing `g ≤ 0` and its positive part lies in `H¹₀(W)`,
then `v ≤ 0` almost everywhere. -/
theorem ae_nonpos_of_isMassiveWeakSolutionOn_of_memH10_posPart
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {c rho : Vec d → ℝ} {mu lam rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin) (hlam : 0 < lam)
    (hc : ∀ x ∈ W, lam ≤ c x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {v : H1Function W} (hmem : MemH10 W fun x ↦ max (v.toFun x) 0)
    {g : Vec d → ℝ} (hgL2 : MemL2On W g) (hg : ∀ x ∈ W, g x ≤ 0)
    (hv : IsMassiveWeakSolutionOn c rho mu W v g) :
    ∀ᵐ x ∂(volume.restrict W), v.toFun x ≤ 0 := by
  classical
  have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
  obtain ⟨w, hwf, hwg⟩ := exists_h10_positivePart_of_memH10 hW v hmem
  have hwnn : ∀ x, 0 ≤ w.toH1Function.toFun x := fun x ↦ by
    rw [hwf x]; exact le_max_right _ _
  have heq := hv w
  have hE : 0 ≤ ∫ x in W, vecDot (c x • v.grad x) (w.toH1Function.grad x) ∂volume := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hwg, ae_restrict_mem hWmeas] with x hx hxW
    rw [hx]
    by_cases hmem' : x ∈ {y | (0 : ℝ) < v.toFun y}
    · rw [Set.indicator_of_mem hmem', vecDot_smul_left]
      exact mul_nonneg (le_trans hlam.le (hc x hxW)) (vecNormSq_nonneg _)
    · rw [Set.indicator_of_notMem hmem']
      simp [vecDot]
  have hmassU : Integrable
      (fun x ↦ rho x * v.toFun x * w.toH1Function.toFun x) (volume.restrict W) :=
    integrableOn_mass_term hrhoMeas hrhoBdd v.memL2 w.toH1Function.memL2
  have hmassF : Integrable
      (fun x ↦ rho x * g x * w.toH1Function.toFun x) (volume.restrict W) :=
    integrableOn_mass_term hrhoMeas hrhoBdd hgL2 w.toH1Function.memL2
  have hmassW : Integrable
      (fun x ↦ rho x * w.toH1Function.toFun x * w.toH1Function.toFun x)
      (volume.restrict W) :=
    integrableOn_mass_term hrhoMeas hrhoBdd w.toH1Function.memL2 w.toH1Function.memL2
  have hpt : ∀ᵐ x ∂(volume.restrict W),
      mu * (rho x * w.toH1Function.toFun x * w.toH1Function.toFun x) ≤
        mu * (rho x * v.toFun x * w.toH1Function.toFun x) -
          rho x * g x * w.toH1Function.toFun x := by
    filter_upwards [ae_restrict_mem hWmeas] with x hxW
    have hr : 0 ≤ rho x := le_trans hrhoMin.le (hrhoLow x hxW)
    have hrw : 0 ≤ rho x * w.toH1Function.toFun x := mul_nonneg hr (hwnn x)
    have hsq : w.toH1Function.toFun x * v.toFun x =
        w.toH1Function.toFun x * w.toH1Function.toFun x := by
      rcases le_or_gt (v.toFun x) 0 with hle | hgt
      · have hz : w.toH1Function.toFun x = 0 := by
          rw [hwf x]; exact max_eq_right hle
        rw [hz]; ring
      · have hz : w.toH1Function.toFun x = v.toFun x := by
          rw [hwf x]; exact max_eq_left hgt.le
        rw [hz]
    have hkey : rho x * g x * w.toH1Function.toFun x ≤ 0 := by
      have hcomm : rho x * g x * w.toH1Function.toFun x =
          rho x * w.toH1Function.toFun x * g x := by ring
      rw [hcomm]
      exact mul_nonpos_of_nonneg_of_nonpos hrw (hg x hxW)
    have hprod : rho x * v.toFun x * w.toH1Function.toFun x =
        rho x * w.toH1Function.toFun x * w.toH1Function.toFun x := by
      calc rho x * v.toFun x * w.toH1Function.toFun x
          = rho x * (w.toH1Function.toFun x * v.toFun x) := by ring
        _ = rho x * (w.toH1Function.toFun x * w.toH1Function.toFun x) := by rw [hsq]
        _ = rho x * w.toH1Function.toFun x * w.toH1Function.toFun x := by ring
    rw [hprod]
    linarith [hkey]
  have hint : mu * ∫ x in W,
      rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume ≤
      mu * (∫ x in W, rho x * v.toFun x * w.toH1Function.toFun x ∂volume) -
        ∫ x in W, rho x * g x * w.toH1Function.toFun x ∂volume := by
    have hRint : Integrable
        (fun x ↦ mu * (rho x * v.toFun x * w.toH1Function.toFun x) -
          rho x * g x * w.toH1Function.toFun x) (volume.restrict W) :=
      (hmassU.const_mul mu).sub hmassF
    have hle := integral_mono_ae (hmassW.const_mul mu) hRint hpt
    rwa [integral_const_mul, integral_sub (hmassU.const_mul mu) hmassF,
      integral_const_mul] at hle
  have hWnn : 0 ≤ ∫ x in W,
      rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume := by
    refine setIntegral_nonneg hWmeas fun x hx ↦ ?_
    have hr : 0 ≤ rho x := le_trans hrhoMin.le (hrhoLow x hx)
    have hnn : 0 ≤ rho x * (w.toH1Function.toFun x * w.toH1Function.toFun x) :=
      mul_nonneg hr (mul_self_nonneg _)
    simpa [mul_assoc] using hnn
  have hzero : ∫ x in W,
      rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume = 0 := by
    have hmul : mu * ∫ x in W,
        rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume ≤ 0 := by
      linarith [hE, heq, hint]
    have hnn : 0 ≤ mu * ∫ x in W,
        rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume :=
      mul_nonneg hmu.le hWnn
    have hzz : mu * ∫ x in W,
        rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume = 0 :=
      le_antisymm hmul hnn
    exact (mul_eq_zero.1 hzz).resolve_left hmu.ne'
  have hAe : (fun x ↦ rho x * w.toH1Function.toFun x * w.toH1Function.toFun x)
      =ᵐ[volume.restrict W] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ hmassW).1 hzero
    filter_upwards [ae_restrict_mem hWmeas] with x hx
    have hr : 0 ≤ rho x := le_trans hrhoMin.le (hrhoLow x hx)
    have hnn : 0 ≤ rho x * (w.toH1Function.toFun x * w.toH1Function.toFun x) :=
      mul_nonneg hr (mul_self_nonneg _)
    simpa [mul_assoc] using hnn
  filter_upwards [hAe, ae_restrict_mem hWmeas] with x hx hxW
  by_contra hcon
  push Not at hcon
  have hwx : w.toH1Function.toFun x = v.toFun x := by
    rw [hwf x]; exact max_eq_left hcon.le
  have hr : rhoMin ≤ rho x := hrhoLow x hxW
  have hx0 : rho x * w.toH1Function.toFun x * w.toH1Function.toFun x = 0 := hx
  rw [hwx] at hx0
  have hrpos : 0 < rho x := lt_of_lt_of_le hrhoMin hr
  nlinarith [mul_pos hcon hcon, hrpos]

/-! ### Comparison with a smooth supersolution -/

/-- The classical forcing of a smooth barrier is square integrable on a bounded
domain with a positive lower bound on the weight. -/
theorem memL2On_smoothMassiveForcing {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) {c rho b : Vec d → ℝ} {mu rhoMin : ℝ}
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin)
    (hcC1 : ContDiff ℝ 1 c) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x) :
    MemL2On W (smoothMassiveForcing c rho mu b) := by
  classical
  let : MeasureTheory.IsFiniteMeasure (volume.restrict W) :=
    hW.isSobolevRegularDomain.isFiniteMeasure_restrict_volume
  have hcompact : IsCompact (closure W) :=
    hW.isSobolevRegularDomain.isBoundedDomain.isBounded.isCompact_closure
  obtain ⟨Cb, hCb⟩ := hcompact.exists_bound_of_continuousOn hb.continuous.continuousOn
  obtain ⟨Cdiv, hCdiv⟩ := hcompact.exists_bound_of_continuousOn
    (continuous_coeffFluxDiv hcC1 hb).continuousOn
  have hmeas : AEStronglyMeasurable (smoothMassiveForcing c rho mu b)
      (volume.restrict W) := by
    have hnum : AEMeasurable (fun x ↦ coeffFluxDiv c b x) (volume.restrict W) :=
      (continuous_coeffFluxDiv hcC1 hb).measurable.aemeasurable
    have hden : AEMeasurable rho (volume.restrict W) := hrhoMeas.aemeasurable
    have hquot := (hnum.div hden).aestronglyMeasurable
    exact (continuous_const.mul hb.continuous).aestronglyMeasurable.sub hquot
  refine MeasureTheory.MemLp.of_bound hmeas (mu * Cb + Cdiv / rhoMin) ?_
  rw [MeasureTheory.ae_restrict_iff' hW.isOpen.measurableSet]
  refine Filter.Eventually.of_forall fun x hx ↦ ?_
  have hxc : x ∈ closure W := subset_closure hx
  have hbx : |b x| ≤ Cb := by simpa [Real.norm_eq_abs] using hCb x hxc
  have hdx : |coeffFluxDiv c b x| ≤ Cdiv := by
    simpa [Real.norm_eq_abs] using hCdiv x hxc
  have hrx : rhoMin ≤ rho x := hrhoLow x hx
  have hrpos : 0 < rho x := lt_of_lt_of_le hrhoMin hrx
  have hquot : |coeffFluxDiv c b x / rho x| ≤ Cdiv / rhoMin := by
    rw [abs_div, abs_of_pos hrpos]
    have hCd0 : 0 ≤ Cdiv := le_trans (abs_nonneg _) hdx
    calc |coeffFluxDiv c b x| / rho x ≤ Cdiv / rho x := by gcongr
      _ ≤ Cdiv / rhoMin := by gcongr
  have hnorm : ‖smoothMassiveForcing c rho mu b x‖ ≤ mu * Cb + Cdiv / rhoMin := by
    have hsplit : ‖smoothMassiveForcing c rho mu b x‖ ≤
        |mu * b x| + |coeffFluxDiv c b x / rho x| := by
      have habs : |mu * b x - coeffFluxDiv c b x / rho x| ≤
          |mu * b x| + |coeffFluxDiv c b x / rho x| := by
        rcases abs_cases (mu * b x) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          rcases abs_cases (coeffFluxDiv c b x / rho x) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
            rcases abs_cases (mu * b x - coeffFluxDiv c b x / rho x) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
              linarith
      simpa [smoothMassiveForcing, Real.norm_eq_abs] using habs
    have hmul : |mu * b x| ≤ mu * Cb := by
      rw [abs_mul, abs_of_pos hmu]
      exact mul_le_mul_of_nonneg_left hbx hmu.le
    linarith
  exact hnorm

/-- **Comparison with a smooth supersolution.**  Let `b ≥ 0` be smooth with
`f ≤ μ b − ρ⁻¹ ∇·(c ∇b)` pointwise on the bounded convex domain `W`.  Then every
zero-boundary massive solution on `W` with datum `f` satisfies `u ≤ b` almost
everywhere on `W`.

The bound is uniform in `W`: nothing on the right-hand side depends on the
domain.  This is what transfers a decay rate at infinity from the barrier to the
whole-space limit of the centred cube exhaustion. -/
theorem ae_le_barrier_of_isMassiveWeakSolutionOn
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {c rho b : Vec d → ℝ} {mu lam Lam rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hc : ∀ x ∈ W, lam ≤ c x) (hcC1 : ContDiff ℝ 1 c)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hrhoNe : ∀ x, rho x ≠ 0)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbnn : ∀ x, 0 ≤ b x)
    {u : H10Function W} {f : Vec d → ℝ} (hfL2 : MemL2On W f)
    (hf : ∀ x ∈ W, f x ≤ smoothMassiveForcing c rho mu b x)
    (hu : IsMassiveWeakSolutionOn c rho mu W u.toH1Function f) :
    ∀ᵐ x ∂(volume.restrict W), u.toH1Function.toFun x ≤ b x := by
  classical
  set Bh : H1Function W :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hW (hb.of_le (by simp)) with hBdef
  have hBfun : ∀ x, Bh.toFun x = b x := fun _ ↦ rfl
  have hBsol : IsMassiveWeakSolutionOn c rho mu W Bh
      (smoothMassiveForcing c rho mu b) :=
    isMassiveWeakSolutionOn_ofContDiffOnBounded hcC1 hb hW hrhoMeas hrhoBdd hrhoNe
  have hFL2 : MemL2On W (smoothMassiveForcing c rho mu b) :=
    memL2On_smoothMassiveForcing hW hmu hrhoMin hcC1 hb hrhoMeas hrhoLow
  have hvsol := hu.sub hEll hrhoMeas hrhoBdd hfL2 hFL2 hBsol
  set v : H1Function W := u.toH1Function - Bh with hvdef
  have hvfun : ∀ x, v.toFun x = u.toH1Function.toFun x - b x := by
    intro x
    rw [hvdef, H1Function.sub_toFun]
    rfl
  have hmatch : MemH10 W fun x ↦ v.toFun x - (-Bh).toFun x := by
    refine ⟨u, ?_⟩
    funext x
    simp only [hvfun x, H1Function.neg_toFun, hBfun x]
    ring
  have hmem0 := memH10_max_sub_matched hW v (-Bh) hmatch 0
  have hmem : MemH10 W fun x ↦ max (v.toFun x) 0 := by
    have hfun : (fun x ↦ max (v.toFun x - 0) 0 - max ((-Bh).toFun x - 0) 0) =
        fun x ↦ max (v.toFun x) 0 := by
      funext x
      have hneg : (-Bh).toFun x = -(b x) := by
        simp only [H1Function.neg_toFun, hBfun x]
      rw [hneg, sub_zero, sub_zero]
      have : max (-(b x)) 0 = 0 := max_eq_right (neg_nonpos.mpr (hbnn x))
      rw [this, sub_zero]
    rwa [hfun] at hmem0
  have hgL2 : MemL2On W (fun x ↦ f x - smoothMassiveForcing c rho mu b x) :=
    hfL2.sub hFL2
  have hg : ∀ x ∈ W, f x - smoothMassiveForcing c rho mu b x ≤ 0 := by
    intro x hx
    have := hf x hx
    linarith
  have hkey := ae_nonpos_of_isMassiveWeakSolutionOn_of_memH10_posPart hW hmu hrhoMin
    hlam hc hrhoMeas hrhoLow hrhoBdd hmem hgL2 hg hvsol
  filter_upwards [hkey] with x hx
  rw [hvfun x] at hx
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
