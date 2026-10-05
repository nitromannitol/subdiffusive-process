module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
public import Homogenization.Sobolev.Truncation.MatchedTrace
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

@[expose] public section

/-!
# The maximum principle for the local resolvent

The `C₀` package of
`SubdiffusiveProcess/CoarseGrainingVocab/Section8Resolvent/C0ResolventPackage.lean` needs two
pointwise facts about `R_μ`, positivity and the contraction
`μ ‖R_μ f‖_∞ ≤ ‖f‖_∞`.  Both are consequences of the one-sided maximum principle
proved here for the local (zero-boundary) resolvent `R_μ^W` of the pair `(c, ρ)`
of `s.fixed.coefficient` and `mfd:sec-speed`:

> if `f ≤ μ k` on `W` with `k ≥ 0`, then `R_μ^W f ≤ k` almost everywhere on `W`.

The proof is Stampacchia's: test the weak equation against the truncation
`w = (u - k)_+`, which lies in `H¹₀(W)` because `u` does
(`Homogenization.memH10_max_sub_matched`), and whose weak gradient is
`1_{u>k} ∇u` (`Homogenization.exists_h1_max_sub_const`).  The pointwise identity
`w (u - k) = w²` together with `f ≤ μ k` and `w ≥ 0` turns the equation into

  `∫_W c ∇u·∇w + μ ∫_W ρ w² ≤ 0`,

and both summands are nonnegative.

Taking `k = μ⁻¹‖f‖_∞` gives the upper contraction bound, and applying the
statement to `-u`, `-f` gives the lower one; positivity of `R_μ^W` is the case
`k = 0` for `-u`.  Those specializations are recorded as
`ae_abs_le_of_isMassiveWeakSolutionOn` and
`ae_nonneg_of_isMassiveWeakSolutionOn`.

## Main declarations

* `exists_h10_positivePart` — `(u - k)_+ ∈ H¹₀(W)` with its weak gradient.
* `ae_le_of_isMassiveWeakSolutionOn` — the one-sided maximum principle.
* `ae_nonneg_of_isMassiveWeakSolutionOn` — positivity of the local resolvent.
* `ae_abs_le_of_isMassiveWeakSolutionOn` — `μ |R_μ^W f| ≤ ‖f‖_∞` a.e.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### The truncation of a zero-trace function -/

/-- **The positive part above a nonnegative level stays in `H¹₀`.**  If
`u ∈ H¹₀(W)` and `k ≥ 0`, then `(u - k)_+ ∈ H¹₀(W)`, with weak gradient
`1_{u>k} ∇u`. -/
theorem exists_h10_positivePart {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) (u : H10Function W) {k : ℝ} (hk : 0 ≤ k) :
    ∃ w : H10Function W,
      (∀ x, w.toH1Function.toFun x = max (u.toH1Function.toFun x - k) 0) ∧
        w.toH1Function.grad =ᵐ[volume.restrict W]
          fun x ↦ {y | k < u.toH1Function.toFun y}.indicator u.toH1Function.grad x := by
  have hmatch : MemH10 W (fun x ↦ u.toH1Function.toFun x - (0 : H1Function W).toFun x) := by
    refine ⟨u, ?_⟩
    funext x
    show u.toH1Function.toFun x = u.toH1Function.toFun x - (0 : H1Function W).toFun x
    change u.toH1Function.toFun x = u.toH1Function.toFun x - (0 : Vec d → ℝ) x
    simp
  have hmem := memH10_max_sub_matched hW u.toH1Function 0 hmatch k
  have hzero : ∀ x, max ((0 : H1Function W).toFun x - k) 0 = 0 := by
    intro x
    change max ((0 : Vec d → ℝ) x - k) 0 = 0
    simp [hk]
  have hmem' : MemH10 W (fun x ↦ max (u.toH1Function.toFun x - k) 0) := by
    refine hmem.imp fun v hv ↦ ?_
    rw [hv]
    funext x
    rw [hzero x, sub_zero]
  obtain ⟨w, hwf⟩ := hmem'
  obtain ⟨V, hVf, hVg⟩ := exists_h1_max_sub_const hW u.toH1Function k
  have hwfx : ∀ x, w.toH1Function.toFun x = max (u.toH1Function.toFun x - k) 0 := by
    intro x
    rw [hwf]
  have hEq : w.toH1Function.toFun =ᵐ[volume.restrict W] V.toFun := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [hwfx x, hVf]
  refine ⟨w, hwfx, ?_⟩
  have hgrad := Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
    hW.isOpen hEq
  exact hgrad.trans hVg

/-! ### The one-sided maximum principle -/

/-- **The maximum principle for the local resolvent.**  If `u` solves the
zero-boundary massive problem `μ ρ u - ∇·(c∇u) = ρ f` on `W` and `f ≤ μ k` on `W`
for some `k ≥ 0`, then `u ≤ k` almost everywhere on `W`.

With `k = μ⁻¹ ‖f‖_∞` this is the upper half of the Hille--Yosida contraction
`μ ‖R_μ^W f‖_∞ ≤ ‖f‖_∞`; with `k = 0` and `f ≤ 0` it is positivity of `-R_μ^W`. -/
theorem ae_le_of_isMassiveWeakSolutionOn
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {c rho : Vec d → ℝ} {mu k lam rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hk : 0 ≤ k) (hrhoMin : 0 < rhoMin) (hlam : 0 < lam)
    (hc : ∀ x ∈ W, lam ≤ c x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {u : H10Function W} {f : Vec d → ℝ} (hfL2 : MemL2On W f)
    (hf : ∀ x ∈ W, f x ≤ mu * k)
    (hu : IsMassiveWeakSolutionOn c rho mu W u.toH1Function f) :
    ∀ᵐ x ∂(volume.restrict W), u.toH1Function.toFun x ≤ k := by
  classical
  have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
  obtain ⟨w, hwf, hwg⟩ := exists_h10_positivePart hW u hk
  have hwnn : ∀ x, 0 ≤ w.toH1Function.toFun x := fun x ↦ by rw [hwf x]; exact le_max_right _ _
  have heq := hu w
  -- the energy term is nonnegative
  have hE : 0 ≤ ∫ x in W,
      vecDot (c x • u.toH1Function.grad x) (w.toH1Function.grad x) ∂volume := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hwg, ae_restrict_mem hWmeas] with x hx hxW
    rw [hx]
    by_cases hmem : x ∈ {y | k < u.toH1Function.toFun y}
    · rw [Set.indicator_of_mem hmem, vecDot_smul_left]
      exact mul_nonneg (le_trans hlam.le (hc x hxW)) (vecNormSq_nonneg _)
    · rw [Set.indicator_of_notMem hmem]
      simp [vecDot]
  -- the pointwise Stampacchia inequality
  have hmassU : Integrable
      (fun x ↦ rho x * u.toH1Function.toFun x * w.toH1Function.toFun x)
      (volume.restrict W) :=
    integrableOn_mass_term hrhoMeas hrhoBdd u.toH1Function.memL2 w.toH1Function.memL2
  have hmassF : Integrable
      (fun x ↦ rho x * f x * w.toH1Function.toFun x) (volume.restrict W) :=
    integrableOn_mass_term hrhoMeas hrhoBdd hfL2 w.toH1Function.memL2
  have hmassW : Integrable
      (fun x ↦ rho x * w.toH1Function.toFun x * w.toH1Function.toFun x)
      (volume.restrict W) :=
    integrableOn_mass_term hrhoMeas hrhoBdd w.toH1Function.memL2 w.toH1Function.memL2
  have hpt : ∀ᵐ x ∂(volume.restrict W),
      mu * (rho x * w.toH1Function.toFun x * w.toH1Function.toFun x) ≤
        mu * (rho x * u.toH1Function.toFun x * w.toH1Function.toFun x) -
          rho x * f x * w.toH1Function.toFun x := by
    filter_upwards [ae_restrict_mem hWmeas] with x hxW
    have hr : 0 ≤ rho x := le_trans hrhoMin.le (hrhoLow x hxW)
    have hrw : 0 ≤ rho x * w.toH1Function.toFun x := mul_nonneg hr (hwnn x)
    have hsq : w.toH1Function.toFun x * (u.toH1Function.toFun x - k) =
        w.toH1Function.toFun x * w.toH1Function.toFun x := by
      rcases le_or_gt (u.toH1Function.toFun x) k with hle | hgt
      · have : w.toH1Function.toFun x = 0 := by
          rw [hwf x]
          exact max_eq_right (by linarith)
        rw [this]; ring
      · have : w.toH1Function.toFun x = u.toH1Function.toFun x - k := by
          rw [hwf x]
          exact max_eq_left (by linarith)
        rw [this]
    have hfle : f x ≤ mu * k := hf x hxW
    have hkey : rho x * w.toH1Function.toFun x * f x ≤
        rho x * w.toH1Function.toFun x * (mu * k) :=
      mul_le_mul_of_nonneg_left hfle hrw
    have hsq' : mu * (rho x * (w.toH1Function.toFun x * (u.toH1Function.toFun x - k))) =
        mu * (rho x * (w.toH1Function.toFun x * w.toH1Function.toFun x)) := by rw [hsq]
    linarith [hkey, hsq']
  have hint : mu * ∫ x in W,
      rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume ≤
      mu * (∫ x in W, rho x * u.toH1Function.toFun x * w.toH1Function.toFun x ∂volume) -
        ∫ x in W, rho x * f x * w.toH1Function.toFun x ∂volume := by
    have hRint : Integrable
        (fun x ↦ mu * (rho x * u.toH1Function.toFun x * w.toH1Function.toFun x) -
          rho x * f x * w.toH1Function.toFun x) (volume.restrict W) :=
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
    have : mu * ∫ x in W,
        rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume = 0 := le_antisymm hmul hnn
    exact (mul_eq_zero.1 this).resolve_left hmu.ne'
  have hAe : (fun x ↦ rho x * w.toH1Function.toFun x * w.toH1Function.toFun x)
      =ᵐ[volume.restrict W] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ hmassW).1 hzero
    filter_upwards [ae_restrict_mem hWmeas] with x hx
    have hr : 0 ≤ rho x := le_trans hrhoMin.le (hrhoLow x hx)
    have hnn : 0 ≤ rho x * (w.toH1Function.toFun x * w.toH1Function.toFun x) :=
      mul_nonneg hr (mul_self_nonneg _)
    simpa [mul_assoc] using hnn
  filter_upwards [hAe, ae_restrict_mem hWmeas] with x hx hxW
  have hrpos : 0 < rho x := lt_of_lt_of_le hrhoMin (hrhoLow x hxW)
  have hsq : w.toH1Function.toFun x * w.toH1Function.toFun x = 0 := by
    have h0 : rho x * (w.toH1Function.toFun x * w.toH1Function.toFun x) = 0 := by
      simpa [mul_assoc] using hx
    exact (mul_eq_zero.1 h0).resolve_left hrpos.ne'
  have hw0 : w.toH1Function.toFun x = 0 := mul_self_eq_zero.1 hsq
  rw [hwf x] at hw0
  have hle := max_eq_right_iff.1 hw0
  linarith [hle]

/-! ### Linearity in the sign, and the two-sided consequences -/

/-- The weak massive equation is odd: negating the solution negates the source. -/
theorem isMassiveWeakSolutionOn_neg {W : Set (Vec d)} {c rho : Vec d → ℝ} {mu : ℝ}
    {u : H1Function W} {f : Vec d → ℝ}
    (hu : IsMassiveWeakSolutionOn c rho mu W u f) :
    IsMassiveWeakSolutionOn c rho mu W (-u) (fun x ↦ -f x) := by
  intro φ
  have h := hu φ
  have hmass : ∫ x in W, rho x * (-u).toFun x * φ.toH1Function.toFun x ∂volume =
      -∫ x in W, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [H1Function.neg_toFun]
    ring
  have hen : ∫ x in W, vecDot (c x • (-u).grad x) (φ.toH1Function.grad x) ∂volume =
      -∫ x in W, vecDot (c x • u.grad x) (φ.toH1Function.grad x) ∂volume := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [H1Function.neg_grad, smul_neg, vecDot_neg_left]
  have hrhs : ∫ x in W, rho x * (-f x) * φ.toH1Function.toFun x ∂volume =
      -∫ x in W, rho x * f x * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    ring
  show mu * ∫ x in W, rho x * (-u).toFun x * φ.toH1Function.toFun x ∂volume +
      ∫ x in W, vecDot (c x • (-u).grad x) (φ.toH1Function.grad x) ∂volume =
    ∫ x in W, rho x * (-f x) * φ.toH1Function.toFun x ∂volume
  rw [hmass, hen, hrhs]
  linarith [h]

/-- **Positivity of the local resolvent.**  A nonnegative source gives a
nonnegative solution.  This is `C0ResolventDatum.solution_nonneg` at the level of
the local problem. -/
theorem ae_nonneg_of_isMassiveWeakSolutionOn
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {c rho : Vec d → ℝ} {mu lam rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin) (hlam : 0 < lam)
    (hc : ∀ x ∈ W, lam ≤ c x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {u : H10Function W} {f : Vec d → ℝ} (hfL2 : MemL2On W f)
    (hf : ∀ x ∈ W, 0 ≤ f x)
    (hu : IsMassiveWeakSolutionOn c rho mu W u.toH1Function f) :
    ∀ᵐ x ∂(volume.restrict W), 0 ≤ u.toH1Function.toFun x := by
  have hneg : IsMassiveWeakSolutionOn c rho mu W (-u).toH1Function (fun x ↦ -f x) := by
    have : (-u).toH1Function = -u.toH1Function := rfl
    rw [this]
    exact isMassiveWeakSolutionOn_neg hu
  have hfneg : MemL2On W (fun x ↦ -f x) := hfL2.neg
  have := ae_le_of_isMassiveWeakSolutionOn (u := -u) (k := 0) hW hmu le_rfl hrhoMin hlam hc
    hrhoMeas hrhoLow hrhoBdd hfneg (fun x hx ↦ by simpa using hf x hx) hneg
  have hcoe : ((-u : H10Function W)).toH1Function = -u.toH1Function := rfl
  filter_upwards [this] with x hx
  rw [hcoe] at hx
  simp only [H1Function.neg_toFun] at hx
  linarith [hx]

/-- **The two-sided maximum principle**, i.e. the local form of the Hille--Yosida
contraction `μ ‖R_μ f‖_∞ ≤ ‖f‖_∞` (`C0ResolventDatum.norm_solution_le`). -/
theorem ae_abs_le_of_isMassiveWeakSolutionOn
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {c rho : Vec d → ℝ} {mu k lam rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hk : 0 ≤ k) (hrhoMin : 0 < rhoMin) (hlam : 0 < lam)
    (hc : ∀ x ∈ W, lam ≤ c x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {u : H10Function W} {f : Vec d → ℝ} (hfL2 : MemL2On W f)
    (hf : ∀ x ∈ W, |f x| ≤ mu * k)
    (hu : IsMassiveWeakSolutionOn c rho mu W u.toH1Function f) :
    ∀ᵐ x ∂(volume.restrict W), |u.toH1Function.toFun x| ≤ k := by
  have hup := ae_le_of_isMassiveWeakSolutionOn hW hmu hk hrhoMin hlam hc
    hrhoMeas hrhoLow hrhoBdd hfL2 (fun x hx ↦ le_trans (le_abs_self _) (hf x hx)) hu
  have hneg : IsMassiveWeakSolutionOn c rho mu W (-u).toH1Function (fun x ↦ -f x) := by
    have : (-u).toH1Function = -u.toH1Function := rfl
    rw [this]
    exact isMassiveWeakSolutionOn_neg hu
  have hfneg : MemL2On W (fun x ↦ -f x) := hfL2.neg
  have hlow := ae_le_of_isMassiveWeakSolutionOn (u := -u) hW hmu hk hrhoMin hlam hc
    hrhoMeas hrhoLow hrhoBdd hfneg
    (fun x hx ↦ le_trans (neg_le_abs _) (hf x hx)) hneg
  have hcoe : ((-u : H10Function W)).toH1Function = -u.toH1Function := rfl
  filter_upwards [hup, hlow] with x hx1 hx2
  rw [hcoe] at hx2
  simp only [H1Function.neg_toFun] at hx2
  exact abs_le.2 ⟨by linarith [hx2], hx1⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
