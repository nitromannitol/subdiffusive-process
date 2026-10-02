import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserBoundedComposition
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserCutoffEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Admissible nonlinear Moser tests

The positive-part powers `w = u₊^s` and `f = u₊^(2s-1)` belong to `H¹`
for every real `s ≥ 1` when `u` is bounded. Their exact gradient identities
give the nonlinear test `eta² f`. The bound on `u` occurs only in the
construction of these functions, not in either gradient identity.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The two gradient identities needed for the nonlinear energy test. -/
def MoserPowerPair {d : ℕ} {U : Set (Vec d)}
    (u w f : H1Function U) (s : ℝ) : Prop :=
  ∀ᵐ x ∂volume.restrict U,
    s ^ 2 * vecDot (u.grad x) (f.grad x) = (2 * s - 1) * vecNormSq (w.grad x) ∧
    ∀ i, s * f.toFun x * u.grad x i = w.toFun x * w.grad x i

/-- Positive-part powers with their untruncated formulas and exact energy identities. -/
theorem exists_moser_power_pair {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {M : ℝ} (hM : 0 ≤ M) (hu : ∀ᵐ x ∂volume.restrict U, |u.toFun x| ≤ M)
    {s : ℝ} (hs : 1 ≤ s) :
    ∃ w f : H1Function U,
      w.toFun = (fun x => (max (u.toFun x) 0) ^ s) ∧
      f.toFun = (fun x => (max (u.toFun x) 0) ^ (2 * s - 1)) ∧
      MoserPowerPair u w f s := by
  obtain ⟨v, hv, hvg⟩ := exists_h1_max_sub_const hU u 0
  simp only [sub_zero] at hv
  have hv0 (x : Vec d) : 0 ≤ v.toFun x := by rw [hv]; exact le_max_right _ _
  have hvM : ∀ᵐ x ∂volume.restrict U, |v.toFun x| ≤ M := by
    filter_upwards [hu] with x hx
    rw [abs_of_nonneg (hv0 x), hv]
    exact max_le (le_abs_self _ |>.trans hx) hM
  obtain ⟨w, hw, hwg⟩ := exists_moser_h1_comp hU v hM hvM
    (Real.contDiff_rpow_const_of_le (n := 1) (by simpa using hs))
  obtain ⟨f, hf, hfg⟩ := exists_moser_h1_comp hU v hM hvM
    (Real.contDiff_rpow_const_of_le (p := 2 * s - 1) (n := 1) (by norm_num; linarith))
  refine ⟨w, f, by simpa only [hv] using hw, by simpa only [hv] using hf, ?_⟩
  filter_upwards [hvg] with x hx
  have hwg' : w.grad x = fun i => s * v.toFun x ^ (s - 1) * v.grad x i := by
    simp only [hwg, Real.deriv_rpow_const]
  have hfg' : f.grad x = fun i =>
      (2 * s - 1) * v.toFun x ^ (2 * s - 2) * v.grad x i := by
    simp only [hfg, Real.deriv_rpow_const, show 2 * s - 1 - 1 = 2 * s - 2 by ring]
  have hpowsq : (v.toFun x ^ (s - 1)) ^ (2 : ℕ) = v.toFun x ^ (2 * s - 2) := by
    rw [← Real.rpow_mul_natCast (hv0 x)]
    congr 1
    norm_num
    ring
  have hpowadd : v.toFun x ^ s * v.toFun x ^ (s - 1) =
      v.toFun x ^ (2 * s - 1) := by
    rw [← Real.rpow_add_of_nonneg (hv0 x) (by linarith) (by linarith)]
    congr 1
    ring
  by_cases hxpos : 0 < u.toFun x
  · have hvg' : v.grad x = u.grad x := by
      simpa only [indicator_of_mem (show x ∈ {y | 0 < u.toFun y} from hxpos)] using hx
    constructor
    · rw [hwg', hfg', hvg']
      simp only [vecDot, vecNormSq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hpowsq]
      ring
    · intro i
      rw [hw, hf, hwg', hvg']
      dsimp only
      calc
        s * v.toFun x ^ (2 * s - 1) * u.grad x i =
            s * (v.toFun x ^ s * v.toFun x ^ (s - 1)) * u.grad x i := by rw [hpowadd]
        _ = _ := by ring
  · have hvg' : v.grad x = 0 := by
      simpa only [indicator_of_notMem (show x ∉ {y | 0 < u.toFun y} from hxpos)] using hx
    have hvzero : v.toFun x = 0 := by rw [hv]; exact max_eq_right (le_of_not_gt hxpos)
    constructor
    · simp [hwg', hfg', hvg', vecDot, vecNormSq]
    · intro i
      rw [hf, hwg', hvg']
      simp [hvzero, Real.zero_rpow (show 2 * s - 1 ≠ 0 by linarith)]

/-- Testing the original equation by `eta² u₊^(2s-1)` gives the power energy identity. -/
theorem moser_power_test_identity {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {a : Vec d → ℝ}
    (u w f : H1Function U) (hu : IsWeaklyHarmonicOn a U u)
    {s : ℝ} (hpair : MoserPowerPair u w f s)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U) :
    (∫ x in U, a x * ((2 * s - 1) * (eta x ^ 2 * vecNormSq (w.grad x)) +
      s * (w.toFun x * vecDot (w.grad x) ((2 * eta x) • euclideanGradient eta x)))) = 0 := by
  have hsmooth := heta.pow 2
  have hcompact : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [pow_two] using hetac.mul_right (f' := eta)
  have hsupport : tsupport (fun x => eta x ^ 2) ⊆ U := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left (f := eta) (g := eta)).trans hetasub
  let psi := f.mulContDiffHasCompactSupportToH10 hU hsmooth hcompact hsupport
  have hpsi := WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
    f hU hsmooth hcompact hsupport
  have heq : (fun x => s ^ 2 * vecDot (a x • u.grad x) (psi.toH1Function.grad x))
      =ᵐ[volume.restrict U] fun x => a x *
        ((2 * s - 1) * (eta x ^ 2 * vecNormSq (w.grad x)) +
          s * (w.toFun x * vecDot (w.grad x) ((2 * eta x) • euclideanGradient eta x))) := by
    filter_upwards [hpsi, hpair] with x hx hp
    rw [hx]
    simp_rw [Section6BoundedMultiplier.fderiv_cutoff_sq_apply eta heta]
    have hfirst := hp.1
    have hsecond := hp.2
    simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      euclideanGradient, euclideanCoordDeriv] at hfirst ⊢
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i : Fin d, (
          (a x * eta x ^ 2) * (s ^ 2 * (u.grad x i * f.grad x i)) +
          (2 * a x * eta x * s * (fderiv ℝ eta x) (basisVec i)) *
            (s * f.toFun x * u.grad x i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp_rw [hsecond]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [← integral_congr_ae heq, integral_const_mul, hu psi, mul_zero]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
