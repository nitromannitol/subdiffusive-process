import SubdiffusiveProcess.Static.AffineCoercivity
import Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-! # Restricting killed coercivity by zero extension -/

open MeasureTheory Homogenization SubdiffusiveProcess.Static
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Literal fractional integrals respect pointwise equality on their domain. -/
theorem fractionalSeminormSq_congr_on {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {u v : Vec d → ℝ} (huv : ∀ x ∈ U, u x = v x) :
    fractionalSeminormSq U u = fractionalSeminormSq U v := by
  apply setLIntegral_congr_fun hU
  intro x hx
  apply setLIntegral_congr_fun hU
  intro z hz
  simp only [huv x hx, huv z hz]

/-- No measurability assumption is needed for monotonicity of the raw kernel. -/
theorem fractionalSeminormSq_mono_domain {d : ℕ} (u : Vec d → ℝ)
    {U V : Set (Vec d)} (hUV : U ⊆ V) :
    fractionalSeminormSq U u ≤ fractionalSeminormSq V u := by
  apply le_trans (lintegral_mono fun _ => lintegral_mono_set hUV)
  exact lintegral_mono_set hUV

/-- Killed coercivity on an open superset controls every smaller measurable
open domain, with the same coefficient and constant. -/
theorem H10_coercivity_of_superset {d : ℕ} {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : IsOpen V) (hUV : U ⊆ V)
    (A : Vec d → ℝ) (K : ℝ≥0∞)
    (hcoer : ∀ w : H10Function V, fractionalSqNorm V w.toFun ≤ K * energy V A w.grad) :
    ∀ v : H10Function U, fractionalSqNorm U v.toFun ≤ K * energy U A v.grad := by
  classical
  intro v
  let w := v.extendByZeroToOpenSuperset hU hV hUV
  have hwf : ∀ x ∈ U, w.toFun x = v.toFun x := by
    intro x hx
    change (v.extendByZeroToOpenSuperset _ _ hUV).toH1Function.toFun x = _
    rw [H10Function.extendByZeroToOpenSuperset_toFun,
      H10Function.zeroExtension_apply_of_mem v hx]
  have hwg : ∀ x, w.grad x = if x ∈ U then v.grad x else 0 := by
    intro x
    change (v.extendByZeroToOpenSuperset _ _ hUV).toH1Function.grad x = _
    rw [H10Function.extendByZeroToOpenSuperset_grad]
    split_ifs with hx
    · exact H10Function.zeroExtensionGrad_apply_of_mem v hx
    · exact H10Function.zeroExtensionGrad_apply_of_not_mem v hx
  have hfrac : fractionalSeminormSq U v.toFun ≤ fractionalSeminormSq V w.toFun := by
    rw [fractionalSeminormSq_congr_on hU (fun x hx => (hwf x hx).symm)]
    exact fractionalSeminormSq_mono_domain _ hUV
  have hL2 : (∫⁻ x in U, ENNReal.ofReal (v.toFun x ^ 2)) ≤
      ∫⁻ x in V, ENNReal.ofReal (w.toFun x ^ 2) := by
    refine le_trans (le_of_eq ?_) (lintegral_mono_set hUV)
    exact setLIntegral_congr_fun hU (fun x hx => by rw [hwf x hx])
  have henergy : energy V A w.grad = energy U A v.grad := by
    have hind : ∀ x, ENNReal.ofReal (A x * vecDot (w.grad x) (w.grad x)) =
        U.indicator (fun x => ENNReal.ofReal (A x * vecDot (v.grad x) (v.grad x))) x := by
      intro x
      by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem hx, hwg x, if_pos hx]
      · rw [Set.indicator_of_notMem hx, hwg x, if_neg hx]
        simp only [vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, ENNReal.ofReal_zero]
    unfold energy
    simp_rw [hind]
    rw [setLIntegral_indicator hU, Set.inter_eq_left.mpr hUV]
  have hnorm : fractionalSqNorm U v.toFun ≤ fractionalSqNorm V w.toFun :=
    add_le_add hfrac hL2
  exact (hnorm.trans (hcoer w)).trans_eq (congrArg (fun x => K * x) henergy)

end SubdiffusiveProcess.Static
