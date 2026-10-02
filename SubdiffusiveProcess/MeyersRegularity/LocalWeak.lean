import SubdiffusiveProcess.MeyersRegularity.Caccioppoli
import SubdiffusiveProcess.MeyersRegularity.Basic
import Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-! Restriction of the interior weak equation without changing its representatives. -/

open MeasureTheory Filter Set Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity
open CubeCalderonZygmund

theorem smoothEquation_restrict {d : ℕ} {U V : Set (Vec d)} (hV : IsOpen V) (hVU : V ⊆ U)
    (u : H1Function U) (H : Vec d → Vec d) (heq : SmoothEquation H u) :
    SmoothEquation H (u.restrict hV hVU) := by
  intro phi hphi hcompact hsupp
  have hh := heq phi hphi hcompact (hsupp.trans hVU)
  have hzero (A : Vec d → Vec d) : ∀ y, y ∉ V →
      vecDot (A y) (euclideanGradient phi y) = 0 := by
    intro y hy
    have hy' : y ∉ tsupport phi := fun h => hy (hsupp h)
    simp [euclideanGradient_eq_zero_of_notMem_tsupport hy', vecDot_zero_right]
  have hzeroU (A : Vec d → Vec d) : ∀ y, y ∉ U →
      vecDot (A y) (euclideanGradient phi y) = 0 := by
    intro y hy
    exact hzero A y (fun h => hy (hVU h))
  have hleft : (∫ y in V, vecDot (u.grad y) (euclideanGradient phi y)) =
      ∫ y in U, vecDot (u.grad y) (euclideanGradient phi y) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero u.grad),
      setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroU u.grad)]
  have hright : (∫ y in V, vecDot (H y) (euclideanGradient phi y)) =
      ∫ y in U, vecDot (H y) (euclideanGradient phi y) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero H),
      setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroU H)]
  simpa only [H1Function.restrict, hleft, hright] using hh


theorem scalarEquation_restrict {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (a h : Vec d → ℝ) (u : H1Function U) (heq : ScalarEquation a h u) :
    ScalarEquation a h (u.restrict hV hVU) := by exact SubdiffusiveProcess.MeyersRegularity.aux_dedup_d148_scalarEquation_restrict (d := d) (U := U) (V := V) (hU := hU) (hV := hV) (hVU := hVU) (a := a) (h := h) (u := u) (heq := heq)


end SubdiffusiveProcess.MeyersRegularity
