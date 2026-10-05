module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.IntervalGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Sum and absorb the forcing rows in a finite Dirichlet iteration.
The coefficient and stochastic score estimates remain explicit inputs. -/
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- Summing a geometric defect row costs only its parent forcing size. -/
theorem dirichlet_defect_sum_le (n top m : ℤ) (hnt : n ≤ top) (htm : top ≤ m)
    (eps : ℤ → ℝ) (H B R T E : ℝ) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hR : 0 ≤ R) (hT : 0 ≤ T)
    (he : ∑ j ∈ Finset.Icc n top,eps j ≤ E) :
    (∑ j ∈ Finset.Icc n top,
      (eps j*H+B*R*T*(3:ℝ)^(-(((m-j:ℤ):ℝ)/2)))) ≤ E*H+(5/2:ℝ)*B*R*T := by
  have hg := SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.sum_Icc_three_parent_half_le
    (m:=m) hnt
  have hp : (3:ℝ)^(-(((m-top:ℤ):ℝ)/2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
      have hmt : (0:ℝ) ≤ ((m-top:ℤ):ℝ) := by exact_mod_cast (sub_nonneg.mpr htm)
      linarith only [hmt])
  have hg' : (∑ j ∈ Finset.Icc n top,(3:ℝ)^(-(((m-j:ℤ):ℝ)/2))) ≤ 5/2 := by
    have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤5/2)
    linarith only [hg,hh]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
  have he' := mul_le_mul_of_nonneg_right he hH
  have hg'' := mul_le_mul_of_nonneg_left hg' (show 0≤B*R*T by positivity)
  nlinarith only [he',hg'']

/-- A polynomial forcing factor is paid by a fixed exponential rate. -/
theorem dirichlet_forcing_exp_le (K B x O H T : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (hO : 0 ≤ O) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    O+K*x*H+(5/2:ℝ)*B*Real.exp (4*x)*T ≤
      (1+K+(5/2:ℝ)*B)*Real.exp (5*x)*(O+H+T) := by
  have h1 : 1 ≤ Real.exp (5*x) := Real.one_le_exp_iff.mpr (by positivity)
  have h4 : Real.exp (4*x) ≤ Real.exp (5*x) := Real.exp_le_exp.mpr (by linarith only [hx])
  have hxe : x ≤ Real.exp (5*x) := by
    have hh := Real.add_one_le_exp x
    have hm : Real.exp x ≤ Real.exp (5*x) := Real.exp_le_exp.mpr (by linarith only [hx])
    linarith only [hh,hm]
  have ho := mul_le_mul_of_nonneg_right h1 hO
  have hh := mul_le_mul_of_nonneg_right hxe (mul_nonneg hK hH)
  have ht := mul_le_mul_of_nonneg_right h4 (show 0 ≤ (5/2:ℝ)*B*T by positivity)
  have hsum := add_le_add (add_le_add ho hh) ht
  have hcoeff : O+K*H+(5/2:ℝ)*B*T ≤ (1+K+(5/2:ℝ)*B)*(O+H+T) := by
    nlinarith only [mul_nonneg hK hO,mul_nonneg hK hT,
      mul_nonneg hB hO,mul_nonneg hB hH,hH,hT]
  have hfinal := mul_le_mul_of_nonneg_left hcoeff (Real.exp_pos (5*x)).le
  nlinarith only [hsum,hfinal]

/-- A sufficiently small prefix rate pays every finite iteration cost by a prescribed power loss. -/
theorem exists_dirichlet_iteration_cost (CI B K rho : ℝ) (k : ℕ)
    (hCI : 0 < CI) (hB : 0 ≤ B) (hK : 0 ≤ K) (hrho : 0 < rho) :
    ∃ lam C : ℝ, 0 < lam ∧ 0 < C ∧ ∀ len nb es O H T X : ℝ,
      0 ≤ len → 0 ≤ O → 0 ≤ H → 0 ≤ T →
      nb ≤ k+1+lam*len → es ≤ K*lam*len →
      X ≤ Real.exp (CI*(k+1)*(nb+1)+CI*es) *
        (O+es*H+(5/2:ℝ)*B*Real.exp (4*(lam*len))*T) →
      X ≤ C*(3:ℝ)^(rho*len)*(O+H+T) := by
  let P := CI*(k+1)+CI*K+5
  have hP : 0 < P := by dsimp only [P]; positivity
  let lam := rho*Real.log 3/P
  have hlam : 0 < lam := by
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    dsimp only [lam]
    positivity
  let C := (1+K+(5/2:ℝ)*B)*Real.exp (CI*(k+1)*(k+2))
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨lam,C,hlam,hC,?_⟩
  intro len nb es O H T X hlen hO hH hT hnb hes hX
  have hforce := dirichlet_forcing_exp_le K B (lam*len) O H T hK hB
    (mul_nonneg hlam.le hlen) hO hH hT
  have hbracket : O+es*H+(5/2:ℝ)*B*Real.exp (4*(lam*len))*T ≤
      (1+K+(5/2:ℝ)*B)*Real.exp (5*(lam*len))*(O+H+T) := by
    have hh := mul_le_mul_of_nonneg_right hes hH
    nlinarith only [hh,hforce]
  have he : CI*(k+1)*(nb+1)+CI*es ≤
      CI*(k+1)*(k+2)+(CI*(k+1)+CI*K)*(lam*len) := by
    have hn := mul_le_mul_of_nonneg_left hnb (show 0≤CI*(k+1) by positivity)
    have hs := mul_le_mul_of_nonneg_left hes hCI.le
    nlinarith only [hn,hs]
  have hmul := (mul_le_mul_of_nonneg_left hbracket
    (Real.exp_pos (CI*(k+1)*(nb+1)+CI*es)).le).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he)
      (show 0≤(1+K+(5/2:ℝ)*B)*Real.exp (5*(lam*len))*(O+H+T) by positivity))
  apply hX.trans
  apply hmul.trans_eq
  have hrate : P*lam = rho*Real.log 3 := by dsimp only [lam]; field_simp
  dsimp only [C]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  have hexp : Real.exp (CI*(k+1)*(k+2)+(CI*(k+1)+CI*K)*(lam*len))*Real.exp (5*(lam*len)) =
      Real.exp (CI*(k+1)*(k+2))*Real.exp (Real.log 3*(rho*len)) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    dsimp only [P] at hrate
    nlinarith only [congrArg (fun y : ℝ => y*len) hrate]
  nlinarith only [congrArg (fun y : ℝ => y*((1+K+(5/2:ℝ)*B)*(O+H+T))) hexp]

end SubdiffusiveProcess
