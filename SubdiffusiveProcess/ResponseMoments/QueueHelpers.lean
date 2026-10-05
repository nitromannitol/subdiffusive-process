module

public import SubdiffusiveProcess.ResponseMoments.Elementary
public import SubdiffusiveProcess.ResponseMoments.FormAlgebra
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic

@[expose] public section

/-!
# Monotonicity, Borel--Cantelli, and geometric-tail helpers

* `defect_sup_tendsto` is Lemma
* the rest are reusable steps of the Borel--Cantelli and geometric-tail
  arguments of `mfd:prop-allchain` and `mfd:prop-as-response-bank`.
-/

open MeasureTheory Filter Set Topology Finset
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments

theorem defect_sup_tendsto
    (f : ℕ → ℕ → ℝ) (Fk : ℕ → ℝ)
    (hnonneg : ∀ i k, 0 ≤ f i k)
    (hmono : ∀ i k, f i (k + 1) ≤ f i k)
    (hFk : ∀ k, IsLUB (Set.range fun i => f i k) (Fk k)) :
    ∃ eta : ℝ, 0 ≤ eta ∧ Antitone Fk ∧ Tendsto Fk atTop (𝓝 eta) := by
  have hle : ∀ k i, f i k ≤ Fk k := by
    intro k i
    exact mem_upperBounds.mp (hFk k).1 (f i k) ⟨i, rfl⟩
  have hstep : ∀ k, Fk (k + 1) ≤ Fk k := by
    intro k
    rw [isLUB_le_iff (hFk (k + 1)), mem_upperBounds]
    rintro x ⟨i, rfl⟩
    exact le_trans (hmono i k) (hle k i)
  have hanti : Antitone Fk := antitone_nat_of_succ_le hstep
  have hnonnegF : ∀ k, 0 ≤ Fk k := by
    intro k
    exact le_trans (hnonneg 0 k) (hle k 0)
  refine ⟨⨅ k, Fk k, ?_, hanti, ?_⟩
  · exact le_ciInf (f := Fk) (fun k => hnonnegF k)
  · exact tendsto_atTop_ciInf hanti (by
      refine ⟨0, ?_⟩
      intro x hx
      rcases hx with ⟨k, rfl⟩
      exact hnonnegF k)

theorem exists_ae_subseq_of_eLpNorm_tendsto
    (Om : Type) [MeasurableSpace Om] (P : Measure Om)
    (X : ℕ → Om → ℝ) (Xlim : Om → ℝ) (p : ℝ≥0∞) (hp : p ≠ 0)
    (_hmeas : ∀ N, AEStronglyMeasurable (X N) P)
    (_hmeaslim : AEStronglyMeasurable Xlim P)
    (hconv : Tendsto (fun N => eLpNorm (fun ω => X N ω - Xlim ω) p P) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => X (ns i) ω) atTop (𝓝 (Xlim ω)) := by
  have h_tim : TendstoInMeasure P X atTop Xlim :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := p) (f := X) (g := Xlim) (l := atTop)
      hp hconv
  exact h_tim.exists_seq_tendsto_ae

theorem ae_eventually_notMem_of_summable
    (Om : Type) [MeasurableSpace Om] (P : Measure Om)
    (A : ℕ → Set Om) (hsum : (∑' N : ℕ, P (A N)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ᶠ N in atTop, ω ∉ A N := by
  classical
  have h : P {ω : Om | ∃ᶠ N in atTop, ω ∈ A N} = 0 :=
    measure_setOfPred_frequently_eq_zero (μ := P) (p := fun N ω => ω ∈ A N)
      (by simpa using hsum)
  rw [MeasureTheory.ae_iff]
  have hset : {ω : Om | ¬ (∀ᶠ N in atTop, ω ∉ A N)}
      = {ω : Om | ∃ᶠ N in atTop, ω ∈ A N} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [Filter.not_eventually]
    simp only [not_not]
  rw [hset]
  exact h

theorem tsum_ofReal_geom_ne_top {Ce ce : ℝ} (hCe : 0 < Ce) (hce : 0 < ce) :
    (∑' N : ℕ, ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ≠ ⊤ := by
  have hr0 : 0 ≤ (3 : ℝ) ^ (-ce) :=
    le_of_lt (Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num) (-ce))
  have hr1 : (3 : ℝ) ^ (-ce) < 1 := by
    have hneg : (3 : ℝ) ^ (-ce) = ((3 : ℝ) ^ ce)⁻¹ :=
      Real.rpow_neg (show (0 : ℝ) ≤ 3 by norm_num) ce
    rw [hneg]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (show (1 : ℝ) < 3 by norm_num) hce)
  have hnonneg : ∀ N : ℕ, 0 ≤ Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) := by
    intro N
    exact mul_nonneg (le_of_lt hCe)
      (le_of_lt (Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num) (-(ce * (N : ℝ)))))
  have hsummable : Summable (fun N : ℕ => Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
    have hterm : (fun N : ℕ => Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) =
        fun N : ℕ => Ce * ((3 : ℝ) ^ (-ce)) ^ N := by
      funext N
      rw [show -(ce * (N : ℝ)) = (-ce) * (N : ℝ) by ring]
      rw [Real.rpow_mul (show (0 : ℝ) ≤ 3 by norm_num), Real.rpow_natCast]
    rw [hterm]
    exact Summable.mul_left Ce (summable_geometric_of_lt_one hr0 hr1)
  have hEq := ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable
  rw [← hEq]
  exact ne_of_lt ENNReal.ofReal_lt_top

theorem allchain_tail_le {b theta t m : ℝ} (hb : 0 < b) (_hth0 : 0 ≤ theta)
    (_hth1 : theta < 1) (_ht : 0 ≤ t) (hm : t / (1 - theta) ≤ m) :
    (∑' n : ℕ, Real.exp (-b * (m + (n : ℝ)))) ≤
      (1 - Real.exp (-b))⁻¹ * Real.exp (-(b * t / (1 - theta))) := by
  have h_exp_neg : Real.exp (-b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h_one : 0 < 1 - Real.exp (-b) := sub_pos.mpr h_exp_neg
  have h_inv : 0 ≤ (1 - Real.exp (-b))⁻¹ := inv_nonneg.mpr (le_of_lt h_one)
  have hmul : b * (t / (1 - theta)) ≤ b * m := mul_le_mul_of_nonneg_left hm (le_of_lt hb)
  have hbdiv : b * (t / (1 - theta)) = b * t / (1 - theta) := (mul_div_assoc b t (1 - theta)).symm
  have harg : -b * m ≤ -(b * t / (1 - theta)) := by
    rw [hbdiv] at hmul
    linarith
  have hexp : Real.exp (-b * m) ≤ Real.exp (-(b * t / (1 - theta))) := Real.exp_le_exp.mpr harg
  calc (∑' n : ℕ, Real.exp (-b * (m + (n : ℝ))))
      = Real.exp (-b * m) * (1 - Real.exp (-b))⁻¹ := tsum_exp_neg_shift hb m
    _ = (1 - Real.exp (-b))⁻¹ * Real.exp (-b * m) := by ring
    _ ≤ (1 - Real.exp (-b))⁻¹ * Real.exp (-(b * t / (1 - theta))) :=
        mul_le_mul_of_nonneg_left hexp h_inv

theorem gam_expand {V : Type} [AddCommGroup V] [Module ℝ V] {X : Type}
    [MeasurableSpace X] (E : LocalEnergy V X) (t : ℝ) (u v : V) (s : Set X) :
    E.gam (u + t • v) (u + t • v) s =
      E.gam u u s + 2 * t * E.gam u v s + t ^ 2 * E.gam v v s := by
  simp only [E.gam_add_right, E.gam_add_left, E.gam_smul_left, E.gam_smul_right,
    E.gam_symm v u s]
  ring

end ResponseMoments
end SubdiffusiveProcess
