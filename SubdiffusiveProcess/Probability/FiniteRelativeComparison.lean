import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A finite bank of quantitative two-index comparisons has one common tail
rate and future-index threshold. An additive geometric error is absorbed into
a fixed positive baseline. No convergence of the bank is asserted here.
-/
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology
namespace SubdiffusiveProcess

/-- Finite relative comparison tails combine with one common future-index threshold. -/
theorem finite_relative_pair_comparison
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I] [Nonempty I]
    (mu : Measure Omega) (F : I → ℕ → Omega → ℝ)
    (hcomp : ∀ i (eps : ℝ), 0 < eps →
      ∃ C c : ℝ, ∃ N0 : ℕ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, N0 ≤ N → ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
          mu {omega | eps * F i N omega + C * (3 : ℝ) ^ (-c * (N : ℝ)) <
            |F i N omega - F i M omega|} ≤
              ENNReal.ofReal (C * (3 : ℝ) ^ (-c * (N : ℝ))))
    (eps v : ℝ) (heps : 0 < eps) (hv : 0 < v) :
    ∃ C c : ℝ, ∃ N0 : ℕ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, N0 ≤ N → ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
        mu {omega | ∃ i, eps * (v + F i N omega) <
          |F i N omega - F i M omega|} ≤
            ENNReal.ofReal (C * (3 : ℝ) ^ (-c * (N : ℝ))) := by
  classical
  choose C c K hC hc hK using fun i => hcomp i eps heps
  let Csum : ℝ := ∑ i : I, C i
  have hI : (Finset.univ : Finset I).Nonempty := Finset.univ_nonempty
  let cmin : ℝ := Finset.univ.inf' hI c
  have hCsum : 0 < Csum := Finset.sum_pos (fun i _ => hC i) hI
  have hcmin : 0 < cmin := (Finset.lt_inf'_iff hI).2 (fun i _ => hc i)
  have hCi i : C i ≤ Csum := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
  have hci i : cmin ≤ c i := Finset.inf'_le c (Finset.mem_univ i)
  let rho : ℝ := (3 : ℝ) ^ (-cmin)
  have hrho : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _
  have hrho1 : rho < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hcmin)
  have hscale (N : ℕ) : (3 : ℝ) ^ (-cmin * (N : ℝ)) = rho ^ N :=
    Real.rpow_mul_natCast (by norm_num) _ _
  have hzero : Tendsto (fun N : ℕ => Csum * (3 : ℝ) ^ (-cmin * (N : ℝ))) atTop (𝓝 0) := by
    simpa only [hscale, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hrho.le hrho1).const_mul Csum
  obtain ⟨Ktail, hKtail⟩ := eventually_atTop.mp ((tendsto_order.1 hzero).2
    (eps * v) (mul_pos heps hv))
  refine ⟨Csum, cmin, max Ktail (Finset.univ.sup K), hCsum, hcmin, ?_⟩
  intro N hN
  have hlocal i := hK i N ((Finset.le_sup (f := K) (Finset.mem_univ i)).trans
    ((le_max_right Ktail _).trans hN))
  choose M0 hNM0 hM using hlocal
  refine ⟨Finset.univ.sup M0, ?_, ?_⟩
  · exact (hNM0 hI.choose).trans (Finset.le_sup (f := M0) hI.choose_spec)
  · intro M hM0
    have hterm i : C i * (3 : ℝ) ^ (-c i * (N : ℝ)) ≤
        C i * (3 : ℝ) ^ (-cmin * (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (hC i).le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_right (neg_le_neg (hci i)) (Nat.cast_nonneg N)
    have hsmall i : C i * (3 : ℝ) ^ (-c i * (N : ℝ)) ≤ eps * v :=
      (hterm i).trans ((mul_le_mul_of_nonneg_right (hCi i)
        (Real.rpow_nonneg (by norm_num) _)).trans
          (hKtail N ((le_max_left _ _).trans hN)).le)
    have hbound i : mu {omega | eps * (v + F i N omega) < |F i N omega - F i M omega|} ≤
        ENNReal.ofReal (C i * (3 : ℝ) ^ (-cmin * (N : ℝ))) := by
      refine (measure_mono (fun omega homega => ?_)).trans
        ((hM i M ((Finset.le_sup (f := M0) (Finset.mem_univ i)).trans hM0)).trans
          (ENNReal.ofReal_le_ofReal (hterm i)))
      change eps * F i N omega + C i * (3 : ℝ) ^ (-c i * (N : ℝ)) < _
      have ho : eps * v + eps * F i N omega < |F i N omega - F i M omega| := by
        simpa only [Set.mem_setOf_eq, mul_add] using homega
      linarith only [hsmall i, ho]
    calc
      mu {omega | ∃ i, eps * (v + F i N omega) < |F i N omega - F i M omega|} ≤
          ∑ i : I, mu {omega | eps * (v + F i N omega) < |F i N omega - F i M omega|} := by
        rw [setOf_exists]
        exact measure_iUnion_fintype_le mu _
      _ ≤ ∑ i : I, ENNReal.ofReal (C i * (3 : ℝ) ^ (-cmin * (N : ℝ))) :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ = ENNReal.ofReal (Csum * (3 : ℝ) ^ (-cmin * (N : ℝ))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
          mul_nonneg (hC i).le (Real.rpow_nonneg (by norm_num) _)), ← Finset.sum_mul]

end SubdiffusiveProcess
