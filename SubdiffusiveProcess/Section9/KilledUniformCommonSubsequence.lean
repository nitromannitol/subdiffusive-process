module

public import SubdiffusiveProcess.Probability.SubseqInProbability
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section9

/-- Uniform convergence in outer probability on countably many sets gives one
almost sure uniform subsequence on ALL those sets. No measurability of a
supremum or exceptional distance event is needed. -/
theorem exists_ae_uniform_on_countable_sets_subsequence
    {Ω X : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Set X) (D : ℕ → ℕ → Ω → X → ℝ)
    (hconv : ∀ i eps, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N →
        P {omega | ∃ x ∈ S i, eps ≤ D i N omega x} ≤ ENNReal.ofReal rho) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ᵐ omega ∂P, ∀ i eps, 0 < eps →
        ∃ J0 : ℕ, ∀ j, J0 ≤ j → ∀ x ∈ S i, D i (phi j) omega x < eps := by
  classical
  let bad : ℕ → ℕ → Ω → ℝ := fun k N omega =>
    if ∃ x ∈ S (Nat.unpair k).1,
        1 / (((Nat.unpair k).2 : ℝ) + 1) ≤ D (Nat.unpair k).1 N omega x
      then 1 else 0
  have hbad : ∀ (k : ℕ) (eps : ℝ), 0 < eps →
      Tendsto (fun N => P {omega | eps ≤ |bad k N omega|}) atTop (𝓝 0) := by
    intro k eps heps
    apply (SubdiffusiveProcess.tendsto_zero_ennreal_iff_real _).mpr
    intro rho hrho
    obtain ⟨N0, hN0⟩ := hconv (Nat.unpair k).1
      (1 / (((Nat.unpair k).2 : ℝ) + 1)) (by positivity) rho hrho
    refine ⟨N0, fun N hN => (measure_mono ?_).trans (hN0 N hN)⟩
    intro omega hω
    change eps ≤ |bad k N omega| at hω
    by_cases hyes : ∃ x ∈ S (Nat.unpair k).1,
        1 / (((Nat.unpair k).2 : ℝ) + 1) ≤ D (Nat.unpair k).1 N omega x
    · exact hyes
    · have hzero : bad k N omega = 0 := ite_eq_right hyes
      rw [hzero, abs_zero] at hω
      exact False.elim ((not_le.mpr heps) hω)
  obtain ⟨phi, hphi, hae⟩ := SubdiffusiveProcess.exists_strictMono_ae_forall_tendsto_zero
    P bad hbad id tendsto_id
  refine ⟨phi, hphi, ?_⟩
  filter_upwards [hae] with omega hω
  intro i eps heps
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt heps
  have ht := hω (Nat.pair i k)
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨J0, hJ0⟩ := ht (1 / 2) (by norm_num)
  refine ⟨J0, fun j hj x hx => ?_⟩
  have hsmall := hJ0 j hj
  rw [Real.dist_eq, sub_zero] at hsmall
  have hnot : ¬ ∃ y ∈ S i, 1 / ((k : ℝ) + 1) ≤ D i (phi j) omega y := by
    intro hbad'
    simp only [bad, Function.id_def, Nat.unpair_pair, ite_eq_left hbad', abs_one] at hsmall
    norm_num at hsmall
  exact (lt_of_not_ge fun hge => hnot ⟨x, hx, hge⟩).trans hk

end SubdiffusiveProcess.Section9
