import SubdiffusiveProcess.Probability.FiniteBankMoment
import SubdiffusiveProcess.Probability.CountableEnvelope
import SubdiffusiveProcess.Analysis.MeshDiscount
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace SubdiffusiveProcess

/-- Uniform individual Lq moments and polynomial-times-triadic cardinality yield one Lp envelope for every level and index, with an explicit norm bound and the strict margin d < q η. Actual model geometry and moment estimates remain inputs to this internal consumer. -/
theorem exists_triadic_mesh_envelope
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ → ℕ) (d b : ℕ) (C η : ℝ) (hC : 0 ≤ C)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) (hqt : q ≠ ∞)
    (hgap : (d : ℝ) < q.toReal * η)
    (hcard : ∀ n : ℕ, (k n : ℝ) ≤
      C * ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ ((d : ℝ) * n))
    (Z : ∀ n : ℕ, Fin (k n) → Ω → ℝ)
    (hZ : ∀ n i, AEStronglyMeasurable (Z n i) μ)
    (K : ℝ≥0∞) (hKt : K ≠ ∞) (hK : ∀ n i, eLpNorm (Z n i) q μ ≤ K) :
    ∃ W : Ω → ℝ, MemLp W p μ ∧
      (∀ᵐ ω ∂μ, 0 ≤ W ω ∧ ∀ n : ℕ, ∀ i : Fin (k n),
        |Z n i ω| ≤ W ω * (3 : ℝ) ^ (η * n)) ∧
      eLpNorm W p μ ≤
        (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-η * n)) *
          (k n : ℝ≥0∞) ^ (1 / q.toReal)) * K := by
  classical
  have hp_t : p ≠ ∞ := fun h => hqt (top_unique (h ▸ hpq))
  have hq1 : 1 ≤ q.toReal := by
    rw [← ENNReal.toReal_one, ENNReal.toReal_le_toReal (by simp) hqt]
    exact hp.trans hpq
  have hsum_real : Summable (fun n : ℕ =>
      (3 : ℝ) ^ (-η * n) * (k n : ℝ) ^ (1 / q.toReal)) :=
    summable_triadic_mesh_cardinality k d b C q.toReal η hC hq1 hgap hcard
  let B : ℕ → Ω → ℝ := fun n ω => ‖fun i : Fin (k n) => Z n i ω‖
  let F : ℕ → Ω → ℝ := fun n ω => (3 : ℝ) ^ (-η * n) * B n ω
  have hBmeas : ∀ n, AEStronglyMeasurable (B n) μ := by
    intro n
    have hv : AEStronglyMeasurable (fun ω => fun i : Fin (k n) => Z n i ω) μ := by
      have heq : (fun ω => fun i : Fin (k n) => Z n i ω) =
          fun ω => ∑ i : Fin (k n), (Z n i ω) •
            (Pi.single i (1 : ℝ) : Fin (k n) → ℝ) := by
        funext ω
        exact pi_eq_sum_univ' (fun i : Fin (k n) => Z n i ω)
      rw [heq]
      apply Finset.aestronglyMeasurable_fun_sum Finset.univ
      intro i _
      have hc : AEStronglyMeasurable
          (fun _ : Ω => (Pi.single i (1 : ℝ) : Fin (k n) → ℝ)) μ :=
        stronglyMeasurable_const.aestronglyMeasurable
      exact (hZ n i).smul hc
    exact hv.norm
  have hBq : ∀ n, eLpNorm (B n) q μ ≤
      (k n : ℝ≥0∞) ^ (1 / q.toReal) * K := by
    intro n
    exact eLpNorm_finite_bank_le μ (hp.trans hpq) hqt (Z n) (hZ n) K (hK n)
  have hBmemq : ∀ n, MemLp (B n) q μ := by
    intro n
    refine ⟨hBmeas n, (hBq n).trans_lt ?_⟩
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by finiteness))
      (lt_top_iff_ne_top.2 hKt)
  have hFmem : ∀ n, MemLp (F n) p μ := by
    intro n
    exact ((hBmemq n).mono_exponent hpq).const_mul ((3 : ℝ) ^ (-η * n))
  have hFnorm : ∀ n, eLpNorm (F n) p μ ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-η * n)) *
        ((k n : ℝ≥0∞) ^ (1 / q.toReal) * K) := by
    intro n
    rw [show F n = ((3 : ℝ) ^ (-η * n)) • B n by funext ω; simp [F]]
    rw [eLpNorm_const_smul]
    rw [Real.enorm_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    exact mul_le_mul_right ((eLpNorm_le_eLpNorm_of_exponent_le hpq (hBmeas n)).trans
      (hBq n)) _
  have hsum_norm : Summable (fun n => (eLpNorm (F n) p μ).toReal) := by
    have hmajor : ∀ n, (eLpNorm (F n) p μ).toReal ≤
        ((3 : ℝ) ^ (-η * n) * (k n : ℝ) ^ (1 / q.toReal)) * K.toReal := by
      intro n
      calc
        (eLpNorm (F n) p μ).toReal ≤
            (ENNReal.ofReal ((3 : ℝ) ^ (-η * n)) *
              ((k n : ℝ≥0∞) ^ (1 / q.toReal) * K)).toReal :=
          (ENNReal.toReal_le_toReal (hFmem n).2.ne
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (ENNReal.mul_ne_top
                (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by finiteness)) hKt))).2
            (hFnorm n)
        _ = ((3 : ℝ) ^ (-η * n) * (k n : ℝ) ^ (1 / q.toReal)) * K.toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num) _)]
          have hk : ((k n : ℝ≥0∞) ^ (1 / q.toReal)).toReal =
              (k n : ℝ) ^ (1 / q.toReal) := by
            rw [← ENNReal.toReal_rpow]
            norm_cast
          rw [hk]
          ring
    exact Summable.of_nonneg_of_le (fun n => ENNReal.toReal_nonneg) hmajor
      (hsum_real.mul_right K.toReal)
  obtain ⟨W, hW, hdom, hWnorm⟩ :=
    exists_memLp_dominating_of_summable_eLpNorm μ hp hp_t F hFmem hsum_norm
  refine ⟨W, hW, ?_, ?_⟩
  · filter_upwards [hdom] with ω hω
    refine ⟨hω.1, fun n i => ?_⟩
    have hi : |Z n i ω| ≤ B n ω := by
      change |Z n i ω| ≤ ‖fun j : Fin (k n) => Z n j ω‖
      rw [Pi.norm_def]
      change ‖Z n i ω‖ ≤ ↑(Finset.univ.sup fun b => ‖Z n b ω‖₊)
      exact_mod_cast Finset.le_sup (f := fun j : Fin (k n) => ‖Z n j ω‖₊)
        (Finset.mem_univ i)
    have ha : 0 < (3 : ℝ) ^ (-η * n) := Real.rpow_pos_of_pos (by norm_num) _
    apply (mul_le_mul_iff_of_pos_left ha).1
    calc
      (3 : ℝ) ^ (-η * n) * |Z n i ω| ≤ F n ω := by
        simpa [F] using mul_le_mul_of_nonneg_left hi ha.le
      _ ≤ W ω := (le_abs_self (F n ω)).trans (hω.2 n)
      _ = (3 : ℝ) ^ (-η * n) * (W ω * (3 : ℝ) ^ (η * n)) := by
        calc
          W ω = W ω * ((3 : ℝ) ^ (-η * n) * (3 : ℝ) ^ (η * n)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
            simp
          _ = (3 : ℝ) ^ (-η * n) * (W ω * (3 : ℝ) ^ (η * n)) := by ring
  · calc
      eLpNorm W p μ ≤ ∑' n : ℕ, eLpNorm (F n) p μ := hWnorm
      _ ≤ ∑' n : ℕ, (ENNReal.ofReal ((3 : ℝ) ^ (-η * n)) *
          (k n : ℝ≥0∞) ^ (1 / q.toReal)) * K :=
        ENNReal.tsum_le_tsum fun n => by simpa [mul_assoc] using hFnorm n
      _ = (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-η * n)) *
          (k n : ℝ≥0∞) ^ (1 / q.toReal)) * K := ENNReal.tsum_mul_right

end SubdiffusiveProcess
