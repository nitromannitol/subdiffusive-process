import SubdiffusiveProcess.Static.DyadicMajorant
import SubdiffusiveProcess.Static.LocalEstimateClauses

/-! # The dyadic harmonic cutoff clause from uniform pair moments -/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Uniform moments for each pair with gap exponent three produce the literal
harmonic clause with fixed exponent five. -/
theorem exists_local_harmonic_majorant_of_pair_moments
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    {d p : ℕ} (A : Ω → Vec d → ℝ) (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i) {q B : ℝ} (hq : 1 ≤ q) (hB : 0 ≤ B)
    (Z : ∀ n : ℕ, Fin p → Fin (2 ^ n + 1) → Ω → ℝ)
    (hZ : ∀ n i k, AEStronglyMeasurable (Z n i k) mu)
    (hnorm : ∀ n i k, eLpNorm (Z n i k) (ENNReal.ofReal q) mu ≤ ENNReal.ofReal B)
    (hpairs : ∀ (n : ℕ) (i : Fin p) (k : Fin (2 ^ n + 1)),
      ∀ᵐ omega ∂mu, (k : ℕ) < 2 ^ n →
      ∃ chi : Homogenization.H10Function
          (Metric.ball (c i) (((1 - (((k : ℕ) + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
            ((((k : ℕ) + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2)),
        (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
        (∀ x ∈ Metric.ball (c i) (((1 - ((k : ℕ) : ℝ) / 2 ^ n) * s0 i +
            (((k : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2), chi.toFun x = 1) ∧
        tsupport chi.toFun ⊆ Metric.ball (c i)
          (((1 - (((k : ℕ) + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
            ((((k : ℕ) + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2) ∧
        ∀ x r, 0 < r → r ≤ 1 →
          ∫⁻ z in Metric.ball x r ∩ Metric.ball (c i)
              (((1 - (((k : ℕ) + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
                ((((k : ℕ) + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2),
            ENNReal.ofReal (A omega z * Homogenization.vecDot (chi.grad z) (chi.grad z)) ≤
              ENNReal.ofReal (Z n i k omega * ((s1 i - s0 i) / 2 ^ n / 2) ^ (-3 : ℝ) *
                r ^ ((d : ℝ) - 1 / 2))) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : Ω → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
      (∫⁻ omega, ENNReal.ofReal (K omega ^ q) ∂mu) ≤ ENNReal.ofReal C ∧
      ∀ᵐ omega ∂mu, localHarmonicCutoffEstimates (A omega) c s0 s1 (K omega) 5 := by
  classical
  let D := 1 + ∑ i : Fin p, ((s1 i - s0 i) / 2) ^ 2
  have hDone : 1 ≤ D := by
    dsimp only [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hDpos : 0 < D := zero_lt_one.trans_le hDone
  obtain ⟨K, hKmeas, hKone, hKmoment, hKbound⟩ :=
    exists_dyadic_majorant mu p hq hB Z hZ hnorm
  let K' := fun omega => D * K omega
  let C := D ^ q * (1 + 4 * (p : ℝ) * B) ^ q
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos hDpos q)
    (Real.rpow_pos_of_pos (by positivity) q)
  refine ⟨C, hC, K', hKmeas.const_mul D, fun omega => ?_, ?_, ?_⟩
  · change 1 ≤ D * K omega
    simpa only [one_mul] using mul_le_mul hDone (hKone omega) zero_le_one hDpos.le
  · change (∫⁻ omega, ENNReal.ofReal ((D * K omega) ^ q) ∂mu) ≤ _
    simp_rw [Real.mul_rpow hDpos.le (zero_le_one.trans (hKone _)),
      ENNReal.ofReal_mul (Real.rpow_nonneg hDpos.le q)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right hKmoment _).trans_eq ?_
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hDpos.le q)]
  · have hpairsall := ae_all_iff.mpr fun n : ℕ =>
        ae_all_iff.mpr fun i : Fin p => ae_all_iff.mpr (hpairs n i)
    filter_upwards [hKbound, hpairsall] with omega hbound hpair
    intro i n k hk
    let k' : Fin (2 ^ n + 1) := ⟨k, by omega⟩
    obtain ⟨chi, h01, hone, hsupp, he⟩ := hpair n i k' hk
    refine ⟨chi, h01, hone, hsupp, fun x r hr hr1 => (he x r hr hr1).trans ?_⟩
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
    have hdiff : 0 < s1 i - s0 i := sub_pos.mpr (hs i).2
    have hgap : 0 < (s1 i - s0 i) / 2 ^ n / 2 := by positivity
    have hiD : ((s1 i - s0 i) / 2) ^ 2 ≤ D := by
      have hsum := Finset.single_le_sum (f := fun j : Fin p => ((s1 j - s0 j) / 2) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      exact hsum.trans (le_add_of_nonneg_left zero_le_one)
    have hZbound : Z n i k' omega ≤ K omega * (2 : ℝ) ^ (2 * n) :=
      (le_abs_self _).trans (hbound n i k')
    have hid : (2 : ℝ) ^ (2 * n) *
        ((s1 i - s0 i) / 2 ^ n / 2) ^ (-3 : ℝ) =
          ((s1 i - s0 i) / 2) ^ 2 *
            ((s1 i - s0 i) / 2 ^ n / 2) ^ (-5 : ℝ) := by
      rw [Real.rpow_neg hgap.le, Real.rpow_neg hgap.le]
      norm_num only [Real.rpow_ofNat]
      rw [show (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ n) ^ 2 by
        rw [Nat.mul_comm, pow_mul]]
      field_simp [hdiff.ne']
    calc
      Z n i k' omega * ((s1 i - s0 i) / 2 ^ n / 2) ^ (-3 : ℝ)
          ≤ (K omega * (2 : ℝ) ^ (2 * n)) *
              ((s1 i - s0 i) / 2 ^ n / 2) ^ (-3 : ℝ) := by gcongr
      _ = K omega * (((s1 i - s0 i) / 2) ^ 2 *
          ((s1 i - s0 i) / 2 ^ n / 2) ^ (-5 : ℝ)) := by rw [mul_assoc, hid]
      _ ≤ (D * K omega) * ((s1 i - s0 i) / 2 ^ n / 2) ^ (-5 : ℝ) := by
          have hK0 := zero_le_one.trans (hKone omega)
          have hpow0 := Real.rpow_nonneg hgap.le (-5 : ℝ)
          nlinarith [mul_le_mul_of_nonneg_left hiD (mul_nonneg hK0 hpow0)]

end SubdiffusiveProcess.Static
