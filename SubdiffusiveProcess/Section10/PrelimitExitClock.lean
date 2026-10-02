import SubdiffusiveProcess.Section10.StrictDecayProvider
import SubdiffusiveProcess.Section10.PhysicalLocalTransportCoefficients

/-! Raw prelimit clock conversion in the genuine finite window. The provider's
rate is chosen once, before any moment order or deterministic start sequence. -/
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
noncomputable section
namespace SubdiffusiveProcess.Section10.PrelimitExitClock

/-- No normalization by ahom_0 enters the raw local/global clock ratio. -/
theorem rawClock_ratio {d : ℕ} (M : GMCModel d) {N k : ℕ} (hk : k ≤ N) :
    (rawClock M N (N-k) : ℝ) / (rawClock M N N : ℝ) =
      (3 : ℝ) ^ (-2 * (k : ℝ)) * (ahom M N / ahom M (N-k)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hcast : ((N-k : ℕ) : ℝ) = (N : ℝ) - k := Nat.cast_sub hk
  simp only [rawClock, activeScale_coe, min_eq_left (Nat.sub_le N k), min_self,
    NNReal.coe_mk]
  rw [← Real.rpow_natCast (3 : ℝ) (2 * (N-k)),
    ← Real.rpow_natCast (3 : ℝ) (2*N)]
  push_cast
  rw [hcast]
  have he : 2 * ((N : ℝ) - k) = -2 * (k : ℝ) + 2 * N := by ring
  rw [he, Real.rpow_add h3]
  field_simp [(ahom_pos M N).ne', (ahom_pos M (N-k)).ne',
    (Real.rpow_pos_of_pos h3 (2 * (N : ℝ))).ne']

/-- The same strict-decay eta controls every prelimit pair N>=k. -/
theorem rawClock_ratio_le {d : ℕ} (M : GMCModel d) {C eta : ℝ}
    (hdec : ∀ l m : ℕ, l ≤ m → ahom M m / ahom M l ≤
      C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ)))))
    {N k : ℕ} (hk : k ≤ N) :
    (rawClock M N (N-k) : ℝ) / (rawClock M N N : ℝ) ≤
      C * (3 : ℝ) ^ (-((2+eta) * (k : ℝ))) := by
  rw [rawClock_ratio M hk]
  have h := hdec (N-k) N (Nat.sub_le N k)
  have hcast : (N : ℝ) - ((N-k : ℕ) : ℝ) = (k : ℝ) := by
    rw [Nat.cast_sub hk]; ring
  rw [hcast] at h
  calc
    _ ≤ (3 : ℝ) ^ (-2 * (k : ℝ)) *
        (C * (3 : ℝ) ^ (-(eta * (k : ℝ)))) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by
      rw [show -((2+eta) * (k : ℝ)) = -2 * (k : ℝ) + -(eta * (k : ℝ)) by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring

/-- Complete strict-decay application: the witnesses precede all clock windows. -/
theorem exists_prelimit_clock_rate {d : ℕ} (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
        (d = 2 → eta = tauSq M.P / Real.log 3) ∧
        ∀ N k : ℕ, k ≤ N →
          (rawClock M N (N-k) : ℝ) / (rawClock M N N : ℝ) ≤
            C * (3 : ℝ) ^ (-((2+eta) * (k : ℝ))) := by
  obtain ⟨delta0, hdelta0, hmodels⟩ := strict_decay hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hM
  obtain ⟨C, eta, c, hC, heta, _, hplanar, hdec, _, _⟩ := hmodels M hM
  exact ⟨C, eta, hC, heta, hplanar, fun N k hk => rawClock_ratio_le M hdec hk⟩

end SubdiffusiveProcess.Section10.PrelimitExitClock
