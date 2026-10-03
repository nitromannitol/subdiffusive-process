module

public import SubdiffusiveProcess.Section10.StrictDecaySparse
public import SubdiffusiveProcess.Section10.StrictDecayClock

@[expose] public section




namespace SubdiffusiveProcess.Section10

open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (ahom)

noncomputable section

/-- The complete unchanged strict-decay conclusion, including both intrinsic
clock ratios. The disorder threshold precedes the model. -/
theorem strict_decay {d : ℕ} (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
      ∃ C eta c : ℝ, 0 < C ∧ 0 < eta ∧ 0 < c ∧
        (d = 2 → eta = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m / SubdiffusiveProcess.CoarseGrainingVocab.ahom M l ≤
            C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
        (∀ r R : ℝ, 1 ≤ r → r ≤ R →
          c * (R / r) ^ (2 + eta) ≤
            SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) R /
              SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) r) ∧
        ∀ (L : ℕ) (r R : ℝ), 1 ≤ r → r ≤ R → R ≤ (3 : ℝ) ^ L →
          c * (R / r) ^ (2 + eta) ≤
            SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScaleCutoff
                (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) L R /
              SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScaleCutoff
                (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) L r := by
  obtain ⟨delta0, hdelta0, hgeneric⟩ := exists_strictDecay_ratio_of_geometry d hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hM
  have hratio : ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
      (d = 2 → eta = tauSq M.P / Real.log 3) ∧
      ∀ ell m : ℕ, ell ≤ m → ahom M m / ahom M ell ≤
        C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (ell : ℝ)))) := by
    by_cases hd2 : d = 2
    · subst d
      refine ⟨1, tauSq M.P / Real.log 3, zero_lt_one,
        div_pos M.G4.tauSq_pos (Real.log_pos (by norm_num)), ?_, ?_⟩
      · intro _
        rfl
      · intro ell m _
        rw [one_mul]
        exact (strictDecay_planar_ratio M ell m).le
    · obtain ⟨C, eta, hC, heta, hdec⟩ := hgeneric M hM
      exact ⟨C, eta, hC, heta, fun h => False.elim (hd2 h), hdec⟩
  obtain ⟨C, eta, hC, heta, hplanar, hdec⟩ := hratio
  let c := Real.exp (-(Real.log C + eta * Real.log 3 + 2 * tauSq M.P))
  refine ⟨C, eta, c, hC, heta, Real.exp_pos _, hplanar, hdec, ?_, ?_⟩
  · intro r R hr hrR
    exact strictDecay_timeScale_ratio M hC heta.le hdec r R hr hrR
  · intro L r R hr hrR hR
    exact strictDecay_timeScaleCutoff_ratio M hC heta.le hdec L r R hr hrR hR

end

end SubdiffusiveProcess.Section10
