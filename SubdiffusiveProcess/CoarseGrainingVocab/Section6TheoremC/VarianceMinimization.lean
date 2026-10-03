module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization (volumeAverage)

noncomputable section

variable {d : ℕ}

/-! ### The bias-variance split -/

/-- On a window of finite volume the average of the constant `1` is `1`. -/
theorem volumeAverage_one {W : Set (Vec d)} (hW : 0 < (volume W).toReal) :
    volumeAverage W (fun _ ↦ (1 : ℝ)) = 1 := by
  unfold volumeAverage
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  exact inv_mul_cancel₀ hW.ne'

/-- The centered function has vanishing integral on the window. -/
theorem setIntegral_sub_averageOn {W : Set (Vec d)} {f : Vec d → ℝ}
    (hW : 0 < (volume W).toReal) (hWtop : volume W ≠ ⊤)
    (hf : IntegrableOn f W) :
    ∫ x in W, (f x - averageOn W f) = 0 := by
  have hconst : IntegrableOn (fun _ : Vec d ↦ averageOn W f) W :=
    integrableOn_const (by simp [hWtop])
  rw [integral_sub hf hconst, setIntegral_const, smul_eq_mul, measureReal_def]
  unfold averageOn volumeAverage
  field_simp
  ring

/-- **Bias-variance split.**  For any constant `c`, the unnormalized `L²` error
on `W` splits into the centered error plus the squared bias. -/
theorem setIntegral_sub_sq_eq {W : Set (Vec d)} {f : Vec d → ℝ} (c : ℝ)
    (hW : 0 < (volume W).toReal) (hWtop : volume W ≠ ⊤)
    (hf : IntegrableOn f W) (hf2 : IntegrableOn (fun x ↦ f x ^ 2) W) :
    ∫ x in W, (f x - c) ^ 2 =
      (∫ x in W, (f x - averageOn W f) ^ 2) +
        (averageOn W f - c) ^ 2 * (volume W).toReal := by
  set A := averageOn W f with hA
  have e1 : IntegrableOn (fun x ↦ (f x - A) ^ 2) W := by
    have hexp : (fun x ↦ (f x - A) ^ 2) =
        fun x ↦ f x ^ 2 - 2 * A * f x + A ^ 2 := by
      funext x; ring
    rw [hexp]
    exact (hf2.sub (hf.const_mul (2 * A))).add (integrableOn_const hWtop)
  have ecent : IntegrableOn (fun x ↦ f x - A) W :=
    hf.sub (integrableOn_const hWtop)
  have e2 : IntegrableOn (fun x ↦ 2 * (A - c) * (f x - A)) W :=
    ecent.const_mul _
  have e3 : IntegrableOn (fun _ : Vec d ↦ (A - c) ^ 2) W :=
    integrableOn_const hWtop
  have e12 : IntegrableOn
      (fun x ↦ (f x - A) ^ 2 + 2 * (A - c) * (f x - A)) W := e1.add e2
  have hexpand : (fun x ↦ (f x - c) ^ 2) =
      fun x ↦ ((f x - A) ^ 2 + 2 * (A - c) * (f x - A)) + (A - c) ^ 2 := by
    funext x; ring
  rw [hexpand, integral_add e12 e3, integral_add e1 e2, integral_const_mul,
    setIntegral_sub_averageOn hW hWtop hf, mul_zero, add_zero,
    setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]

/-! ### The minimizing property -/



theorem normalizedL2On_sub_averageOn_le {W : Set (Vec d)} {f : Vec d → ℝ}
    (c : ℝ) (hW : 0 < (volume W).toReal) (hWtop : volume W ≠ ⊤)
    (hf : IntegrableOn f W) (hf2 : IntegrableOn (fun x ↦ f x ^ 2) W) :
    normalizedL2On W (fun x ↦ f x - averageOn W f) ≤
      normalizedL2On W (fun x ↦ f x - c) := by
  have hsplit := setIntegral_sub_sq_eq c hW hWtop hf hf2
  have hbias : 0 ≤ (averageOn W f - c) ^ 2 * (volume W).toReal :=
    mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg
  have hint : (∫ x in W, (f x - averageOn W f) ^ 2) ≤
      ∫ x in W, (f x - c) ^ 2 := by linarith
  unfold normalizedL2On volumeAverage
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left hint (by positivity))

/-- The centered seminorm is therefore the infimum over constants, in exactly
the shape the frozen Liouville hypothesis uses. -/
theorem isLeast_normalizedL2On_sub_const {W : Set (Vec d)} {f : Vec d → ℝ}
    (hW : 0 < (volume W).toReal) (hWtop : volume W ≠ ⊤)
    (hf : IntegrableOn f W) (hf2 : IntegrableOn (fun x ↦ f x ^ 2) W) :
    IsLeast {r : ℝ | ∃ c : ℝ, r = normalizedL2On W (fun x ↦ f x - c)}
      (normalizedL2On W (fun x ↦ f x - averageOn W f)) :=
  ⟨⟨averageOn W f, rfl⟩, by
    rintro r ⟨c, rfl⟩
    exact normalizedL2On_sub_averageOn_le c hW hWtop hf hf2⟩

/-- Consequently the frozen `sInf` of the Liouville hypothesis is attained at
the window average. -/
theorem sInf_normalizedL2On_sub_const {W : Set (Vec d)} {f : Vec d → ℝ}
    (hW : 0 < (volume W).toReal) (hWtop : volume W ≠ ⊤)
    (hf : IntegrableOn f W) (hf2 : IntegrableOn (fun x ↦ f x ^ 2) W) :
    sInf {r : ℝ | ∃ c : ℝ, r = normalizedL2On W (fun x ↦ f x - c)} =
      normalizedL2On W (fun x ↦ f x - averageOn W f) :=
  (isLeast_normalizedL2On_sub_const hW hWtop hf hf2).csInf_eq

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
