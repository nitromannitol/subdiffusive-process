import SubdiffusiveProcess.Static.HarmonicPairGeometry

/-! # Translation of the literal harmonic cutoff witness -/
open MeasureTheory Homogenization Metric
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal Pointwise
noncomputable section
namespace SubdiffusiveProcess.Static

private theorem pair_translate_ball {d : ℕ} (c : Vec d) (r : ℝ) :
    translateSet c (ball (0 : Vec d) r) = ball c r := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  simp only [mem_ball, dist_eq_norm, sub_zero]

private def pairTranslationCastH10 {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (e : H10Function U) : H10Function V := h ▸ e

@[simp] private theorem pairTranslationCastH10_fun {d : ℕ} {U V : Set (Vec d)}
    (h : U = V) (e : H10Function U) :
    (pairTranslationCastH10 h e).toFun = e.toFun := by subst V; rfl

@[simp] private theorem pairTranslationCastH10_grad {d : ℕ} {U V : Set (Vec d)}
    (h : U = V) (e : H10Function U) :
    (pairTranslationCastH10 h e).grad = e.grad := by subst V; rfl

private def pairTranslateH10 {d : ℕ} (c : Vec d) {r : ℝ}
    (chi : H10Function (ball (0 : Vec d) r)) : H10Function (ball c r) :=
  pairTranslationCastH10 (pair_translate_ball c r) (chi.translate c)

@[simp] private theorem pairTranslateH10_fun {d : ℕ} (c : Vec d) {r : ℝ}
    (chi : H10Function (ball (0 : Vec d) r)) (x : Vec d) :
    (pairTranslateH10 c chi).toFun x = chi.toFun (x - c) := by
  simp [pairTranslateH10, H10Function.translate_toH1Function, H1Function.translate_toFun]

@[simp] private theorem pairTranslateH10_grad {d : ℕ} (c : Vec d) {r : ℝ}
    (chi : H10Function (ball (0 : Vec d) r)) (x : Vec d) :
    (pairTranslateH10 c chi).grad x = chi.grad (x - c) := by
  simp [pairTranslateH10, H10Function.translate_toH1Function, H1Function.translate_grad]

/-- Translation preserves every witness clause and the exact ball-energy price. -/
theorem exists_pair_translated_cutoff {d : ℕ} (c : Vec d) (A : Vec d → ℝ)
    (R1 R2 G : ℝ) (chi : H10Function (ball (0 : Vec d) R2))
    (h01 : ∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1)
    (hone : ∀ x ∈ ball (0 : Vec d) R1, chi.toFun x = 1)
    (hsupp : tsupport chi.toFun ⊆ ball (0 : Vec d) R2)
    (he : ∀ (x : Vec d) (r : ℝ), 0 < r → r ≤ 1 →
      ∫⁻ w in ball x r ∩ ball (0 : Vec d) R2,
        ENNReal.ofReal (A (c + w) * vecDot (chi.grad w) (chi.grad w)) ≤
          ENNReal.ofReal (G * r ^ ((d : ℝ) - 1 / 2))) :
    ∃ psi : H10Function (ball c R2),
      (∀ x, 0 ≤ psi.toFun x ∧ psi.toFun x ≤ 1) ∧
      (∀ x ∈ ball c R1, psi.toFun x = 1) ∧ tsupport psi.toFun ⊆ ball c R2 ∧
      ∀ (x : Vec d) (r : ℝ), 0 < r → r ≤ 1 →
        ∫⁻ w in ball x r ∩ ball c R2,
          ENNReal.ofReal (A w * vecDot (psi.grad w) (psi.grad w)) ≤
            ENNReal.ofReal (G * r ^ ((d : ℝ) - 1 / 2)) := by
  refine ⟨pairTranslateH10 c chi, fun x => by simpa using h01 (x - c), ?_, ?_, ?_⟩
  · intro x hx
    rw [pairTranslateH10_fun]
    apply hone
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hx
  · have heq : (pairTranslateH10 c chi).toFun =
        chi.toFun ∘ (Homeomorph.addRight (-c)) := by
      funext x
      simp [sub_eq_add_neg]
    rw [heq, tsupport_comp_eq_preimage]
    intro x hx
    have h := hsupp hx
    simpa [mem_ball, dist_eq_norm, sub_eq_add_neg] using h
  · intro x r hr hr1
    rw [lintegral_window_affine c zero_lt_one (measurableSet_ball.inter measurableSet_ball),
      Set.preimage_inter, pair_affine_preimage_ball c x zero_lt_one,
      pair_affine_preimage_ball c c zero_lt_one]
    simpa only [one_pow, ENNReal.ofReal_one, one_mul, inv_one, one_smul, div_one,
      sub_self, pairTranslateH10_grad, add_sub_cancel_left] using he (x - c) r hr hr1

end SubdiffusiveProcess.Static
