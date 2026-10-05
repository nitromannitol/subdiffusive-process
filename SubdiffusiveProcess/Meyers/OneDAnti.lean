module

public import SubdiffusiveProcess.Meyers.OneDBump

@[expose] public section

/-! Antiderivative of a difference of two unit bumps: a smooth compactly supported test function
`φ` with `φ' = f₁ - f₂` and `|φ| ≤ 1`. -/

open MeasureTheory Set Filter Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

theorem antideriv_test {A B A' B' : ℝ} (hAA : A < A') (hAB : A' < B') (hBB : B' < B)
    {f1 f2 : ℝ → ℝ} (hc1 : ContDiff ℝ (⊤ : ℕ∞) f1) (hc2 : ContDiff ℝ (⊤ : ℕ∞) f2)
    (hn1 : ∀ s, 0 ≤ f1 s) (hn2 : ∀ s, 0 ≤ f2 s)
    (hs1 : Function.support f1 ⊆ Ioo A' B') (hs2 : Function.support f2 ⊆ Ioo A' B')
    (hi1 : ∫ s, f1 s = 1) (hi2 : ∫ s, f2 s = 1) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo A B ∧
      (∀ t, deriv φ t = f1 t - f2 t) ∧ ∀ t, |φ t| ≤ 1 := by
  have hcont1 : Continuous f1 := hc1.continuous
  have hcont2 : Continuous f2 := hc2.continuous
  have hcs1 : HasCompactSupport f1 := by
    have hsub : tsupport f1 ⊆ Icc A' B' :=
      closure_minimal (fun s hs => Ioo_subset_Icc_self (hs1 hs)) isClosed_Icc
    exact isCompact_Icc.of_isClosed_subset isClosed_closure hsub
  have hcs2 : HasCompactSupport f2 := by
    have hsub : tsupport f2 ⊆ Icc A' B' :=
      closure_minimal (fun s hs => Ioo_subset_Icc_self (hs2 hs)) isClosed_Icc
    exact isCompact_Icc.of_isClosed_subset isClosed_closure hsub
  have hint1 : Integrable f1 := hcont1.integrable_of_hasCompactSupport hcs1
  have hint2 : Integrable f2 := hcont2.integrable_of_hasCompactSupport hcs2
  set φ : ℝ → ℝ := fun t => ∫ s in A..t, (f1 s - f2 s) with hφ
  have hfc : Continuous (fun s => f1 s - f2 s) := hcont1.sub hcont2
  have hderiv : ∀ t, HasDerivAt φ (f1 t - f2 t) t := fun t =>
    (hfc.integral_hasStrictDerivAt A t).hasDerivAt
  have hderiv' : ∀ t, deriv φ t = f1 t - f2 t := fun t => (hderiv t).deriv
  -- vanishing outside [A', B']
  have hz1 : ∀ s, (s ≤ A' ∨ B' ≤ s) → f1 s = 0 := by
    intro s hs
    by_contra h
    have := hs1 (Function.mem_support.mpr h)
    rcases hs with hs | hs
    · exact absurd hs (not_le.mpr this.1)
    · exact absurd hs (not_le.mpr this.2)
  have hz2 : ∀ s, (s ≤ A' ∨ B' ≤ s) → f2 s = 0 := by
    intro s hs
    by_contra h
    have := hs2 (Function.mem_support.mpr h)
    rcases hs with hs | hs
    · exact absurd hs (not_le.mpr this.1)
    · exact absurd hs (not_le.mpr this.2)
  have hzero_left : ∀ t, t ≤ A' → φ t = 0 := by
    intro t ht
    simp only [hφ]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => by
      rw [Set.mem_uIcc] at hs
      have hsA' : s ≤ A' := by
        rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2.trans ht
        · linarith
      simp only [hz1 s (Or.inl hsA'), hz2 s (Or.inl hsA'), sub_self])]
    simp
  have hzero_right : ∀ t, B' ≤ t → φ t = 0 := by
    intro t ht
    simp only [hφ]
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have : x ≤ A ∨ t < x := by
          by_contra hcon
          push Not at hcon
          exact hx ⟨by linarith [hcon.1], hcon.2⟩
        rcases this with h | h
        · simp [hz1 x (Or.inl (by linarith)), hz2 x (Or.inl (by linarith))]
        · simp [hz1 x (Or.inr (by linarith)), hz2 x (Or.inr (by linarith))]),
      integral_sub hint1 hint2, hi1, hi2, sub_self]
  -- bound
  have hΦ : ∀ (f : ℝ → ℝ), Continuous f → Integrable f → (∀ s, 0 ≤ f s) →
      (∀ s, s ≤ A' → f s = 0) → ∫ s, f s = 1 →
      ∀ t, 0 ≤ ∫ s in A..t, f s ∧ ∫ s in A..t, f s ≤ 1 := by
    intro f hf hfi hfn hfz hfi1 t
    have e : ∫ s in A..t, f s = (∫ s in Iic t, f s) - ∫ s in Iic A, f s :=
      (intervalIntegral.integral_Iic_sub_Iic hfi.integrableOn hfi.integrableOn).symm
    have e0 : ∫ s in Iic A, f s = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun x hx => hfz x ((mem_Iic.mp hx).trans hAA.le))
    rw [e, e0, sub_zero]
    exact ⟨setIntegral_nonneg measurableSet_Iic (fun s _ => hfn s),
      hfi1 ▸ setIntegral_le_integral hfi (Eventually.of_forall hfn)⟩
  have hb1 := hΦ f1 hcont1 hint1 hn1 (fun s hs => hz1 s (Or.inl hs)) hi1
  have hb2 := hΦ f2 hcont2 hint2 hn2 (fun s hs => hz2 s (Or.inl hs)) hi2
  have hφ_eq : ∀ t, φ t = (∫ s in A..t, f1 s) - ∫ s in A..t, f2 s := fun t =>
    intervalIntegral.integral_sub (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)
  refine ⟨φ, ?_, ?_, ?_, hderiv', ?_⟩
  · rw [contDiff_infty_iff_deriv]
    refine ⟨fun t => (hderiv t).differentiableAt, ?_⟩
    have : deriv φ = fun t => f1 t - f2 t := funext hderiv'
    rw [this]
    exact hc1.sub hc2
  · have hsub : tsupport φ ⊆ Icc A' B' := by
      apply closure_minimal _ isClosed_Icc
      intro t ht
      rw [Function.mem_support] at ht
      constructor
      · by_contra h; exact ht (hzero_left t (by linarith [not_le.mp h]))
      · by_contra h; exact ht (hzero_right t (by linarith [not_le.mp h]))
    exact isCompact_Icc.of_isClosed_subset isClosed_closure hsub
  · have hsub : tsupport φ ⊆ Icc A' B' := by
      apply closure_minimal _ isClosed_Icc
      intro t ht
      rw [Function.mem_support] at ht
      constructor
      · by_contra h; exact ht (hzero_left t (by linarith [not_le.mp h]))
      · by_contra h; exact ht (hzero_right t (by linarith [not_le.mp h]))
    exact hsub.trans (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  · intro t
    rw [hφ_eq t, abs_le]
    constructor <;> linarith [hb1 t, hb2 t]

end SubdiffusiveProcess.Meyers
