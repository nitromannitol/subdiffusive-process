module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.HahnBanach

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open InnerProductSpace

noncomputable section

/-- A functional bounded by the image norm has a Riesz representative in the
target Hilbert space.  No density hypothesis on the test map is needed. -/
theorem exists_riesz_representative_of_norm_le
    {S H : Type*} [AddCommGroup S] [Module ℂ S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : S →ₗ[ℂ] H) (L : S →ₗ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s, ‖L s‖ ≤ C * ‖T s‖) :
    ∃ h : H, ‖h‖ ≤ C ∧ ∀ s, L s = inner ℂ h (T s) := by
  have hker : LinearMap.ker T ≤ LinearMap.ker L := by
    intro s hs
    have hzero : ‖L s‖ ≤ 0 := by
      simpa only [LinearMap.mem_ker.mp hs, norm_zero, mul_zero] using hbound s
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))
  have hwell : ∀ x y : S, T x = T y → L x = L y := by
    intro x y hxy
    have hsub : x - y ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    have := hker hsub
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  let R : LinearMap.range T →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ L (Classical.choose y.property)
      map_add' := by
        intro x y
        rw [← map_add]
        apply hwell
        rw [map_add]
        exact (Classical.choose_spec (x + y).property).trans <|
          congrArg₂ (fun a b : H ↦ a + b)
            (Classical.choose_spec x.property).symm
            (Classical.choose_spec y.property).symm
      map_smul' := by
        intro c x
        rw [← map_smul]
        apply hwell
        rw [map_smul]
        exact (Classical.choose_spec (c • x).property).trans <|
          congrArg (fun a : H ↦ c • a) (Classical.choose_spec x.property).symm }
  have hRbound : ∀ y : LinearMap.range T, ‖R y‖ ≤ C * ‖y‖ := by
    intro y
    change ‖L (Classical.choose y.property)‖ ≤ C * ‖y‖
    calc
      ‖L (Classical.choose y.property)‖ ≤
          C * ‖T (Classical.choose y.property)‖ := hbound _
      _ = C * ‖y‖ := by
        change C * ‖T (Classical.choose y.property)‖ = C * ‖(y : H)‖
        rw [Classical.choose_spec y.property]
  let Rc : LinearMap.range T →L[ℂ] ℂ := R.mkContinuous C hRbound
  have hRcNorm : ‖Rc‖ ≤ C :=
    LinearMap.mkContinuous_norm_le R hC hRbound
  obtain ⟨Le, hLe, hLeNorm⟩ := exists_extension_norm_eq (LinearMap.range T) Rc
  let h : H := (toDual ℂ H).symm Le
  refine ⟨h, ?_, ?_⟩
  · calc
      ‖h‖ = ‖Le‖ := (toDual ℂ H).symm.norm_map Le
      _ = ‖Rc‖ := hLeNorm
      _ ≤ C := hRcNorm
  · intro s
    have hrange : T s ∈ LinearMap.range T := ⟨s, rfl⟩
    let y : LinearMap.range T := ⟨T s, hrange⟩
    calc
      L s = R y := by
        change L s = L (Classical.choose y.property)
        exact hwell _ _ (Classical.choose_spec y.property).symm
      _ = Rc y := rfl
      _ = Le y := (hLe y).symm
      _ = inner ℂ h (T s) := by
        change Le (T s) = inner ℂ h (T s)
        exact (congrFun
          (congrArg DFunLike.coe ((toDual ℂ H).apply_symm_apply Le)) (T s)).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
