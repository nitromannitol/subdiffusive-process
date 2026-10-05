module

public import SubdiffusiveProcess.Variational.QuadraticMinimizers

@[expose] public section

/-! # Transport of a coercive equation through a concrete linear equivalence -/

open InnerProductSpace
namespace SubdiffusiveProcess
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A continuous linear equivalence transports the weak solution and its uniqueness,
without requiring the source space to carry the target Hilbert norm. -/
theorem existsUnique_pullback_bilin_eq_load (T : V ≃L[ℝ] H)
    {B : H →L[ℝ] H →L[ℝ] ℝ} (hB : IsCoercive B) (L : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V, B (T u) (T v) = L v := by
  obtain ⟨g, hg, huniq⟩ := existsUnique_bilin_eq_load hB (L.comp T.symm.toContinuousLinearMap)
  refine ⟨T.symm g, ?_, ?_⟩
  · intro v
    simpa only [T.apply_symm_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, T.symm_apply_apply] using hg (T v)
  · intro u hu
    have ht : T u = g := huniq (T u) (by
      intro k
      simpa only [T.apply_symm_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe] using hu (T.symm k))
    calc
      u = T.symm (T u) := (T.symm_apply_apply u).symm
      _ = T.symm g := congrArg T.symm ht

end SubdiffusiveProcess
