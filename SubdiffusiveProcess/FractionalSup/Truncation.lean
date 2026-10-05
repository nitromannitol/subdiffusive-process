module

public import SubdiffusiveProcess.Sobolev.HarmonicDiffMaxPrinciple
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.Sobolev.NativeH10Reverse
public import SubdiffusiveProcess.Sobolev.NativeH1
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector

@[expose] public section

/-!
# Positive-part truncations of a Dirichlet solution are killed test functions

If `u - b ∈ H¹₀(Q)` and `b ≤ c` almost everywhere, then `(u - c)₊` is an element of the killed
Sobolev graph with weak gradient `1_{u>c} ∇u` (matched-trace truncation).
-/

open MeasureTheory Set TopologicalSpace

namespace SubdiffusiveProcess

variable {d : ℕ}

theorem exists_killed_positivePart {Q : Opens (SpatialCoordinates d)}
    (hQ : Homogenization.IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)))
    (u b : weakSobolevGraph Q) (hdiff : u.val - b.val ∈ killedSobolevGraph Q) (c : ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), b.val.1 x ≤ c) :
    ∃ Ψ : SobolevData Q, Ψ ∈ killedSobolevGraph Q ∧
      (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        Ψ.1 x = max (u.val.1 x - c) 0) ∧
      ∀ i, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        Ψ.2 i x = if c < u.val.1 x then u.val.2 i x else 0 := by
  classical
  obtain ⟨uN, uNval, uNgrad⟩ := exists_nativeH1Function_of_weakSobolevGraph u
  obtain ⟨bN, bNval, -⟩ := exists_nativeH1Function_of_weakSobolevGraph b
  obtain ⟨e, hefun, -⟩ := exists_nativeH10Function_of_killedSobolevGraph
    (⟨u.val - b.val, hdiff⟩ : killedSobolevGraph Q)
  have hdiffN : Homogenization.MemH10 (Q : Set (SpatialCoordinates d))
      (fun y => uN.toFun y - bN.toFun y) := by
    refine memH10_congr (f := e.toH1Function.toFun) ⟨e, rfl⟩ ?_
    filter_upwards [Lp.coeFn_sub u.val.1 b.val.1] with x hx
    have h1 : e.toH1Function.toFun x = (u.val - b.val).1 x := congrFun hefun x
    rw [h1]
    change (u.val.1 - b.val.1 : DomainL2 Q) x = _
    rw [hx]
    simp only [Pi.sub_apply]
    rw [show uN.toFun x = u.val.1 x from congrFun uNval x,
      show bN.toFun x = b.val.1 x from congrFun bNval x]
  have hmatch := Homogenization.memH10_max_sub_matched hQ uN bN hdiffN c
  have hbz : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      max (bN.toFun x - c) 0 = 0 := by
    filter_upwards [hb] with x hx
    rw [show bN.toFun x = b.val.1 x from congrFun bNval x]
    exact max_eq_right (by linarith)
  have hmem : Homogenization.MemH10 (Q : Set (SpatialCoordinates d))
      (fun x => max (uN.toFun x - c) 0) := by
    refine memH10_congr hmatch ?_
    filter_upwards [hbz] with x hx
    rw [hx, sub_zero]
  obtain ⟨ρ, hρ⟩ := hmem
  obtain ⟨V, hVf, hVg⟩ := Homogenization.exists_h1_max_sub_const hQ uN c
  have hgrad : ρ.toH1Function.grad =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V.grad :=
    Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hQ.isOpen
      (u := ρ.toH1Function) (v := V)
      (Filter.Eventually.of_forall fun x => by rw [hρ, hVf])
  obtain ⟨Ψ, hΨk, hΨ1, hΨ2⟩ := exists_killedSobolevGraph_of_h10Function ρ
  refine ⟨Ψ, hΨk, ?_, fun i => ?_⟩
  · filter_upwards [hΨ1] with x hx
    rw [hx, hρ]
    simp only [show uN.toFun x = u.val.1 x from congrFun uNval x]
  · filter_upwards [hΨ2 i, hgrad, hVg] with x h1 h2 h3
    have h2' : ρ.toH1Function.grad x i = V.grad x i := by rw [h2]
    rw [h1, h2', h3]
    simp only [Set.indicator_apply, mem_ofPred_eq]
    have hu1 : uN.toFun x = u.val.1 x := congrFun uNval x
    have hu2 : uN.grad x i = u.val.2 i x := congrFun (congrFun uNgrad x) i
    by_cases hc : c < u.val.1 x
    · simp [hu1, hc, hu2]
    · simp [hu1, hc]

end SubdiffusiveProcess
