module

public import SubdiffusiveProcess.Sobolev.ContinuousZeroExtension
public import SubdiffusiveProcess.Sobolev.NativeRepresentativeData
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet

@[expose] public section

/-! # Continuous native zero extension

This module extends a continuous, boundary-zero native killed datum to a larger
open set while retaining its continuous representative and zero-extended
Sobolev data. It makes no claim about quantitative regularity or energy bounds.
-/

open MeasureTheory Set TopologicalSpace Homogenization
noncomputable section
namespace SubdiffusiveProcess

/-- A continuous killed native datum extends by zero as a continuous killed native datum with exactly the zero-extended Sobolev data. -/
theorem exists_continuous_native_zero_extension
    {d : ℕ} {V Q : Opens (SpatialCoordinates d)} (hVQ : V ≤ Q)
    (v : H10Function (V : Set (SpatialCoordinates d)))
    (hcont : ContinuousOn v.toH1Function.toFun (closure (V : Set (SpatialCoordinates d))))
    (hzero : ∀ x ∈ frontier (V : Set (SpatialCoordinates d)), v.toH1Function.toFun x = 0) :
    ∃ w : H10Function (Q : Set (SpatialCoordinates d)),
      Continuous w.toH1Function.toFun ∧
      sobolevDataOfH1 w.toH1Function = zeroExtensionSobolevData hVQ (sobolevDataOfH1 v.toH1Function) ∧
      EqOn w.toH1Function.toFun v.toH1Function.toFun (closure (V : Set (SpatialCoordinates d))) ∧
      ∀ x ∉ (V : Set (SpatialCoordinates d)), w.toH1Function.toFun x = 0 := by
  classical
  let W : SpatialCoordinates d → ℝ :=
    (V : Set (SpatialCoordinates d)).piecewise v.toH1Function.toFun (fun _ => 0)
  have hWcont : Continuous W :=
    continuous_piecewise hzero hcont continuousOn_const
  have hWagree : EqOn W v.toH1Function.toFun (closure (V : Set (SpatialCoordinates d))) := by
    intro x hx
    by_cases hxV : x ∈ (V : Set (SpatialCoordinates d))
    · simp only [W, Set.piecewise, ite_eq_left hxV]
    · have hxfront : x ∈ frontier (V : Set (SpatialCoordinates d)) := by
        rw [frontier_eq_closure_inter_closure]
        refine ⟨hx, ?_⟩
        rw [closure_compl, V.isOpen.interior_eq]
        exact hxV
      simp only [W, Set.piecewise, ite_eq_right hxV]
      exact (hzero x hxfront).symm
  let data := zeroExtensionSobolevData hVQ (sobolevDataOfH1 v.toH1Function)
  have hdataKilled : data ∈ killedSobolevGraph Q := by
    exact zeroExtensionSobolevData_mem_killed hVQ
      (sobolevDataOfH1_mem_killed v)
  have hIndicators :
      (V : Set (SpatialCoordinates d)).indicator
          ((sobolevDataOfH1 v.toH1Function).1 : SpatialCoordinates d → ℝ) =ᵐ[volume]
        (V : Set (SpatialCoordinates d)).indicator v.toH1Function.toFun := by
    exact (ae_eq_restrict_iff_indicator_ae_eq V.isOpen.measurableSet).mp
      (sobolevDataOfH1_fst_coeFn v.toH1Function)
  have hdataW :
      (data.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] W := by
    have hExt := zeroExtensionLp_coeFn hVQ (sobolevDataOfH1 v.toH1Function).1
    have hIndicatorQ :
        (V : Set (SpatialCoordinates d)).indicator
            ((sobolevDataOfH1 v.toH1Function).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (V : Set (SpatialCoordinates d)).indicator v.toH1Function.toFun :=
      ae_restrict_of_ae hIndicators
    filter_upwards [hExt, hIndicatorQ] with x hxExt hxIndicator
    change (zeroExtensionLp hVQ (sobolevDataOfH1 v.toH1Function).1) x = W x
    rw [hxExt, hxIndicator]
    simp only [W, Set.piecewise, Set.indicator_apply]
  obtain ⟨v0, hv0, _hgrad0⟩ := exists_nativeH10Function_of_killedSobolevGraph ⟨data, hdataKilled⟩
  have hv0W : W =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] v0.toH1Function.toFun := by
    filter_upwards [hdataW] with x hx
    rw [hv0]
    exact hx.symm
  let w := H10ofAEEq v0 W hv0W
  have hwfun : w.toH1Function.toFun = W := rfl
  have hwcont : Continuous w.toH1Function.toFun := by
    change Continuous W
    exact hWcont
  have hwagree : EqOn w.toH1Function.toFun v.toH1Function.toFun
      (closure (V : Set (SpatialCoordinates d))) := by
    intro x hx
    change W x = v.toH1Function.toFun x
    exact hWagree hx
  have hwzero : ∀ x ∉ (V : Set (SpatialCoordinates d)), w.toH1Function.toFun x = 0 := by
    intro x hx
    change W x = 0
    simp only [W, Set.piecewise, ite_eq_right hx]
  have hleftW :
      ((sobolevDataOfH1 w.toH1Function).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] W := by
    calc
      ((sobolevDataOfH1 w.toH1Function).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] w.toH1Function.toFun :=
            sobolevDataOfH1_fst_coeFn w.toH1Function
      _ =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] W :=
            Filter.EventuallyEq.of_eq hwfun
  have hfst : (sobolevDataOfH1 w.toH1Function).1 = data.1 := by
    apply Lp.ext
    exact hleftW.trans hdataW.symm
  have hleftWeak :
      (data.1, (sobolevDataOfH1 w.toH1Function).2) ∈ weakSobolevGraph Q := by
    rw [← hfst]
    exact sobolevDataOfH1_mem_weak w.toH1Function
  have hdataWeak : (data.1, data.2) ∈ weakSobolevGraph Q :=
    killedSobolevGraph_le_weakSobolevGraph hdataKilled
  have hgrad : (sobolevDataOfH1 w.toH1Function).2 = data.2 :=
    weakSobolevGraph_gradient_unique hleftWeak hdataWeak
  have hdata : sobolevDataOfH1 w.toH1Function = data := Prod.ext hfst hgrad
  exact ⟨w, hwcont, hdata, hwagree, hwzero⟩

end SubdiffusiveProcess
