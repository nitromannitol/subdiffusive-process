import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Carrier
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.ZeroTrace
import Homogenization.Sobolev.W1p.ZeroExtensionGraph

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/Regularity/StepFourHarmonicWindowSeam.lean




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2

open MeasureTheory
open Homogenization (Vec H1Function H10Function MemH10 LocalizedZeroTraceFunctionOn vecDot
  openCubeSet originCube)
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-! ### Weak harmonicity restricts -/

/-- The zero extension of a test function pairs with a fixed field exactly as the
test function itself does. -/
theorem setIntegral_vecDot_extendByZero {W V : Set (Vec d)} (hW : IsOpen W)
    (hV : IsOpen V) (hVW : V ⊆ W) (F : Vec d → Vec d) (φ : H10Function V) :
    ∫ p in W, vecDot (F p)
        ((φ.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.grad p) ∂volume
      = ∫ p in V, vecDot (F p) (φ.toH1Function.grad p) ∂volume := by
  have hind : (fun p => vecDot (F p)
        ((φ.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.grad p))
      = Set.indicator V (fun p => vecDot (F p) (φ.toH1Function.grad p)) := by
    funext p
    by_cases hp : p ∈ V
    · rw [Set.indicator_of_mem hp,
        Homogenization.H10Function.extendByZeroToOpenSuperset_grad,
        Homogenization.H10Function.zeroExtensionGrad_apply_of_mem φ hp]
    · rw [Set.indicator_of_notMem hp,
        Homogenization.H10Function.extendByZeroToOpenSuperset_grad,
        Homogenization.H10Function.zeroExtensionGrad_apply_of_not_mem φ hp,
        Homogenization.vecDot_zero_right]
  rw [hind, MeasureTheory.integral_indicator hV.measurableSet,
    Measure.restrict_restrict hV.measurableSet, Set.inter_eq_left.mpr hVW]

/-- **Weak harmonicity restricts to every open subset.**  Every test function of
`H¹₀(V)` extends by zero to one of `H¹₀(W)`, and the pairing is unchanged. -/
theorem isWeaklyHarmonicOn_restrict {a : Vec d → ℝ} {W V : Set (Vec d)} (hW : IsOpen W)
    (hV : IsOpen V) (hVW : V ⊆ W) {v : H1Function W}
    (h : IsWeaklyHarmonicOn a W v) :
    IsWeaklyHarmonicOn a V (v.restrict hV hVW) := by
  intro φ
  have hext := setIntegral_vecDot_extendByZero hW hV hVW (fun p => a p • v.grad p) φ
  have h0 := h (φ.extendByZeroToOpenSuperset hV.measurableSet hW hVW)
  rw [hext] at h0
  exact h0

/-- The unit-coefficient spelling of `isWeaklyHarmonicOn_restrict`. -/
theorem isUnitWeaklyHarmonicOn_restrict {W V : Set (Vec d)} (hW : IsOpen W)
    (hV : IsOpen V) (hVW : V ⊆ W) {v : H1Function W}
    (h : IsUnitWeaklyHarmonicOn W v) :
    IsUnitWeaklyHarmonicOn V (v.restrict hV hVW) :=
  isUnitWeaklyHarmonicOn_iff.2
    (isWeaklyHarmonicOn_restrict hW hV hVW (isUnitWeaklyHarmonicOn_iff.1 h))

/-! ### The localized zero trace from an intermediate superset -/

/-- **Localized zero trace from `H¹₀` of an intermediate superset.**  A cutoff
supported in the open window `R` localizes an `H¹₀(Y)` function into `H¹₀(R ∩ Y)`;
when `R ∩ Y = Ω` that is the localized zero trace on `Ω` against `R`. -/
theorem localizedZeroTraceFunctionOn_of_memH10_inter {Y R Omega : Set (Vec d)}
    (hY : IsOpen Y) (hR : IsOpen R) (hRY : R ∩ Y = Omega)
    {f : Vec d → ℝ} (hf : MemH10 Y f) :
    LocalizedZeroTraceFunctionOn Omega R f := by
  intro eta heta hetac hetaR
  have h := Section6SchauderDatum.memH10_mul_of_tsupport_subset hY hR hf heta hetac hetaR
  rwa [hRY] at h

/-- **The reflected window meets the anchor's replacement cube in the one-step
window.**  `reflectedWindow ∩ □_m = W` (`ZeroTrace.reflectedWindow_inter_openCubeSet`)
and `W ⊆ Y ⊆ □_m`. -/
theorem reflectedWindow_inter_eq_truncatedWindow {m k : ℤ} {x : Vec d} {Y : Set (Vec d)}
    (hWY : truncatedWindow x m k ⊆ Y) (hYm : Y ⊆ openCubeSet (originCube d m)) :
    reflectedWindow x m k ∩ Y = truncatedWindow x m k := by
  refine Set.Subset.antisymm ?_ ?_
  · intro p hp
    have hpm : p ∈ reflectedWindow x m k ∩ openCubeSet (originCube d m) :=
      ⟨hp.1, hYm hp.2⟩
    rwa [Section6SchauderDatum.reflectedWindow_inter_openCubeSet x m k] at hpm
  · exact fun p hp => ⟨truncatedWindow_subset_reflectedWindow x m k hp, hWY hp⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2
