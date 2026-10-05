module

public import Homogenization.Sobolev.Foundations.AxisCube
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Providers.Section8.CommonSemigroupCrossing
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section


theorem SubdiffusiveProcess.Section8.common_semigroup_crossing (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ d : ℕ, ∀ _hd : 2 ≤ d, ∀ mu : Measure (Path d), IsProbabilityMeasure mu →
        ∀ t F0 : ℝ, 0 < t → 0 < F0 → ∀ n : ℕ, ∀ event : Set (Path d),
          MeasurableSet[LifetimePath.canonicalFiltration (Real.toNNReal t)] event →
          Crossing mu c0 F0 t n event →
          mu event ≤ ENNReal.ofReal (Real.exp (C * t / F0 - c * n))) ∧
      (∀ d : ℕ, ∀ _hd : 2 ≤ d, ∀ law : Kernel (Vec d) (Path d), StrongMarkov law →
        ∀ t F0 : ℝ, 0 < t → 0 < F0 → ∀ n : ℕ, ∀ E F : Set (Vec d),
        MeasurableSet E → MeasurableSet F →
        let rowEvent := fun B : Set (Vec d) =>
          {w : Path d | LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B}
        (∀ z ∈ E, Crossing (law z) c0 F0 t n (rowEvent F)) →
          (∀ z ∈ E, law z (rowEvent F) ≤
            ENNReal.ofReal (Real.exp (C * t / F0 - c * n))) ∧
          (∀ mu : Measure (Vec d), SFinite mu →
            (∀ B D : Set (Vec d), MeasurableSet B → MeasurableSet D →
              (∫⁻ x in B, law x (rowEvent D) ∂mu) =
              ∫⁻ x in D, law x (rowEvent B) ∂mu) →
            (∀ z ∈ F, Crossing (law z) c0 F0 t n (rowEvent E)) →
            ∀ f : Vec d → ℝ, MemLp f 2 mu →
              eLpNorm (F.indicator (fun x => ∫ w,
                (LifetimePath.coordinate (Real.toNNReal t) w).elim
                  (E.indicator f) (fun _ => 0) ∂law x)) 2 mu ≤
                ENNReal.ofReal (Real.exp (C * t / F0 - c * n)) * eLpNorm f 2 mu)) ∧
      (∀ d : ℕ, ∀ _hd : 2 ≤ d, ∀ law : Kernel (Vec d) (Path d), StrongMarkov law →
        ∀ t F0 : ℝ, 0 < t → 0 < F0 → ∀ n : ℕ,
        ∀ x : Vec d, ∀ T : Path d → ENNReal,
        ∀ hT : IsStoppingTime LifetimePath.canonicalFiltration T,
        ∀ event : Set (Path d × Path d),
        MeasurableSet[hT.measurableSpace.prod inferInstance] event →
        (∀ᵐ w ∂law x, T w < w.lifetime →
          MeasurableSet[LifetimePath.canonicalFiltration (Real.toNNReal t)]
            {v | (w, v) ∈ event} ∧
          Crossing (law (position (T w).toNNReal w)) c0 F0 t n {v | (w, v) ∈ event}) →
        ∀ B : Set (Path d), MeasurableSet[hT.measurableSpace] B →
          law x (B ∩ {w | T w < w.lifetime ∧
            (w, LifetimePath.shift (T w).toNNReal w) ∈ event}) ≤
          ENNReal.ofReal (Real.exp (C * t / F0 - c * n)) *
            law x (B ∩ {w | T w < w.lifetime}))

:= SubdiffusiveProcess.Providers.Section8.common_semigroup_crossing c0 hc0
