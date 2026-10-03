module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossingProbability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossingSchur
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossingMarkov
public import Homogenization.Sobolev.Foundations.AxisCube
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing
open scoped ENNReal NNReal
noncomputable section


set_option linter.unusedVariables false in

theorem SubdiffusiveProcess.Providers.Section8.common_semigroup_crossing (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ d : ℕ, ∀ hd : 2 ≤ d, ∀ mu : Measure (Path d), IsProbabilityMeasure mu →
        ∀ t F0 : ℝ, 0 < t → 0 < F0 → ∀ n : ℕ, ∀ event : Set (Path d),
          MeasurableSet[LifetimePath.canonicalFiltration (Real.toNNReal t)] event →
          Crossing mu c0 F0 t n event →
          mu event ≤ ENNReal.ofReal (Real.exp (C * t / F0 - c * n))) ∧
      (∀ d : ℕ, ∀ hd : 2 ≤ d, ∀ law : Kernel (Vec d) (Path d), StrongMarkov law →
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
      (∀ d : ℕ, ∀ hd : 2 ≤ d, ∀ law : Kernel (Vec d) (Path d), StrongMarkov law →
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

:= by
  refine ⟨min c0 1*(1-Real.exp (-c0)), 1,
    rate_pos c0 hc0 (rate_neg_exp_lt c0 hc0), zero_lt_one, ?_, ?_, ?_⟩
  · intro d _hd mu hmu t F0 ht hF0 n event _hmeas hcross
    letI : IsProbabilityMeasure mu := hmu
    simpa only [one_mul] using crossing_bound c0 hc0 mu t F0 ht hF0 n event hcross
  · intro d _hd law hSM t F0 ht hF0 n E F hE hF
    letI : IsMarkovKernel law := is_markov_kernel_of_strong_markov hSM
    dsimp only
    intro hcross
    have hrow : ∀ z ∈ E,
        law z {w | LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' F} ≤
          ENNReal.ofReal (Real.exp (1*t/F0 - (min c0 1*(1-Real.exp (-c0)))*n)) := by
      intro z hz
      simpa only [one_mul] using crossing_bound c0 hc0 (law z) t F0 ht hF0 n _
        (hcross z hz)
    refine ⟨hrow, ?_⟩
    intro mu _hfinite hsym hreverse f hf
    refine SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossingSchur.eLpNorm_pathIntegral_le
      law (Real.toNNReal t) hE hF _ (Real.exp_pos _) mu hsym hrow ?_ f hf
    intro z hz
    simpa only [one_mul] using crossing_bound c0 hc0 (law z) t F0 ht hF0 n _
      (hreverse z hz)
  · intro d _hd law hSM t F0 ht hF0 n x T hT event hevent hcross B hB
    letI : IsMarkovKernel law := is_markov_kernel_of_strong_markov hSM
    refine strong_markov_random_section_le hSM x T hT event hevent _ ?_ B hB
    filter_upwards [hcross] with w hw
    intro hAlive
    simpa only [one_mul] using crossing_bound c0 hc0
      (law (position (T w).toNNReal w)) t F0 ht hF0 n {v | (w, v) ∈ event}
      (hw hAlive).2
