module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.DepthGammaOne
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.MeasurableNatEnvelope

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The literal depth attached to an index valued in `{-1, 0, …, m}`. -/
noncomputable def stoppingDepth (m : ℕ) (J : Ω → ℤ) : Ω → ℕ :=
  fun omega => ((m : ℤ) - J omega).toNat

omit [MeasurableSpace Ω] in
theorem stoppingDepth_le_succ {m : ℕ} {J : Ω → ℤ}
    (hJ : ∀ omega, J omega ∈ Set.Icc (-1 : ℤ) m) (omega : Ω) :
    stoppingDepth m J omega ≤ m + 1 := by
  have h := (hJ omega).1
  unfold stoppingDepth
  omega

omit [MeasurableSpace Ω] in
theorem cast_stoppingDepth {m : ℕ} {J : Ω → ℤ}
    (hJ : ∀ omega, J omega ∈ Set.Icc (-1 : ℤ) m) (omega : Ω) :
    ((stoppingDepth m J omega : ℤ)) = (m : ℤ) - J omega := by
  have h := (hJ omega).2
  unfold stoppingDepth
  omega

/-- The measurable envelope of a stopping depth, capped at the deterministic
bound `m + 1`. -/
noncomputable def envelopedDepth (mu : Measure Ω) (m : ℕ) (J : Ω → ℤ) : Ω → ℕ :=
  measurableNatEnvelope mu (stoppingDepth m J) (m + 1)

theorem measurable_envelopedDepth (mu : Measure Ω) (m : ℕ) (J : Ω → ℤ) :
    Measurable (envelopedDepth mu m J) :=
  measurable_measurableNatEnvelope _ _ _

theorem envelopedDepth_le_succ (mu : Measure Ω) (m : ℕ) (J : Ω → ℤ)
    (omega : Ω) : envelopedDepth mu m J omega ≤ m + 1 :=
  measurableNatEnvelope_le _ _ _ _

theorem stoppingDepth_le_envelopedDepth {mu : Measure Ω} {m : ℕ} {J : Ω → ℤ}
    (hJ : ∀ omega, J omega ∈ Set.Icc (-1 : ℤ) m) (omega : Ω) :
    stoppingDepth m J omega ≤ envelopedDepth mu m J omega :=
  le_measurableNatEnvelope (stoppingDepth_le_succ hJ omega)



theorem measureReal_envelopedDepth_tail_le [IsFiniteMeasure μ]
    (m : ℕ) (J : Ω → ℤ) (q : ℕ) :
    μ.real {omega | q < envelopedDepth μ m J omega} ≤
      μ.real {omega | q < stoppingDepth m J omega} := by
  refine ENNReal.toReal_mono (measure_ne_top μ _) ?_
  exact measure_measurableNatEnvelope_tail_le _ _ _ _

/-- **The frozen stopping-witness shape.**  From a geometric tail on the
literal depth of an index valued in `{-1, 0, …, m}`, produce an index `X`
with the same range, dominated by the literal index (so every pathwise
conclusion below the literal index survives), whose depth satisfies the
frozen `O_{Γ_1}` bound at the sharp scale `4 (1 + log K) / r`. -/
theorem exists_stopping_witness_ogammaLE
    [IsProbabilityMeasure μ] (m : ℕ) (J : Ω → ℤ)
    (hJ : ∀ omega, J omega ∈ Set.Icc (-1 : ℤ) m)
    {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r)
    (htail : ∀ q : ℕ, 0 < q →
      μ.real {omega | q < ((m : ℤ) - J omega).toNat} ≤
        K * Real.exp (-(r * (q : ℝ)))) :
    ∃ X : Ω → ℤ,
      (∀ omega, X omega ∈ Set.Icc (-1 : ℤ) m) ∧
      (∀ omega, X omega ≤ J omega) ∧
      Measurable (fun omega => max ((((m : ℤ) - X omega).toNat : ℝ) - 1) 0) ∧
      SubdiffusiveProcess.OGammaLE μ 1 (depthGammaOneScaleSharp K r)
        (fun omega => max ((((m : ℤ) - X omega).toNat : ℝ) - 1) 0) := by
  set D : Ω → ℕ := envelopedDepth μ m J with hDdef
  have hdepth : (fun omega => max ((((m : ℤ) -
      ((m : ℤ) - (D omega : ℤ))).toNat : ℝ) - 1) 0) = depthObservable D := by
    funext omega
    have hsimp : (m : ℤ) - ((m : ℤ) - (D omega : ℤ)) = (D omega : ℤ) := by ring
    rw [hsimp, Int.toNat_natCast]
    rfl
  refine ⟨fun omega => (m : ℤ) - (D omega : ℤ), ?_, ?_, ?_, ?_⟩
  · intro omega
    show (m : ℤ) - (D omega : ℤ) ∈ Set.Icc (-1 : ℤ) (m : ℤ)
    have hle : D omega ≤ m + 1 := envelopedDepth_le_succ μ m J omega
    have hcast : (D omega : ℤ) ≤ (m : ℤ) + 1 := by exact_mod_cast hle
    have hnonneg : (0 : ℤ) ≤ (D omega : ℤ) := Int.natCast_nonneg _
    exact Set.mem_Icc.2 ⟨by omega, by omega⟩
  · intro omega
    show (m : ℤ) - (D omega : ℤ) ≤ J omega
    have hdom : stoppingDepth m J omega ≤ D omega :=
      stoppingDepth_le_envelopedDepth hJ omega
    have hcast : (stoppingDepth m J omega : ℤ) ≤ (D omega : ℤ) := by
      exact_mod_cast hdom
    rw [cast_stoppingDepth hJ omega] at hcast
    omega
  · rw [hdepth]
    exact measurable_depthObservable (measurable_envelopedDepth μ m J)
  · -- the depth of the produced index is exactly the envelope
    rw [hdepth]
    refine ogammaLE_one_depthObservable_sharp (μ := μ)
      (measurable_envelopedDepth μ m J) hK hr ?_
    intro q hq
    exact (measureReal_envelopedDepth_tail_le m J q).trans (htail q hq)

/-- The witness at any scale at least the sharp one.  Proof a frozen clause
whose printed constant exceeds the constant produced by the proof route uses
this form. -/
theorem exists_stopping_witness_ogammaLE_of_le
    [IsProbabilityMeasure μ] (m : ℕ) (J : Ω → ℤ)
    (hJ : ∀ omega, J omega ∈ Set.Icc (-1 : ℤ) m)
    {K r A : ℝ} (hK : 1 ≤ K) (hr : 0 < r)
    (hA : depthGammaOneScaleSharp K r ≤ A)
    (htail : ∀ q : ℕ, 0 < q →
      μ.real {omega | q < ((m : ℤ) - J omega).toNat} ≤
        K * Real.exp (-(r * (q : ℝ)))) :
    ∃ X : Ω → ℤ,
      (∀ omega, X omega ∈ Set.Icc (-1 : ℤ) m) ∧
      (∀ omega, X omega ≤ J omega) ∧
      SubdiffusiveProcess.OGammaLE μ 1 A
        (fun omega => max ((((m : ℤ) - X omega).toNat : ℝ) - 1) 0) := by
  obtain ⟨X, hrange, hdom, hmeas, hog⟩ :=
    exists_stopping_witness_ogammaLE (μ := μ) m J hJ hK hr htail
  exact ⟨X, hrange, hdom,
    ogammaLE_mono_scale zero_lt_one
      (depthGammaOneScaleSharp_pos hK hr) hA hmeas hog⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
