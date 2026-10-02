import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.StoppingWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Section6
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The existing envelope witness, retaining measurability of the index itself. -/
theorem exists_measurable_stopping_witness_ogammaLE
    [IsProbabilityMeasure μ] (m : ℕ) (J : Ω → ℤ)
    (hJ : ∀ omega, J omega ∈ Set.Icc (-1 : ℤ) m)
    {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r)
    (htail : ∀ q : ℕ, 0 < q →
      μ.real {omega | q < ((m : ℤ) - J omega).toNat} ≤
        K * Real.exp (-(r * (q : ℝ)))) :
    ∃ X : Ω → ℤ,
      Measurable X ∧
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
  refine ⟨fun omega => (m : ℤ) - (D omega : ℤ), ?_, ?_, ?_, ?_, ?_⟩
  · exact (measurable_of_countable (fun n : ℕ => (m : ℤ) - (n : ℤ))).comp
      (measurable_envelopedDepth μ m J)
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



theorem exists_measurable_stopping_witness_ogammaLE_of_le
    [IsProbabilityMeasure μ] (m : ℕ) (J : Ω → ℤ)
    (hJ : ∀ omega, J omega ∈ Set.Icc (-1 : ℤ) m)
    {K r A : ℝ} (hK : 1 ≤ K) (hr : 0 < r)
    (hA : depthGammaOneScaleSharp K r ≤ A)
    (htail : ∀ q : ℕ, 0 < q →
      μ.real {omega | q < ((m : ℤ) - J omega).toNat} ≤
        K * Real.exp (-(r * (q : ℝ)))) :
    ∃ X : Ω → ℤ,
      Measurable X ∧
      (∀ omega, X omega ∈ Set.Icc (-1 : ℤ) m) ∧
      (∀ omega, X omega ≤ J omega) ∧
      SubdiffusiveProcess.OGammaLE μ 1 A
        (fun omega => max ((((m : ℤ) - X omega).toNat : ℝ) - 1) 0) := by
  obtain ⟨X, hX, hrange, hdom, hmeas, hog⟩ :=
    exists_measurable_stopping_witness_ogammaLE (μ := μ) m J hJ hK hr htail
  exact ⟨X, hX, hrange, hdom,
    ogammaLE_mono_scale zero_lt_one
      (depthGammaOneScaleSharp_pos hK hr) hA hmeas hog⟩


end
end SubdiffusiveProcess.Section6
