module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ErrorStoppingAnalytic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.StoppingSplit

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- On a probability law, a real-valued bound is an `ENNReal` bound. -/
theorem measure_le_ofReal_of_measureReal_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (E : Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) {r : ℝ}
    (h : M.P.toMeasure.real E ≤ r) : M.P.toMeasure E ≤ ENNReal.ofReal r := by
  have hne : M.P.toMeasure E ≠ ⊤ := measure_ne_top _ _
  calc M.P.toMeasure E = ENNReal.ofReal (M.P.toMeasure E).toReal :=
        (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal h

/-! ### Depth caps -/

/-- The cutoff-free good-scale stopping depth never exceeds `m + 1`. -/
theorem goodStoppingDepth_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (lambda epsilon s : ℝ) (m : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Section6Stopping.goodStoppingDepth M lambda epsilon s m omega ≤ m + 1 := by
  have hidx := (goodStoppingIndex M none lambda epsilon s m omega).property.1
  unfold Section6Stopping.goodStoppingDepth
  omega

/-- The finite-cutoff good-scale stopping depth never exceeds `m + 1`. -/
theorem cutoffGoodStoppingDepth_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : ℕ) (lambda epsilon s : ℝ) (m : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Section6Stopping.cutoffGoodStoppingDepth M L lambda epsilon s m omega ≤ m + 1 := by
  have hidx := (goodStoppingIndex M (some L) lambda epsilon s m omega).property.1
  unfold Section6Stopping.cutoffGoodStoppingDepth
  omega

/-- Above the cap the good-scale tail event is empty. -/
theorem goodStoppingDepth_tail_eq_empty (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (lambda epsilon s : ℝ) (m q : ℕ) (hq : m + 1 ≤ q) :
    {omega | q < Section6Stopping.goodStoppingDepth M lambda epsilon s m omega} = ∅ := by
  ext omega
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  exact le_trans (goodStoppingDepth_le M lambda epsilon s m omega) hq

/-- Above the cap the finite-cutoff good-scale tail event is empty. -/
theorem cutoffGoodStoppingDepth_tail_eq_empty
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (lambda epsilon s : ℝ)
    (m q : ℕ) (hq : m + 1 ≤ q) :
    {omega | q < Section6Stopping.cutoffGoodStoppingDepth M L lambda epsilon s m omega}
      = ∅ := by
  ext omega
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  exact le_trans (cutoffGoodStoppingDepth_le M L lambda epsilon s m omega) hq

/-! ### The error tails in `ENNReal` form -/

/-- `Section6Stopping.exists_errorStoppingDepth_tail`, in `ENNReal`. -/
theorem exists_errorStoppingDepth_tail_ennreal (d : ℕ) [NeZero d] :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ K⁻¹ →
      ∀ lambda : ℝ,
        Section6Stopping.holderErrorSpatialCoeff d C * M.delta *
            Real.sqrt |Real.log M.delta| ≤ lambda →
        ∀ q m : ℕ, 0 < q →
          M.P.toMeasure {omega |
              q < Section6Stopping.errorStoppingDepth M lambda
                Section6Stopping.holderStoppingS m omega} ≤
            ENNReal.ofReal (Section6Stopping.holderGammaOneGeometricConst * Real.exp
              (-(lambda ^ 2 * max ((q : ℝ) - 1) 0 /
                (Section6Stopping.holderErrorSpatialCoeff d C ^ 2 *
                  M.delta ^ 2 * |Real.log M.delta|)))) := by
  obtain ⟨K, C, hK, hC, hbound⟩ := Section6Stopping.exists_errorStoppingDepth_tail (d := d)
  exact ⟨K, C, hK, hC, fun M hdelta lambda hlambda q m hq =>
    measure_le_ofReal_of_measureReal_le M _ (hbound M hdelta lambda hlambda q m hq)⟩

/-- `Section6Cutoff.exists_cutoffErrorStoppingDepth_tail`, in `ENNReal`. -/
theorem exists_cutoffErrorStoppingDepth_tail_ennreal (d : ℕ) [NeZero d] :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ K⁻¹ →
      ∀ lambda : ℝ,
        Section6Stopping.holderErrorSpatialCoeff d C * M.delta *
            Real.sqrt |Real.log M.delta| ≤ lambda →
        ∀ L q m : ℕ, 0 < q →
          M.P.toMeasure {omega |
              q < Section6Stopping.cutoffErrorStoppingDepth M L lambda
                Section6Stopping.holderStoppingS m omega} ≤
            ENNReal.ofReal (Section6Stopping.holderGammaOneGeometricConst * Real.exp
              (-(lambda ^ 2 * max ((q : ℝ) - 1) 0 /
                (Section6Stopping.holderErrorSpatialCoeff d C ^ 2 *
                  M.delta ^ 2 * |Real.log M.delta|)))) := by
  obtain ⟨K, C, hK, hC, hbound⟩ :=
    Section6Cutoff.exists_cutoffErrorStoppingDepth_tail (d := d)
  exact ⟨K, C, hK, hC, fun M hdelta lambda hlambda L q m hq =>
    measure_le_ofReal_of_measureReal_le M _ (hbound M hdelta lambda hlambda L q m hq)⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
