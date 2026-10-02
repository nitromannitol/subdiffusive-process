import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CoarseResponseMoments




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

private abbrev Sample'' (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-- The centered one-cube response has every moment. -/
theorem memLp_centeredCutoffResponseOnCube [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) {xi : ℝ} (hxi : 1 ≤ xi) :
    MemLp (centeredCutoffResponseOnCube M L n p q R) (ENNReal.ofReal xi)
      M.P.toMeasure := by
  have hbase := memLp_cutoffResponseOnCube M L p q R hxi
  simpa [centeredCutoffResponseOnCube, sub_eq_add_neg] using
    hbase.sub (memLp_const
      (μ := M.P.toMeasure) (p := ENNReal.ofReal xi)
      (∫ eta, cutoffResponseOnCube M L p q (originCube d (n : ℤ)) eta
        ∂M.P.toMeasure))

/-- Integrability of the `xi`-th power of the centered one-cube response. -/
theorem integrable_abs_centeredCutoffResponseOnCube_rpow [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) {xi : ℝ} (hxi : 1 ≤ xi) :
    Integrable
      (fun omega => |centeredCutoffResponseOnCube M L n p q R omega| ^ xi)
      M.P.toMeasure := by
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hmem := memLp_centeredCutoffResponseOnCube M L n p q R hxi
  have := hmem.integrable_norm_rpow
    (by simpa using (ENNReal.ofReal_pos.mpr hxi0).ne') ENNReal.ofReal_ne_top
  simpa [ENNReal.toReal_ofReal hxi0.le, Real.norm_eq_abs] using this

/-- **Step 2.**  The unconditional Rosenthal deviation bound for the centered
response average over the scale-`n` triadic descendants of a scale-`m` cube.

The right-hand root is the `L^xi` norm of the centered one-cube response, which
is finite at every order by §46. -/
theorem centeredCutoffResponseAverage_le_of_moments (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (L n m : ℕ), L ≤ n → n ≤ m →
        ∀ (p q : Vec d) (xi : ℝ), 2 ≤ xi →
        (∫ omega,
            |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
              ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
                centeredCutoffResponseOnCube M L n p q R omega| ^ xi
              ∂M.P.toMeasure) ^ xi⁻¹ ≤
          C * xi *
            ((∫ omega,
              |centeredCutoffResponseOnCube M L n p q
                (originCube d (n : ℤ)) omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹) *
            Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) := by
  obtain ⟨C, hC, hmain⟩ :=
    exists_centeredCutoffResponseAverage_dimensional_bound d
  refine ⟨C, hC, ?_⟩
  intro _ M L n m hLn hnm p q xi hxi
  have hxi1 : (1 : ℝ) ≤ xi := le_trans (by norm_num) hxi
  have hint := integrable_abs_centeredCutoffResponseOnCube_rpow
    M L n p q (originCube d (n : ℤ)) hxi1
  have hK : (0 : ℝ) ≤
      (∫ omega,
        |centeredCutoffResponseOnCube M L n p q
          (originCube d (n : ℤ)) omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ := by
    refine Real.rpow_nonneg ?_ _
    exact integral_nonneg fun omega => Real.rpow_nonneg (abs_nonneg _) _
  exact hmain M L n m hLn hnm p q xi _ hxi hK hint le_rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
