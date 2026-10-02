import SubdiffusiveProcess.Paper.thm_prop_affine_supplier_allchain

open MeasureTheory Filter Set SubdiffusiveProcess
open scoped ENNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Apply the uniform all-chain counting estimate to witnesses at the current model.
No family of auxiliary choices at other models is needed. The exponential rate still
precedes the model, failure events and witnesses. -/
theorem allchain_witness_model
    (d : ℕ) (_hd : 2 ≤ d) (H1 : ℕ) (hH1 : 0 < H1)
    (theta bstar : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < 1) (hbstar : 0 < bstar)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ A : ℝ, 0 < A ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (fail : List (Fin d → Fin (3 ^ H1)) → Set (BilateralField d)),
    (∀ word, MeasurableSet (fail word)) →
    (∀ (word : List (Fin d → Fin (3 ^ H1))), 1 ≤ word.length →
          ∃ W : PNat → Set (BilateralField d),
            (∀ h : PNat,
              MeasurableSet[
                MeasurableSpace.comap
                  (fun omega : BilateralField d =>
                    fun j : Set.Icc
                        (((H1 * word.length : ℕ) : ℤ) - (h : ℤ))
                        (((H1 * word.length : ℕ) : ℤ) + 2 * (h : ℤ)) =>
                      omega (-(j : ℤ)))
                  (inferInstance : MeasurableSpace
                    ((j : Set.Icc
                        (((H1 * word.length : ℕ) : ℤ) - (h : ℤ))
                        (((H1 * word.length : ℕ) : ℤ) + 2 * (h : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]
                (W h)) ∧
            (∀ h : PNat,
              (chaosSampleLaw M).toMeasure (W h) ≤
                ENNReal.ofReal (Real.exp (-(A * (h : ℝ))))) ∧
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              omega ∈ fail word → omega ∈ ⋃ h : PNat, W h)) →
      let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let badCount : (J : ℕ) → (Fin J → (Fin d → Fin (3 ^ H1))) → BilateralField d → ℕ :=
        fun J pi omega =>
          Set.ncard {i : Fin J |
            omega ∈ fail ((List.ofFn pi).take (i.val + 1))}
      (∀ (J : ℕ), 1 ≤ J →
        P {omega |
            ∃ pi : Fin J → (Fin d → Fin (3 ^ H1)),
              theta * (J : ℝ) ≤ (badCount J pi omega : ℝ)} ≤
          ENNReal.ofReal (Real.exp (-(bstar * (J : ℝ))))) ∧
      ∃ B : BilateralField d → ℝ, Measurable B ∧
        (∀ omega, 0 ≤ B omega) ∧
        (∀ᵐ omega ∂P, ∀ (J : ℕ) (pi : Fin J → (Fin d → Fin (3 ^ H1))), 1 ≤ J →
          badCount J pi omega ≤ theta * (J : ℝ) + B omega) ∧
        (∀ t : ℝ, 0 ≤ t →
          P {omega | t < B omega} ≤
            ENNReal.ofReal ((1 - Real.exp (-bstar))⁻¹ *
              Real.exp (-(bstar * t / (1 - theta))))) := by
  obtain ⟨A, hA, hchain⟩ := thm_prop_affine_supplier_allchain d _hd H1 hH1 theta bstar hθ0 hθ1 hbstar
  refine ⟨A, hA, ?_⟩
  intro M fail hmeas hwitness
  classical
  let fail' (M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) := if M' = M then fail else fun _ => ∅
  have hm : ∀ M' word, MeasurableSet (fail' M' word) := by
    intro M' word
    by_cases h : M' = M
    · simpa only [fail', if_pos h] using hmeas word
    · simp only [fail', if_neg h, MeasurableSet.empty]
  have h := hchain fail' hm (max M.delta 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    (by
      intro M' _ word hword
      by_cases h : M' = M
      · subst M'
        simpa only [fail', if_pos rfl] using hwitness word hword
      · refine ⟨fun _ => ∅, fun _ => MeasurableSpace.measurableSet_empty _, ?_, ?_⟩
        · intro i
          simp only [measure_empty]
          exact bot_le
        · exact Filter.Eventually.of_forall fun omega hbad => by
            simpa only [fail', if_neg h, Set.mem_empty_iff_false] using hbad)
    M (le_max_left _ _)
  simpa only [fail', if_pos rfl] using h

end Paper
