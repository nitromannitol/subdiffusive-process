module

public import SubdiffusiveProcess.Section10.LimitMeasureLawsRestriction
public import SubdiffusiveProcess.Section10.LimitMeasureLawsFieldRange
public import SubdiffusiveProcess.Section10.SeparationOpenNeighborhoods

@[expose] public section

/-! The exact all-Borel restriction-independence component of
`lim:thm-measure` (i), for the same supplied actual chaos limit. -/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess Homogenization

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The SAME actual limiting measure has independent Giry-valued restrictions
to all deterministic Borel sets satisfying the uniform squared-distance
condition. The proof supplies locality and independence from the original
model; neither property is a root premise. -/
theorem same_limit_restrictions_independent {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => chaosCutoff M N w) (mu0 w)) :
    ∀ A B : Set (SpatialCoordinates d), MeasurableSet A → MeasurableSet B →
      (∃ c : ℝ, (d : ℝ) < c ∧ ∀ a ∈ A, ∀ b ∈ B, c ≤ ∑ i, (a i - b i) ^ 2) →
      Indep (MeasurableSpace.comap (fun w => (mu0 w).restrict A) inferInstance)
        (MeasurableSpace.comap (fun w => (mu0 w).restrict B) inferInstance)
        (chaosSampleLaw M).toMeasure := by
  intro A B hA hB hsep
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := open_neighborhoods_of_squared_separation A B hsep
  obtain ⟨F, hF, hFA⟩ := same_limit_borel_restriction_local M mu0 hm hl hc U A hU hA hAU
  obtain ⟨G, hG, hGB⟩ := same_limit_borel_restriction_local M mu0 hm hl hc V B hV hB hBV
  have hfg : IndepFun F G (chaosSampleLaw M).toMeasure := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (fine_spatial_sigma_independent M U V hU hV hUV)
        hF.comap_le) hG.comap_le
  exact (IndepFun_iff_Indep _ _ _).mp (hfg.congr hFA hGB)

/-- The two law components of the source for any supplied same-limit
witness, with exactly its existing measurability/convergence/local-finiteness
properties. Invariance is a separate source application. -/
theorem same_limit_stationary_and_independent {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => chaosCutoff M N w) (mu0 w)) :
    (∀ y : SpatialCoordinates d,
      (chaosSampleLaw M).toMeasure.map (fun w => (mu0 w).map (fun z => z + y)) =
        (chaosSampleLaw M).toMeasure.map mu0) ∧
    (∀ A B : Set (SpatialCoordinates d), MeasurableSet A → MeasurableSet B →
      (∃ c : ℝ, (d : ℝ) < c ∧ ∀ a ∈ A, ∀ b ∈ B, c ≤ ∑ i, (a i - b i) ^ 2) →
      Indep (MeasurableSpace.comap (fun w => (mu0 w).restrict A) inferInstance)
        (MeasurableSpace.comap (fun w => (mu0 w).restrict B) inferInstance)
        (chaosSampleLaw M).toMeasure) :=
  ⟨same_chaos_limit_stationary M mu0 hm hl hc,
    same_limit_restrictions_independent M mu0 hm hl hc⟩

end SubdiffusiveProcess.Section10
