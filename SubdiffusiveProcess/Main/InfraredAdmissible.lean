import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Analysis.InfraredExpMomentBound
import SubdiffusiveProcess.Analysis.InfraredTruncationBound
import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment

/-!
# Admissible infrared fields

The characterized infrared field `H` and every finite truncation `H_L = ∑_{n ≤ L}` of its layers
(`H_0 = 0`) enjoy the same measurability and the same Gaussian-type compact exponential moment
bound, with a constant independent of the model and of `L`.  `InfraredAdmissible M H` packages the
two cases.  The statistics lemmas of the regularity chain that consume only these two properties
are generalized to it: in place for the non-approved nodes, and as `aux_<id>_adm` siblings next to
the (unchanged) principals of the approved nodes.
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

/-- `H` is an admissible infrared field of the model `M`: the characterized field, or a finite
truncation `H_L` (`L = 0` is `H = 0`). -/
def InfraredAdmissible [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) : Prop :=
  InfraredCharacterization M H ∨ ∃ L : ℕ, H = fun om => infraredPartialSum om L

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem InfraredAdmissible.of_char {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (h : InfraredCharacterization M H) :
    InfraredAdmissible M H :=
  Or.inl h

/-- Coercion: a characterized field is admissible, so generalized statements accept the
characterization at every existing call site unchanged. -/
instance (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ)) :
    Coe (InfraredCharacterization M H) (InfraredAdmissible M H) :=
  ⟨InfraredAdmissible.of_char⟩

theorem InfraredAdmissible.of_trunc (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    InfraredAdmissible M (fun om => infraredPartialSum om L) :=
  Or.inr ⟨L, rfl⟩

theorem InfraredAdmissible.zero (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    InfraredAdmissible M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) := by
  refine Or.inr ⟨0, ?_⟩
  funext om
  simp [infraredPartialSum]

theorem InfraredAdmissible.measurable {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (h : InfraredAdmissible M H) :
    Measurable H := by
  rcases h with h | ⟨L, rfl⟩
  · exact h.1
  · exact (continuous_infraredPartialSum L).measurable

/-- **Uniform compact exponential moment** for every admissible field: one constant `C K`, chosen
before the model and the field, bounds `E exp(λ ‖H|_K‖)` by `2 exp(C_K λ² δ²)` (the characterized
field: `exists_uniform_compactExponentialMoment_of_infraredCharacterization`; the truncations:
`infraredCharacterization_truncation_exp_moment_bound`, uniform in `L`). -/
theorem exists_uniform_compactExponentialMoment_of_admissible (hd : 2 ≤ d) :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ C K) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H →
        ∀ (K : Compacts (SpatialCoordinates d)) (lambda : ℝ), 0 ≤ lambda →
          Integrable (fun omega => Real.exp
            (lambda * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖))
            (chaosSampleLaw M).toMeasure ∧
          (∫ omega, Real.exp
            (lambda * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖)
            ∂(chaosSampleLaw M).toMeasure) ≤
            2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) := by
  obtain ⟨C1, hC1nonneg, hC1⟩ := exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  obtain ⟨C2, hC2nonneg, hC2⟩ := infraredCharacterization_truncation_exp_moment_bound hd
  refine ⟨fun K => max (C1 K) (C2 K), fun K => le_trans (hC1nonneg K) (le_max_left _ _), ?_⟩
  intro M H hH K lambda hlambda
  have hmono : ∀ c : ℝ, c ≤ max (C1 K) (C2 K) →
      2 * Real.exp (c * lambda ^ 2 * M.delta ^ 2) ≤
        2 * Real.exp (max (C1 K) (C2 K) * lambda ^ 2 * M.delta ^ 2) := by
    intro c hc
    gcongr
  rcases hH with hH | ⟨L, rfl⟩
  · have h := hC1 M H hH K lambda hlambda
    exact ⟨h.1, h.2.trans (hmono _ (le_max_left _ _))⟩
  · have h := hC2 M K lambda hlambda L
    exact ⟨h.1, h.2.trans (hmono _ (le_max_right _ _))⟩

end SubdiffusiveProcess
