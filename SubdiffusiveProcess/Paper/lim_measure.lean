module

public import SubdiffusiveProcess.Paper.lim_thm_measure
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.Path.ExitTime

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Paper

theorem lim_measure
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ delta0 →
      ∃ Mlim : BilateralField d → Measure (SpatialCoordinates d),
        Measurable Mlim ∧
        -- almost surely: local weak convergence, local finiteness, no atoms, full support and
        -- singularity, for `M` and for the anchored speed measure `μ = e^H M`
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun N => chaosCutoff M N omega) (Mlim omega) ∧
          MeasuresConvergeLocally (fun N => weightedChaosCutoff M H N omega)
            ((Mlim omega).withDensity (fun y => ENNReal.ofReal (Real.exp (H omega y)))) ∧
          IsLocallyFiniteMeasure (Mlim omega) ∧ NoAtoms (Mlim omega) ∧
          (Mlim omega).IsOpenPosMeasure ∧ Mlim omega ⟂ₘ volume ∧
          IsLocallyFiniteMeasure
            ((Mlim omega).withDensity (fun y => ENNReal.ofReal (Real.exp (H omega y)))) ∧
          NoAtoms ((Mlim omega).withDensity (fun y => ENNReal.ofReal (Real.exp (H omega y)))) ∧
          ((Mlim omega).withDensity
            (fun y => ENNReal.ofReal (Real.exp (H omega y)))).IsOpenPosMeasure ∧
          (Mlim omega).withDensity (fun y => ENNReal.ofReal (Real.exp (H omega y))) ⟂ₘ
            volume) ∧
        -- `M` is non-deterministic
        (¬ ∃ m : Measure (SpatialCoordinates d),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, Mlim omega = m) ∧
        -- mean Lebesgue measure: `E[M(dx)] = dx`
        (∀ A : Set (SpatialCoordinates d), MeasurableSet A →
          ∫⁻ omega, Mlim omega A ∂(chaosSampleLaw M).toMeasure = volume A) ∧
        -- stationarity: translation leaves the law of the random measure unchanged
        (∀ y : SpatialCoordinates d,
          (chaosSampleLaw M).toMeasure.map (fun omega => (Mlim omega).map (fun z => z + y)) =
            (chaosSampleLaw M).toMeasure.map Mlim) ∧
        -- independent restrictions to sets at Euclidean distance greater than `√d` (inf distance)
        (∀ A B : Set (SpatialCoordinates d), MeasurableSet A → MeasurableSet B →
          (∃ c : ℝ, (d : ℝ) < c ∧ ∀ a ∈ A, ∀ b ∈ B, c ≤ ∑ i, (a i - b i) ^ 2) →
          Indep (MeasurableSpace.comap (fun omega => (Mlim omega).restrict A) inferInstance)
            (MeasurableSpace.comap (fun omega => (Mlim omega).restrict B) inferInstance)
            (chaosSampleLaw M).toMeasure) := by
  obtain ⟨delta0, hdelta0, hlimit⟩ := lim_thm_measure hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M H hH hM
  obtain ⟨mu0, hmeas, hae, hnonconstant, hmean, hstationary, hindependent, _⟩ :=
    hlimit M hM H hH
  refine ⟨mu0, hmeas, ?_, hnonconstant, hmean, hstationary, hindependent⟩
  filter_upwards [hae] with omega hproperties
  obtain ⟨hconv, hweighted, hfinite, hnoatoms, hpositive, hwfinite, hwnoatoms,
    hwpositive, _, _, _, hsingular, hwsingular⟩ := hproperties
  exact ⟨hconv, hweighted, hfinite, hnoatoms, hpositive, hsingular,
    hwfinite, hwnoatoms, hwpositive, hwsingular⟩

end Paper
