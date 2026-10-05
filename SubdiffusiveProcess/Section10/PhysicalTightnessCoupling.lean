module

public import SubdiffusiveProcess.Section10.PhysicalTightnessClocks

@[expose] public section

/-!
# Actual two-branch common-scale coupling consumer

This export assembles the genuine canonical maps, both exact pushforward laws,
and the coefficient, speed and clock identities required when transporting a
physical static certificate into the literal `tight_prop_tightness` families.
The only inputs are the source model, its characterized infrared field, the
source branch choice and the base cutoff. There is no caller environment or
coefficient equality, static estimate or diffusion witness.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport

/-- The literal physical/chaos marginals and all-scale generator normalizations
in one genuine coupling, for either authorized physical family. -/
theorem actual_common_local_coupling {d : ℕ}
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(Vec d, ℝ))
    (hH : InfraredCharacterization M H)
    (Hf : BilateralField d → C(Vec d, ℝ)) (hHf : Hf = H ∨ Hf = fun _ => 0)
    (N : ℕ) :
    ∃ L : WithTop ℕ,
      ((L = ⊤ ∧ Hf = H) ∨ (L = (N : WithTop ℕ) ∧ Hf = fun _ => 0)) ∧
      MeasurePreserving (physicalEnvironment M N 0) (nativeLaw M)
        (anchoredC11SampleLaw M (Section6Anchored.measurableSet_anchoredC11GoodSet d)
          (Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure ∧
      MeasurePreserving bilateralEnvironment (nativeLaw M) (chaosSampleLaw M).toMeasure ∧
      (∀ m : ℕ, relativeClock M L N m =
        (3 : ℝ) ^ (2 * ((m : ℤ) - (N : ℤ))) * ahom M N / ahom M (activeScale L m)) ∧
      ∀ᵐ eta ∂nativeLaw M, ∀ (m : ℕ) (y x : Vec d),
        let omega := physicalEnvironment M N 0 eta
        let xi := bilateralEnvironment eta
        let c := commonLocalFactor M L N m y omega
        0 < c ∧
          cutoffSpeedDensity M Hf xi N (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
            c * localSpeed M L m ((3 : ℝ) ^ N • y) omega x ∧
          cutoffCoefficient M Hf xi N (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
            (c * ahom M (activeScale L m) / ahom M N) *
              localCoefficient M L m ((3 : ℝ) ^ N • y) omega x := by
  rcases hHf with htop | hfinite
  · subst Hf
    refine ⟨⊤, Or.inl ⟨rfl, rfl⟩, physicalEnvironment_preserving M N 0,
      bilateralEnvironment_preserving M, ?_, ?_⟩
    · intro m
      exact relativeClock_eq M ⊤ N m (by simp [activeScale])
    · filter_upwards [top_common_local_dilation M H hH N] with eta heta
      intro m y x
      refine ⟨commonLocalFactor_pos M ⊤ N m y _, ?_⟩
      simpa only [activeScale, WithTop.untopD_top, min_self] using heta m y x
  · subst Hf
    refine ⟨(N : WithTop ℕ), Or.inr ⟨rfl, rfl⟩, physicalEnvironment_preserving M N 0,
      bilateralEnvironment_preserving M, ?_, ?_⟩
    · intro m
      exact relativeClock_eq M (N : WithTop ℕ) N m (by rw [activeScale_coe, min_self])
    · filter_upwards [finite_common_local_dilation M N] with eta heta
      intro m y x
      refine ⟨commonLocalFactor_pos M (N : WithTop ℕ) N m y _, ?_⟩
      simpa only [activeScale_coe] using heta m y x

end SubdiffusiveProcess.Section10.PhysicalTightness
