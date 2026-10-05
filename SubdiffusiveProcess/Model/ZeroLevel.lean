module

public import SubdiffusiveProcess.Model.GMCModel
public import SubdiffusiveProcess.Assumptions.Observables
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-!
# Reducing a `GMCModel` to its level-zero law

`SubdiffusiveProcess.Model.GMCModel d` bundles a probability measure on the whole
sequence space `PotentialSample d = ℕ → PotentialField d` together with the five
shell laws.  Four of those five laws only constrain the *level-zero marginal*
`zeroPotentialLaw`, and the fifth (`ShellLawPrefix`) is a purely structural
requirement: the layers are independent and the `k`-th layer is the level-zero
layer scaled triadically.

This file makes that reduction precise.  Given a single probability measure `μ`
on `PotentialField d` satisfying the level-zero requirements
(`SubdiffusiveProcess.Model.ZeroLevelLaw`), the product measure

  `sampleLaw μ = ⨂ₖ (μ.map (triadicScale k))`

is a `GMCModel d`.  So the entire model-existence question is reduced to the
construction of one measure on one potential field.

## Main definitions

* `SubdiffusiveProcess.Model.ZeroLevelBasic` — the ten level-zero clauses that do not mention
  finite-range independence or non-degeneracy of the disorder.
* `SubdiffusiveProcess.Model.ZeroLevelLaw` — `ZeroLevelBasic` plus finite-range independence and
  `0 < τ²`.
* `SubdiffusiveProcess.Model.sampleLaw` — the product model built from a level-zero law.

## Main results

* `SubdiffusiveProcess.Model.nonempty_gmcModel_of_zeroLevelLaw` — a level-zero law yields a
  `GMCModel`.
-/

open MeasureTheory ProbabilityTheory _root_.SubdiffusiveProcess.Model Homogenization

namespace SubdiffusiveProcess.Model

variable {d : ℕ}

/-! ## The triadic tower over a level-zero law -/

@[simp]
theorem triadicScale_zero (g : PotentialField d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale 0 g = g :=
  _root_.SubdiffusiveProcess.Model.PotentialField.ext (fun x => by simp)

/-- The law of the `k`-th layer of the tower built over the level-zero law `μ`. -/
noncomputable def levelLaw (μ : ProbabilityMeasure (PotentialField d)) (k : ℕ) :
    Measure (PotentialField d) :=
  (μ : Measure (PotentialField d)).map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)

instance (μ : ProbabilityMeasure (PotentialField d)) (k : ℕ) :
    IsProbabilityMeasure (levelLaw μ k) :=
  by
    dsimp [levelLaw]
    infer_instance

theorem levelLaw_zero (μ : ProbabilityMeasure (PotentialField d)) :
    levelLaw μ 0 = (μ : Measure (PotentialField d)) := by
  unfold levelLaw
  simp only [funext (triadicScale_zero (d := d))]
  exact Measure.map_id

/-- The sequence measure attached to a level-zero law: the layers are
independent, and the `k`-th layer is the triadic rescaling of the level-zero
layer. -/
noncomputable def sampleLaw (μ : ProbabilityMeasure (PotentialField d)) :
    ProbabilityMeasure (PotentialSample d) :=
  ⟨Measure.infinitePi (levelLaw μ), inferInstance⟩

theorem sampleLaw_toMeasure (μ : ProbabilityMeasure (PotentialField d)) :
    (sampleLaw μ : Measure (PotentialSample d)) = Measure.infinitePi (levelLaw μ) :=
  rfl

theorem marginal_eq (μ : ProbabilityMeasure (PotentialField d)) (k : ℕ) :
    (potentialMarginalLaw (sampleLaw μ) k : Measure (PotentialField d)) = levelLaw μ k := by
  show (sampleLaw μ : Measure (PotentialSample d)).map
      (fun ω : PotentialSample d => ω k) = levelLaw μ k
  exact Measure.infinitePi_map_eval _ k

theorem zeroLaw_eq (μ : ProbabilityMeasure (PotentialField d)) :
    (zeroPotentialLaw (sampleLaw μ) : Measure (PotentialField d))
      = (μ : Measure (PotentialField d)) := by
  rw [zeroPotentialLaw, marginal_eq, levelLaw_zero]

theorem indepFun_sampleLaw (μ : ProbabilityMeasure (PotentialField d)) :
    iIndepFun (fun k : ℕ => fun ω : PotentialSample d => ω k)
      (sampleLaw μ).toMeasure :=
  iIndepFun_infinitePi (fun _ => measurable_id)

/-! ## Separation properties of the potential carrier -/

instance : T1Space (PotentialField d) := by
  refine ⟨fun g => ?_⟩
  have hcont : Continuous (fun (h : PotentialField d) (x : Vec d) => h x) :=
    continuous_pi (fun x => _root_.SubdiffusiveProcess.Model.PotentialField.continuous_eval x)
  have hset : ({g} : Set (PotentialField d))
      = (fun (h : PotentialField d) (x : Vec d) => h x) ⁻¹' {fun x => g x} := by
    ext h
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun hh => by rw [hh], fun hh => _root_.SubdiffusiveProcess.Model.PotentialField.ext (fun x => congrFun hh x)⟩
  rw [hset]
  exact isClosed_singleton.preimage hcont

instance : MeasurableSingletonClass (PotentialField d) :=
  ⟨fun g => (isClosed_singleton (x := g)).measurableSet⟩

/-- Every local σ-algebra is coarser than the carrier σ-algebra. -/
theorem localSigma_le (U : Set (Vec d)) :
    _root_.SubdiffusiveProcess.Model.PotentialField.localSigma U ≤ potentialFieldMeasurableSpace d :=
  le_trans (MeasurableSpace.comap_mono (LocalSigmaR_le U))
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_forgetPotential.comap_le

/-! ## The level-zero requirements -/

/-- The level-zero clauses of a `GMCModel` that constrain neither finite-range
independence nor the non-degeneracy of the disorder. -/
structure ZeroLevelBasic (d : ℕ) (delta : ℝ)
    (μ : ProbabilityMeasure (PotentialField d)) : Prop where
  /-- The dimension is at least two. -/
  dimension : 2 ≤ d
  /-- The disorder range is positive. -/
  delta_pos : 0 < delta
  /-- The disorder range is at most one half. -/
  delta_le_half : delta ≤ (1 : ℝ) / 2
  /-- Pointwise integrability of the level-zero field. -/
  integrable : ∀ x : Vec d,
    Integrable (fun g : PotentialField d => g x) (μ : Measure (PotentialField d))
  /-- The level-zero field has mean zero. -/
  mean_zero : ∀ x : Vec d,
    ∫ g : PotentialField d, g x ∂(μ : Measure (PotentialField d)) = 0
  /-- The level-zero law is translation invariant. -/
  stationary : ∀ z : Vec d,
    Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate z) (μ : Measure (PotentialField d))
      = (μ : Measure (PotentialField d))
  /-- Stretched-exponential control of the unit-cube `C¹ˑ¹` observable. -/
  regularity : SubdiffusiveProcess.OGammaLE (μ : Measure (PotentialField d)) 2 delta
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
  /-- Invariance under signed coordinate permutations. -/
  signed_permutation : ∀ (R : Mat d) (hR : IsSignedPermutationMatrix R),
    Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR) (μ : Measure (PotentialField d))
      = (μ : Measure (PotentialField d))
  /-- Invariance under negation. -/
  negation : Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate (μ : Measure (PotentialField d))
      = (μ : Measure (PotentialField d))
  /-- The exponential of the field at the origin is integrable. -/
  exponential_integrable :
    Integrable (fun g : PotentialField d => Real.exp (g 0))
      (μ : Measure (PotentialField d))

/-- The full set of level-zero requirements: `ZeroLevelBasic`, finite-range
independence, and positive disorder strength. -/
structure ZeroLevelLaw (d : ℕ) (delta : ℝ)
    (μ : ProbabilityMeasure (PotentialField d)) : Prop
    extends ZeroLevelBasic d delta μ where
  /-- Observations at Euclidean distance at least `√d` are independent. -/
  range_dependence : ∀ (U V : Set (Vec d)),
    MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) →
      Indep (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U) (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma V)
        (μ : Measure (PotentialField d))
  /-- The disorder strength is positive. -/
  tauSq_pos :
    0 < Real.log (∫ g : PotentialField d, Real.exp (g 0)
      ∂(μ : Measure (PotentialField d)))

/-! ## The reduction -/

theorem coord_zero_map (μ : ProbabilityMeasure (PotentialField d)) :
    (sampleLaw μ : Measure (PotentialSample d)).map (fun ω : PotentialSample d => ω 0)
      = (μ : Measure (PotentialField d)) := by
  have h := marginal_eq μ 0
  rwa [levelLaw_zero] at h

/-- **The model reduction.**  A single probability measure on `PotentialField d`
satisfying the level-zero requirements determines a full `GMCModel d`. -/
theorem nonempty_gmcModel_of_zeroLevelLaw {delta : ℝ}
    {μ : ProbabilityMeasure (PotentialField d)} (h : ZeroLevelLaw d delta μ) :
    Nonempty (GMCModel d) := by
  classical
  have hzero : (zeroPotentialLaw (sampleLaw μ) : Measure (PotentialField d))
      = (μ : Measure (PotentialField d)) := zeroLaw_eq μ
  have hm : AEMeasurable (fun ω : PotentialSample d => ω 0)
      (sampleLaw μ : Measure (PotentialSample d)) :=
    (measurable_potentialCoordinate 0).aemeasurable
  refine ⟨{ delta := delta, P := sampleLaw μ, shellPrefix := ?_, G1 := ?_, G2 := ?_,
            G3 := ?_, G4 := ?_ }⟩
  · exact
      { dimension := h.dimension
        delta_pos := h.delta_pos
        delta_le_half := h.delta_le_half
        independent := indepFun_sampleLaw μ
        marginal_scaling := by
          intro k
          apply ProbabilityMeasure.toMeasure_injective
          show (potentialMarginalLaw (sampleLaw μ) k : Measure (PotentialField d))
            = (zeroPotentialLaw (sampleLaw μ) : Measure (PotentialField d)).map
                (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
          rw [marginal_eq, hzero, levelLaw] }
  · refine { integrable := ?_, mean_zero := ?_, stationary := ?_, range_dependence := ?_ }
    · intro x
      have hi := integrable_map_measure
        (g := fun g : PotentialField d => g x)
        (by rw [coord_zero_map]; exact (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).aestronglyMeasurable)
        hm
      rw [coord_zero_map] at hi
      exact hi.mp (h.integrable x)
    · intro x
      have hmap := integral_map (μ := (sampleLaw μ : Measure (PotentialSample d)))
        (φ := fun ω : PotentialSample d => ω 0) (f := fun g : PotentialField d => g x)
        hm (by rw [coord_zero_map]; exact (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).aestronglyMeasurable)
      rw [coord_zero_map] at hmap
      rw [← hmap]
      exact h.mean_zero x
    · intro z; rw [hzero]; exact h.stationary z
    · intro U V hU hV hsep; rw [hzero]; exact h.range_dependence U V hU hV hsep
  · exact { regularity_expectation := by rw [hzero]; exact h.regularity }
  · refine { signed_coordinate_permutations := ?_, negation := ?_ }
    · intro R hR
      apply ProbabilityMeasure.toMeasure_injective
      show (zeroPotentialLaw (sampleLaw μ) : Measure (PotentialField d)).map
          (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR) = _
      rw [hzero]; exact h.signed_permutation R hR
    · apply ProbabilityMeasure.toMeasure_injective
      show (zeroPotentialLaw (sampleLaw μ) : Measure (PotentialField d)).map
          _root_.SubdiffusiveProcess.Model.PotentialField.negate = _
      rw [hzero]; exact h.negation
  · refine { exponential_integrable := ?_, tauSq_pos := ?_ }
    · rw [hzero]; exact h.exponential_integrable
    · show 0 < Real.log (∫ g : PotentialField d, Real.exp (g 0)
        ∂(zeroPotentialLaw (sampleLaw μ) : Measure (PotentialField d)))
      rw [hzero]
      exact h.tauSq_pos

end SubdiffusiveProcess.Model
