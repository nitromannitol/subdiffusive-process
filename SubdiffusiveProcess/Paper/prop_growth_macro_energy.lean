import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Frozen.Section6.CutoffHolderRegularity
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
import SubdiffusiveProcess.Lane4.HolderSobolevBridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import Mathlib.Probability.Independence.InfinitePi
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.VecDotForm
import SubdiffusiveProcess.Lane2.LocalRepresentative
import SubdiffusiveProcess.Sobolev.NativeH10
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationTranslation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.EnergyReadout
import SubdiffusiveProcess.MacroAllCube.ResidualShiftFactor
import SubdiffusiveProcess.MacroAllCube.ResidualCoefficient
import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.CellSupMoment
import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Sobolev.BoundaryEnergy
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Paper.coefficient_physical_identity
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.lem_primitive
import SubdiffusiveProcess.Paper.quadratic_inverse_response
import SubdiffusiveProcess.Paper.aux_source_primitive
import SubdiffusiveProcess.Paper.aux_macro_moment_bank

/-!
# Native construction of `in_6_16` — base layer

Auxiliary construction for `prop_growth_macro_energy`. The published input
`in_6_16 d M = PaperSourcedRegularity d M` is constructed here for **every** GMC model from
the axiom-clean native export `SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity` (its intended
upstream provider).  This file holds the non-PDE part: the dimensional constants, the
bilateral-to-potential lift and its law, the prefix witness and its tail, the cutoff
coefficient and the reference average.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

open SubdiffusiveProcess.Frozen.Assumptions

attribute [local instance] Classical.propDecidable

/-! ### 1. Constants -/

/-- The native dimensional constant of `SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity`. -/
def aux_prop_growth_macro_energy_nC (d : ℕ) : ℝ :=
  Classical.choose (SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d)

theorem aux_prop_growth_macro_energy_nC_pos (d : ℕ) : 0 < aux_prop_growth_macro_energy_nC d :=
  (Classical.choose_spec (SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d)).1

/-- The enlarged constant pinned by `PaperSourcedRegularity.C_eq_dimensional`. -/
def aux_prop_growth_macro_energy_C (d : ℕ) : ℝ :=
  ((d : ℝ) + 1) ^ 2 * max 1 (aux_prop_growth_macro_energy_nC d)

theorem aux_prop_growth_macro_energy_one_le_C (d : ℕ) : 1 ≤ aux_prop_growth_macro_energy_C d := by
  unfold aux_prop_growth_macro_energy_C
  have h1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  have h2 : (1 : ℝ) ≤ max 1 (aux_prop_growth_macro_energy_nC d) := le_max_left _ _
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ _ := mul_le_mul h1 h2 zero_le_one (by linarith)

theorem aux_prop_growth_macro_energy_nC_le_C (d : ℕ) :
    aux_prop_growth_macro_energy_nC d ≤ aux_prop_growth_macro_energy_C d := by
  unfold aux_prop_growth_macro_energy_C
  have h1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  calc aux_prop_growth_macro_energy_nC d ≤ max 1 (aux_prop_growth_macro_energy_nC d) :=
        le_max_right _ _
    _ = 1 * max 1 (aux_prop_growth_macro_energy_nC d) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (le_trans zero_le_one (le_max_left _ _))

/-- The native admissibility of `(M, alpha)`. -/
def aux_prop_growth_macro_energy_nativeOK {d : ℕ} (M : GMCModel d) (alpha : ℝ) : Prop :=
  M.delta ≤ (aux_prop_growth_macro_energy_nC d)⁻¹ ∧
    alpha ∈ Set.Icc (1 / 2 : ℝ)
      (1 - aux_prop_growth_macro_energy_nC d * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ))

/-- The MFD admissibility (`M.delta ≤ C⁻¹`, `alpha ∈ alphaRange`) implies the native one. -/
theorem aux_prop_growth_macro_energy_nativeOK_of {d : ℕ} (M : GMCModel d) {alpha : ℝ}
    (hδ : M.delta ≤ (aux_prop_growth_macro_energy_C d)⁻¹)
    (hα : alpha ∈ Set.Icc (1 / 2 : ℝ)
      (1 - aux_prop_growth_macro_energy_C d * M.delta * Real.sqrt |Real.log M.delta|)) :
    aux_prop_growth_macro_energy_nativeOK M alpha := by
  have hn := aux_prop_growth_macro_energy_nC_pos d
  have hnC := aux_prop_growth_macro_energy_nC_le_C d
  have hδ0 : 0 < M.delta := M.shellPrefix.delta_pos
  refine ⟨hδ.trans (inv_anti₀ hn hnC), hα.1, hα.2.trans ?_⟩
  rw [← Real.sqrt_eq_rpow]
  have hs : 0 ≤ M.delta * Real.sqrt |Real.log M.delta| :=
    mul_nonneg hδ0.le (Real.sqrt_nonneg _)
  have : aux_prop_growth_macro_energy_nC d * M.delta * Real.sqrt |Real.log M.delta| ≤
      aux_prop_growth_macro_energy_C d * M.delta * Real.sqrt |Real.log M.delta| := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hnC hs
  linarith

/-! ### 2. The bilateral-to-potential lift (copied from `lem_crossing`, renamed) -/

section Lift

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The underlying continuous function of a potential field. -/
def aux_prop_growth_macro_energy_forget (g : PotentialField d) : C(SpatialCoordinates d, ℝ) :=
  g.1.1

theorem aux_prop_growth_macro_energy_continuous_forget :
    Continuous (aux_prop_growth_macro_energy_forget (d := d)) :=
  continuous_fst.comp continuous_subtype_val

theorem aux_prop_growth_macro_energy_measurable_forget :
    Measurable (aux_prop_growth_macro_energy_forget (d := d)) :=
  aux_prop_growth_macro_energy_continuous_forget.measurable

/-- The zero potential field. -/
def aux_prop_growth_macro_energy_zeroField : PotentialField d := by
  refine ⟨(0, 0), ?_, ?_⟩
  · intro x
    simpa using (hasFDerivAt_const (x := x) (c := (0 : ℝ)))
  · intro K _hK
    exact ⟨0, by simp [LipschitzOnWith]⟩

theorem aux_prop_growth_macro_energy_forget_injective :
    Function.Injective (aux_prop_growth_macro_energy_forget (d := d)) := by
  intro g h hgh
  apply Subtype.ext
  apply Prod.ext hgh
  apply ContinuousMap.ext
  intro x
  have h1 := (g.2.1 x).fderiv
  have h2 := (h.2.1 x).fderiv
  have hfun : (g.1.1 : SpatialCoordinates d → ℝ) = h.1.1 := congrArg DFunLike.coe hgh
  rw [← h1, ← h2, hfun]

theorem aux_prop_growth_macro_energy_measurableEmbedding_forget :
    MeasurableEmbedding (aux_prop_growth_macro_energy_forget (d := d)) :=
  aux_prop_growth_macro_energy_measurable_forget.measurableEmbedding
    aux_prop_growth_macro_energy_forget_injective

theorem aux_prop_growth_macro_energy_exists_unforget :
    ∃ g' : C(SpatialCoordinates d, ℝ) → PotentialField d, Measurable g' ∧
      g' ∘ aux_prop_growth_macro_energy_forget = id :=
  aux_prop_growth_macro_energy_measurableEmbedding_forget.exists_measurable_extend measurable_id
    (fun _ => ⟨aux_prop_growth_macro_energy_zeroField⟩)

/-- A measurable left inverse of `forget`. -/
def aux_prop_growth_macro_energy_unforget : C(SpatialCoordinates d, ℝ) → PotentialField d :=
  Classical.choose (aux_prop_growth_macro_energy_exists_unforget (d := d))

theorem aux_prop_growth_macro_energy_measurable_unforget :
    Measurable (aux_prop_growth_macro_energy_unforget (d := d)) :=
  (Classical.choose_spec (aux_prop_growth_macro_energy_exists_unforget (d := d))).1

theorem aux_prop_growth_macro_energy_unforget_forget (g : PotentialField d) :
    aux_prop_growth_macro_energy_unforget (aux_prop_growth_macro_energy_forget g) = g :=
  congrFun (Classical.choose_spec (aux_prop_growth_macro_energy_exists_unforget (d := d))).2 g

/-- The lift of a bilateral field to a GMC potential sample (layers `k ≥ 0`). -/
def aux_prop_growth_macro_energy_lift (omega : BilateralField d) : PotentialSample d :=
  fun k => aux_prop_growth_macro_energy_unforget (omega (k : ℤ))

theorem aux_prop_growth_macro_energy_measurable_lift :
    Measurable (aux_prop_growth_macro_energy_lift (d := d)) :=
  measurable_pi_iff.mpr fun k =>
    aux_prop_growth_macro_energy_measurable_unforget.comp (measurable_pi_apply (k : ℤ))

theorem aux_prop_growth_macro_energy_layerScaling_forget (k : ℕ) (g : PotentialField d) :
    SubdiffusiveProcess.layerScaling d (k : ℤ) (aux_prop_growth_macro_energy_forget g) =
      aux_prop_growth_macro_energy_forget (PotentialField.triadicScale k g) := by
  apply ContinuousMap.ext
  intro x
  simp only [SubdiffusiveProcess.layerScaling, ContinuousMap.compRightContinuousMap_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, aux_prop_growth_macro_energy_forget]
  change g.1.1 _ = (PotentialField.triadicScale k g) x
  rw [PotentialField.triadicScale_apply, zpow_neg, zpow_natCast]

/-- The lift is measure preserving from the chaos sample law to the GMC sample law. -/
theorem aux_prop_growth_macro_energy_measurePreserving_lift (M : GMCModel d) :
    MeasurePreserving (aux_prop_growth_macro_energy_lift (d := d))
      (SubdiffusiveProcess.chaosSampleLaw M).toMeasure M.P.toMeasure := by
  refine ⟨aux_prop_growth_macro_energy_measurable_lift, ?_⟩
  set ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := SubdiffusiveProcess.chaosRootFieldLaw M
  have hlaw : (SubdiffusiveProcess.chaosSampleLaw M).toMeasure =
      Measure.infinitePi (fun j : ℤ =>
        (SubdiffusiveProcess.scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))) := rfl
  have hind0 := ProbabilityTheory.iIndepFun_infinitePi
    (P := fun j : ℤ => (SubdiffusiveProcess.scaledLayerLaw d ν j :
      Measure C(SpatialCoordinates d, ℝ)))
    (X := fun _ : ℤ => aux_prop_growth_macro_energy_unforget (d := d))
    (fun _ => aux_prop_growth_macro_energy_measurable_unforget)
  have hind : ProbabilityTheory.iIndepFun
      (fun (k : ℕ) (omega : SubdiffusiveProcess.BilateralField d) =>
        aux_prop_growth_macro_energy_unforget (omega (k : ℤ)))
      (SubdiffusiveProcess.chaosSampleLaw M).toMeasure := by
    rw [hlaw]
    exact hind0.precomp (g := fun k : ℕ => (k : ℤ)) (fun a b h => Int.ofNat.inj h)
  have hmarg : ∀ k : ℕ, Measure.map (fun omega : SubdiffusiveProcess.BilateralField d =>
      aux_prop_growth_macro_energy_unforget (omega (k : ℤ)))
        (SubdiffusiveProcess.chaosSampleLaw M).toMeasure =
      (potentialMarginalLaw M.P k : Measure (PotentialField d)) := by
    intro k
    have h1 : (fun omega : SubdiffusiveProcess.BilateralField d =>
        aux_prop_growth_macro_energy_unforget (omega (k : ℤ))) =
        aux_prop_growth_macro_energy_unforget ∘
          (fun omega : SubdiffusiveProcess.BilateralField d => omega (k : ℤ)) :=
      rfl
    rw [h1, ← Measure.map_map aux_prop_growth_macro_energy_measurable_unforget
      (measurable_pi_apply (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ)) (k : ℤ)), hlaw,
      Measure.infinitePi_map_eval]
    rw [M.shellPrefix.marginal_scaling k]
    change Measure.map aux_prop_growth_macro_energy_unforget
      (Measure.map (SubdiffusiveProcess.layerScaling d (k : ℤ))
        (Measure.map aux_prop_growth_macro_energy_forget (zeroPotentialLaw M.P).toMeasure)) =
      Measure.map (PotentialField.triadicScale k) (zeroPotentialLaw M.P).toMeasure
    rw [Measure.map_map (SubdiffusiveProcess.layerScaling d (k : ℤ)).continuous.measurable
        aux_prop_growth_macro_energy_measurable_forget,
      Measure.map_map aux_prop_growth_macro_energy_measurable_unforget
        ((SubdiffusiveProcess.layerScaling d (k : ℤ)).continuous.measurable.comp
          aux_prop_growth_macro_energy_measurable_forget)]
    congr 1
    funext g
    simp only [Function.comp_apply, aux_prop_growth_macro_energy_layerScaling_forget,
      aux_prop_growth_macro_energy_unforget_forget]
  haveI : IsProbabilityMeasure M.P.toMeasure := inferInstance
  have hP := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => measurable_potentialCoordinate k)).mp M.shellPrefix.independent
  have hlift := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => aux_prop_growth_macro_energy_measurable_unforget.comp
      (measurable_pi_apply (k : ℤ)))).mp hind
  change Measure.map (fun (omega : SubdiffusiveProcess.BilateralField d) (k : ℕ) =>
      aux_prop_growth_macro_energy_unforget (omega (k : ℤ)))
    (SubdiffusiveProcess.chaosSampleLaw M).toMeasure = M.P.toMeasure
  have hlift' : Measure.map (fun (omega : SubdiffusiveProcess.BilateralField d) (k : ℕ) =>
      aux_prop_growth_macro_energy_unforget (omega (k : ℤ)))
        (SubdiffusiveProcess.chaosSampleLaw M).toMeasure =
      Measure.infinitePi fun (k : ℕ) =>
        Measure.map (fun omega : SubdiffusiveProcess.BilateralField d =>
          aux_prop_growth_macro_energy_unforget (omega (k : ℤ)))
          (SubdiffusiveProcess.chaosSampleLaw M).toMeasure :=
    hlift
  rw [hlift']
  conv_rhs => rw [show M.P.toMeasure =
    Measure.map (fun (omega : PotentialSample d) (k : ℕ) => omega k) M.P.toMeasure by
    rw [Measure.map_id']]
  rw [hP]
  congr 1
  funext k
  rw [hmarg k]
  rfl

/-- The good set: every nonnegative layer is (the continuous part of) a potential field. -/
def aux_prop_growth_macro_energy_good (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] : Set (BilateralField d) :=
  {om | ∀ k : ℕ, om (k : ℤ) ∈ Set.range (aux_prop_growth_macro_energy_forget (d := d))}

theorem aux_prop_growth_macro_energy_measurableSet_good :
    MeasurableSet (aux_prop_growth_macro_energy_good d) := by
  have hrange : MeasurableSet (Set.range (aux_prop_growth_macro_energy_forget (d := d))) :=
    aux_prop_growth_macro_energy_measurableEmbedding_forget.measurableSet_range
  have : aux_prop_growth_macro_energy_good d =
      ⋂ k : ℕ, (fun om : BilateralField d => om (k : ℤ)) ⁻¹'
        Set.range (aux_prop_growth_macro_energy_forget (d := d)) := by
    ext om
    simp [aux_prop_growth_macro_energy_good]
  rw [this]
  exact MeasurableSet.iInter fun k => (measurable_pi_apply (k : ℤ)) hrange

/-- Almost every chaos sample is good. -/
theorem aux_prop_growth_macro_energy_ae_good (M : GMCModel d) :
    ∀ᵐ om ∂(SubdiffusiveProcess.chaosSampleLaw M).toMeasure,
      om ∈ aux_prop_growth_macro_energy_good d := by
  change ∀ᵐ om ∂(SubdiffusiveProcess.chaosSampleLaw M).toMeasure,
    ∀ k : ℕ, om (k : ℤ) ∈ Set.range (aux_prop_growth_macro_energy_forget (d := d))
  rw [ae_all_iff]
  intro k
  set ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := SubdiffusiveProcess.chaosRootFieldLaw M
  have hrange : MeasurableSet (Set.range (aux_prop_growth_macro_energy_forget (d := d))) :=
    aux_prop_growth_macro_energy_measurableEmbedding_forget.measurableSet_range
  have hmeas : MeasurableSet {omega : SubdiffusiveProcess.BilateralField d |
      omega (k : ℤ) ∈ Set.range (aux_prop_growth_macro_energy_forget (d := d))} :=
    (measurable_pi_apply (k : ℤ)) hrange
  rw [ae_iff, ← Set.compl_setOf]
  rw [prob_compl_eq_zero_iff hmeas]
  change (Measure.infinitePi (fun j : ℤ =>
      (SubdiffusiveProcess.scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))))
    ((fun omega : SubdiffusiveProcess.BilateralField d => omega (k : ℤ)) ⁻¹'
      Set.range aux_prop_growth_macro_energy_forget) = 1
  rw [← Measure.map_apply (measurable_pi_apply (k : ℤ)) hrange, Measure.infinitePi_map_eval]
  change (Measure.map (SubdiffusiveProcess.layerScaling d (k : ℤ))
      (Measure.map aux_prop_growth_macro_energy_forget (zeroPotentialLaw M.P).toMeasure)) _ = 1
  rw [Measure.map_map (SubdiffusiveProcess.layerScaling d (k : ℤ)).continuous.measurable
      aux_prop_growth_macro_energy_measurable_forget,
    Measure.map_apply ((SubdiffusiveProcess.layerScaling d (k : ℤ)).continuous.measurable.comp
      aux_prop_growth_macro_energy_measurable_forget) hrange]
  have : (SubdiffusiveProcess.layerScaling d (k : ℤ) ∘ aux_prop_growth_macro_energy_forget) ⁻¹'
      Set.range aux_prop_growth_macro_energy_forget = Set.univ := by
    ext g
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨_, (aux_prop_growth_macro_energy_layerScaling_forget k g).symm⟩
  rw [this, measure_univ]

/-- On the good set the lift reads the bilateral layers exactly. -/
theorem aux_prop_growth_macro_energy_lift_apply_of_good {om : BilateralField d}
    (hom : om ∈ aux_prop_growth_macro_energy_good d) (k : ℕ) (x : SpatialCoordinates d) :
    (aux_prop_growth_macro_energy_lift om k) x = om (k : ℤ) x := by
  obtain ⟨g, hg⟩ := hom k
  change (aux_prop_growth_macro_energy_unforget (om (k : ℤ))) x = om (k : ℤ) x
  rw [← hg, aux_prop_growth_macro_energy_unforget_forget]
  rfl

end Lift

/-! ### 3. Native witness, prefix and tail -/

section Prefix

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The native translated-centre clause at an admissible `(M, alpha)`. -/
theorem aux_prop_growth_macro_energy_native_y (M : GMCModel d) {alpha : ℝ}
    (h : aux_prop_growth_macro_energy_nativeOK M alpha) (L m : ℕ)
    (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) :
    ∃ Xy : PotentialSample d → ℕ,
      Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
      (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
        (aux_prop_growth_macro_energy_nC d *
          Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - aux_prop_growth_macro_energy_nC d) 0) /
          (aux_prop_growth_macro_energy_nC d * M.delta ^ 2 * |Real.log M.delta|)))) ∧
      ∀ ω, ∀ (u h : Homogenization.H1Function
            (Homogenization.openCubeSet (Homogenization.originCube d m)))
          (g : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → SubdiffusiveProcess.CoarseGrainingVocab.Vec d),
        SubdiffusiveProcess.CoarseGrainingVocab.IsDirichletSolutionOn
            (aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y ω))
            (Homogenization.originCube d m) u h g →
        SubdiffusiveProcess.CoarseGrainingVocab.MemHolder (SubdiffusiveProcess.CoarseGrainingVocab.cube d m) (1 / 2) g →
        SubdiffusiveProcess.CoarseGrainingVocab.MemHolder (SubdiffusiveProcess.CoarseGrainingVocab.cube d m) (1 / 2) h.grad →
        SubdiffusiveProcess.CoarseGrainingVocab.HolderRegularityConclusions M (aux_prop_growth_macro_energy_nC d) L
          (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y ω) alpha m (Xy ω) u h g :=
  (((Classical.choose_spec (SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d)).2 M h.1 alpha h.2
    L m).2.2 y).1

/-- The native prefix witness (constant `1` off the admissible range). -/
def aux_prop_growth_macro_energy_X (M : GMCModel d) (L : ℕ) (alpha : ℝ) (m : ℕ)
    (y : SpatialCoordinates d) : PotentialSample d → ℕ :=
  if h : aux_prop_growth_macro_energy_nativeOK M alpha then
    Classical.choose (aux_prop_growth_macro_energy_native_y M h L m y)
  else fun _ => 1

theorem aux_prop_growth_macro_energy_X_eq (M : GMCModel d) {L : ℕ} {alpha : ℝ} {m : ℕ}
    {y : SpatialCoordinates d} (h : aux_prop_growth_macro_energy_nativeOK M alpha) :
    aux_prop_growth_macro_energy_X M L alpha m y =
      Classical.choose (aux_prop_growth_macro_energy_native_y M h L m y) := by
  unfold aux_prop_growth_macro_energy_X
  rw [dif_pos h]

theorem aux_prop_growth_macro_energy_X_measurable (M : GMCModel d) (L : ℕ) (alpha : ℝ) (m : ℕ)
    (y : SpatialCoordinates d) : Measurable (aux_prop_growth_macro_energy_X M L alpha m y) := by
  by_cases h : aux_prop_growth_macro_energy_nativeOK M alpha
  · rw [aux_prop_growth_macro_energy_X_eq M h]
    exact (Classical.choose_spec (aux_prop_growth_macro_energy_native_y M h L m y)).1
  · unfold aux_prop_growth_macro_energy_X
    rw [dif_neg h]
    exact measurable_const

theorem aux_prop_growth_macro_energy_X_pos (M : GMCModel d) (L : ℕ) (alpha : ℝ) (m : ℕ)
    (y : SpatialCoordinates d) (ω : PotentialSample d) :
    0 < aux_prop_growth_macro_energy_X M L alpha m y ω := by
  by_cases h : aux_prop_growth_macro_energy_nativeOK M alpha
  · rw [aux_prop_growth_macro_energy_X_eq M h]
    exact (Classical.choose_spec (aux_prop_growth_macro_energy_native_y M h L m y)).2.1 ω
  · unfold aux_prop_growth_macro_energy_X
    rw [dif_neg h]
    exact one_pos

/-- The MFD prefix: the native witness at the lifted sample on the good set, and the
vacuous value `m + 1` off it. -/
def aux_prop_growth_macro_energy_prefix (M : GMCModel d) (L : ℕ) (alpha : ℝ) (m : ℕ)
    (y : SpatialCoordinates d) (om : BilateralField d) : ℕ :=
  if om ∈ aux_prop_growth_macro_energy_good d then
    aux_prop_growth_macro_energy_X M L alpha m y (aux_prop_growth_macro_energy_lift om)
  else m + 1

theorem aux_prop_growth_macro_energy_prefix_measurable (M : GMCModel d) (L : ℕ) (alpha : ℝ)
    (m : ℕ) (y : SpatialCoordinates d) :
    Measurable (aux_prop_growth_macro_energy_prefix M L alpha m y) := by
  unfold aux_prop_growth_macro_energy_prefix
  exact Measurable.ite aux_prop_growth_macro_energy_measurableSet_good
    ((aux_prop_growth_macro_energy_X_measurable M L alpha m y).comp
      aux_prop_growth_macro_energy_measurable_lift) measurable_const

theorem aux_prop_growth_macro_energy_prefix_pos (M : GMCModel d) (L : ℕ) (alpha : ℝ) (m : ℕ)
    (y : SpatialCoordinates d) (om : BilateralField d) :
    0 < aux_prop_growth_macro_energy_prefix M L alpha m y om := by
  unfold aux_prop_growth_macro_energy_prefix
  split_ifs
  · exact aux_prop_growth_macro_energy_X_pos M L alpha m y _
  · exact Nat.succ_pos m

/-- Monotonicity of the tail profile in the constant. -/
theorem aux_prop_growth_macro_energy_tail_const_mono {c C A D E k : ℝ} (hc : 0 < c) (hcC : c ≤ C)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    c * Real.exp (-(A * max (k - c) 0) / (c * D * E)) ≤
      C * Real.exp (-(A * max (k - C) 0 / (C * D * E))) := by
  have hC : 0 < C := hc.trans_le hcC
  refine mul_le_mul hcC (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hC.le
  rw [neg_div]
  refine neg_le_neg ?_
  have hB : 0 ≤ D * E := mul_nonneg hD hE
  rw [mul_assoc, mul_assoc]
  rcases hB.lt_or_eq with hB | hB
  · have hm : max (k - C) 0 ≤ max (k - c) 0 := max_le_max (by linarith) le_rfl
    exact div_le_div₀ (mul_nonneg hA (le_max_right _ _)) (mul_le_mul_of_nonneg_left hm hA)
      (mul_pos hc hB) (mul_le_mul_of_nonneg_right hcC hB.le)
  · rw [← hB, mul_zero, mul_zero, div_zero, div_zero]

/-- The tail of the MFD prefix under the chaos sample law (`eq:mfd-L-tail`). -/
theorem aux_prop_growth_macro_energy_prefix_tail (M : GMCModel d) (L : ℕ) (alpha : ℝ)
    (hδ : M.delta ≤ (aux_prop_growth_macro_energy_C d)⁻¹)
    (hα : alpha ∈ Set.Icc (1 / 2 : ℝ)
      (1 - aux_prop_growth_macro_energy_C d * M.delta * Real.sqrt |Real.log M.delta|))
    (m : ℕ) (y : SpatialCoordinates d) (k : ℕ) :
    (chaosSampleLaw M).toMeasure {om | k < aux_prop_growth_macro_energy_prefix M L alpha m y om} ≤
      ENNReal.ofReal (aux_prop_growth_macro_energy_C d *
        Real.exp (-((1 - alpha) ^ 2 * (max ((k : ℝ) - aux_prop_growth_macro_energy_C d) 0) /
          (aux_prop_growth_macro_energy_C d * M.delta ^ 2 * |Real.log M.delta|)))) := by
  have hC1 := aux_prop_growth_macro_energy_one_le_C d
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hmax : max ((0 : ℕ) - aux_prop_growth_macro_energy_C d : ℝ) 0 = 0 := by
      push_cast; exact max_eq_right (by linarith)
    rw [hmax, mul_zero, zero_div, neg_zero, Real.exp_zero, mul_one]
    calc (chaosSampleLaw M).toMeasure _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hC1
  have hOK := aux_prop_growth_macro_energy_nativeOK_of M hδ hα
  have hspec := Classical.choose_spec (aux_prop_growth_macro_energy_native_y M hOK L m y)
  set X := Classical.choose (aux_prop_growth_macro_energy_native_y M hOK L m y) with hXdef
  have hXeq : aux_prop_growth_macro_energy_X M L alpha m y = X :=
    aux_prop_growth_macro_energy_X_eq M hOK
  have hsub : {om | k < aux_prop_growth_macro_energy_prefix M L alpha m y om} ⊆
      (aux_prop_growth_macro_energy_good d)ᶜ ∪
        aux_prop_growth_macro_energy_lift ⁻¹' {ω | k < X ω} := by
    intro om hom
    by_cases hg : om ∈ aux_prop_growth_macro_energy_good d
    · right
      simp only [Set.mem_setOf_eq, aux_prop_growth_macro_energy_prefix, if_pos hg, hXeq] at hom
      exact hom
    · left; exact hg
  have hnull : (chaosSampleLaw M).toMeasure (aux_prop_growth_macro_energy_good d)ᶜ = 0 := by
    have := aux_prop_growth_macro_energy_ae_good M
    rwa [ae_iff] at this
  have hmp := aux_prop_growth_macro_energy_measurePreserving_lift M
  have hXm : MeasurableSet {ω : PotentialSample d | k < X ω} :=
    measurableSet_lt measurable_const hspec.1
  calc (chaosSampleLaw M).toMeasure {om | k < aux_prop_growth_macro_energy_prefix M L alpha m y om}
      ≤ (chaosSampleLaw M).toMeasure ((aux_prop_growth_macro_energy_good d)ᶜ ∪
          aux_prop_growth_macro_energy_lift ⁻¹' {ω | k < X ω}) := measure_mono hsub
    _ ≤ (chaosSampleLaw M).toMeasure (aux_prop_growth_macro_energy_good d)ᶜ +
          (chaosSampleLaw M).toMeasure (aux_prop_growth_macro_energy_lift ⁻¹' {ω | k < X ω}) :=
        measure_union_le _ _
    _ = M.P.toMeasure {ω | k < X ω} := by rw [hnull, zero_add, hmp.measure_preimage hXm.nullMeasurableSet]
    _ ≤ _ := hspec.2.2.1 k hk
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        exact aux_prop_growth_macro_energy_tail_const_mono (aux_prop_growth_macro_energy_nC_pos d)
          (aux_prop_growth_macro_energy_nC_le_C d) (sq_nonneg _) (sq_nonneg _) (abs_nonneg _)

end Prefix

/-! ### 4. Cutoff coefficient and reference average -/

section Coefficient

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]



theorem aux_prop_growth_macro_energy_normalized_coeFn'
    {Ω : Opens (SpatialCoordinates d)} (K : Compacts (SpatialCoordinates d))
    [hΩ : Fact (((Ω : Set (SpatialCoordinates d)) ⊆ K))]
    (a : C(K, ℝ)) (ha : ∀ x, 0 < a x) (a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), ∀ hx : x ∈ Ω,
      (normalizedContinuousPositiveCoefficient (Ω := Ω) K a ha a₀ ha₀).val x =
        a ⟨x, hΩ.out hx⟩ / a₀ := by
  filter_upwards [
    expPotentialCoefficient_coeFn (compactPotentialToLp (Ω := Ω) K
      (continuousPositiveLog a ha - ContinuousMap.const K (Real.log a₀))),
    compactPotentialToLp_on_domain (Ω := Ω) K
      (continuousPositiveLog a ha - ContinuousMap.const K (Real.log a₀))] with x hexp hroot
  intro hx
  unfold normalizedContinuousPositiveCoefficient
  rw [hexp, hroot hx]
  change Real.exp (Real.log (a ⟨x, hΩ.out hx⟩) - Real.log a₀) = _
  rw [Real.exp_sub, Real.exp_log (ha _), Real.exp_log ha₀]

/-- The layer formula of the stationary cutoff coefficient. -/
def aux_prop_growth_macro_energy_cutoffFun (M : GMCModel d) (L : ℕ) (om : BilateralField d)
    (x : SpatialCoordinates d) : ℝ :=
  Real.exp ((∑ j ∈ Finset.range (L + 1), (om (j : ℤ)) x) - (L + 1 : ℝ) * tauSq M.P)

theorem aux_prop_growth_macro_energy_cutoffFun_continuous (M : GMCModel d) (L : ℕ)
    (om : BilateralField d) : Continuous (aux_prop_growth_macro_energy_cutoffFun M L om) := by
  unfold aux_prop_growth_macro_energy_cutoffFun
  exact Real.continuous_exp.comp
    ((continuous_finset_sum _ fun (j : ℕ) _ => (om (j : ℤ)).continuous).sub continuous_const)

/-- The cutoff coefficient as a continuous map on the closed cube. -/
def aux_prop_growth_macro_energy_cutoffCM (M : GMCModel d) (L : ℕ) (om : BilateralField d)
    (y : SpatialCoordinates d) {R : ℝ} (hR : 0 < R) : C(closedCube y R hR, ℝ) :=
  ⟨fun x => aux_prop_growth_macro_energy_cutoffFun M L om (x : SpatialCoordinates d),
    (aux_prop_growth_macro_energy_cutoffFun_continuous M L om).comp continuous_subtype_val⟩

/-- The stationary cutoff coefficient `a_L` on `y + Q_R`. -/
def aux_prop_growth_macro_energy_cutoffOn (M : GMCModel d) (L : ℕ) (om : BilateralField d)
    (y : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) : PositiveCoefficient (centeredCube y R hR) :=
  @normalizedContinuousPositiveCoefficient d (centeredCube y R hR) (closedCube y R hR)
    ⟨centeredCube_subset_closedCube y hR⟩
    (aux_prop_growth_macro_energy_cutoffCM M L om y hR) (fun _ => Real.exp_pos _) 1 one_pos

theorem aux_prop_growth_macro_energy_cutoffOn_eq (M : GMCModel d) (L : ℕ) (om : BilateralField d)
    (y : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    ∀ᵐ x ∂volume.restrict (centeredCube y R hR : Set (SpatialCoordinates d)),
      (aux_prop_growth_macro_energy_cutoffOn M L om y R hR).val x =
        Real.exp ((∑ j ∈ Finset.range (L + 1), (om (j : ℤ)) x) - (L + 1 : ℝ) * tauSq M.P) := by
  letI : Fact (((centeredCube y R hR : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) ⊆
      closedCube y R hR) := ⟨centeredCube_subset_closedCube y hR⟩
  filter_upwards [aux_prop_growth_macro_energy_normalized_coeFn'
      (Ω := centeredCube y R hR) (closedCube y R hR)
      (aux_prop_growth_macro_energy_cutoffCM M L om y hR) (fun _ => Real.exp_pos _) 1 one_pos,
    ae_restrict_mem (centeredCube y R hR).isOpen.measurableSet] with x hx hxΩ
  rw [aux_prop_growth_macro_energy_cutoffOn, hx hxΩ, div_one]
  rfl

/-- The reference integrand `ahom_{min m L} · a_L / a_{min m L}` in layer form. -/
def aux_prop_growth_macro_energy_refFun (M : GMCModel d) (L m : ℕ) (om : BilateralField d)
    (x : SpatialCoordinates d) : ℝ :=
  SubdiffusiveProcess.CoarseGrainingVocab.ahom M (min m L) *
    Real.exp ((∑ j ∈ Finset.range (L + 1), (om (j : ℤ)) x) -
      (∑ j ∈ Finset.range (min m L + 1), (om (j : ℤ)) x) -
      ((L : ℝ) - (min m L : ℝ)) * tauSq M.P)

theorem aux_prop_growth_macro_energy_refFun_continuous (M : GMCModel d) (L m : ℕ)
    (om : BilateralField d) : Continuous (aux_prop_growth_macro_energy_refFun M L m om) := by
  unfold aux_prop_growth_macro_energy_refFun
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  exact ((continuous_finset_sum _ fun (j : ℕ) _ => (om (j : ℤ)).continuous).sub
    (continuous_finset_sum _ fun (j : ℕ) _ => (om (j : ℤ)).continuous)).sub continuous_const

theorem aux_prop_growth_macro_energy_refFun_pos (M : GMCModel d) (L m : ℕ)
    (om : BilateralField d) (x : SpatialCoordinates d) :
    0 < aux_prop_growth_macro_energy_refFun M L m om x :=
  mul_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _) (Real.exp_pos _)

/-- The original reference average `(b_{L,m})_{y + Q_{3^m}}`. -/
def aux_prop_growth_macro_energy_refAvg (M : GMCModel d) (L m : ℕ) (y : SpatialCoordinates d)
    (om : BilateralField d) : ℝ :=
  (volume.real (centeredCube y ((3 : ℝ) ^ m) (pow_pos (by norm_num) m) :
      Set (SpatialCoordinates d)))⁻¹ *
    ∫ x in (centeredCube y ((3 : ℝ) ^ m) (pow_pos (by norm_num) m) : Set (SpatialCoordinates d)),
      aux_prop_growth_macro_energy_refFun M L m om x

theorem aux_prop_growth_macro_energy_setIntegral_pos_of_continuous {f : SpatialCoordinates d → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) (y : SpatialCoordinates d) {R : ℝ} (hR : 0 < R) :
    0 < ∫ x in (centeredCube y R hR : Set (SpatialCoordinates d)), f x := by
  have hint : IntegrableOn f (centeredCube y R hR : Set (SpatialCoordinates d)) :=
    (hf.continuousOn.integrableOn_compact (closedCube y R hR).isCompact).mono_set
      (centeredCube_subset_closedCube y hR)
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (hpos x).le) hint]
  have hsupp : Function.support f = Set.univ :=
    Set.eq_univ_of_forall fun x => (hpos x).ne'
  rw [hsupp, Set.univ_inter]
  exact (centeredCube y R hR).isOpen.measure_pos volume ⟨y, Metric.mem_ball_self (by linarith)⟩

theorem aux_prop_growth_macro_energy_refAvg_pos (M : GMCModel d) (L m : ℕ)
    (y : SpatialCoordinates d) (om : BilateralField d) :
    0 < aux_prop_growth_macro_energy_refAvg M L m y om := by
  unfold aux_prop_growth_macro_energy_refAvg
  refine mul_pos (inv_pos.2 ?_) (aux_prop_growth_macro_energy_setIntegral_pos_of_continuous
    (aux_prop_growth_macro_energy_refFun_continuous M L m om)
    (aux_prop_growth_macro_energy_refFun_pos M L m om) y _)
  rw [centeredCube_volume_real]
  positivity

end Coefficient

end Paper




open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (cube truncatedCube translatedCube MemHolder holderSeminormOn
  IsDirichletSolutionOn IsDivFormWeakSolutionOn HasZeroTraceDifferenceOn)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### 1. Cube geometry -/

/-- The native integer-scale origin cube is the sup-norm ball of radius `3^k/2`. -/
theorem aux_prop_growth_macro_energy_cube_eq_ball (k : ℤ) :
    (cube d k : Set (SpatialCoordinates d)) = Metric.ball (0 : SpatialCoordinates d) ((3 : ℝ) ^ k / 2) := by
  unfold cube
  rw [← SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube (d := d) k
    (by positivity)]
  rfl

theorem aux_prop_growth_macro_energy_mem_cube_iff (k : ℤ) (x : SpatialCoordinates d) :
    x ∈ cube d k ↔ ‖x‖ < (3 : ℝ) ^ k / 2 := by
  rw [aux_prop_growth_macro_energy_cube_eq_ball, Metric.mem_ball, dist_zero_right]

/-- A translated native cube is the sup-norm ball about its centre. -/
theorem aux_prop_growth_macro_energy_translatedCube_eq_ball (k : ℤ) (x : SpatialCoordinates d) :
    (translatedCube d k x : Set (SpatialCoordinates d)) = Metric.ball x ((3 : ℝ) ^ k / 2) := by
  ext w
  unfold translatedCube
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [aux_prop_growth_macro_energy_mem_cube_iff] at hv
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hv
  · intro hw
    refine ⟨w - x, ?_, add_sub_cancel x w⟩
    rw [aux_prop_growth_macro_energy_mem_cube_iff]
    rw [Metric.mem_ball, dist_eq_norm] at hw
    exact hw

/-- Membership in a centred cube, read at the translated point. -/
theorem aux_prop_growth_macro_energy_mem_centeredCube_iff_sub (y x : SpatialCoordinates d) (k : ℤ) :
    x ∈ (centeredCube y ((3 : ℝ) ^ k) (by positivity) : Set (SpatialCoordinates d)) ↔
      x - y ∈ cube d k := by
  rw [aux_prop_growth_macro_energy_mem_cube_iff]
  change dist x y < (3 : ℝ) ^ k / 2 ↔ _
  rw [dist_eq_norm]

theorem aux_prop_growth_macro_energy_mem_centeredCube_nat_iff_sub (y x : SpatialCoordinates d) (m : ℕ)
    (hR : (0 : ℝ) < 3 ^ m) :
    x ∈ (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) ↔ x - y ∈ cube d (m : ℤ) := by
  rw [aux_prop_growth_macro_energy_mem_cube_iff]
  change dist x y < (3 : ℝ) ^ m / 2 ↔ _
  rw [dist_eq_norm, zpow_natCast]

/-- The translated truncated window is the MFD ball–root intersection. -/
theorem aux_prop_growth_macro_energy_translateSet_truncatedCube (m : ℕ) (k : ℤ)
    (y x : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m) :
    Homogenization.translateSet y (truncatedCube d m k (x - y)) =
      Metric.ball x ((3 : ℝ) ^ k / 2) ∩
        (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) := by
  ext w
  rw [Homogenization.mem_translateSet_iff_sub_mem]
  unfold truncatedCube
  rw [Set.mem_inter_iff, Set.mem_inter_iff, aux_prop_growth_macro_energy_translatedCube_eq_ball,
    aux_prop_growth_macro_energy_mem_centeredCube_nat_iff_sub y w m hR, Metric.mem_ball,
    Metric.mem_ball, dist_eq_norm, dist_eq_norm]
  have : w - y - (x - y) = w - x := sub_sub_sub_cancel_right w x y
  rw [this]

theorem aux_prop_growth_macro_energy_truncatedCube_subset (m : ℕ) (k : ℤ) (x : SpatialCoordinates d) :
    truncatedCube d m k x ⊆ cube d (m : ℤ) :=
  Set.inter_subset_right

theorem aux_prop_growth_macro_energy_measurableSet_cube (k : ℤ) :
    MeasurableSet (cube d k : Set (SpatialCoordinates d)) := by
  rw [aux_prop_growth_macro_energy_cube_eq_ball]
  exact measurableSet_ball

theorem aux_prop_growth_macro_energy_measurableSet_truncatedCube (m : ℕ) (k : ℤ) (x : SpatialCoordinates d) :
    MeasurableSet (truncatedCube d m k x) := by
  unfold truncatedCube
  rw [aux_prop_growth_macro_energy_translatedCube_eq_ball]
  exact measurableSet_ball.inter (aux_prop_growth_macro_energy_measurableSet_cube _)

/-- The root is the translate of the origin chart. -/
theorem aux_prop_growth_macro_energy_root_eq_translateSet (m : ℕ) (y : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m) :
    (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) =
      Homogenization.translateSet y (Homogenization.openCubeSet (Homogenization.originCube d m)) :=
  SubdiffusiveProcess.Lane4.centeredCube_eq_translateSet_cube m y hR

/-! ### 2. A.e. transport along the translation -/

/-- Pull an a.e. statement on `y + U` back to `U` along `x ↦ x + y`. -/
theorem aux_prop_growth_macro_energy_ae_pull_translate (y : SpatialCoordinates d)
    (U : Set (SpatialCoordinates d)) {p : SpatialCoordinates d → Prop}
    (h : ∀ᵐ w ∂volume.restrict (Homogenization.translateSet y U), p w) :
    ∀ᵐ x ∂volume.restrict U, p (x + y) :=
  (Homogenization.measurePreserving_addRight_restrict_translateSet (d := d) y U).quasiMeasurePreserving.ae h

/-! ### 3. Coordinatewise Hölder guards give the vector Hölder class -/

theorem aux_prop_growth_macro_energy_euclideanNorm_eq (v : SpatialCoordinates d) :
    Homogenization.euclideanNorm v = Real.sqrt (∑ i : Fin d, (v i) ^ 2) :=
  SubdiffusiveProcess.Lane4.euclideanNorm_eq_sqrt_sum_sq v

/-- A coordinatewise `C^{1/2}` bound on `S` gives a vector `C^{1/2}` bound on `S`. -/
theorem aux_prop_growth_macro_energy_holder_vector_bound {S : Set (SpatialCoordinates d)}
    (g : SpatialCoordinates d → Fin d → ℝ)
    (hg : ∀ i : Fin d, IsHolderOn (1 / 2) S (fun x => g x i)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ S, ∀ w ∈ S,
      Homogenization.euclideanNorm (g x - g w) ≤ K * Homogenization.euclideanNorm (x - w) ^ (1 / 2 : ℝ) := by
  choose K hK using fun i => hg i
  refine ⟨Real.sqrt d * ∑ i, max (K i) 0, mul_nonneg (Real.sqrt_nonneg _)
    (Finset.sum_nonneg fun i _ => le_max_right _ _), ?_⟩
  intro x hx w hw
  by_cases hxw : x = w
  · subst hxw
    simp only [sub_self]
    rw [aux_prop_growth_macro_energy_euclideanNorm_eq]
    simp only [Pi.zero_apply]
    norm_num
  set D : ℝ := Homogenization.euclideanNorm (x - w) ^ (1 / 2 : ℝ) with hD
  have hdist : Homogenization.euclideanNorm (x - w) = Real.sqrt (∑ j : Fin d, (x j - w j) ^ 2) := by
    rw [aux_prop_growth_macro_energy_euclideanNorm_eq]; rfl
  have hpos : 0 < Real.sqrt (∑ j : Fin d, (x j - w j) ^ 2) := by
    rw [← hdist]
    rw [aux_prop_growth_macro_energy_euclideanNorm_eq]
    apply Real.sqrt_pos.2
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ w j := by
      by_contra hcon
      push_neg at hcon
      exact hxw (funext hcon)
    have hj2 : 0 < (x j - w j) ^ 2 := by
      have : x j - w j ≠ 0 := sub_ne_zero.2 hj
      positivity
    calc (0 : ℝ) < (x j - w j) ^ 2 := hj2
      _ ≤ ∑ i : Fin d, ((x - w) i) ^ 2 := by
        simp only [Pi.sub_apply]
        exact Finset.single_le_sum (f := fun i => (x i - w i) ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ j)
  have hDpos : 0 < D := by
    rw [hD, hdist]; exact Real.rpow_pos_of_pos hpos _
  have hcoord : ∀ i : Fin d, |g x i - g w i| ≤ max (K i) 0 * D := by
    intro i
    have hmem : |g x i - g w i| / (Real.sqrt (∑ j : Fin d, (x j - w j) ^ 2)) ^ (1 / 2 : ℝ) ∈
        holderRatioSet (1 / 2) S (fun x => g x i) := ⟨x, hx, w, hw, hxw, rfl⟩
    have h1 := hK i hmem
    rw [← hdist, ← hD, div_le_iff₀ hDpos] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hDpos.le)
  have hsum : ∑ i : Fin d, ((g x - g w) i) ^ 2 ≤ (d : ℝ) * ((∑ i, max (K i) 0) * D) ^ 2 := by
    have hle : ∀ i : Fin d, ((g x - g w) i) ^ 2 ≤ ((∑ i, max (K i) 0) * D) ^ 2 := by
      intro i
      have hKi : max (K i) 0 ≤ ∑ i, max (K i) 0 :=
        Finset.single_le_sum (f := fun i => max (K i) 0) (fun i _ => le_max_right _ _)
          (Finset.mem_univ i)
      have h2 : |(g x - g w) i| ≤ (∑ i, max (K i) 0) * D :=
        (hcoord i).trans (mul_le_mul_of_nonneg_right hKi hDpos.le)
      calc ((g x - g w) i) ^ 2 = |(g x - g w) i| ^ 2 := (sq_abs _).symm
        _ ≤ ((∑ i, max (K i) 0) * D) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    calc ∑ i : Fin d, ((g x - g w) i) ^ 2 ≤ ∑ _i : Fin d, ((∑ i, max (K i) 0) * D) ^ 2 :=
          Finset.sum_le_sum fun i _ => hle i
      _ = (d : ℝ) * ((∑ i, max (K i) 0) * D) ^ 2 := by simp
  rw [aux_prop_growth_macro_energy_euclideanNorm_eq]
  have hKD : 0 ≤ (∑ i, max (K i) 0) * D :=
    mul_nonneg (Finset.sum_nonneg fun i _ => le_max_right _ _) hDpos.le
  calc Real.sqrt (∑ i : Fin d, ((g x - g w) i) ^ 2)
      ≤ Real.sqrt ((d : ℝ) * ((∑ i, max (K i) 0) * D) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * ((∑ i, max (K i) 0) * D) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hKD]
    _ = Real.sqrt d * (∑ i, max (K i) 0) * D := by ring

/-- The native vector Hölder class on the origin chart, from MFD coordinatewise guards on the
closed root. -/
theorem aux_prop_growth_macro_energy_memHolder_translate (m : ℕ) (y : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m) (g : SpatialCoordinates d → Fin d → ℝ)
    (hg : ∀ i : Fin d, IsHolderOn (1 / 2)
      (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => g x i)) :
    MemHolder (cube d (m : ℤ)) (1 / 2) (fun x => g (x + y)) := by
  obtain ⟨K, hK, hb⟩ := aux_prop_growth_macro_energy_holder_vector_bound g hg
  have hmem : MemHolder (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g :=
    ⟨K, hK, fun x hx w hw => hb x (centeredCube_subset_closedCube y hR hx) w
      (centeredCube_subset_closedCube y hR hw)⟩
  exact SubdiffusiveProcess.Lane4.folded_source_memHolder m y hR g hmem

end Paper

/-!
# Native construction of `in_6_16` — the Dirichlet package

An MFD weak Dirichlet problem on the root `y + Q_{3^m}` (weak equation against the killed
graph, datum difference in the killed graph, datum-gradient representative `gh`) becomes the
native `IsDirichletSolutionOn` on the origin chart `□_m`, with the native datum gradient equal
**everywhere** to the translated representative `gh`.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (cube truncatedCube translatedCube MemHolder holderSeminormOn
  IsDirichletSolutionOn IsDivFormWeakSolutionOn HasZeroTraceDifferenceOn)

variable {d : ℕ}

/-- A native `H¹` carrier of a weak Sobolev datum, with a prescribed everywhere-defined
gradient representative. -/
theorem aux_prop_growth_macro_energy_nativeH1_of_weak_grad {Ω : Opens (SpatialCoordinates d)}
    (h : weakSobolevGraph Ω) (gh : SpatialCoordinates d → Fin d → ℝ)
    (hgh : ∀ i : Fin d, (((h : SobolevData Ω).2 i : DomainL2 Ω) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => gh x i) :
    ∃ v : Homogenization.H1Function (Ω : Set (SpatialCoordinates d)),
      v.toFun = (fun x => (h : SobolevData Ω).1 x) ∧ v.grad = gh := by
  have hweak : Homogenization.HasWeakGradientOn (Ω : Set (SpatialCoordinates d))
      (fun x => (h : SobolevData Ω).1 x) (fun x i => (h : SobolevData Ω).2 i x) :=
    (mem_weakSobolevGraph_iff_hasWeakGradientOn (h : SobolevData Ω)).mp h.property
  exact ⟨{ toFun := fun x => (h : SobolevData Ω).1 x
           grad := gh
           memL2 := Lp.memLp _
           gradMemL2 := fun i => (Lp.memLp ((h : SobolevData Ω).2 i)).ae_eq (hgh i)
           hasWeakGradient := fun i =>
             SubdiffusiveProcess.Lane4.hasWeakPartialDerivOn_congr_ae
               Filter.EventuallyEq.rfl (hgh i) (hweak i) }, rfl, rfl⟩

/-- The divergence-form weak equation only sees the solution gradient a.e. -/
theorem aux_prop_growth_macro_energy_isDivForm_congr_grad {W : Set (SpatialCoordinates d)}
    {a : SpatialCoordinates d → ℝ} {u u2 : Homogenization.H1Function W}
    {g : SpatialCoordinates d → SpatialCoordinates d}
    (hgrad : ∀ᵐ x ∂volume.restrict W, u.grad x = u2.grad x)
    (h : IsDivFormWeakSolutionOn a W u g) : IsDivFormWeakSolutionOn a W u2 g := by
  intro φ
  rw [← h φ]
  refine integral_congr_ae ?_
  filter_upwards [hgrad] with x hx
  rw [hx]

/-- Copy of `aux_prop_folded_iteration_inner_eq`: the source pairing `⟪hgrad, ∇φ⟫` is the
literal integral `∫ g·∇φ` against the Sobolev data of a native `H¹₀` test. -/
theorem aux_prop_growth_macro_energy_inner_eq {Ω : Opens (SpatialCoordinates d)}
    (hgrad : HilbertGradient Ω) (g : SpatialCoordinates d → Fin d → ℝ)
    (hg : ∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => g x i)
    (φ : Homogenization.H10Function (Ω : Set (SpatialCoordinates d))) :
    inner ℝ hgrad (sobolevGradient (sobolevDataOfH1 φ.toH1Function)) =
      ∫ x in (Ω : Set (SpatialCoordinates d)),
        Homogenization.vecDot (g x) (φ.toH1Function.grad x) := by
  rw [PiLp.inner_apply]
  have hterm : ∀ i : Fin d,
      inner ℝ (hgrad i) ((sobolevGradient (sobolevDataOfH1 φ.toH1Function)) i) =
        ∫ x in (Ω : Set (SpatialCoordinates d)), g x i * φ.toH1Function.grad x i := by
    intro i
    change inner ℝ (hgrad i) ((sobolevDataOfH1 φ.toH1Function).2 i) = _
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg i, sobolevDataOfH1_snd_coeFn φ.toH1Function i] with x hx1 hx2
    rw [RCLike.inner_apply, conj_trivial, hx1, hx2]
    ring
  simp only [hterm]
  rw [← integral_finset_sum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Homogenization.vecDot]
  · intro i _
    have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hgrad i)
      ((sobolevDataOfH1 φ.toH1Function).2 i)
    refine hint.congr ?_
    filter_upwards [hg i, sobolevDataOfH1_snd_coeFn φ.toH1Function i] with x hx1 hx2
    rw [RCLike.inner_apply, conj_trivial, hx1, hx2]
    ring

/-- The MFD Dirichlet problem on a domain, as native carriers on the same domain. -/
theorem aux_prop_growth_macro_energy_root_package {Ω : Opens (SpatialCoordinates d)}
    (aC : PositiveCoefficient Ω)
    (g : SpatialCoordinates d → Fin d → ℝ) (hgrad : HilbertGradient Ω)
    (hgi : ∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => g x i)
    (h u : weakSobolevGraph Ω) (gh : SpatialCoordinates d → Fin d → ℝ)
    (hghi : ∀ i : Fin d, (sobolevGradient (h : SobolevData Ω) i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => gh x i)
    (hweak : ∀ φ : killedSobolevGraph Ω,
      sobolevCoefficientForm aC (u : SobolevData Ω) (φ : SobolevData Ω) =
        -inner ℝ hgrad (subspaceGradient (killedSobolevGraph Ω) φ))
    (htr : (u : SobolevData Ω) - (h : SobolevData Ω) ∈ killedSobolevGraph Ω) :
    ∃ u'' h'' : Homogenization.H1Function (Ω : Set (SpatialCoordinates d)),
      HasZeroTraceDifferenceOn (Ω : Set (SpatialCoordinates d)) u'' h'' ∧
      IsDivFormWeakSolutionOn aC.val (Ω : Set (SpatialCoordinates d)) u'' g ∧
      h''.grad = gh ∧
      (u''.toFun =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => (u : SobolevData Ω).1 x) ∧
      (∀ i : Fin d, (fun x => u''.grad x i) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => (u : SobolevData Ω).2 i x) := by
  obtain ⟨h'', hh1, hh2⟩ := aux_prop_growth_macro_energy_nativeH1_of_weak_grad h gh hghi
  obtain ⟨w, hw1, hw2⟩ := exists_nativeH10Function_of_killedSobolevGraph
    (⟨(u : SobolevData Ω) - (h : SobolevData Ω), htr⟩ : killedSobolevGraph Ω)
  let u'' : Homogenization.H1Function (Ω : Set (SpatialCoordinates d)) := h'' + w.toH1Function
  have hu''fun : ∀ x, u''.toFun x = h''.toFun x + w.toH1Function.toFun x := fun x => rfl
  have hu''grad : ∀ x, u''.grad x = h''.grad x + w.toH1Function.grad x := fun x => rfl
  -- a.e. identities
  have hsub1 := Lp.coeFn_sub ((u : SobolevData Ω).1) ((h : SobolevData Ω).1)
  have hfun : u''.toFun =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      fun x => (u : SobolevData Ω).1 x := by
    filter_upwards [hsub1] with x hx
    rw [hu''fun, hh1]
    have hwx : w.toH1Function.toFun x =
        (((u : SobolevData Ω) - (h : SobolevData Ω)).1 : SpatialCoordinates d → ℝ) x :=
      congrFun hw1 x
    rw [hwx]
    change (h : SobolevData Ω).1 x + ((u : SobolevData Ω).1 - (h : SobolevData Ω).1 : DomainL2 Ω) x = _
    rw [hx, Pi.sub_apply]
    ring
  have hgradc : ∀ i : Fin d, (fun x => u''.grad x i)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => (u : SobolevData Ω).2 i x := by
    intro i
    have hsub2 := Lp.coeFn_sub ((u : SobolevData Ω).2 i) ((h : SobolevData Ω).2 i)
    filter_upwards [hsub2, hghi i] with x hx hgx
    rw [hu''grad, hh2]
    have hwx : w.toH1Function.grad x i =
        (((u : SobolevData Ω) - (h : SobolevData Ω)).2 i : SpatialCoordinates d → ℝ) x :=
      congrFun (congrFun hw2 x) i
    change gh x i + w.toH1Function.grad x i = _
    rw [hwx]
    change gh x i + ((u : SobolevData Ω).2 i - (h : SobolevData Ω).2 i : DomainL2 Ω) x = _
    rw [hx, Pi.sub_apply]
    change gh x i + (((u : SobolevData Ω).2 i x) - (sobolevGradient (h : SobolevData Ω) i) x) = _
    rw [hgx]
    ring
  -- the weak equation for the exact-representative carrier of `u`
  obtain ⟨v, hv1, hv2⟩ := exists_nativeH1Function_of_weakSobolevGraph u
  have hsd : sobolevDataOfH1 v = (u : SobolevData Ω) := by
    refine Prod.ext ?_ ?_
    · refine Lp.ext ((sobolevDataOfH1_fst_coeFn v).trans ?_)
      exact Filter.EventuallyEq.of_eq (by rw [show v.toFun = _ from hv1])
    · funext i
      refine Lp.ext ((sobolevDataOfH1_snd_coeFn v i).trans ?_)
      exact Filter.EventuallyEq.of_eq (by rw [hv2])
  have hwv : IsDivFormWeakSolutionOn (aC.val : SpatialCoordinates d → ℝ)
      (Ω : Set (SpatialCoordinates d)) v g := by
    refine isDivFormWeakSolutionOn_of_weak_equation aC v g ?_ ?_
    · intro w' i
      have h' := integrable_weighted_coordinates aC.val
        (sobolevGradient (sobolevDataOfH1 v)) (sobolevGradient (sobolevDataOfH1 w')) i
      refine h'.congr ?_
      filter_upwards [sobolevDataOfH1_snd_coeFn v i, sobolevDataOfH1_snd_coeFn w' i]
        with x hx1 hx2
      change aC.val x * ((sobolevDataOfH1 v).2 i x * (sobolevDataOfH1 w').2 i x) = _
      rw [hx1, hx2]
    · intro φ
      have h' := hweak ⟨sobolevDataOfH1 φ.toH1Function, sobolevDataOfH1_mem_killed φ⟩
      rw [hsd, h']
      congr 1
      exact aux_prop_growth_macro_energy_inner_eq hgrad g hgi φ
  have hvgrad : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), v.grad x = u''.grad x := by
    have hall : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
        ∀ i : Fin d, u''.grad x i = (u : SobolevData Ω).2 i x := by
      rw [ae_all_iff]; exact hgradc
    filter_upwards [hall] with x hx
    funext i
    rw [hx i, hv2]
  exact ⟨u'', h'', ⟨w, hu''fun, hu''grad⟩,
    aux_prop_growth_macro_energy_isDivForm_congr_grad hvgrad hwv, hh2, hfun, hgradc⟩

end Paper

/-!
# Native construction of `in_6_16` — the Dirichlet package on the origin chart
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (cube truncatedCube translatedCube MemHolder holderSeminormOn
  IsDirichletSolutionOn IsDivFormWeakSolutionOn HasZeroTraceDifferenceOn)

variable {d : ℕ}

/-- Pull an a.e. statement on a set equal to `U + y` back to `U`. -/
theorem aux_prop_growth_macro_energy_ae_pull_translate' (y : SpatialCoordinates d)
    (U V : Set (SpatialCoordinates d)) (hV : V = Homogenization.translateSet y U)
    {p : SpatialCoordinates d → Prop} (h : ∀ᵐ w ∂volume.restrict V, p w) :
    ∀ᵐ x ∂volume.restrict U, p (x + y) := by
  subst hV
  exact aux_prop_growth_macro_energy_ae_pull_translate y U h

/-- Untranslating a native Dirichlet problem on `U + z` to `U`. -/
theorem aux_prop_growth_macro_energy_untranslate_package {U V : Set (SpatialCoordinates d)}
    (z : SpatialCoordinates d) (hV : V = Homogenization.translateSet z U)
    {a : SpatialCoordinates d → ℝ} {g : SpatialCoordinates d → SpatialCoordinates d}
    (u h : Homogenization.H1Function V) (hz : HasZeroTraceDifferenceOn V u h)
    (hs : IsDivFormWeakSolutionOn a V u g) :
    ∃ u' h' : Homogenization.H1Function U,
      (∀ x, u'.toFun x = u.toFun (x + z)) ∧ (∀ x, u'.grad x = u.grad (x + z)) ∧
      (∀ x, h'.grad x = h.grad (x + z)) ∧
      HasZeroTraceDifferenceOn U u' h' ∧
      IsDivFormWeakSolutionOn (fun x => a (x + z)) U u' (fun x => g (x + z)) := by
  subst hV
  obtain ⟨w, hw1, hw2⟩ := hz
  refine ⟨Homogenization.H1Function.untranslate z u, Homogenization.H1Function.untranslate z h,
    fun x => rfl, fun x => rfl, fun x => rfl,
    ⟨Homogenization.H10Function.untranslate z w, fun x => ?_, fun x => ?_⟩,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.isDivFormWeakSolutionOn_untranslate z hs⟩
  · rw [Homogenization.H10Function.untranslate_toH1Function,
      Homogenization.H1Function.untranslate_toFun, Homogenization.H1Function.untranslate_toFun,
      Homogenization.H1Function.untranslate_toFun]
    exact hw1 (x + z)
  · rw [Homogenization.H10Function.untranslate_toH1Function,
      Homogenization.H1Function.untranslate_grad, Homogenization.H1Function.untranslate_grad,
      Homogenization.H1Function.untranslate_grad]
    exact hw2 (x + z)

/-- **The native Dirichlet package on the origin chart `□_m`.**  From the MFD Dirichlet
problem on the root `y + Q_{3^m}`, for any global representative `a'` of the translated
coefficient. -/
theorem aux_prop_growth_macro_energy_origin_package (m : ℕ) (y : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m)
    (aC : PositiveCoefficient (centeredCube y ((3 : ℝ) ^ m) hR))
    (a' : SpatialCoordinates d → ℝ)
    (ha' : ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m)),
      a' x = aC.val (x + y))
    (g : SpatialCoordinates d → Fin d → ℝ)
    (hgrad : HilbertGradient (centeredCube y ((3 : ℝ) ^ m) hR))
    (hgi : ∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
        fun x => g x i)
    (h u : weakSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR))
    (gh : SpatialCoordinates d → Fin d → ℝ)
    (hghi : ∀ i : Fin d,
      (sobolevGradient (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) i :
          SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
          fun x => gh x i)
    (hweak : ∀ φ : killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR),
      sobolevCoefficientForm aC (u : SobolevData _) (φ : SobolevData _) =
        -inner ℝ hgrad (subspaceGradient (killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR)) φ))
    (htr : (u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) -
        (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) ∈
      killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR)) :
    ∃ u' h' : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d m)),
      IsDirichletSolutionOn a' (Homogenization.originCube d m) u' h' (fun x => g (x + y)) ∧
      (∀ x, h'.grad x = gh (x + y)) ∧
      (u'.toFun =ᵐ[volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m))]
        fun x => (u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)).1 (x + y)) ∧
      (∀ i : Fin d, (fun x => u'.grad x i)
        =ᵐ[volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m))]
          fun x => (u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)).2 i (x + y)) := by
  obtain ⟨u'', h'', hz, hs, hgh, hfun, hgr⟩ :=
    aux_prop_growth_macro_energy_root_package aC g hgrad hgi h u gh hghi hweak htr
  have hV := aux_prop_growth_macro_energy_root_eq_translateSet m y hR
  obtain ⟨u', h', hu'1, hu'2, hh'2, hz', hs'⟩ :=
    aux_prop_growth_macro_energy_untranslate_package y hV u'' h'' hz hs
  have hfun' := aux_prop_growth_macro_energy_ae_pull_translate' y _ _ hV hfun
  have hgr' := fun i : Fin d => aux_prop_growth_macro_energy_ae_pull_translate' y _ _ hV (hgr i)
  refine ⟨u', h', ⟨hz', ?_⟩, fun x => by rw [hh'2, hgh], ?_, fun i => ?_⟩
  · refine lane2_isDivFormWeakSolutionOn_congr_coefficient ?_ hs'
    filter_upwards [ha'] with x hx
    rw [hx]
  · filter_upwards [hfun'] with x hx
    rw [hu'1]; exact hx
  · filter_upwards [hgr' i] with x hx
    rw [hu'2]; exact hx

end Paper

/-!
# Native construction of `in_6_16` — readouts

The native quantities of `HolderRegularityConclusions` on the origin chart, read as the MFD
quantities of `PaperSourcedRegularity` on the root: the cutoff coefficient, the reference
average, the normalized energy on windows, the window oscillations, and the fractional datum
norm.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (cube truncatedCube translatedCube MemHolder holderSeminormOn
  IsDirichletSolutionOn IsDivFormWeakSolutionOn HasZeroTraceDifferenceOn)

variable {d : ℕ}

/-! ### 1. Coefficient and reference -/

section Coeff

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- On the good set, the native translated cutoff coefficient is the layer formula. -/
theorem aux_prop_growth_macro_energy_aCutoff_translate_lift (M : GMCModel d) (L : ℕ)
    {om : BilateralField d} (hom : om ∈ aux_prop_growth_macro_energy_good d)
    (y x : SpatialCoordinates d) :
    aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y
        (aux_prop_growth_macro_energy_lift om)) x =
      aux_prop_growth_macro_energy_cutoffFun M L om (x + y) := by
  unfold aCutoff aux_prop_growth_macro_energy_cutoffFun
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    change (aux_prop_growth_macro_energy_lift om k) (x + y) = _
    exact aux_prop_growth_macro_energy_lift_apply_of_good hom k (x + y)
  · push_cast; ring

theorem aux_prop_growth_macro_energy_aCutoff_translate_lift_nonneg (M : GMCModel d) (L : ℕ)
    (om : BilateralField d) (y x : SpatialCoordinates d) :
    0 ≤ aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y
        (aux_prop_growth_macro_energy_lift om)) x :=
  (Real.exp_pos _).le

/-- The native coefficient is a.e. the translated MFD cutoff coefficient on `□_m`. -/
theorem aux_prop_growth_macro_energy_aCutoff_ae (M : GMCModel d) (L : ℕ)
    {om : BilateralField d} (hom : om ∈ aux_prop_growth_macro_energy_good d)
    (m : ℕ) (y : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m) :
    ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m)),
      aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y
          (aux_prop_growth_macro_energy_lift om)) x =
        (aux_prop_growth_macro_energy_cutoffOn M L om y ((3 : ℝ) ^ m) hR).val (x + y) := by
  have h := aux_prop_growth_macro_energy_ae_pull_translate' y _ _
    (aux_prop_growth_macro_energy_root_eq_translateSet m y hR)
    (aux_prop_growth_macro_energy_cutoffOn_eq M L om y ((3 : ℝ) ^ m) hR)
  filter_upwards [h] with x hx
  rw [hx, aux_prop_growth_macro_energy_aCutoff_translate_lift M L hom]
  rfl

/-- On the good set, the native tail average on `□_m` is the MFD reference average. -/
theorem aux_prop_growth_macro_energy_tailAverage_eq (M : GMCModel d) (L m : ℕ)
    {om : BilateralField d} (hom : om ∈ aux_prop_growth_macro_energy_good d)
    (y : SpatialCoordinates d) :
    SubdiffusiveProcess.CoarseGrainingVocab.tailAverage M L m (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y
        (aux_prop_growth_macro_energy_lift om)) (cube d m) =
      aux_prop_growth_macro_energy_refAvg M L m y om := by
  have hR : (0 : ℝ) < 3 ^ m := pow_pos (by norm_num) m
  have hV := aux_prop_growth_macro_energy_root_eq_translateSet m y hR
  have hpt : ∀ x, SubdiffusiveProcess.CoarseGrainingVocab.tailCoefficient M L m
      (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y (aux_prop_growth_macro_energy_lift om)) x =
      aux_prop_growth_macro_energy_refFun M L m om (x + y) := by
    intro x
    unfold SubdiffusiveProcess.CoarseGrainingVocab.tailCoefficient aux_prop_growth_macro_energy_refFun
    rw [aux_prop_growth_macro_energy_aCutoff_translate_lift M L hom,
      aux_prop_growth_macro_energy_aCutoff_translate_lift M (min m L) hom]
    unfold aux_prop_growth_macro_energy_cutoffFun
    rw [← Real.exp_sub]
    congr 2
    push_cast
    ring
  unfold SubdiffusiveProcess.CoarseGrainingVocab.tailAverage Homogenization.volumeAverage
    aux_prop_growth_macro_energy_refAvg
  simp only [hpt]
  have hcube : (cube d (m : ℤ) : Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet (Homogenization.originCube d m) := rfl
  rw [hcube, Homogenization.setIntegral_comp_addRight_translateSet, ← hV]
  congr 2
  rw [Measure.real, ← Homogenization.volume_translateSet_eq y, ← hV]

end Coeff

/-! ### 2. Energy and oscillation on windows -/

/-- The normalized MFD energy of a window `S = y + W` is the native normalized vector `L²`
norm of `√a' ∇u'` on `W`. -/
theorem aux_prop_growth_macro_energy_energy_window (m : ℕ) (y : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m)
    (aC : PositiveCoefficient (centeredCube y ((3 : ℝ) ^ m) hR))
    (a' : SpatialCoordinates d → ℝ) (ha'0 : ∀ x, 0 ≤ a' x)
    (ha' : ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m)),
      a' x = aC.val (x + y))
    (u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR))
    (G : SpatialCoordinates d → SpatialCoordinates d)
    (hG : ∀ i : Fin d, (fun x => G x i)
      =ᵐ[volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m))]
        fun x => u.2 i (x + y))
    (W : Set (SpatialCoordinates d)) (hWm : MeasurableSet W)
    (hW : W ⊆ Homogenization.openCubeSet (Homogenization.originCube d m))
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S)
    (hSW : S = Homogenization.translateSet y W) :
    normalizedEnergyNorm aC hS (sobolevGradient u) =
      SubdiffusiveProcess.CoarseGrainingVocab.vectorNormalizedL2On W (fun x => Real.sqrt (a' x) • G x) := by
  have hV := aux_prop_growth_macro_energy_root_eq_translateSet m y hR
  have hSΩ : S ⊆ (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) := by
    rw [hSW, hV]
    intro w hw
    rw [Homogenization.mem_translateSet_iff_sub_mem] at hw ⊢
    exact hW hw
  set Gs : SpatialCoordinates d → ℝ := fun x =>
    ∑ i : Fin d, (aC.val : SpatialCoordinates d → ℝ) x * (u.2 i x) ^ 2 with hGsdef
  have hint : ∀ i : Fin d, Integrable
      (fun x => (aC.val : SpatialCoordinates d → ℝ) x * (u.2 i x) ^ 2)
      ((volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR :
        Set (SpatialCoordinates d))).restrict S) := by
    intro i
    have h := integrable_weighted_coordinates aC.val (sobolevGradient u) (sobolevGradient u) i
    refine (h.restrict (s := S)).congr (Filter.Eventually.of_forall fun x => ?_)
    change (aC.val : SpatialCoordinates d → ℝ) x * (u.2 i x * u.2 i x) = _
    ring
  have hloc : localGradientEnergy aC hS (sobolevGradient u) = ∫ x in S, Gs x := by
    rw [localGradientEnergy_eq_integral]
    change ∑ i : Fin d, ∫ x in S, (aC.val : SpatialCoordinates d → ℝ) x * (u.2 i x) ^ 2
        ∂volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) = _
    rw [← integral_finset_sum _ (fun i _ => hint i)]
    rw [Measure.restrict_restrict hS, Set.inter_eq_left.mpr hSΩ]
  have htr : ∫ x in S, Gs x = ∫ x in W, Gs (x + y) := by
    rw [hSW, Homogenization.setIntegral_comp_addRight_translateSet]
  have hcongr : ∫ x in W, Gs (x + y) = ∫ x in W, a' x * Homogenization.vecNormSq (G x) := by
    refine setIntegral_congr_ae hWm ?_
    have hall : ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m)),
        ∀ i : Fin d, G x i = u.2 i (x + y) := by
      rw [ae_all_iff]; exact hG
    have h2 := ae_restrict_of_ae_restrict_of_subset hW (ha'.and hall)
    rw [ae_restrict_iff' hWm] at h2
    filter_upwards [h2] with x hx hxW
    obtain ⟨hx1, hx2⟩ := hx hxW
    rw [hx1, hGsdef]
    simp only [Homogenization.vecNormSq, Homogenization.vecDot, hx2]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hvol : (volume W).toReal = volume.real S := by
    rw [hSW, Measure.real, Homogenization.volume_translateSet_eq]
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.vectorNormalizedL2On_sqrt_smul_eq_sqrt_volumeAverage _
    a' _ ha'0]
  unfold normalizedEnergyNorm Homogenization.volumeAverage
  rw [hloc, htr, hcongr, hvol, div_eq_inv_mul]

/-- The MFD window oscillation of `v` on `S = y + W` is the native normalized oscillation of
any a.e. representative `f` of `v (· + y)` on `W`. -/
theorem aux_prop_growth_macro_energy_osc_window (m : ℕ) (y : SpatialCoordinates d)
    (v f : SpatialCoordinates d → ℝ)
    (hf : f =ᵐ[volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m))]
      fun x => v (x + y))
    (W : Set (SpatialCoordinates d))
    (hW : W ⊆ Homogenization.openCubeSet (Homogenization.originCube d m))
    (S : Set (SpatialCoordinates d)) (hSW : S = Homogenization.translateSet y W) :
    Real.sqrt ((volume.real S)⁻¹ *
        ∫ w in S, (v w - (volume.real S)⁻¹ * ∫ w in S, v w) ^ 2) =
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On W
        (fun z => f z - SubdiffusiveProcess.CoarseGrainingVocab.averageOn W f) := by
  have hvol : volume.real S = (volume W).toReal := by
    rw [hSW, Measure.real, Homogenization.volume_translateSet_eq]
  have hfW : f =ᵐ[volume.restrict W] fun x => v (x + y) :=
    ae_restrict_of_ae_restrict_of_subset hW hf
  have hint1 : ∫ w in S, v w = ∫ x in W, f x := by
    rw [hSW, ← Homogenization.setIntegral_comp_addRight_translateSet]
    exact integral_congr_ae hfW.symm
  have havg : (volume.real S)⁻¹ * ∫ w in S, v w = SubdiffusiveProcess.CoarseGrainingVocab.averageOn W f := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.averageOn Homogenization.volumeAverage
    rw [hvol, hint1]
  rw [havg]
  unfold SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On Homogenization.volumeAverage
  congr 1
  rw [hvol]
  congr 1
  rw [hSW, ← Homogenization.setIntegral_comp_addRight_translateSet]
  refine integral_congr_ae ?_
  filter_upwards [hfW] with x hx
  rw [hx]

/-! ### 3. The fractional datum norm -/

theorem aux_prop_growth_macro_energy_norm_le_euclideanNorm (v : SpatialCoordinates d) :
    ‖v‖ ≤ Homogenization.euclideanNorm v := by
  rw [aux_prop_growth_macro_energy_euclideanNorm_eq]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => (v j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- The native full fractional norm of the translated datum gradient is the MFD
seminorm-plus-sup. -/
theorem aux_prop_growth_macro_energy_frac_identity (m : ℕ) (y : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m) (gh : SpatialCoordinates d → Fin d → ℝ)
    (hghH : ∀ i : Fin d, IsHolderOn (1 / 2)
      (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => gh x i)) :
    SubdiffusiveProcess.CoarseGrainingVocab.fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ m) (1 / 2)
        (fun x => gh (x + y)) =
      halfHolderSeminorm (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) gh +
        ((3 : ℝ) ^ m) ^ (-(1 / 2 : ℝ)) *
          sSup {v : ℝ | ∃ x ∈ (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)),
            v = Real.sqrt (∑ i : Fin d, (gh x i) ^ 2)} := by
  obtain ⟨K, hK, hb⟩ := aux_prop_growth_macro_energy_holder_vector_bound gh hghH
  have hmemC : ∀ x ∈ cube d (m : ℤ), x + y ∈ (closedCube y ((3 : ℝ) ^ m) hR : Set _) :=
    fun x hx => centeredCube_subset_closedCube y hR
      ((SubdiffusiveProcess.Lane4.mem_cube_iff_add_mem_centeredCube m y hR x).1 hx)
  have hsemi : BddAbove {r : ℝ | ∃ x ∈ cube d (m : ℤ), ∃ w ∈ cube d (m : ℤ), x ≠ w ∧
      r = Homogenization.euclideanNorm (gh (x + y) - gh (w + y)) /
        Homogenization.euclideanNorm (x - w) ^ (1 / 2 : ℝ)} := by
    refine ⟨K, ?_⟩
    rintro r ⟨x, hx, w, hw, hxw, rfl⟩
    have hpos : 0 < Homogenization.euclideanNorm (x - w) ^ (1 / 2 : ℝ) := by
      apply Real.rpow_pos_of_pos
      rcases (Homogenization.euclideanNorm_nonneg (x - w)).lt_or_eq with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 (Homogenization.euclideanNorm_eq_zero_iff.1 h.symm)) hxw
    rw [div_le_iff₀ hpos]
    have := hb (x + y) (hmemC x hx) (w + y) (hmemC w hw)
    rwa [add_sub_add_right_eq_sub] at this
  have hvalues : BddAbove {r : ℝ | ∃ x ∈ cube d (m : ℤ),
      r = Homogenization.euclideanNorm (gh (x + y))} := by
    refine ⟨(d : ℝ) * (K * ((d : ℝ) * (3 : ℝ) ^ m) ^ (1 / 2 : ℝ) + ‖gh y‖), ?_⟩
    rintro r ⟨x, hx, rfl⟩
    have hy0 : (0 : SpatialCoordinates d) ∈ cube d (m : ℤ) := by
      rw [aux_prop_growth_macro_energy_mem_cube_iff, norm_zero]; positivity
    have h1 := hb (x + y) (hmemC x hx) (0 + y) (hmemC 0 hy0)
    rw [zero_add, add_sub_cancel_right] at h1
    have hxn : ‖x‖ < (3 : ℝ) ^ (m : ℤ) / 2 := (aux_prop_growth_macro_energy_mem_cube_iff _ x).1 hx
    have hxe : Homogenization.euclideanNorm x ≤ (d : ℝ) * (3 : ℝ) ^ m := by
      refine (Homogenization.euclideanNorm_le_dimension_mul_norm x).trans ?_
      rw [zpow_natCast] at hxn
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have hpow : Homogenization.euclideanNorm x ^ (1 / 2 : ℝ) ≤
        ((d : ℝ) * (3 : ℝ) ^ m) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (Homogenization.euclideanNorm_nonneg _) hxe (by norm_num)
    have hsup : ‖gh (x + y)‖ ≤ K * ((d : ℝ) * (3 : ℝ) ^ m) ^ (1 / 2 : ℝ) + ‖gh y‖ := by
      calc ‖gh (x + y)‖ ≤ ‖gh (x + y) - gh y‖ + ‖gh y‖ := norm_le_norm_sub_add _ _
        _ ≤ Homogenization.euclideanNorm (gh (x + y) - gh y) + ‖gh y‖ := by
            gcongr; exact aux_prop_growth_macro_energy_norm_le_euclideanNorm _
        _ ≤ K * Homogenization.euclideanNorm x ^ (1 / 2 : ℝ) + ‖gh y‖ := by gcongr
        _ ≤ _ := by gcongr
    calc Homogenization.euclideanNorm (gh (x + y)) ≤ (d : ℝ) * ‖gh (x + y)‖ :=
          Homogenization.euclideanNorm_le_dimension_mul_norm _
      _ ≤ _ := mul_le_mul_of_nonneg_left hsup (Nat.cast_nonneg _)
  rw [SubdiffusiveProcess.CoarseGrainingVocab.fractionalInfinityNormOnReal_eq_of_bddAbove _ hsemi hvalues,
    SubdiffusiveProcess.Lane4.folded_source_holderSeminormOn_eq m y hR gh]
  congr 2
  unfold SubdiffusiveProcess.CoarseGrainingVocab.vectorSupNormOn
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x + y, (SubdiffusiveProcess.Lane4.mem_cube_iff_add_mem_centeredCube m y hR x).1 hx,
      aux_prop_growth_macro_energy_euclideanNorm_eq _⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w - y, ?_, ?_⟩
    · rw [SubdiffusiveProcess.Lane4.mem_cube_iff_add_mem_centeredCube m y hR, sub_add_cancel]
      exact hw
    · change _ = Homogenization.euclideanNorm (gh (w - y + y))
      rw [sub_add_cancel, aux_prop_growth_macro_energy_euclideanNorm_eq]

end Paper




open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (cube truncatedCube translatedCube MemHolder holderSeminormOn
  IsDirichletSolutionOn IsDivFormWeakSolutionOn HasZeroTraceDifferenceOn)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Real-arithmetic combination -/

theorem aux_prop_growth_macro_energy_combine {lhs nC C E A B Dn D : ℝ} {P Q : Prop}
    [Decidable P] [Decidable Q] (hPQ : P ↔ Q) (hnC : nC ≤ C) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hDn : Dn = D)
    (h : lhs ≤ nC * E * (A + B + if P then 0 else Dn)) :
    lhs ≤ C * E * (A + B) + if Q then 0 else C * E * D := by
  subst hDn
  by_cases hQ : Q
  · have hP : P := hPQ.2 hQ
    rw [if_pos hP] at h
    rw [if_pos hQ, add_zero]
    refine h.trans ?_
    rw [add_zero]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnC hE) (add_nonneg hA hB)
  · have hP : ¬P := fun hp => hQ (hPQ.1 hp)
    rw [if_neg hP] at h
    rw [if_neg hQ]
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnC hE)
      (add_nonneg (add_nonneg hA hB) hD)
    linarith

theorem aux_prop_growth_macro_energy_halfHolderSeminorm_nonneg {k : ℕ}
    (S : Set (SpatialCoordinates d)) (g : SpatialCoordinates d → Fin k → ℝ) :
    0 ≤ halfHolderSeminorm S g :=
  Real.sSup_nonneg (by
    rintro v ⟨x, _, y, _, _, rfl⟩
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem aux_prop_growth_macro_energy_halfHolderNorm_nonneg {k : ℕ} (r : ℝ)
    (S : Set (SpatialCoordinates d)) (g : SpatialCoordinates d → Fin k → ℝ) :
    0 ≤ halfHolderNorm r S g :=
  add_nonneg (Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (aux_prop_growth_macro_energy_halfHolderSeminorm_nonneg S g))

/-- `3^{m/2} = √(3^m)`. -/
theorem aux_prop_growth_macro_energy_rpow_half (m : ℕ) :
    (3 : ℝ) ^ ((m : ℝ) / 2) = Real.sqrt ((3 : ℝ) ^ m) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- The native energy-density boundary term is the MFD one. -/
theorem aux_prop_growth_macro_energy_boundary_energy_eq (m : ℕ) (t semi sup : ℝ) (ht : 0 < t) :
    t ^ (1 / 2 : ℝ) * (3 : ℝ) ^ ((m : ℝ) / 2) *
        (semi + ((3 : ℝ) ^ m) ^ (-(1 / 2 : ℝ)) * sup) =
      Real.sqrt t * (sup + Real.sqrt ((3 : ℝ) ^ m) * semi) := by
  have hq : 0 < Real.sqrt ((3 : ℝ) ^ m) := Real.sqrt_pos.2 (by positivity)
  rw [← Real.sqrt_eq_rpow, aux_prop_growth_macro_energy_rpow_half, Real.rpow_neg (by positivity),
    ← Real.sqrt_eq_rpow]
  field_simp
  ring

/-- The native Hölder-estimate boundary term is the MFD one. -/
theorem aux_prop_growth_macro_energy_boundary_holder_eq (m : ℕ) (semi sup : ℝ) :
    (3 : ℝ) ^ (3 * (m : ℝ) / 2) * (semi + ((3 : ℝ) ^ m) ^ (-(1 / 2 : ℝ)) * sup) =
      (3 : ℝ) ^ (m : ℝ) * (sup + Real.sqrt ((3 : ℝ) ^ m) * semi) := by
  have hq : 0 < Real.sqrt ((3 : ℝ) ^ m) := Real.sqrt_pos.2 (by positivity)
  have h32 : (3 : ℝ) ^ (3 * (m : ℝ) / 2) = (3 : ℝ) ^ (m : ℝ) * (3 : ℝ) ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf
  rw [h32, aux_prop_growth_macro_energy_rpow_half, Real.rpow_neg (by positivity),
    ← Real.sqrt_eq_rpow]
  field_simp
  ring

/-! ### The energy-density field -/

section Fields

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- `energy_density` (`eq:mfd-6.3`) for the native construction. -/
theorem aux_prop_growth_macro_energy_energy_density (M : GMCModel d) :
    ∀ (L : ℕ) (om : BilateralField d) (alpha : ℝ),
      M.delta ≤ (aux_prop_growth_macro_energy_C d)⁻¹ →
      alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - aux_prop_growth_macro_energy_C d * M.delta * Real.sqrt |Real.log M.delta|) →
    ∀ (m : ℕ) (y : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
      (g : SpatialCoordinates d → Fin d → ℝ)
      (hgrad : HilbertGradient (centeredCube y (3 ^ m) hR)),
      (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
        =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR :
          Set (SpatialCoordinates d))] fun x => g x i) →
      (∀ i : Fin d, IsHolderOn (1 / 2)
        (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => g x i)) →
    ∀ (h u : weakSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR))
      (gh : SpatialCoordinates d → Fin d → ℝ),
      (∀ i : Fin d,
        (sobolevGradient (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) i :
            SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
            (fun x => gh x i)) →
      (∀ i : Fin d, IsHolderOn (1 / 2)
        (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => gh x i)) →
      (∀ φ : killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR),
        sobolevCoefficientForm (aux_prop_growth_macro_energy_cutoffOn M L om y (3 ^ m) hR)
            (u : SobolevData _) (φ : SobolevData _) =
          -inner ℝ hgrad
            (subspaceGradient (killedSobolevGraph (centeredCube y (3 ^ m) hR)) φ)) →
      ((u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) -
          (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR))) ∈
        killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR) →
    ∀ (x : SpatialCoordinates d), x ∈ centeredCube y ((3 : ℝ) ^ m) hR →
    ∀ (n : ℕ), (n : ℤ) ≤ (m : ℤ) - aux_prop_growth_macro_energy_prefix M L alpha m y om →
      normalizedEnergyNorm (aux_prop_growth_macro_energy_cutoffOn M L om y (3 ^ m) hR)
          ((isOpen_ball (x := x) (ε := (3 : ℝ) ^ n / 2)).measurableSet.inter
            (centeredCube y ((3 : ℝ) ^ m) hR).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData _)) ≤
        aux_prop_growth_macro_energy_C d * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
          (normalizedEnergyNorm (aux_prop_growth_macro_energy_cutoffOn M L om y (3 ^ m) hR)
              (centeredCube y ((3 : ℝ) ^ m) hR).isOpen.measurableSet
              (sobolevGradient (u : SobolevData _)) +
            Real.sqrt (aux_prop_growth_macro_energy_refAvg M L m y om)⁻¹ *
              (3 : ℝ) ^ ((m : ℝ) / 2) *
              halfHolderSeminorm
                (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g) +
        (if x ∈ (centeredCube y ((3 : ℝ) ^ ((m : ℤ) - 1)) (by positivity) :
            Set (SpatialCoordinates d)) then 0 else
          aux_prop_growth_macro_energy_C d * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
            Real.sqrt (aux_prop_growth_macro_energy_refAvg M L m y om) *
            halfHolderNorm ((3 : ℝ) ^ m)
              (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
              gh) := by
  intro L om alpha hδ hα m y hR g hgrad hgi hgH h u gh hghi hghH hweak htr x hx n hn
  by_cases hom : om ∈ aux_prop_growth_macro_energy_good d
  swap
  · exfalso
    have hp : aux_prop_growth_macro_energy_prefix M L alpha m y om = m + 1 := by
      unfold aux_prop_growth_macro_energy_prefix; rw [if_neg hom]
    rw [hp] at hn; push_cast at hn; omega
  have hOK := aux_prop_growth_macro_energy_nativeOK_of M hδ hα
  obtain ⟨-, -, -, hXreg⟩ :=
    Classical.choose_spec (aux_prop_growth_macro_energy_native_y M hOK L m y)
  have hpre : aux_prop_growth_macro_energy_prefix M L alpha m y om =
      Classical.choose (aux_prop_growth_macro_energy_native_y M hOK L m y)
        (aux_prop_growth_macro_energy_lift om) := by
    unfold aux_prop_growth_macro_energy_prefix
    rw [if_pos hom, aux_prop_growth_macro_energy_X_eq M hOK]
  set ω' := SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y
    (aux_prop_growth_macro_energy_lift om) with hω'
  set aC := aux_prop_growth_macro_energy_cutoffOn M L om y ((3 : ℝ) ^ m) hR with haC
  obtain ⟨u', h', hsol, hh'g, hu'f, hu'g⟩ :=
    aux_prop_growth_macro_energy_origin_package m y hR aC (aCutoff M L ω')
      (aux_prop_growth_macro_energy_aCutoff_ae M L hom m y hR) g hgrad hgi h u gh hghi hweak htr
  have hgM := aux_prop_growth_macro_energy_memHolder_translate m y hR g hgH
  have hh'fun : h'.grad = fun x => gh (x + y) := funext hh'g
  have hghM : MemHolder (cube d (m : ℤ)) (1 / 2) h'.grad := by
    rw [hh'fun]; exact aux_prop_growth_macro_energy_memHolder_translate m y hR gh hghH
  have hconc := hXreg (aux_prop_growth_macro_energy_lift om) u' h' (fun x => g (x + y)) hsol hgM
    hghM
  have hx' : x - y ∈ cube d (m : ℤ) :=
    (aux_prop_growth_macro_energy_mem_centeredCube_nat_iff_sub y x m hR).1 hx
  have hn' : (n : ℤ) ≤ (m : ℤ) -
      (Classical.choose (aux_prop_growth_macro_energy_native_y M hOK L m y)
        (aux_prop_growth_macro_energy_lift om) : ℤ) := by
    rw [← hpre]; exact hn
  have h2 := hconc.2.1 n hn' (x - y) hx'
  -- the windows
  have hSW : Metric.ball x ((3 : ℝ) ^ n / 2) ∩
      (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) =
      Homogenization.translateSet y (truncatedCube d m n (x - y)) := by
    rw [aux_prop_growth_macro_energy_translateSet_truncatedCube m (n : ℤ) y x hR, zpow_natCast]
  have hEloc := aux_prop_growth_macro_energy_energy_window m y hR aC (aCutoff M L ω')
    (aux_prop_growth_macro_energy_aCutoff_translate_lift_nonneg M L om y)
    (aux_prop_growth_macro_energy_aCutoff_ae M L hom m y hR) (u : SobolevData _) u'.grad hu'g
    (truncatedCube d m n (x - y)) (aux_prop_growth_macro_energy_measurableSet_truncatedCube m n _)
    (aux_prop_growth_macro_energy_truncatedCube_subset m n _) _
    ((isOpen_ball (x := x) (ε := (3 : ℝ) ^ n / 2)).measurableSet.inter
      (centeredCube y ((3 : ℝ) ^ m) hR).isOpen.measurableSet) hSW
  have hEroot := aux_prop_growth_macro_energy_energy_window m y hR aC (aCutoff M L ω')
    (aux_prop_growth_macro_energy_aCutoff_translate_lift_nonneg M L om y)
    (aux_prop_growth_macro_energy_aCutoff_ae M L hom m y hR) (u : SobolevData _) u'.grad hu'g
    (cube d (m : ℤ)) (aux_prop_growth_macro_energy_measurableSet_cube _) subset_rfl _
    (centeredCube y ((3 : ℝ) ^ m) hR).isOpen.measurableSet
    (aux_prop_growth_macro_energy_root_eq_translateSet m y hR)
  have htail := aux_prop_growth_macro_energy_tailAverage_eq M L m hom y
  have hholder := SubdiffusiveProcess.Lane4.folded_source_holderSeminormOn_eq m y hR g
  have hfrac := aux_prop_growth_macro_energy_frac_identity m y hR gh hghH
  rw [hh'fun] at h2
  rw [← hEloc, ← hEroot, htail, hholder, hfrac] at h2
  have hrefpos := aux_prop_growth_macro_energy_refAvg_pos M L m y om
  have hinv : aux_prop_growth_macro_energy_refAvg M L m y om ^ (-1 / 2 : ℝ) =
      Real.sqrt (aux_prop_growth_macro_energy_refAvg M L m y om)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hrefpos.le, ← Real.sqrt_eq_rpow,
      Real.sqrt_inv]
  rw [hinv, aux_prop_growth_macro_energy_boundary_energy_eq m _ _ _ hrefpos] at h2
  have hPQ : x - y ∈ cube d ((m : ℤ) - 1) ↔
      x ∈ (centeredCube y ((3 : ℝ) ^ ((m : ℤ) - 1)) (by positivity) :
        Set (SpatialCoordinates d)) :=
    (aux_prop_growth_macro_energy_mem_centeredCube_iff_sub y x ((m : ℤ) - 1)).symm
  have hfinal := aux_prop_growth_macro_energy_combine hPQ
    (aux_prop_growth_macro_energy_nC_le_C d) (Real.rpow_nonneg (by norm_num) _)
    (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (aux_prop_growth_macro_energy_halfHolderSeminorm_nonneg _ g))
    (mul_nonneg (Real.sqrt_nonneg _) (aux_prop_growth_macro_energy_halfHolderNorm_nonneg
      ((3 : ℝ) ^ m) (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) gh))
    rfl h2
  refine hfinal.trans (le_of_eq ?_)
  congr 1
  split_ifs
  · rfl
  · unfold halfHolderNorm; ring

end Fields

end Paper

/-!
# Native construction of `in_6_16` — the Hölder field and the structure
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (cube truncatedCube translatedCube MemHolder holderSeminormOn
  IsDirichletSolutionOn IsDivFormWeakSolutionOn HasZeroTraceDifferenceOn)

attribute [local instance] Classical.propDecidable

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- `holder_estimate` (`e.Holder.estimate.boxes.local`) for the native construction. -/
theorem aux_prop_growth_macro_energy_holder_estimate (M : GMCModel d) :
    ∀ (L : ℕ) (om : BilateralField d) (alpha : ℝ),
      M.delta ≤ (aux_prop_growth_macro_energy_C d)⁻¹ →
      alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - aux_prop_growth_macro_energy_C d * M.delta * Real.sqrt |Real.log M.delta|) →
    ∀ (m : ℕ) (y : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
      (g : SpatialCoordinates d → Fin d → ℝ)
      (hgrad : HilbertGradient (centeredCube y (3 ^ m) hR)),
      (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
        =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR :
          Set (SpatialCoordinates d))] fun x => g x i) →
      (∀ i : Fin d, IsHolderOn (1 / 2)
        (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => g x i)) →
    ∀ (h u : weakSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR))
      (gh : SpatialCoordinates d → Fin d → ℝ),
      (∀ i : Fin d,
        (sobolevGradient (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) i :
            SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
            (fun x => gh x i)) →
      (∀ i : Fin d, IsHolderOn (1 / 2)
        (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => gh x i)) →
      (∀ φ : killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR),
        sobolevCoefficientForm (aux_prop_growth_macro_energy_cutoffOn M L om y (3 ^ m) hR)
            (u : SobolevData _) (φ : SobolevData _) =
          -inner ℝ hgrad
            (subspaceGradient (killedSobolevGraph (centeredCube y (3 ^ m) hR)) φ)) →
      ((u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) -
          (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR))) ∈
        killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR) →
    ∀ (x : SpatialCoordinates d), x ∈ centeredCube y ((3 : ℝ) ^ m) hR →
    ∀ (n : ℕ), (n : ℤ) ≤ (m : ℤ) - aux_prop_growth_macro_energy_prefix M L alpha m y om →
    ∀ (ell : ℕ), ell ≤ n →
    ∀ (z : SpatialCoordinates d),
      (∃ k : Fin d → ℤ, ∀ i, z i = y i + (3 : ℝ) ^ ell * (k i : ℝ)) →
      z ∈ Metric.ball x ((3 : ℝ) ^ n / 2) ∩
        (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) →
      let S : Set (SpatialCoordinates d) := Metric.ball z ((3 : ℝ) ^ ell / 2) ∩
        (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
      let rootSet : Set (SpatialCoordinates d) := centeredCube y ((3 : ℝ) ^ m) hR
      let v : SpatialCoordinates d → ℝ :=
        ((u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)).1 : SpatialCoordinates d → ℝ)
      let avg : Set (SpatialCoordinates d) → ℝ :=
        fun T => (volume.real T)⁻¹ * ∫ w in T, v w
      let osc : Set (SpatialCoordinates d) → ℝ :=
        fun T => Real.sqrt ((volume.real T)⁻¹ * ∫ w in T, (v w - avg T) ^ 2)
      (3 : ℝ) ^ (alpha * ((n : ℝ) - (ell : ℝ))) * osc S ≤
        aux_prop_growth_macro_energy_C d * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
          (osc rootSet + (aux_prop_growth_macro_energy_refAvg M L m y om)⁻¹ *
            (3 : ℝ) ^ (3 * (m : ℝ) / 2) * halfHolderSeminorm rootSet g) +
        (if x ∈ Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - 1) / 2) then 0 else
          aux_prop_growth_macro_energy_C d * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (m : ℝ) * halfHolderNorm ((3 : ℝ) ^ m) rootSet gh) := by
  intro L om alpha hδ hα m y hR g hgrad hgi hgH h u gh hghi hghH hweak htr x hx n hn ell hell z
    hzgrid hzmem S rootSet v avg osc
  by_cases hom : om ∈ aux_prop_growth_macro_energy_good d
  swap
  · exfalso
    have hp : aux_prop_growth_macro_energy_prefix M L alpha m y om = m + 1 := by
      unfold aux_prop_growth_macro_energy_prefix; rw [if_neg hom]
    rw [hp] at hn; push_cast at hn; omega
  have hOK := aux_prop_growth_macro_energy_nativeOK_of M hδ hα
  obtain ⟨-, -, -, hXreg⟩ :=
    Classical.choose_spec (aux_prop_growth_macro_energy_native_y M hOK L m y)
  have hpre : aux_prop_growth_macro_energy_prefix M L alpha m y om =
      Classical.choose (aux_prop_growth_macro_energy_native_y M hOK L m y)
        (aux_prop_growth_macro_energy_lift om) := by
    unfold aux_prop_growth_macro_energy_prefix
    rw [if_pos hom, aux_prop_growth_macro_energy_X_eq M hOK]
  set ω' := SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y
    (aux_prop_growth_macro_energy_lift om) with hω'
  set aC := aux_prop_growth_macro_energy_cutoffOn M L om y ((3 : ℝ) ^ m) hR with haC
  obtain ⟨u', h', hsol, hh'g, hu'f, hu'g⟩ :=
    aux_prop_growth_macro_energy_origin_package m y hR aC (aCutoff M L ω')
      (aux_prop_growth_macro_energy_aCutoff_ae M L hom m y hR) g hgrad hgi h u gh hghi hweak htr
  have hgM := aux_prop_growth_macro_energy_memHolder_translate m y hR g hgH
  have hh'fun : h'.grad = fun x => gh (x + y) := funext hh'g
  have hghM : MemHolder (cube d (m : ℤ)) (1 / 2) h'.grad := by
    rw [hh'fun]; exact aux_prop_growth_macro_energy_memHolder_translate m y hR gh hghH
  have hconc := hXreg (aux_prop_growth_macro_energy_lift om) u' h' (fun x => g (x + y)) hsol hgM
    hghM
  have hx' : x - y ∈ cube d (m : ℤ) :=
    (aux_prop_growth_macro_energy_mem_centeredCube_nat_iff_sub y x m hR).1 hx
  have hn' : (n : ℤ) ≤ (m : ℤ) -
      (Classical.choose (aux_prop_growth_macro_energy_native_y M hOK L m y)
        (aux_prop_growth_macro_energy_lift om) : ℤ) := by
    rw [← hpre]; exact hn
  -- the grid point, moved to the origin chart
  have hgrid : SubdiffusiveProcess.CoarseGrainingVocab.OnTriadicGrid ell (z - y) := by
    obtain ⟨k, hk⟩ := hzgrid
    intro i
    exact ⟨k i, by rw [Pi.sub_apply, hk i]; ring⟩
  have hzT : z - y ∈ truncatedCube d m n (x - y) := by
    have hset := aux_prop_growth_macro_energy_translateSet_truncatedCube m (n : ℤ) y x hR
    rw [zpow_natCast] at hset
    rw [← hset, Homogenization.mem_translateSet_iff_sub_mem] at hzmem
    exact hzmem
  have h1 := hconc.1 n hn' (x - y) hx' ell hell (z - y) hgrid hzT
  -- oscillations
  have hSW : S = Homogenization.translateSet y (truncatedCube d m ell (z - y)) := by
    rw [aux_prop_growth_macro_energy_translateSet_truncatedCube m (ell : ℤ) y z hR, zpow_natCast]
  have hoscS := aux_prop_growth_macro_energy_osc_window m y v u'.toFun hu'f
    (truncatedCube d m ell (z - y)) (aux_prop_growth_macro_energy_truncatedCube_subset m ell _)
    S hSW
  have hoscR := aux_prop_growth_macro_energy_osc_window m y v u'.toFun hu'f
    (cube d (m : ℤ)) subset_rfl rootSet (aux_prop_growth_macro_energy_root_eq_translateSet m y hR)
  have htail := aux_prop_growth_macro_energy_tailAverage_eq M L m hom y
  have hholder := SubdiffusiveProcess.Lane4.folded_source_holderSeminormOn_eq m y hR g
  have hfrac := aux_prop_growth_macro_energy_frac_identity m y hR gh hghH
  rw [hh'fun] at h1
  have hoscS' : osc S = SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On (truncatedCube d m ell (z - y))
      (fun w => u'.toFun w - SubdiffusiveProcess.CoarseGrainingVocab.averageOn
        (truncatedCube d m ell (z - y)) u'.toFun) := hoscS
  have hoscR' : osc rootSet = SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On (cube d (m : ℤ))
      (fun w => u'.toFun w - SubdiffusiveProcess.CoarseGrainingVocab.averageOn (cube d (m : ℤ)) u'.toFun) := hoscR
  rw [hoscS', hoscR']
  rw [htail, hholder, hfrac, aux_prop_growth_macro_energy_boundary_holder_eq] at h1
  have hPQ : x - y ∈ cube d ((m : ℤ) - 1) ↔
      x ∈ Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - 1) / 2) := by
    rw [aux_prop_growth_macro_energy_mem_cube_iff, Metric.mem_ball, dist_eq_norm]
  have hrefpos := aux_prop_growth_macro_energy_refAvg_pos M L m y om
  have hfinal := aux_prop_growth_macro_energy_combine hPQ
    (aux_prop_growth_macro_energy_nC_le_C d) (Real.rpow_nonneg (by norm_num) _)
    (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (inv_pos.2 hrefpos).le (Real.rpow_nonneg (by norm_num) _))
      (aux_prop_growth_macro_energy_halfHolderSeminorm_nonneg _ g))
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_prop_growth_macro_energy_halfHolderNorm_nonneg
      ((3 : ℝ) ^ m) (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) gh))
    rfl h1
  refine hfinal.trans (le_of_eq ?_)
  congr 1
  split_ifs
  · rfl
  · unfold halfHolderNorm; ring

/-- **The native construction of the published input `in_6_16` for every GMC model.** -/
def aux_prop_growth_macro_energy_nativeSreg (M : GMCModel d) : in_6_16 d M where
  cutoffOn := aux_prop_growth_macro_energy_cutoffOn M
  cutoffOn_eq := aux_prop_growth_macro_energy_cutoffOn_eq M
  prefixLen := aux_prop_growth_macro_energy_prefix M
  prefix_measurable := aux_prop_growth_macro_energy_prefix_measurable M
  prefix_pos := aux_prop_growth_macro_energy_prefix_pos M
  refAvg := aux_prop_growth_macro_energy_refAvg M
  refAvg_pos := aux_prop_growth_macro_energy_refAvg_pos M
  refAvg_eq := fun _ _ _ _ _ => rfl
  C := aux_prop_growth_macro_energy_C d
  C_pos := lt_of_lt_of_le one_pos (aux_prop_growth_macro_energy_one_le_C d)
  C_ge_one := aux_prop_growth_macro_energy_one_le_C d
  C_eq_dimensional := rfl
  alphaRange := Set.Icc (1 / 2 : ℝ)
    (1 - aux_prop_growth_macro_energy_C d * M.delta * Real.sqrt |Real.log M.delta|)
  alphaRange_eq := rfl
  tail := fun L alpha hδ hα m y k =>
    aux_prop_growth_macro_energy_prefix_tail M L alpha hδ hα m y k
  energy_density := aux_prop_growth_macro_energy_energy_density M
  holder_estimate := aux_prop_growth_macro_energy_holder_estimate M

theorem aux_prop_growth_macro_energy_nativeSreg_C (M : GMCModel d) :
    (aux_prop_growth_macro_energy_nativeSreg M).C = aux_prop_growth_macro_energy_C d := rfl

/-- Every GMC model carries the published regularity input. -/
theorem aux_prop_growth_macro_energy_nonempty_in_6_16 (M : GMCModel d) : Nonempty (in_6_16 d M) :=
  ⟨aux_prop_growth_macro_energy_nativeSreg M⟩

end Paper

/-!
# The residual transfer for `prop_growth_macro_energy`

For a root of side `r = s 3^{-k}`, `s ∈ [1,3]`, the shifted field `T ω = residualShift r k ω`
has the law of the constructed residual model `M_s`.  This file proves

* all exponential moments of the finite low anchor `A_k(ω) = Σ_{i<k} ω(-i)(0)` and of the
  shift envelope `E_k = exp(3k|τ²| + |A_k|)`;
* almost surely, the infrared identity `H_s(Tω)(x) = H(ω)(r x) + Σ_{i<k} ω(-i)(r x) - A_k`
  and the coefficient identity `A^M_{n+k}(ω)(r x) = c_n(ω) A^{M_s}_n(Tω)(x)`, with
  `c_n, c_n⁻¹ ≤ E_k` uniformly in `n`;
* the deterministic transfer of the Dirichlet problem from `Q(z,r)` to `Q(z/r,1)`;
* the `C²` datum bound under the dilation `y ↦ r y`.
-/

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

open SubdiffusiveProcess.Frozen.Assumptions

variable {d : ℕ}

/-! ### 1. Exponential moments of layer values and of the low anchor -/

section Moments

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- (g2): every exponential moment of `|g₀(0)|` is finite (copy of the large-root lemma). -/
theorem aux_prop_growth_macro_energy_integrable_exp_mul_abs_zero (M : GMCModel d) (c : ℝ)
    (hc : 0 ≤ c) :
    Integrable (fun g : PotentialField d => Real.exp (c * |g 0|))
      (zeroPotentialLaw M.P).toMeasure := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  set E : PotentialField d → ℝ := PotentialField.g2Observable with hEdef
  set Z : PotentialField d → ℝ := fun g =>
    Real.exp ((M.delta⁻¹ * max (E g) 0) ^ (2 : ℝ)) with hZdef
  have hZint : Integrable Z (zeroPotentialLaw M.P).toMeasure := by
    simpa [hZdef, hEdef, SubdiffusiveProcess.OGammaLE] using M.G2.regularity_expectation.1
  have h0 : (0 : Homogenization.Vec d) ∈ Metric.closedBall
      (Homogenization.cubeCenter (Homogenization.originCube d 0))
      (Homogenization.cubeRadius (Homogenization.originCube d 0)) := by
    have hc0 : Homogenization.cubeCenter (Homogenization.originCube d 0) = 0 := by
      funext i
      simp [Homogenization.cubeCenter, Homogenization.originCube]
    rw [hc0]
    exact Metric.mem_closedBall_self (Homogenization.cubeRadius_pos _).le
  have hmeasEv : Measurable fun g : PotentialField d => g 0 := by
    have hforget : Continuous fun g : PotentialField d =>
        (g.1.1 : C(SpatialCoordinates d, ℝ)) := continuous_subtype_val.fst
    exact ((continuous_eval_const (0 : SpatialCoordinates d)).comp hforget).measurable
  have hmeas : Measurable fun g : PotentialField d =>
      Real.exp (c * |g 0|) := (measurable_const.mul (continuous_abs.measurable.comp hmeasEv)).exp
  have hdom : ∀ g : PotentialField d,
      Real.exp (c * |g 0|) ≤ Real.exp ((c * M.delta) ^ 2 / 4) * Z g := by
    intro g
    have hE0 : 0 ≤ E g := PotentialField.g2Observable_nonneg g
    have hg0 : |g 0| ≤ E g :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.abs_apply_le_g2Observable_of_mem_closedBall g h0
    have hZg : Z g = Real.exp ((M.delta⁻¹ * E g) ^ (2 : ℕ)) := by
      simp only [hZdef, max_eq_left hE0]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hZg, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hexpand : (c * M.delta) ^ 2 / 4 + (M.delta⁻¹ * E g) ^ (2 : ℕ) - c * E g
        = (E g - c * M.delta ^ 2 / 2) ^ 2 / M.delta ^ 2 := by
      field_simp
      ring
    have h2 : 0 ≤ (c * M.delta) ^ 2 / 4 + (M.delta⁻¹ * E g) ^ (2 : ℕ) - c * E g := by
      rw [hexpand]; positivity
    have h3 : c * |g 0| ≤ c * E g := mul_le_mul_of_nonneg_left hg0 hc
    linarith
  refine (hZint.const_mul (Real.exp ((c * M.delta) ^ 2 / 4))).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact hdom g

/-- Every layer value at the origin has the law of `g₀(0)`. -/
theorem aux_prop_growth_macro_energy_integrable_exp_mul_abs_layer (M : GMCModel d) (m : ℤ)
    (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun om : BilateralField d => Real.exp (c * |om m 0|))
      (chaosSampleLaw M).toMeasure := by
  change Integrable _ (Measure.infinitePi (fun n : ℤ =>
    (scaledLayerLaw d (chaosRootFieldLaw M) n : Measure C(SpatialCoordinates d, ℝ))))
  set laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun n =>
    (scaledLayerLaw d (chaosRootFieldLaw M) n : Measure C(SpatialCoordinates d, ℝ)) with hlaws
  set F : C(SpatialCoordinates d, ℝ) → ℝ := fun f => Real.exp (c * |f 0|) with hF
  have hFm : Measurable F :=
    (measurable_const.mul (continuous_abs.measurable.comp
      (continuous_eval_const (0 : SpatialCoordinates d)).measurable)).exp
  have hev := measurePreserving_eval_infinitePi laws m
  have h1 : Integrable F (laws m) := by
    simp only [hlaws, scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
    rw [integrable_map_measure hFm.aestronglyMeasurable
      (layerScaling d m).continuous.measurable.aemeasurable]
    have hcomp : F ∘ (layerScaling d m) = F := by
      funext f
      simp [hF, layerScaling]
    rw [hcomp]
    simp only [chaosRootFieldLaw, ProbabilityMeasure.toMeasure_map]
    rw [integrable_map_measure hFm.aestronglyMeasurable
      (ContinuousMap.continuous _).measurable.aemeasurable]
    exact aux_prop_growth_macro_energy_integrable_exp_mul_abs_zero M c hc
  exact (hev.integrable_comp hFm.aestronglyMeasurable).2 h1

theorem aux_prop_growth_macro_energy_exp_mul_sum_le (a : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (j : ℕ)
    (hj : 0 < j) :
    Real.exp (c * ∑ n ∈ Finset.range j, a n) ≤
      ∑ n ∈ Finset.range j, Real.exp (c * j * a n) := by
  have hne : (Finset.range j).Nonempty := Finset.nonempty_range_iff.2 (by omega)
  obtain ⟨n0, hn0, hmax⟩ := Finset.exists_max_image (Finset.range j) a hne
  have hsum : (∑ n ∈ Finset.range j, a n) ≤ j * a n0 := by
    have := Finset.sum_le_card_nsmul (Finset.range j) a (a n0) hmax
    simpa [Finset.card_range, nsmul_eq_mul] using this
  calc Real.exp (c * ∑ n ∈ Finset.range j, a n) ≤ Real.exp (c * j * a n0) := by
        apply Real.exp_le_exp.2
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hsum hc
    _ ≤ ∑ n ∈ Finset.range j, Real.exp (c * j * a n) :=
        Finset.single_le_sum (f := fun n => Real.exp (c * j * a n))
          (fun n _ => (Real.exp_pos _).le) hn0

theorem aux_prop_growth_macro_energy_measurable_lowAnchor (k : ℕ) :
    Measurable (MacroAllCube.lowAnchor (d := d) k) := by
  unfold MacroAllCube.lowAnchor
  exact Finset.measurable_sum _ fun n _ =>
    (continuous_eval_const (0 : SpatialCoordinates d)).measurable.comp (measurable_pi_apply _)

/-- All exponential moments of the finite low anchor. -/
theorem aux_prop_growth_macro_energy_integrable_exp_mul_abs_lowAnchor (M : GMCModel d) (k : ℕ)
    (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun om : BilateralField d => Real.exp (c * |MacroAllCube.lowAnchor k om|))
      (chaosSampleLaw M).toMeasure := by
  have hmeas : Measurable fun om : BilateralField d =>
      Real.exp (c * |MacroAllCube.lowAnchor k om|) :=
    (measurable_const.mul (continuous_abs.measurable.comp
      (aux_prop_growth_macro_energy_measurable_lowAnchor k))).exp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [MacroAllCube.lowAnchor, Finset.range_zero, Finset.sum_empty, abs_zero, mul_zero,
      Real.exp_zero]
    exact integrable_const _
  have hsum : Integrable (fun om : BilateralField d => ∑ n ∈ Finset.range k,
      Real.exp (c * k * |om (-(Int.ofNat n)) 0|)) (chaosSampleLaw M).toMeasure :=
    integrable_finset_sum _ fun n _ =>
      aux_prop_growth_macro_energy_integrable_exp_mul_abs_layer M _ _
        (mul_nonneg hc (Nat.cast_nonneg k))
  refine hsum.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun om => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (c * |MacroAllCube.lowAnchor k om|)
      ≤ Real.exp (c * ∑ n ∈ Finset.range k, |om (-(Int.ofNat n)) 0|) := by
        apply Real.exp_le_exp.2
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc
    _ ≤ _ := aux_prop_growth_macro_energy_exp_mul_sum_le
        (fun n => |om (-(Int.ofNat n)) 0|) c hc k hk

/-- The shift envelope `E_k = exp(3k|τ²| + |A_k|)`. -/
def aux_prop_growth_macro_energy_env (M : GMCModel d) (k : ℕ) (om : BilateralField d) : ℝ :=
  Real.exp (3 * (k : ℝ) * |tauSq M.P| + |MacroAllCube.lowAnchor k om|)

theorem aux_prop_growth_macro_energy_one_le_env (M : GMCModel d) (k : ℕ) (om : BilateralField d) :
    1 ≤ aux_prop_growth_macro_energy_env M k om :=
  Real.one_le_exp (by positivity)

theorem aux_prop_growth_macro_energy_measurable_env (M : GMCModel d) (k : ℕ) :
    Measurable (aux_prop_growth_macro_energy_env (d := d) M k) :=
  (measurable_const.add (continuous_abs.measurable.comp
    (aux_prop_growth_macro_energy_measurable_lowAnchor k))).exp

/-- Every power of the envelope has every finite moment. -/
theorem aux_prop_growth_macro_energy_memLp_env_pow (M : GMCModel d) (k j : ℕ) (q : ℝ)
    (hq : 1 ≤ q) :
    MemLp (fun om => aux_prop_growth_macro_energy_env M k om ^ j) (ENNReal.ofReal q)
      (chaosSampleLaw M).toMeasure := by
  have hmeas : Measurable (fun om => aux_prop_growth_macro_energy_env M k om ^ j) :=
    (aux_prop_growth_macro_energy_measurable_env M k).pow_const j
  have hq0 : (ENNReal.ofReal q) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  rw [← integrable_norm_rpow_iff hmeas.aestronglyMeasurable hq0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)]
  have hint := (aux_prop_growth_macro_energy_integrable_exp_mul_abs_lowAnchor M k (q * j)
    (by positivity)).const_mul (Real.exp (q * j * (3 * (k : ℝ) * |tauSq M.P|)))
  refine hint.congr (Filter.Eventually.of_forall fun om => ?_)
  have hpos : 0 < aux_prop_growth_macro_energy_env M k om ^ j := pow_pos (Real.exp_pos _) _
  dsimp only
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  unfold aux_prop_growth_macro_energy_env
  rw [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

end Moments

/-! ### 2. Almost-sure infrared and coefficient identities -/

section Identities

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The shifted partial sums, as continuous maps. -/
theorem aux_prop_growth_macro_energy_infraredPartialSum_residualShift_cm (r : ℝ) (k L : ℕ)
    (om : BilateralField d) :
    infraredPartialSum (MacroAllCube.residualShift r k om) (k + L) =
      MacroAllCube.dilateField d r (infraredPartialSum om L) +
        (∑ i ∈ Finset.range k, MacroAllCube.dilateField d r (om (-(Int.ofNat i)))) -
          ContinuousMap.const _ (MacroAllCube.lowAnchor k om) := by
  ext x
  rw [MacroAllCube.infraredPartialSum_residualShift]
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.coe_sum,
    Finset.sum_apply, ContinuousMap.const_apply]
  rfl

/-- **The infrared identity of the residual shift**, almost surely. -/
theorem aux_prop_growth_macro_energy_ir_identity (M M' : GMCModel d)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (hH' : InfraredCharacterization M' H') (r : ℝ) (k : ℕ)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r k)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      Tendsto (infraredPartialSum (MacroAllCube.residualShift r k om)) atTop
          (nhds (H' (MacroAllCube.residualShift r k om))) ∧
      ∀ x : SpatialCoordinates d,
        H' (MacroAllCube.residualShift r k om) x = H om (r • x) +
          (∑ i ∈ Finset.range k, om (-(Int.ofNat i)) (r • x)) - MacroAllCube.lowAnchor k om := by
  filter_upwards [hH.2, hT.quasiMeasurePreserving.ae hH'.2] with om h1 h2
  refine ⟨h2, fun x => ?_⟩
  set G : C(SpatialCoordinates d, ℝ) := MacroAllCube.dilateField d r (H om) +
    (∑ i ∈ Finset.range k, MacroAllCube.dilateField d r (om (-(Int.ofNat i)))) -
      ContinuousMap.const _ (MacroAllCube.lowAnchor k om) with hG
  have hcont : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
      MacroAllCube.dilateField d r f +
        (∑ i ∈ Finset.range k, MacroAllCube.dilateField d r (om (-(Int.ofNat i)))) -
          ContinuousMap.const _ (MacroAllCube.lowAnchor k om)) :=
    ((MacroAllCube.dilateField d r).continuous.add continuous_const).sub continuous_const
  have hlimG : Tendsto (fun L => infraredPartialSum (MacroAllCube.residualShift r k om) (k + L))
      atTop (nhds G) := by
    have := (hcont.tendsto (H om)).comp h1
    refine this.congr (fun L => ?_)
    simp only [Function.comp_apply]
    rw [aux_prop_growth_macro_energy_infraredPartialSum_residualShift_cm]
  have hlimH : Tendsto (fun L => infraredPartialSum (MacroAllCube.residualShift r k om) (k + L))
      atTop (nhds (H' (MacroAllCube.residualShift r k om))) := by
    have hshift : Tendsto (fun L : ℕ => k + L) atTop atTop := by
      simpa [add_comm] using tendsto_add_atTop_nat k
    exact h2.comp hshift
  have heq := tendsto_nhds_unique hlimH hlimG
  rw [heq, hG]
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.coe_sum,
    Finset.sum_apply, ContinuousMap.const_apply]
  rfl

/-- The random shift factor `c_n(ω) = [ahom(M',n)/ahom(M,n+k)] exp(A_k - kτ²)`. -/
def aux_prop_growth_macro_energy_shiftC (M M' : GMCModel d) (k n : ℕ) (om : BilateralField d) :
    ℝ :=
  SubdiffusiveProcess.CoarseGrainingVocab.ahom M' n / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (n + k) *
    Real.exp (MacroAllCube.lowAnchor k om - (k : ℝ) * tauSq M.P)

theorem aux_prop_growth_macro_energy_shiftC_pos (M M' : GMCModel d) (k n : ℕ)
    (om : BilateralField d) : 0 < aux_prop_growth_macro_energy_shiftC M M' k n om :=
  mul_pos (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M' n) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _))
    (Real.exp_pos _)

/-- **The coefficient identity of the residual shift**, almost surely, for every cutoff. -/
theorem aux_prop_growth_macro_energy_coeff_identity (M M' : GMCModel d)
    (htau : tauSq M'.P = tauSq M.P)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (hH' : InfraredCharacterization M' H') (r : ℝ) (k : ℕ)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r k)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      Tendsto (infraredPartialSum (MacroAllCube.residualShift r k om)) atTop
          (nhds (H' (MacroAllCube.residualShift r k om))) ∧
      ∀ (n : ℕ) (x : SpatialCoordinates d),
        cutoffCoefficient M H om (n + k) (r • x) =
          aux_prop_growth_macro_energy_shiftC M M' k n om *
            cutoffCoefficient M' H' (MacroAllCube.residualShift r k om) n x := by
  filter_upwards [aux_prop_growth_macro_energy_ir_identity M M' H H' hH hH' r k hT]
    with om hom
  refine ⟨hom.1, fun n x => ?_⟩
  have hpot := MacroAllCube.cutoffPotential_residualShift H H' r k n om hom.2 x
  unfold cutoffCoefficient aux_prop_growth_macro_energy_shiftC
  rw [hpot, htau]
  have h := MacroAllCube.normalized_coefficient_shift (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (n + k))
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M' n)
    (cutoffPotential H' (MacroAllCube.residualShift r k om) n x) (MacroAllCube.lowAnchor k om)
    (tauSq M.P) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M' n).ne' k n
  rw [show ((n + k : ℕ) + 1 : ℝ) = ((n + k : ℕ) : ℝ) + 1 by push_cast; ring] at h
  convert h using 2

end Identities

/-- The shift factor and its inverse are dominated by the envelope, uniformly in the cutoff. -/
theorem aux_prop_growth_macro_energy_shiftC_bounds (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s)
    (hs3 : s ≤ 3) (hδ : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹) (k n : ℕ)
    (om : BilateralField d) :
    aux_prop_growth_macro_energy_shiftC M (ResidualModel.residualModel M hs1 hs3 hδ) k n om ≤
        aux_prop_growth_macro_energy_env M k om ∧
      (aux_prop_growth_macro_energy_shiftC M (ResidualModel.residualModel M hs1 hs3 hδ) k n om)⁻¹ ≤
        aux_prop_growth_macro_energy_env M k om := by
  obtain ⟨h1, h2⟩ := ResidualNormalization.residual_ahom_shift_ratio M hs1 hs3 hδ n k
  have htau : 0 < tauSq M.P := M.G4.tauSq_pos
  set ρ := SubdiffusiveProcess.CoarseGrainingVocab.ahom (ResidualModel.residualModel M hs1 hs3 hδ) n /
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M (n + k) with hρ
  set A := MacroAllCube.lowAnchor k om with hA
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos h1
  unfold aux_prop_growth_macro_energy_shiftC aux_prop_growth_macro_energy_env
  rw [← hρ, ← hA, abs_of_pos htau]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · calc ρ * Real.exp (A - (k : ℝ) * tauSq M.P)
        ≤ Real.exp (2 * tauSq M.P * (k : ℝ)) * Real.exp (A - (k : ℝ) * tauSq M.P) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (2 * tauSq M.P * (k : ℝ) + (A - (k : ℝ) * tauSq M.P)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (3 * (k : ℝ) * tauSq M.P + |A|) := by
          apply Real.exp_le_exp.2
          have := le_abs_self A
          nlinarith [mul_nonneg hk0 htau.le]
  · rw [mul_inv, ← Real.exp_neg]
    calc ρ⁻¹ * Real.exp (-(A - (k : ℝ) * tauSq M.P))
        ≤ 1 * Real.exp (-(A - (k : ℝ) * tauSq M.P)) :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ h1) (Real.exp_pos _).le
      _ ≤ Real.exp (3 * (k : ℝ) * tauSq M.P + |A|) := by
          rw [one_mul]
          apply Real.exp_le_exp.2
          have := neg_abs_le A
          nlinarith [mul_nonneg hk0 htau.le]

/-! ### 3. The deterministic Dirichlet transfer `Q(z,r) → Q(z/r,1)` -/

/-- The physical cube is the `r`-dilate of the unit cube about `z/r`. -/
theorem aux_prop_growth_macro_energy_cube_eq_smul (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) =
      r • (centeredCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d)) := by
  change Metric.ball z (r / 2) = r • Metric.ball (r⁻¹ • z) (1 / 2)
  rw [_root_.smul_ball hr.ne', Real.norm_eq_abs, abs_of_pos hr, smul_smul,
    mul_inv_cancel₀ hr.ne', one_smul, mul_one_div]

theorem aux_prop_growth_macro_energy_cube_eq_inv_smul (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0 : ℝ) < 1) :
    (centeredCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d)) =
      r⁻¹ • (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  rw [aux_prop_growth_macro_energy_cube_eq_smul z hr h1, smul_smul, inv_mul_cancel₀ hr.ne',
    one_smul]

/-- **Dirichlet transfer along a dilation.**  A solution on `Q` with coefficient
`aQ(x) = c · aT(r⁻¹ x)` becomes, on `T = r⁻¹ Q`, a solution with source `c⁻¹ r² F(r ·)` and
datum `φ(r ·)`; local energies and the global form scale by `c⁻¹ r^{2-d}`. -/
theorem aux_prop_growth_macro_energy_dirichlet_transfer {Q T : Opens (SpatialCoordinates d)}
    {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hQT : (Q : Set (SpatialCoordinates d)) = r • (T : Set (SpatialCoordinates d)))
    (hTQ : (T : Set (SpatialCoordinates d)) = r⁻¹ • (Q : Set (SpatialCoordinates d)))
    (aQ : PositiveCoefficient Q) (aT : PositiveCoefficient T)
    (hcoef : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      aQ.val x = c * aT.val (r⁻¹ • x))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ)
    (hFm : AEMeasurable F (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (b u : weakSobolevGraph Q)
    (hb : ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi)
    (hsol : SolvesDirichlet aQ F b u) :
    ∃ (F' : SpatialCoordinates d → ℝ) (b' v : weakSobolevGraph T),
      AEMeasurable F' (volume.restrict (T : Set (SpatialCoordinates d))) ∧
      (∀ᵐ y ∂volume.restrict (T : Set (SpatialCoordinates d)), |F' y| ≤ c⁻¹ * r ^ 2 * Kf) ∧
      (((b' : SobolevData T).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))] fun y => phi (r • y)) ∧
      SolvesDirichlet aT F' b' v ∧
      (∀ (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (hrS : MeasurableSet (r⁻¹ • S)),
        localGradientEnergy aT hrS (sobolevGradient (v : SobolevData T)) =
          c⁻¹ * (r⁻¹) ^ d * r ^ 2 *
            localGradientEnergy aQ hS (sobolevGradient (u : SobolevData Q))) ∧
      sobolevCoefficientForm aT (v : SobolevData T) (v : SobolevData T) =
        c⁻¹ * (r⁻¹) ^ d * r ^ 2 * sobolevCoefficientForm aQ (u : SobolevData Q) (u : SobolevData Q) := by
  have hri : 0 < r⁻¹ := inv_pos.2 hr
  have hinv : (r⁻¹)⁻¹ = r := inv_inv r
  have hQT' : (Q : Set (SpatialCoordinates d)) = (r⁻¹)⁻¹ • (T : Set (SpatialCoordinates d)) := by
    rw [hinv]; exact hQT
  obtain ⟨v, hv1, hv2⟩ := aux_aux_macro_energy_recurrence_weak_unscale hr hQT u
  obtain ⟨b', hb'1, hb'2⟩ := aux_aux_macro_energy_recurrence_weak_unscale hr hQT b
  have hv2' : ∀ i : Fin d, (((v : SobolevData T).2 i : DomainL2 T) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
        fun y => (r⁻¹)⁻¹ * ((u : SobolevData Q).2 i : SpatialCoordinates d → ℝ) ((r⁻¹)⁻¹ • y) := by
    intro i; rw [hinv]; exact hv2 i
  have hv1' : ((v : SobolevData T).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
        fun y => ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) ((r⁻¹)⁻¹ • y) := by
    rw [hinv]; exact hv1
  have hb'1' : ((b' : SobolevData T).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
        fun y => ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) ((r⁻¹)⁻¹ • y) := by
    rw [hinv]; exact hb'1
  have hb'2' : ∀ i : Fin d, (((b' : SobolevData T).2 i : DomainL2 T) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
        fun y => (r⁻¹)⁻¹ * ((b : SobolevData Q).2 i : SpatialCoordinates d → ℝ) ((r⁻¹)⁻¹ • y) := by
    intro i; rw [hinv]; exact hb'2 i
  have hDir := aux_aux_macro_energy_recurrence_dirichlet_push hri hTQ hQT' u b hsol.1 v b'
    hv1' hv2' hb'1' hb'2'
  -- the source
  set Fm := hFm.mk F with hFmdef
  have hFmm : Measurable Fm := hFm.measurable_mk
  refine ⟨fun y => c⁻¹ * r ^ 2 * Fm (r • y), b', v,
    (measurable_const.mul (hFmm.comp (measurable_const_smul r))).aemeasurable, ?_, ?_,
    ⟨hDir, fun Φ => ?_⟩, ?_, ?_⟩
  · have h1 := aux_aux_macro_energy_recurrence_ae_pull hr T.isOpen.measurableSet
      Q.isOpen.measurableSet hQT hFb
    have h2 := aux_aux_macro_energy_recurrence_ae_pull hr T.isOpen.measurableSet
      Q.isOpen.measurableSet hQT hFm.ae_eq_mk
    filter_upwards [h1, h2] with y hy1 hy2
    have hy3 : Fm (r • y) = F (r • y) := hy2.symm
    rw [hy3, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c⁻¹ * r ^ 2)]
    exact mul_le_mul_of_nonneg_left hy1 (by positivity)
  · have h1 := aux_aux_macro_energy_recurrence_ae_pull hr T.isOpen.measurableSet
      Q.isOpen.measurableSet hQT hb
    filter_upwards [hb'1, h1] with y hy1 hy2
    rw [hy1, hy2]
  · have hcoef' : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        aQ.val x = c * aT.val (r⁻¹ • x) := hcoef
    rw [aux_aux_macro_energy_recurrence_equation_T hri hc hTQ aT aQ hcoef' F b u hsol
      (v : SobolevData T) hv2' Φ]
    refine integral_congr_ae ?_
    have h2 := aux_aux_macro_energy_recurrence_ae_pull hr T.isOpen.measurableSet
      Q.isOpen.measurableSet hQT hFm.ae_eq_mk
    filter_upwards [h2] with y hy
    rw [hinv, hy]
  · intro S hS hrS
    rw [aux_aux_macro_energy_recurrence_localEnergy_scale hri hc hTQ aT aQ hcoef
      (v : SobolevData T) (u : SobolevData Q) hv2' hS hrS, hinv]
  · have hu2 : ∀ i : Fin d, (((u : SobolevData Q).2 i : DomainL2 Q) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          fun x => r⁻¹ * ((v : SobolevData T).2 i : SpatialCoordinates d → ℝ) (r⁻¹ • x) := by
      intro i
      have h := aux_aux_macro_energy_recurrence_ae_pull hri Q.isOpen.measurableSet
        T.isOpen.measurableSet hTQ (hv2 i)
      filter_upwards [h] with x hx
      rw [hx, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, ← mul_assoc, inv_mul_cancel₀ hr.ne',
        one_mul]
    rw [aux_aux_macro_energy_recurrence_form_scale hri hc hTQ aT aQ hcoef (v : SobolevData T)
      (v : SobolevData T) (u : SobolevData Q) (u : SobolevData Q) hv2' hu2, hinv]

/-! ### 4. The datum under the dilation -/

theorem aux_prop_growth_macro_energy_c2Norm_dilate (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (h1 : (0 : ℝ) < 1) (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ 2 phi) (Cphi : ℝ)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi) :
    c2Norm (closedCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d)) (fun y => phi (r • y)) ≤
      3 * Cphi := by
  have hdil : (fun y => phi (r • y)) = fun y => phi (cubeDilation z (r⁻¹ • z) r y) := by
    funext y
    congr 1
    funext i
    simp only [cubeDilation, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [hdil]
  set lam := r with hlam
  have hmap : ∀ x ∈ (closedCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d)),
      cubeDilation z (r⁻¹ • z) lam x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    intro y hy
    change dist (cubeDilation z (r⁻¹ • z) lam y) z ≤ r / 2
    have hy' : dist y (r⁻¹ • z) ≤ 1 / 2 := hy
    have heq : cubeDilation z (r⁻¹ • z) lam y - z = lam • (y - r⁻¹ • z) := by
      funext i
      simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr, ← dist_eq_norm]
    nlinarith
  have hz : z ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    change dist z z ≤ r / 2
    simp only [dist_self]
    linarith
  have hz' : r⁻¹ • z ∈ (closedCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d)) := by
    change dist (r⁻¹ • z) (r⁻¹ • z) ≤ 1 / 2
    simp only [dist_self]
    linarith
  have hcompact : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
    (closedCube z r hr).isCompact
  have hbdd0 := aux_lem_as_regularity_affine_transport_sup_bdd
    (closedCube z r hr : Set (SpatialCoordinates d)) hcompact (fun x => |phi x|)
    (continuous_abs.comp hphi.continuous)
  have hfd : ContDiff ℝ 1 (fderiv ℝ phi) :=
    (contDiff_succ_iff_fderiv.mp hphi).2.2
  have hbdd1 := aux_lem_as_regularity_affine_transport_sup_bdd
    (closedCube z r hr : Set (SpatialCoordinates d)) hcompact
    (fun x => ‖fderiv ℝ phi x‖)
    (continuous_norm.comp (hphi.continuous_fderiv (by norm_num)))
  have hbdd2 := aux_lem_as_regularity_affine_transport_sup_bdd
    (closedCube z r hr : Set (SpatialCoordinates d)) hcompact
    (fun x => ‖fderiv ℝ (fderiv ℝ phi) x‖)
    (continuous_norm.comp (hfd.continuous_fderiv (by norm_num)))
  obtain ⟨_, _, hderiv_bound, hsecond_bound⟩ :=
    aux_lem_as_regularity_affine_transport_c2_chain_rule d z (r⁻¹ • z) lam hr phi hphi
  have ht0 := aux_lem_as_regularity_affine_transport_sup_comp_le
    (closedCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d))
    (closedCube z r hr : Set (SpatialCoordinates d)) (cubeDilation z (r⁻¹ • z) lam)
    (fun x => |phi (cubeDilation z (r⁻¹ • z) lam x)|) (fun x => |phi x|) 1
    ⟨r⁻¹ • z, hz'⟩ (by norm_num) hmap hbdd0 (by intro x hx; simp)
  have ht1 := aux_lem_as_regularity_affine_transport_sup_comp_le
    (closedCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d))
    (closedCube z r hr : Set (SpatialCoordinates d)) (cubeDilation z (r⁻¹ • z) lam)
    (fun x => ‖fderiv ℝ (fun y => phi (cubeDilation z (r⁻¹ • z) lam y)) x‖)
    (fun x => ‖fderiv ℝ phi x‖) lam
    ⟨r⁻¹ • z, hz'⟩ hr.le hmap hbdd1 (by intro x hx; exact hderiv_bound x)
  have ht2 := aux_lem_as_regularity_affine_transport_sup_comp_le
    (closedCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d))
    (closedCube z r hr : Set (SpatialCoordinates d)) (cubeDilation z (r⁻¹ • z) lam)
    (fun x => ‖fderiv ℝ (fderiv ℝ (fun y => phi (cubeDilation z (r⁻¹ • z) lam y))) x‖)
    (fun x => ‖fderiv ℝ (fderiv ℝ phi) x‖) (lam ^ 2)
    ⟨r⁻¹ • z, hz'⟩ (sq_nonneg lam) hmap hbdd2 (by intro x hx; exact hsecond_bound x)
  change
    sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), v = |phi x|} +
        sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          v = ‖fderiv ℝ phi x‖} +
        sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          v = ‖fderiv ℝ (fderiv ℝ phi) x‖} ≤ Cphi at hCphi
  change
    sSup {v : ℝ | ∃ x ∈ (closedCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d)),
        v = |phi (cubeDilation z (r⁻¹ • z) lam x)|} +
      sSup {v : ℝ | ∃ x ∈ (closedCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d)),
        v = ‖fderiv ℝ (fun y => phi (cubeDilation z (r⁻¹ • z) lam y)) x‖} +
      sSup {v : ℝ | ∃ x ∈ (closedCube (r⁻¹ • z) 1 h1 : Set (SpatialCoordinates d)),
        v = ‖fderiv ℝ (fderiv ℝ (fun y => phi (cubeDilation z (r⁻¹ • z) lam y))) x‖} ≤
      3 * Cphi
  have hs0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = |phi x|} :=
    (abs_nonneg (phi z)).trans (le_csSup hbdd0 ⟨z, hz, rfl⟩)
  have hs1 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = ‖fderiv ℝ phi x‖} :=
    (norm_nonneg (fderiv ℝ phi z)).trans (le_csSup hbdd1 ⟨z, hz, rfl⟩)
  have hs2 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = ‖fderiv ℝ (fderiv ℝ phi) x‖} :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ phi) z)).trans (le_csSup hbdd2 ⟨z, hz, rfl⟩)
  have hlam1 : lam ≤ 1 := hr1
  have hlam2 : lam ^ 2 ≤ 1 := by nlinarith
  nlinarith [ht0, ht1, ht2, mul_le_mul_of_nonneg_right hlam1 hs1,
    mul_le_mul_of_nonneg_right hlam2 hs2]

end Paper

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_prop_growth_macro_energy_normalized_coeFn
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (K : Compacts (SpatialCoordinates d))
    [hΩ : Fact (((Ω : Set (SpatialCoordinates d)) ⊆ K))]
    (a : C(K, ℝ)) (ha : ∀ x, 0 < a x) (a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), ∀ hx : x ∈ Ω,
      (normalizedContinuousPositiveCoefficient (Ω := Ω) K a ha a₀ ha₀).val x =
        a ⟨x, hΩ.out hx⟩ / a₀ := by
  filter_upwards [
    expPotentialCoefficient_coeFn (compactPotentialToLp (Ω := Ω) K
      (continuousPositiveLog a ha - ContinuousMap.const K (Real.log a₀))),
    compactPotentialToLp_on_domain (Ω := Ω) K
      (continuousPositiveLog a ha - ContinuousMap.const K (Real.log a₀))] with x hexp hroot
  intro hx
  unfold normalizedContinuousPositiveCoefficient
  rw [hexp, hroot hx]
  change Real.exp (Real.log (a ⟨x, hΩ.out hx⟩) - Real.log a₀) = _
  rw [Real.exp_sub, Real.exp_log (ha _), Real.exp_log ha₀]

/-- The cutoff positive coefficient is a.e. the continuous cutoff coefficient. -/
theorem aux_prop_growth_macro_energy_coeff_ae
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H om N z hr).val y =
        SubdiffusiveProcess.cutoffCoefficient M H om N y := by
  let Ω := centeredCube z r hr
  letI : Fact (((Ω : Set (SpatialCoordinates d)) ⊆ closedCube z r hr)) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  filter_upwards [
    aux_prop_growth_macro_energy_normalized_coeFn
      (Ω := Ω) (K := closedCube z r hr)
      (SubdiffusiveProcess.Lane4.cutoffCoefficientCM M H om N z hr)
      (SubdiffusiveProcess.Lane4.cutoffCoefficientCM_pos M H om N z hr)
      1 one_pos,
    ae_restrict_mem Ω.isOpen.measurableSet] with y hy hyΩ
  simpa [Ω, SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient,
    SubdiffusiveProcess.Lane4.cutoffCoefficientCM] using hy hyΩ

/-- `Sreg.cutoffOn_eq` pulled back along the dilation `y ↦ s • y`. -/
theorem aux_prop_growth_macro_energy_cutoffOn_scaled
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M)
    (L : ℕ) (om' : BilateralField d) {s : ℝ} (hs : 0 < s)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hsr : 0 < s * r) :
    ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (Sreg.cutoffOn L om' (s • z) (s * r) hsr).val (s • y) =
        Real.exp ((∑ j ∈ Finset.range (L + 1), (om' (j : ℤ)) (s • y)) -
          (L + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
  have h := Sreg.cutoffOn_eq L om' (s • z) (s * r) hsr
  rw [ae_restrict_iff' (centeredCube (s • z) (s * r) hsr).isOpen.measurableSet] at h
  have h2 := (Measure.quasiMeasurePreserving_smul
    (volume : Measure (SpatialCoordinates d)) hs.ne').ae h
  rw [ae_restrict_iff' (centeredCube z r hr).isOpen.measurableSet]
  filter_upwards [h2] with y hy hyQ
  apply hy
  change s • y ∈ Metric.ball (s • z) (s * r / 2)
  change y ∈ Metric.ball z (r / 2) at hyQ
  rw [Metric.mem_ball] at hyQ ⊢
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hs]
  calc s * dist y z < s * (r / 2) := mul_lt_mul_of_pos_left hyQ hs
    _ = s * r / 2 := by ring

/-- Evaluation of the spatially relabelled field at a dilated point. -/
theorem aux_prop_growth_macro_energy_relabel_apply
    {d : ℕ} (om : BilateralField d) (N : ℕ) (j : ℤ) (y : SpatialCoordinates d) :
    (ContinuousMap.compRightContinuousMap ℝ
        (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
          continuous_const.smul continuous_id⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d))
        (om (j - (N : ℤ)))) ((3 : ℝ) ^ (N : ℤ) • y) = om (j - (N : ℤ)) y := by
  rw [ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply]
  congr 1
  change (3 : ℝ) ^ (-(N : ℤ)) • (3 : ℝ) ^ (N : ℤ) • y = y
  rw [smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero,
    one_smul]

/-- Reindexing the layer sum of the `N`-relabelled field. -/
theorem aux_prop_growth_macro_energy_reindex
    (f : ℤ → ℝ) (N L' : ℕ) :
    ∑ j ∈ Finset.range (N + L' + 1), f ((j : ℤ) - (N : ℤ)) =
      ∑ j ∈ Finset.range (N + 1), f (-(Int.ofNat j)) +
        ∑ n ∈ Finset.range L', f (Int.ofNat (n + 1)) := by
  rw [show N + L' + 1 = (N + 1) + L' by omega, Finset.sum_range_add]
  congr 1
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    congr 1
    rw [show N + 1 - 1 - j = N - j by omega, Nat.cast_sub hjN, Int.ofNat_eq_natCast]
    ring
  · refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    rw [Int.ofNat_eq_natCast]
    push_cast
    ring

/-- The finite-infrared physical coefficient is, a.e. on the working cube, the paper's
positive random multiple `c_{N,L'}` of the relabelled stationary cutoff coefficient
`a_{N+L'}` evaluated at the dilated point (paper lines 605--617). -/
theorem aux_prop_growth_macro_energy_finite_identity
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M)
    (om : BilateralField d) (N L' : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hNr : 0 < (3 : ℝ) ^ (N : ℤ) * r) :
    ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
            (fun om' => infraredPartialSum om' L') om N z hr).val y =
          cFin *
            (Sreg.cutoffOn (N + L')
              (fun j => ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (om (j - (N : ℤ))))
              ((3 : ℝ) ^ (N : ℤ) • z) ((3 : ℝ) ^ (N : ℤ) * r) hNr).val
              ((3 : ℝ) ^ (N : ℤ) • y) := by
  set t := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P with ht
  refine ⟨(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
      Real.exp ((L' : ℝ) * t -
        ∑ n ∈ Finset.range L', om (Int.ofNat (n + 1)) 0),
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _), ?_⟩
  filter_upwards [aux_prop_growth_macro_energy_coeff_ae M
      (fun om' => infraredPartialSum om' L') om N z hr,
    aux_prop_growth_macro_energy_cutoffOn_scaled Sreg (N + L')
      (fun j => ContinuousMap.compRightContinuousMap ℝ
        (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
          continuous_const.smul continuous_id⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d))
        (om (j - (N : ℤ))))
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ)) z hr hNr] with y h1 h2
  rw [h1, h2]
  simp only [aux_prop_growth_macro_energy_relabel_apply]
  rw [aux_prop_growth_macro_energy_reindex (fun i => om i y)]
  simp only [SubdiffusiveProcess.cutoffCoefficient, SubdiffusiveProcess.cutoffPotential,
    infraredPartialSum, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, Finset.sum_sub_distrib]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- Removing the infrared truncation (paper lines 727--738): on an environment where the
infrared partial sums converge in `C(ℝ^d, ℝ)`, the finite-infrared physical coefficients
converge essentially uniformly on the working cube to the continuous cutoff coefficient. -/
theorem aux_prop_growth_macro_energy_finite_tendsto
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (hom : Filter.Tendsto (infraredPartialSum om) Filter.atTop (nhds (H om)))
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ ε : ℝ, 0 < ε →
      ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
        ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
          |(SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
              (fun om' => infraredPartialSum om' L') om N z hr).val y -
            SubdiffusiveProcess.cutoffCoefficient M H om N y| < ε := by
  intro ε hε
  let G : C(ℝ, ℝ) := ⟨fun t => (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * Real.exp t,
    continuous_const.mul Real.continuous_exp⟩
  let P : C(SpatialCoordinates d, ℝ) :=
    (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j))) -
      ContinuousMap.const _ ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  let Φ : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) := fun h => G.comp (h + P)
  have hΦ : Continuous Φ :=
    (ContinuousMap.continuous_postcomp G).comp (continuous_id.add continuous_const)
  have hΦeq : ∀ (H' : BilateralField d → C(SpatialCoordinates d, ℝ))
      (y : SpatialCoordinates d),
      SubdiffusiveProcess.cutoffCoefficient M H' om N y = Φ (H' om) y := by
    intro H' y
    simp only [Φ, G, P, SubdiffusiveProcess.cutoffCoefficient,
      SubdiffusiveProcess.cutoffPotential, ContinuousMap.comp_apply,
      ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.coe_sum,
      Finset.sum_apply, ContinuousMap.const_apply, ContinuousMap.coe_mk]
    ring_nf
  have hlim : Filter.Tendsto (fun L' => Φ (infraredPartialSum om L')) Filter.atTop
      (nhds (Φ (H om))) := (hΦ.tendsto (H om)).comp hom
  have hU := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hlim)
    (closedCube z r hr : Set (SpatialCoordinates d)) (closedCube z r hr).isCompact
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hU ε hε)
  refine ⟨L₀, fun L' hL' => ?_⟩
  filter_upwards [aux_prop_growth_macro_energy_coeff_ae M
      (fun om' => infraredPartialSum om' L') om N z hr,
    ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy hyQ
  rw [hy, hΦeq, hΦeq, abs_sub_comm, ← Real.dist_eq]
  exact hL₀ L' hL' y (centeredCube_subset_closedCube z hr hyQ)





end Paper

/-!
# Middle scales of an arbitrary-side cube

The per-sample middle-scale estimate uses the finite-infrared helpers
`aux_prop_growth_macro_energy_finite_identity/_tendsto` proved above.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The unit-cube estimate for a model `M'` at one sample, from the proved unit-side
recurrence (`aux_aux_macro_energy_recurrence_recurrence_om`) with `R = 1`. -/
theorem aux_prop_growth_macro_energy_unit_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg' : in_6_16 d M')
    (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg'.alphaRange)
    (H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (om' : BilateralField d)
    (hom' : Filter.Tendsto (infraredPartialSum om') Filter.atTop (nhds (H' om')))
    (z' : SpatialCoordinates d) (n P0 : ℕ)
    (hpre : ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧
      Sreg'.prefixLen (n + L') (1 - ((d : ℝ) - t1) / 4) n ((3 : ℝ) ^ n • z')
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
    (K' : ℝ)
    (hKref : ∀ x ∈ (closedCube z' 1 one_pos : Set (SpatialCoordinates d)),
      (3 : ℝ) ^ (t1 * (P0 : ℝ)) * Real.exp (|H' om' x|) ≤ K')
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F
      (volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
      |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z' 1 one_pos : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z' 1 one_pos))
    (hb : ((b : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M' H' om' n z' one_pos) F b u)
    (hKsrc : (3 : ℝ) ^ (t1 * (P0 : ℝ)) *
      sobolevCoefficientForm (cutoffPositiveCoefficient M' H' om' n z' one_pos)
        (u : SobolevData (centeredCube z' 1 one_pos))
        (u : SobolevData (centeredCube z' 1 one_pos)) ≤ K' * (Kf + Cφ) ^ 2)
    (x : SpatialCoordinates d) (ρ : ℝ)
    (hx : x ∈ (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hρN : (3 : ℝ) ^ (-(n : ℤ)) ≤ ρ) :
    localGradientEnergy (cutoffPositiveCoefficient M' H' om' n z' one_pos)
        (s := Metric.ball x ρ ∩ (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z' 1 one_pos).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z' 1 one_pos))) ≤
      2 * aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d * ρ ^ t1 * K' * (Kf + Cφ) ^ 2 := by
  have hR : (0 : ℝ) < 3 ^ n := by positivity
  have hfinc : ∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M' (fun om'' => infraredPartialSum om'' L') om' n z'
            one_pos).val y =
          cFin * (Sreg'.cutoffOn (n + L') (aux_aux_macro_energy_recurrence_relabel n om')
            ((3 : ℝ) ^ n • z') (3 ^ n) hR).val ((3 : ℝ) ^ n • y) := by
    intro L'
    obtain ⟨cFin, hcF, hae⟩ := aux_prop_growth_macro_energy_finite_identity Sreg' om' n L' z'
      one_pos (by positivity)
    refine ⟨cFin, hcF, ?_⟩
    filter_upwards [hae] with y hy
    rw [hy]
    congr 1
    exact aux_aux_macro_energy_recurrence_cutoffOn_congr Sreg' (n + L') rfl
      (by rw [zpow_natCast]) (by rw [zpow_natCast, mul_one]) _ _ (by rw [zpow_natCast])
  have hrec := aux_aux_macro_energy_recurrence_recurrence_om hd Cp hFE M' Sreg'
    Sreg'.energy_density t1 ht1 ht1' hδC hα H' om' z' one_pos n hR
    (fun L' => cutoffPositiveCoefficient M' (fun om'' => infraredPartialSum om'' L') om' n z'
      one_pos)
    hfinc (aux_prop_growth_macro_energy_finite_tendsto M' H' om' hom' n z' one_pos) P0 hpre K'
    hKref F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu hKsrc x ρ 1 hx hρ hρ1 le_rfl hρN
  set Z := aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d with hZ
  have hZ0 : 0 ≤ Z := aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 < t1 := by linarith
  have h3P : 1 ≤ (3 : ℝ) ^ (t1 * (P0 : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg ht10.le (Nat.cast_nonneg _))
  set a := cutoffPositiveCoefficient M' H' om' n z' one_pos
  have hform0 := sobolevCoefficientForm_nonneg a (u : SobolevData (centeredCube z' 1 one_pos))
  have hform : sobolevCoefficientForm a (u : SobolevData (centeredCube z' 1 one_pos))
      (u : SobolevData (centeredCube z' 1 one_pos)) ≤ K' * (Kf + Cφ) ^ 2 :=
    (le_mul_of_one_le_left hform0 h3P).trans hKsrc
  have hB1 : localGradientEnergy a
      (s := Metric.ball x 1 ∩ (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (centeredCube z' 1 one_pos).isOpen.measurableSet)
      (sobolevGradient (u : SobolevData (centeredCube z' 1 one_pos))) ≤ K' * (Kf + Cφ) ^ 2 :=
    (localGradientEnergy_le _ _ _).trans hform
  have hρt : 0 ≤ ρ ^ t1 := Real.rpow_nonneg hρ.le _
  rw [div_one] at hrec
  calc _ ≤ _ := hrec
    _ ≤ Z * (ρ ^ t1 * (K' * (Kf + Cφ) ^ 2) + ρ ^ t1 * K' * (Kf + Cφ) ^ 2) := by
        gcongr
    _ = 2 * Z * ρ ^ t1 * K' * (Kf + Cφ) ^ 2 := by ring

/-- The middle-scale majorant. -/
def aux_prop_growth_macro_energy_Kmid (d : ℕ) (Z t1 r E P0 Rs Kg : ℝ) : ℝ :=
  18 * Z * (3 : ℝ) ^ t1 * (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1)) * E ^ 3 *
    ((3 : ℝ) ^ (t1 * P0) * (Rs + E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg))

/-- The pulled-back coefficient relation on the physical cube. -/
theorem aux_prop_growth_macro_energy_coef_rel {d : ℕ} (M M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (om om' : BilateralField d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (k n : ℕ) (c : ℝ)
    (hcoefid : ∀ x : SpatialCoordinates d,
      cutoffCoefficient M H om (n + k) (r • x) = c * cutoffCoefficient M' H' om' n x) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om (n + k) z hr).val x =
        c * (cutoffPositiveCoefficient M' H' om' n (r⁻¹ • z) one_pos).val (r⁻¹ • x) := by
  have hri : 0 < r⁻¹ := inv_pos.2 hr
  have hTQ := aux_prop_growth_macro_energy_cube_eq_inv_smul z hr one_pos
  have h1 := aux_aux_macro_energy_recurrence_coeff_ae M H om (n + k) z hr
  have h2 := aux_aux_macro_energy_recurrence_coeff_ae M' H' om' n (r⁻¹ • z) one_pos
  have h2' := aux_aux_macro_energy_recurrence_ae_pull hri
    (centeredCube z r hr).isOpen.measurableSet
    (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet hTQ h2
  filter_upwards [h1, h2'] with y hy1 hy2
  rw [hy1, hy2, ← hcoefid, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

/-- Source and datum sizes before and after the transfer. -/
theorem aux_prop_growth_macro_energy_sum_sq {c E r Kf Cphi : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hr1 : r ≤ 1) (hcE : c ≤ E) (hcE' : c⁻¹ ≤ E) (hE1 : 1 ≤ E) (hKf : 0 ≤ Kf) (hC : 0 ≤ Cphi) :
    (Kf + Cphi) ^ 2 ≤ E ^ 2 * ((r⁻¹) ^ 2) ^ 2 * (c⁻¹ * r ^ 2 * Kf + 3 * Cphi) ^ 2 ∧
      (c⁻¹ * r ^ 2 * Kf + 3 * Cphi) ^ 2 ≤ 9 * E ^ 2 * (Kf + Cphi) ^ 2 := by
  have hri1 : 1 ≤ r⁻¹ := (one_le_inv₀ hr).2 hr1
  have hri2 : 1 ≤ (r⁻¹) ^ 2 := one_le_pow₀ hri1
  have hEr : 1 ≤ E * (r⁻¹) ^ 2 := by nlinarith
  have hEc : 1 ≤ E * c⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hc, one_mul]; exact hcE
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hrr : (r⁻¹) ^ 2 * r ^ 2 = 1 := by field_simp
  constructor
  · have h1 : Kf ≤ E * (r⁻¹) ^ 2 * (c⁻¹ * r ^ 2 * Kf) := by
      have : E * (r⁻¹) ^ 2 * (c⁻¹ * r ^ 2 * Kf) = (E * c⁻¹) * Kf := by
        calc E * (r⁻¹) ^ 2 * (c⁻¹ * r ^ 2 * Kf) = (E * c⁻¹) * ((r⁻¹) ^ 2 * r ^ 2) * Kf := by ring
          _ = (E * c⁻¹) * Kf := by rw [hrr, mul_one]
      rw [this]
      nlinarith
    have h2 : Cphi ≤ E * (r⁻¹) ^ 2 * (3 * Cphi) := by nlinarith
    have hsum : Kf + Cphi ≤ E * (r⁻¹) ^ 2 * (c⁻¹ * r ^ 2 * Kf + 3 * Cphi) := by nlinarith
    have h0 : 0 ≤ Kf + Cphi := by positivity
    calc (Kf + Cphi) ^ 2 ≤ (E * (r⁻¹) ^ 2 * (c⁻¹ * r ^ 2 * Kf + 3 * Cphi)) ^ 2 :=
          pow_le_pow_left₀ h0 hsum 2
      _ = _ := by ring
  · have h1 : c⁻¹ * r ^ 2 ≤ E := by
      have : c⁻¹ * r ^ 2 ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left hr2 (inv_pos.2 hc).le
      linarith
    have h1' : c⁻¹ * r ^ 2 * Kf ≤ E * Kf := mul_le_mul_of_nonneg_right h1 hKf
    have h2 : 0 ≤ c⁻¹ * r ^ 2 * Kf + 3 * Cphi := by positivity
    have h3 : c⁻¹ * r ^ 2 * Kf + 3 * Cphi ≤ 3 * E * (Kf + Cphi) := by nlinarith
    calc (c⁻¹ * r ^ 2 * Kf + 3 * Cphi) ^ 2 ≤ (3 * E * (Kf + Cphi)) ^ 2 :=
          pow_le_pow_left₀ h2 h3 2
      _ = 9 * E ^ 2 * (Kf + Cphi) ^ 2 := by ring

/-- The source bound of the transferred problem. -/
theorem aux_prop_growth_macro_energy_ksrc_arith (d : ℕ) {c E r Kg Rs p3 form form' A B : ℝ}
    (hr : 0 < r) (hcE' : c⁻¹ ≤ E) (hE1 : 1 ≤ E) (hKg : 0 ≤ Kg) (hRs : 0 ≤ Rs)
    (hp3 : 0 ≤ p3) (hform0 : 0 ≤ form)
    (hform' : form' = c⁻¹ * (r⁻¹) ^ d * r ^ 2 * form) (hglob : form ≤ Kg * A)
    (hA : A ≤ E ^ 2 * ((r⁻¹) ^ 2) ^ 2 * B) (hB : 0 ≤ B) :
    p3 * form' ≤ p3 * (Rs + E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg) * B := by
  have hE0 : 0 ≤ E := le_trans zero_le_one hE1
  have hri : 0 < r⁻¹ := inv_pos.2 hr
  have hstep : form' ≤ E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg * B := by
    rw [hform']
    calc c⁻¹ * (r⁻¹) ^ d * r ^ 2 * form ≤ E * (r⁻¹) ^ d * r ^ 2 * (Kg * A) := by
          have h0 : 0 ≤ (r⁻¹) ^ d * r ^ 2 := by positivity
          have := mul_le_mul hcE' (le_refl ((r⁻¹) ^ d * r ^ 2)) h0 hE0
          calc c⁻¹ * (r⁻¹) ^ d * r ^ 2 * form = (c⁻¹ * ((r⁻¹) ^ d * r ^ 2)) * form := by ring
            _ ≤ (E * ((r⁻¹) ^ d * r ^ 2)) * (Kg * A) :=
                mul_le_mul this hglob hform0 (by positivity)
            _ = E * (r⁻¹) ^ d * r ^ 2 * (Kg * A) := by ring
      _ ≤ E * (r⁻¹) ^ d * r ^ 2 * (Kg * (E ^ 2 * ((r⁻¹) ^ 2) ^ 2 * B)) := by
          gcongr
      _ = E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg * B := by
          have hrr : r ^ 2 * ((r⁻¹) ^ 2) ^ 2 = (r⁻¹) ^ 2 := by field_simp
          calc E * (r⁻¹) ^ d * r ^ 2 * (Kg * (E ^ 2 * ((r⁻¹) ^ 2) ^ 2 * B))
              = E ^ 3 * ((r⁻¹) ^ d * (r ^ 2 * ((r⁻¹) ^ 2) ^ 2)) * Kg * B := by ring
            _ = _ := by rw [hrr]
  have hW0 : 0 ≤ E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg := by positivity
  calc p3 * form' ≤ p3 * (E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg * B) :=
        mul_le_mul_of_nonneg_left hstep hp3
    _ ≤ p3 * (Rs + E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg) * B := by
        rw [mul_assoc p3]
        refine mul_le_mul_of_nonneg_left ?_ hp3
        nlinarith

/-- The unit radius and its comparison with the physical one. -/
theorem aux_prop_growth_macro_energy_radius {r rad t1 : ℝ} {n k : ℕ} (hr : 0 < r)
    (hrad0 : 0 < rad) (hradr : rad ≤ r) (hrk3 : r * (3 : ℝ) ^ k ≤ 3)
    (hradN : (3 : ℝ) ^ (-((n + k : ℕ) : ℤ)) ≤ rad) (ht1 : 0 ≤ t1) :
    0 < max (rad / r) ((3 : ℝ) ^ (-(n : ℤ))) ∧ max (rad / r) ((3 : ℝ) ^ (-(n : ℤ))) ≤ 1 ∧
      (max (rad / r) ((3 : ℝ) ^ (-(n : ℤ)))) ^ t1 ≤ (3 : ℝ) ^ t1 * rad ^ t1 * r ^ (-t1) := by
  have hρ'0 : 0 < max (rad / r) ((3 : ℝ) ^ (-(n : ℤ))) :=
    lt_of_lt_of_le (div_pos hrad0 hr) (le_max_left _ _)
  refine ⟨hρ'0, max_le ((div_le_one hr).2 hradr) (zpow_le_one_of_nonpos₀ (by norm_num)
    (by simp)), ?_⟩
  have hρ'3 : max (rad / r) ((3 : ℝ) ^ (-(n : ℤ))) ≤ 3 * (rad / r) := by
    refine max_le (by linarith [div_pos hrad0 hr]) ?_
    have h3k : (3 : ℝ) ^ (-(n : ℤ)) = (3 : ℝ) ^ k * (3 : ℝ) ^ (-((n + k : ℕ) : ℤ)) := by
      rw [← zpow_natCast (3 : ℝ) k, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1; push_cast; ring
    rw [h3k]
    have hk3 : (3 : ℝ) ^ k ≤ 3 / r := by rw [le_div_iff₀ hr]; linarith
    calc (3 : ℝ) ^ k * (3 : ℝ) ^ (-((n + k : ℕ) : ℤ)) ≤ (3 / r) * rad :=
          mul_le_mul hk3 hradN (by positivity) (by positivity)
      _ = 3 * (rad / r) := by ring
  calc (max (rad / r) ((3 : ℝ) ^ (-(n : ℤ)))) ^ t1 ≤ (3 * (rad / r)) ^ t1 :=
        Real.rpow_le_rpow hρ'0.le hρ'3 ht1
    _ = (3 : ℝ) ^ t1 * rad ^ t1 * r ^ (-t1) := by
        rw [Real.mul_rpow (by norm_num) (div_pos hrad0 hr).le,
          Real.div_rpow hrad0.le hr.le, Real.rpow_neg hr.le]
        ring

/-- The closing arithmetic of the middle scales. -/
theorem aux_prop_growth_macro_energy_middle_arith (d : ℕ) {Γ c E r Z t1 rad K' Kf Cphi : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hcE : c ≤ E) (hZ : 0 ≤ Z) (hK' : 0 ≤ K') (hrad : 0 < rad)
    (hkey : c⁻¹ * (r⁻¹) ^ d * r ^ 2 * Γ ≤
      2 * Z * ((3 : ℝ) ^ t1 * rad ^ t1 * r ^ (-t1)) * K' * (9 * E ^ 2 * (Kf + Cphi) ^ 2)) :
    Γ ≤ 18 * Z * (3 : ℝ) ^ t1 * (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1)) * E ^ 3 * K' *
      (Kf + Cphi) ^ 2 * rad ^ t1 := by
  have hinv : c * r ^ d * (r⁻¹) ^ 2 * (c⁻¹ * (r⁻¹) ^ d * r ^ 2) = 1 := by
    have e1 : r ^ d * (r⁻¹) ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]
    have e2 : (r⁻¹) ^ 2 * r ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
    calc c * r ^ d * (r⁻¹) ^ 2 * (c⁻¹ * (r⁻¹) ^ d * r ^ 2)
        = (c * c⁻¹) * (r ^ d * (r⁻¹) ^ d) * ((r⁻¹) ^ 2 * r ^ 2) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hc.ne', e1, e2, one_mul, one_mul]
  have hE0 : 0 ≤ E := hc.le.trans hcE
  have hΓ : Γ = c * r ^ d * (r⁻¹) ^ 2 * (c⁻¹ * (r⁻¹) ^ d * r ^ 2 * Γ) := by
    rw [← mul_assoc, hinv, one_mul]
  have hA : 0 ≤ 2 * Z * ((3 : ℝ) ^ t1 * rad ^ t1 * r ^ (-t1)) * K' * 9 * (Kf + Cphi) ^ 2 *
      r ^ d * (r⁻¹) ^ 2 := by positivity
  have hcE3 : c * E ^ 2 ≤ E ^ 3 := by
    calc c * E ^ 2 ≤ E * E ^ 2 := mul_le_mul_of_nonneg_right hcE (sq_nonneg _)
      _ = E ^ 3 := by ring
  calc Γ = c * r ^ d * (r⁻¹) ^ 2 * (c⁻¹ * (r⁻¹) ^ d * r ^ 2 * Γ) := hΓ
    _ ≤ c * r ^ d * (r⁻¹) ^ 2 *
        (2 * Z * ((3 : ℝ) ^ t1 * rad ^ t1 * r ^ (-t1)) * K' * (9 * E ^ 2 * (Kf + Cphi) ^ 2)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (c * E ^ 2) * (2 * Z * ((3 : ℝ) ^ t1 * rad ^ t1 * r ^ (-t1)) * K' * 9 *
          (Kf + Cphi) ^ 2 * r ^ d * (r⁻¹) ^ 2) := by ring
    _ ≤ E ^ 3 * (2 * Z * ((3 : ℝ) ^ t1 * rad ^ t1 * r ^ (-t1)) * K' * 9 *
          (Kf + Cphi) ^ 2 * r ^ d * (r⁻¹) ^ 2) := mul_le_mul_of_nonneg_right hcE3 hA
    _ = _ := by ring

/-- **Middle scales `3^{-N} ≤ ρ ≤ r` of an arbitrary side `r = s 3^{-k}`**, for one sample: the
physical problem is transferred to the unit cube of the residual model, where the unit-side
recurrence applies (paper lines 598, 605–640). -/
theorem aux_prop_growth_macro_energy_middle {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg' : in_6_16 d M')
    (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg'.alphaRange)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (om om' : BilateralField d)
    (hom' : Filter.Tendsto (infraredPartialSum om') Filter.atTop (nhds (H' om')))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (k n : ℕ)
    (hrk3 : r * (3 : ℝ) ^ k ≤ 3)
    (c E : ℝ) (hc : 0 < c) (hcE : c ≤ E) (hcE' : c⁻¹ ≤ E) (hE1 : 1 ≤ E)
    (hcoefid : ∀ x : SpatialCoordinates d,
      cutoffCoefficient M H om (n + k) (r • x) = c * cutoffCoefficient M' H' om' n x)
    (P0 : ℕ)
    (hpre : ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧
      Sreg'.prefixLen (n + L') (1 - ((d : ℝ) - t1) / 4) n ((3 : ℝ) ^ n • (r⁻¹ • z))
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
    (Rs : ℝ) (hRs : ∀ x ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp (|H' om' x|) ≤ Rs)
    (Kg : ℝ) (hKg0 : 0 ≤ Kg)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om (n + k) z hr) F b u)
    (hglob : sobolevCoefficientForm (cutoffPositiveCoefficient M H om (n + k) z hr)
        (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) ≤
      Kg * (Kf + Cphi) ^ 2)
    (x : SpatialCoordinates d) (rad : ℝ) (hx : x ∈ centeredCube z r hr) (hrad0 : 0 < rad)
    (hradr : rad ≤ r) (hradN : (3 : ℝ) ^ (-((n + k : ℕ) : ℤ)) ≤ rad) :
    localGradientEnergy (cutoffPositiveCoefficient M H om (n + k) z hr)
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
      aux_prop_growth_macro_energy_Kmid d (aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d)
          t1 r E P0 Rs Kg * (Kf + Cphi) ^ 2 * rad ^ t1 := by
  have hri : 0 < r⁻¹ := inv_pos.2 hr
  have hQT := aux_prop_growth_macro_energy_cube_eq_smul z hr one_pos
  have hTQ := aux_prop_growth_macro_energy_cube_eq_inv_smul z hr one_pos
  have hcoef := aux_prop_growth_macro_energy_coef_rel M M' H H' om om' z hr k n c hcoefid
  obtain ⟨F', b', v, hF'm, hF'b, hb', hsol', hloc, hform⟩ :=
    aux_prop_growth_macro_energy_dirichlet_transfer hr hc hQT hTQ _ _ hcoef F Kf hFm hFb phi b u
      hb hu
  have hphi' : ContDiff ℝ 2 (fun y : SpatialCoordinates d => phi (r • y)) :=
    hphi.comp (contDiff_id.const_smul r)
  have hCphi' := aux_prop_growth_macro_energy_c2Norm_dilate z hr hr1 one_pos phi hphi Cphi hCphi
  have hCphi0 : 0 ≤ Cphi := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ phi).trans hCphi
  have hKf' : 0 ≤ c⁻¹ * r ^ 2 * Kf := by positivity
  have hZ0 := aux_aux_macro_energy_recurrence_Z_nonneg Sreg'.C Cp t1 d
  have hE0 : 0 ≤ E := le_trans zero_le_one hE1
  have h3P0 : 0 ≤ (3 : ℝ) ^ (t1 * (P0 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hRs0 : 0 ≤ Rs := (Real.exp_pos _).le.trans (hRs (r⁻¹ • z)
    (Metric.mem_closedBall_self (by norm_num)))
  have hW0 : 0 ≤ E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg := by positivity
  have hK'0 : 0 ≤ (3 : ℝ) ^ (t1 * (P0 : ℝ)) * (Rs + E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg) := by
    positivity
  have hKref : ∀ y ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      (3 : ℝ) ^ (t1 * (P0 : ℝ)) * Real.exp (|H' om' y|) ≤
        (3 : ℝ) ^ (t1 * (P0 : ℝ)) * (Rs + E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg) := by
    intro y hy
    exact mul_le_mul_of_nonneg_left ((hRs y hy).trans (le_add_of_nonneg_right hW0)) h3P0
  obtain ⟨hsq1, hsq2⟩ := aux_prop_growth_macro_energy_sum_sq hc hr hr1 hcE hcE' hE1 hKf hCphi0
  have hKsrc := aux_prop_growth_macro_energy_ksrc_arith d hr hcE' hE1 hKg0 hRs0 h3P0
    (sobolevCoefficientForm_nonneg _ _) hform hglob hsq1 (sq_nonneg _)
  have hx' : r⁻¹ • x ∈ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)) := by
    rw [hTQ]; exact Set.smul_mem_smul_set hx
  have ht10 : 0 < t1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hρ'0, hρ'1, hρpow⟩ := aux_prop_growth_macro_energy_radius hr hrad0 hradr hrk3 hradN
    ht10.le (t1 := t1)
  have hunit := aux_prop_growth_macro_energy_unit_bound hd Cp hFE M' Sreg' t1 ht1 ht1' hδC hα H'
    om' hom' (r⁻¹ • z) n P0 hpre _ hKref F' (c⁻¹ * r ^ 2 * Kf) hKf' hF'm hF'b
    (fun y => phi (r • y)) (3 * Cphi) hphi' hCphi' b' v hb' hsol' hKsrc (r⁻¹ • x)
    (max (rad / r) ((3 : ℝ) ^ (-(n : ℤ)))) hx' hρ'0 hρ'1 (le_max_right _ _)
  have hS : MeasurableSet (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet
  have hball : r⁻¹ • (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) =
      Metric.ball (r⁻¹ • x) (rad / r) ∩
        (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)) := by
    rw [aux_aux_macro_energy_recurrence_ball_inter_smul x rad _ hri, ← hTQ, inv_mul_eq_div]
  have hrS : MeasurableSet
      (r⁻¹ • (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
    rw [hball]
    exact isOpen_ball.measurableSet.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet
  have hl := hloc _ hS hrS
  rw [aux_aux_macro_energy_recurrence_localEnergy_congr _ hball hrS
    (isOpen_ball.measurableSet.inter
      (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet)] at hl
  have hmono := aux_aux_macro_energy_recurrence_localEnergy_mono
    (cutoffPositiveCoefficient M' H' om' n (r⁻¹ • z) one_pos)
    (isOpen_ball.measurableSet.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet :
      MeasurableSet (Metric.ball (r⁻¹ • x) (rad / r) ∩
        (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))))
    (isOpen_ball.measurableSet.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet :
      MeasurableSet (Metric.ball (r⁻¹ • x) (max (rad / r) ((3 : ℝ) ^ (-(n : ℤ)))) ∩
        (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))))
    (Set.inter_subset_inter_left _ (Metric.ball_subset_ball (le_max_left _ _)))
    (sobolevGradient (v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)))
  have hkey : c⁻¹ * (r⁻¹) ^ d * r ^ 2 *
      localGradientEnergy (cutoffPositiveCoefficient M H om (n + k) z hr) hS
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
      2 * aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d *
        ((3 : ℝ) ^ t1 * rad ^ t1 * r ^ (-t1)) *
        ((3 : ℝ) ^ (t1 * (P0 : ℝ)) * (Rs + E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg)) *
        (9 * E ^ 2 * (Kf + Cphi) ^ 2) := by
    rw [← hl]
    refine hmono.trans (hunit.trans ?_)
    gcongr
  have hfin := aux_prop_growth_macro_energy_middle_arith d hc hr hcE hZ0 hK'0 hrad0 hkey
  refine hfin.trans (le_of_eq ?_)
  unfold aux_prop_growth_macro_energy_Kmid
  ring

/-- Moments of the middle-scale majorant by Hölder aggregation. -/
theorem aux_prop_growth_macro_energy_kmid_moment {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (P : ℝ) (hP : 1 ≤ P) (C0 K1 : ℝ) (hC0 : 0 ≤ C0) (hK1 : 0 ≤ K1) (E X R G : α → ℝ)
    (hE : AEStronglyMeasurable E μ) (hX : AEStronglyMeasurable X μ)
    (hR : AEStronglyMeasurable R μ) (hG : AEStronglyMeasurable G μ) :
    eLpNorm (fun a => C0 * E a ^ 3 * (X a * (R a + E a ^ 3 * K1 * G a))) (ENNReal.ofReal P) μ ≤
      ENNReal.ofReal C0 * (eLpNorm (fun a => E a ^ 3) (ENNReal.ofReal (2 * P)) μ *
          (eLpNorm X (ENNReal.ofReal (2 * (2 * P))) μ * eLpNorm R (ENNReal.ofReal (2 * (2 * P))) μ)) +
        ENNReal.ofReal (C0 * K1) * (eLpNorm (fun a => E a ^ 6) (ENNReal.ofReal (2 * P)) μ *
          (eLpNorm X (ENNReal.ofReal (2 * (2 * P))) μ *
            eLpNorm G (ENNReal.ofReal (2 * (2 * P))) μ)) := by
  have hP1 : 1 ≤ ENNReal.ofReal P := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hP
  have hfun : (fun a => C0 * E a ^ 3 * (X a * (R a + E a ^ 3 * K1 * G a))) =
      (fun a => C0 • (E a ^ 3 * (X a * R a))) + (fun a => (C0 * K1) • (E a ^ 6 * (X a * G a))) := by
    funext a
    simp only [Pi.add_apply, smul_eq_mul]
    ring
  have hE3 : AEStronglyMeasurable (fun a => E a ^ 3) μ := hE.pow 3
  have hE6 : AEStronglyMeasurable (fun a => E a ^ 6) μ := hE.pow 6
  have h1 : AEStronglyMeasurable (fun a => C0 • (E a ^ 3 * (X a * R a))) μ :=
    (hE3.mul (hX.mul hR)).const_smul C0
  have h2 : AEStronglyMeasurable (fun a => (C0 * K1) • (E a ^ 6 * (X a * G a))) μ :=
    (hE6.mul (hX.mul hG)).const_smul (C0 * K1)
  rw [hfun]
  refine (eLpNorm_add_le h1 h2 hP1).trans (add_le_add ?_ ?_)
  · refine (eLpNorm_const_smul_le (c := C0)
      (f := fun a => E a ^ 3 * (X a * R a))).trans ?_
    rw [Real.enorm_of_nonneg hC0]
    refine mul_le_mul_right ?_ _
    refine (aux_aux_macro_moment_bank_product_moment μ P _ _ hE3 (hX.mul hR)).trans ?_
    exact mul_le_mul_right (aux_aux_macro_moment_bank_product_moment μ (2 * P) X R hX hR) _
  · refine (eLpNorm_const_smul_le (c := C0 * K1)
      (f := fun a => E a ^ 6 * (X a * G a))).trans ?_
    rw [Real.enorm_of_nonneg (mul_nonneg hC0 hK1)]
    refine mul_le_mul_right ?_ _
    refine (aux_aux_macro_moment_bank_product_moment μ P _ _ hE6 (hX.mul hG)).trans ?_
    exact mul_le_mul_right (aux_aux_macro_moment_bank_product_moment μ (2 * P) X G hX hG) _

/-- At the initial scales and the early cutoffs, the global energy suffices. -/
theorem aux_prop_growth_macro_energy_global_factor {r rad t1 : ℝ} {N k : ℕ} (hr : 0 < r)
    (hr1 : r ≤ 1) (hrad0 : 0 < rad) (ht1 : 0 ≤ t1) (hradN : (3 : ℝ) ^ (-(N : ℤ)) ≤ rad)
    (hcase : ¬(k ≤ N ∧ rad < r)) :
    1 ≤ (3 : ℝ) ^ ((k : ℝ) * t1) * r ^ (-t1) * rad ^ t1 := by
  have h3 : 1 ≤ (3 : ℝ) ^ ((k : ℝ) * t1) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg _) ht1)
  have hr' : 1 ≤ r ^ (-t1) := by
    rw [Real.rpow_neg hr.le]
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hr _)).2 (Real.rpow_le_one hr.le hr1 ht1)
  rw [not_and_or, not_le, not_lt] at hcase
  rcases hcase with hNk | hrr
  · -- `N < k`: `rad ≥ 3^{-N} ≥ 3^{-k}`
    have hk : (3 : ℝ) ^ (-(k : ℤ)) ≤ rad := by
      refine le_trans ?_ hradN
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hpow : ((3 : ℝ) ^ (-(k : ℤ))) ^ t1 ≤ rad ^ t1 :=
      Real.rpow_le_rpow (by positivity) hk ht1
    have heq : ((3 : ℝ) ^ (-(k : ℤ))) ^ t1 * (3 : ℝ) ^ ((k : ℝ) * t1) = 1 := by
      rw [zpow_neg, zpow_natCast, Real.inv_rpow (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), inv_mul_cancel₀ (by positivity)]
    have hkr : 1 ≤ (3 : ℝ) ^ ((k : ℝ) * t1) * rad ^ t1 := by
      calc (1 : ℝ) = ((3 : ℝ) ^ (-(k : ℤ))) ^ t1 * (3 : ℝ) ^ ((k : ℝ) * t1) := heq.symm
        _ ≤ rad ^ t1 * (3 : ℝ) ^ ((k : ℝ) * t1) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
        _ = _ := by ring
    calc (1 : ℝ) ≤ 1 * ((3 : ℝ) ^ ((k : ℝ) * t1) * rad ^ t1) := by linarith
      _ ≤ r ^ (-t1) * ((3 : ℝ) ^ ((k : ℝ) * t1) * rad ^ t1) :=
          mul_le_mul_of_nonneg_right hr' (by positivity)
      _ = _ := by ring
  · -- `rad ≥ r`
    have hrr' : 1 ≤ r ^ (-t1) * rad ^ t1 := by
      rw [Real.rpow_neg hr.le, ← div_eq_inv_mul, ← Real.div_rpow hrad0.le hr.le]
      exact Real.one_le_rpow ((one_le_div hr).2 hrr) ht1
    calc (1 : ℝ) ≤ 1 * (r ^ (-t1) * rad ^ t1) := by linarith
      _ ≤ (3 : ℝ) ^ ((k : ℝ) * t1) * (r ^ (-t1) * rad ^ t1) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = _ := by ring

end Paper

/-!
# The all-cube macro energy
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The residual reference majorant on the closed unit cube about `z / r`. -/
def aux_prop_growth_macro_energy_Rs {d : ℕ} (H' : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (om' : BilateralField d) : ℝ :=
  Real.exp ‖(H' om').restrict ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))‖

/-- The final all-cube majorant: the global-energy term at every cutoff, plus the middle-scale
term from the residual model for the cutoffs `N ≥ k`. -/
def aux_prop_growth_macro_energy_Kfinal {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (kk : ℕ)
    (r t1 Z : ℝ) (Lm : ℕ → BilateralField d → ℕ) (Rs : BilateralField d → ℝ)
    (Kg : ℕ → BilateralField d → ℝ) (N : ℕ) (om : BilateralField d) : ℝ :=
  (3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) * Kg N om +
    (if kk ≤ N then
      aux_prop_growth_macro_energy_Kmid d Z t1 r (aux_prop_growth_macro_energy_env M kk om)
        (Lm (N - kk) (MacroAllCube.residualShift r kk om))
        (Rs (MacroAllCube.residualShift r kk om)) (Kg N om)
    else 0)

theorem aux_prop_growth_macro_energy_Kmid_nonneg (d : ℕ) {Z t1 r E P0 Rs Kg : ℝ} (hZ : 0 ≤ Z)
    (hr : 0 < r) (hE : 1 ≤ E) (hRs : 0 ≤ Rs) (hKg : 0 ≤ Kg) :
    0 ≤ aux_prop_growth_macro_energy_Kmid d Z t1 r E P0 Rs Kg := by
  unfold aux_prop_growth_macro_energy_Kmid
  have hE0 : 0 ≤ E := le_trans zero_le_one hE
  positivity

/-- **The almost-sure all-cube bound**, for a model `M'` carrying the residual structure. -/
theorem aux_prop_growth_macro_energy_ae_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg' : in_6_16 d M')
    (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg'.alphaRange)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (hH' : InfraredCharacterization M' H')
    (htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M'.P = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (kk : ℕ)
    (hk3 : r * (3 : ℝ) ^ kk ≤ 3)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure)
    (hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤ aux_prop_growth_macro_energy_env M kk om)
    (Lm : ℕ → BilateralField d → ℕ)
    (hLpre : ∀ᵐ om' ∂(chaosSampleLaw M').toMeasure, ∀ N L0 : ℕ,
      ∃ L' : ℕ, L0 ≤ L' ∧
        Sreg'.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • (r⁻¹ • z))
          (aux_aux_macro_moment_bank_relabel N om') ≤ Lm N om')
    (Kg : ℕ → BilateralField d → ℝ) (hKg0 : ∀ N om, 0 ≤ Kg N om)
    (hKgsrc : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
        ContDiff ℝ 2 phi →
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ),
          x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
          (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
          localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
              (s := Metric.ball x rad ∩
                (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter
                (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
            aux_prop_growth_macro_energy_Kfinal M kk r t1
                (aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d) Lm
                (aux_prop_growth_macro_energy_Rs H' z r) Kg N om * (Kf + Cphi) ^ 2 * rad ^ t1 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 < t1 := by linarith
  filter_upwards [hKgsrc,
    aux_prop_growth_macro_energy_coeff_identity M M' htau H H' hH hH' r kk hT,
    hT.quasiMeasurePreserving.ae hLpre] with om hsrc hcoef hpre
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve x rad hx hrad0 hrad1 hradN
  have hglob := hsrc N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
  have hZ0 := aux_aux_macro_energy_recurrence_Z_nonneg Sreg'.C Cp t1 d
  have hcg0 : 0 ≤ (3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) * Kg N om := by
    have := hKg0 N om
    positivity
  have hsq0 : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
  have hradt : 0 ≤ rad ^ t1 := Real.rpow_nonneg hrad0.le _
  unfold aux_prop_growth_macro_energy_Kfinal
  by_cases hcase : kk ≤ N ∧ rad < r
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + kk := ⟨N - kk, by omega⟩
    rw [if_pos hcase.1, Nat.add_sub_cancel]
    have hRdom : ∀ y ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
        Real.exp (|H' (MacroAllCube.residualShift r kk om) y|) ≤
          aux_prop_growth_macro_energy_Rs H' z r (MacroAllCube.residualShift r kk om) := by
      intro y hy
      refine Real.exp_le_exp.2 ?_
      have h := ContinuousMap.norm_coe_le_norm
        ((H' (MacroAllCube.residualShift r kk om)).restrict
          ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))) ⟨y, hy⟩
      rwa [Real.norm_eq_abs] at h
    have hmid := aux_prop_growth_macro_energy_middle hd Cp hFE M M' Sreg' t1 ht1 ht1' hδC hα H H'
      om (MacroAllCube.residualShift r kk om) hcoef.1 z r hr hr1 kk n hk3
      (aux_prop_growth_macro_energy_shiftC M M' kk n om) (aux_prop_growth_macro_energy_env M kk om)
      (aux_prop_growth_macro_energy_shiftC_pos M M' kk n om) (hshift n om).1 (hshift n om).2
      (aux_prop_growth_macro_energy_one_le_env M kk om) (hcoef.2 n)
      (Lm n (MacroAllCube.residualShift r kk om)) (hpre n)
      (aux_prop_growth_macro_energy_Rs H' z r (MacroAllCube.residualShift r kk om)) hRdom
      (Kg (n + kk) om) (hKg0 _ _) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve hglob x rad
      hx hrad0 hcase.2.le hradN
    refine hmid.trans ?_
    have hmul := mul_le_mul_of_nonneg_right hcg0 (mul_nonneg hsq0 hradt)
    nlinarith
  · have hif0 : 0 ≤ (if kk ≤ N then
        aux_prop_growth_macro_energy_Kmid d (aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d) t1 r
          (aux_prop_growth_macro_energy_env M kk om)
          (Lm (N - kk) (MacroAllCube.residualShift r kk om))
          (aux_prop_growth_macro_energy_Rs H' z r (MacroAllCube.residualShift r kk om)) (Kg N om)
        else 0) := by
      split_ifs
      · exact aux_prop_growth_macro_energy_Kmid_nonneg d hZ0 hr
          (aux_prop_growth_macro_energy_one_le_env M kk om) (Real.exp_pos _).le (hKg0 N om)
      · exact le_refl 0
    have hfac := aux_prop_growth_macro_energy_global_factor hr hr1 hrad0 ht10.le hradN hcase
    have hloc : localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
          (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) :=
      localGradientEnergy_le _ _ _
    have hK0 : 0 ≤ Kg N om * (Kf + Cphi) ^ 2 := mul_nonneg (hKg0 N om) hsq0
    calc _ ≤ Kg N om * (Kf + Cphi) ^ 2 := hloc.trans hglob
      _ ≤ Kg N om * (Kf + Cphi) ^ 2 * ((3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) * rad ^ t1) :=
          le_mul_of_one_le_right hK0 hfac
      _ = (3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) * Kg N om * (Kf + Cphi) ^ 2 * rad ^ t1 := by ring
      _ ≤ _ := by
          have := mul_nonneg hif0 (mul_nonneg hsq0 hradt)
          nlinarith

/-- **Moments of the final majorant**, uniformly in the cutoff. -/
theorem aux_prop_growth_macro_energy_Kfinal_moment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (kk : ℕ) (r t1 Z Pexp : ℝ) (hr : 0 < r)
    (hZ0 : 0 ≤ Z) (hP1 : 1 ≤ Pexp)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure)
    (Lm : ℕ → BilateralField d → ℕ) (hLmeas : ∀ n, Measurable (Lm n)) (BX : ℝ≥0∞)
    (hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M').toMeasure ≤ BX)
    (Rs : BilateralField d → ℝ) (hRsm : Measurable Rs) (BR : ℝ≥0∞)
    (hR : eLpNorm Rs (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M').toMeasure ≤ BR)
    (Kg : ℕ → BilateralField d → ℝ) (BG : ℝ≥0∞)
    (hKgm : ∀ N, AEStronglyMeasurable (Kg N) (chaosSampleLaw M).toMeasure)
    (hKg : ∀ N, eLpNorm (Kg N) (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M).toMeasure ≤ BG)
    (N : ℕ) :
    AEStronglyMeasurable (aux_prop_growth_macro_energy_Kfinal M kk r t1 Z Lm Rs Kg N)
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (aux_prop_growth_macro_energy_Kfinal M kk r t1 Z Lm Rs Kg N) (ENNReal.ofReal Pexp)
          (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1)) * BG +
          (ENNReal.ofReal (18 * Z * (3 : ℝ) ^ t1 * (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1))) *
              (eLpNorm (fun om => aux_prop_growth_macro_energy_env M kk om ^ 3)
                  (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure * (BX * BR)) +
            ENNReal.ofReal (18 * Z * (3 : ℝ) ^ t1 * (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1)) *
                ((r⁻¹) ^ d * (r⁻¹) ^ 2)) *
              (eLpNorm (fun om => aux_prop_growth_macro_energy_env M kk om ^ 6)
                  (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure * (BX * BG))) := by
  set μ := (chaosSampleLaw M).toMeasure with hμ
  have hP1' : 1 ≤ ENNReal.ofReal Pexp := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hP1
  have hle4 : ENNReal.ofReal Pexp ≤ ENNReal.ofReal (2 * (2 * Pexp)) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  set cg : ℝ := (3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) with hcg
  have hcg0 : 0 ≤ cg := by positivity
  set C0 : ℝ := 18 * Z * (3 : ℝ) ^ t1 * (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1)) with hC0
  set K1 : ℝ := (r⁻¹) ^ d * (r⁻¹) ^ 2 with hK1
  have hC00 : 0 ≤ C0 := by positivity
  have hK10 : 0 ≤ K1 := by positivity
  have hEm : AEStronglyMeasurable (aux_prop_growth_macro_energy_env M kk) μ :=
    (aux_prop_growth_macro_energy_measurable_env M kk).aestronglyMeasurable
  have hXm : ∀ n, Measurable (fun om : BilateralField d => (3 : ℝ) ^ (t1 * (Lm n om : ℝ))) :=
    fun n => measurable_const.pow (measurable_const.mul
      ((measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp (hLmeas n)))
  have hXTm : ∀ n, AEStronglyMeasurable
      (fun om => (3 : ℝ) ^ (t1 * (Lm n (MacroAllCube.residualShift r kk om) : ℝ))) μ :=
    fun n => ((hXm n).comp hT.measurable).aestronglyMeasurable
  have hRTm : AEStronglyMeasurable (fun om => Rs (MacroAllCube.residualShift r kk om)) μ :=
    (hRsm.comp hT.measurable).aestronglyMeasurable
  have hXT : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n (MacroAllCube.residualShift r kk om) : ℝ)))
      (ENNReal.ofReal (2 * (2 * Pexp))) μ ≤ BX := by
    intro n
    have h := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (2 * (2 * Pexp)))
      (hXm n).aestronglyMeasurable hT
    exact (le_of_eq h).trans (hX n)
  have hRT : eLpNorm (fun om => Rs (MacroAllCube.residualShift r kk om))
      (ENNReal.ofReal (2 * (2 * Pexp))) μ ≤ BR := by
    have h := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (2 * (2 * Pexp)))
      hRsm.aestronglyMeasurable hT
    exact (le_of_eq h).trans hR
  -- the global term
  have hglobm : AEStronglyMeasurable (fun om => cg * Kg N om) μ := (hKgm N).const_mul cg
  have hglob : eLpNorm (fun om => cg * Kg N om) (ENNReal.ofReal Pexp) μ ≤ ENNReal.ofReal cg * BG := by
    have h := eLpNorm_const_smul_le (c := cg) (f := Kg N) (p := ENNReal.ofReal Pexp) (μ := μ)
    rw [Real.enorm_of_nonneg hcg0] at h
    refine h.trans (mul_le_mul_right ?_ _)
    exact (eLpNorm_le_eLpNorm_of_exponent_le hle4 (hKgm N)).trans (hKg N)
  -- the middle term
  have hK : aux_prop_growth_macro_energy_Kfinal M kk r t1 Z Lm Rs Kg N =
      fun om => cg * Kg N om + (if kk ≤ N then
        C0 * aux_prop_growth_macro_energy_env M kk om ^ 3 *
          ((3 : ℝ) ^ (t1 * (Lm (N - kk) (MacroAllCube.residualShift r kk om) : ℝ)) *
            (Rs (MacroAllCube.residualShift r kk om) +
              aux_prop_growth_macro_energy_env M kk om ^ 3 * K1 * Kg N om)) else 0) := by
    funext om
    rfl
  rw [hK]
  by_cases hN : kk ≤ N
  · simp only [if_pos hN]
    have hmidm : AEStronglyMeasurable (fun om => C0 * aux_prop_growth_macro_energy_env M kk om ^ 3 *
        ((3 : ℝ) ^ (t1 * (Lm (N - kk) (MacroAllCube.residualShift r kk om) : ℝ)) *
          (Rs (MacroAllCube.residualShift r kk om) +
            aux_prop_growth_macro_energy_env M kk om ^ 3 * K1 * Kg N om))) μ :=
      ((hEm.pow 3).const_mul C0).mul ((hXTm (N - kk)).mul
        (hRTm.add (((hEm.pow 3).mul_const K1).mul (hKgm N))))
    refine ⟨hglobm.add hmidm, (eLpNorm_add_le hglobm hmidm hP1').trans (add_le_add hglob ?_)⟩
    refine (aux_prop_growth_macro_energy_kmid_moment μ Pexp hP1 C0 K1 hC00 hK10 _ _ _ _ hEm
      (hXTm (N - kk)) hRTm (hKgm N)).trans ?_
    gcongr
    · exact hXT _
    · exact hXT _
    · exact hKg N
  · simp only [if_neg hN, add_zero]
    refine ⟨hglobm, hglob.trans le_self_add⟩

theorem aux_prop_growth_macro_energy_allcube :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (t1 : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t1 → t1 < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (Kmac : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
            (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              Kmac N om * (Kf + Cphi) ^ 2 * rad ^ t1 := by
  intro d hd _ _ E P X S t1 k ps ht1 ht2 hps
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 < t1 := by linarith
  -- one exponent for all listed orders
  obtain ⟨Pexp, hPdef⟩ : ∃ Pexp : ℝ, Pexp = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => by linarith [hps i]
  have hP1 : 1 ≤ Pexp := by rw [hPdef]; linarith
  have hpsP : ∀ i, ps i ≤ Pexp := by
    intro i
    rw [hPdef]
    have := Finset.single_le_sum (f := ps) (fun j _ => by linarith [hps j]) (Finset.mem_univ i)
    linarith
  -- the original global-energy bank at the quadrupled order (thresholds before the model)
  obtain ⟨dB, hdB, hbank⟩ := aux_macro_moment_bank d hd E P X S t1 1
    (fun _ => 2 * (2 * Pexp)) ht1 ht2 (fun _ => by linarith)
  obtain ⟨dA, hdA, hthr⟩ := aux_aux_macro_moment_bank_threshold (d := d) t1 (2 * Pexp) ht1 ht2
    ht10.le (by linarith)
  obtain ⟨Cp, -, hFE⟩ := aux_aux_macro_energy_recurrence_finite_estimate (d := d) hd
  have hD0 := ResidualModel.residualDisorderFactor_pos d
  refine ⟨min dB (min (dA / ResidualModel.residualDisorderFactor d)
    (2 * ResidualModel.residualDisorderFactor d)⁻¹), lt_min hdB (lt_min (div_pos hdA hD0)
      (by positivity)), ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hr1
  have hδB : M.delta ≤ dB := hδ.trans (min_le_left _ _)
  have hδA : M.delta ≤ dA / ResidualModel.residualDisorderFactor d :=
    hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδD : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹ :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the residual scale and the bounded-dilation model `M_s`
  obtain ⟨kk, hk1, hk3⟩ := MacroAllCube.exists_residual_scale hr hr1
  obtain ⟨M', hM'⟩ : ∃ M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      M' = ResidualModel.residualModel M hk1.le hk3 hδD := ⟨_, rfl⟩
  have hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure := by
    rw [hM']; exact ResidualModel.measurePreserving_residualModel M r kk hk1.le hk3 hδD
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M'.P = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
    rw [hM']; exact ResidualModel.residualModel_tauSq M hk1.le hk3 hδD
  have hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤
        aux_prop_growth_macro_energy_env M kk om := by
    intro n om; rw [hM']; exact aux_prop_growth_macro_energy_shiftC_bounds M hk1.le hk3 hδD kk n om
  have hδ' : M'.delta ≤ dA := by
    rw [hM', ResidualModel.residualModel_delta]
    rw [le_div_iff₀ hD0] at hδA
    linarith
  -- the native regularity input of `M_s` and its thresholds
  obtain ⟨hδC', hα', hκ'⟩ := hthr M' (aux_prop_growth_macro_energy_nativeSreg M') hδ'
  obtain ⟨H', hH'⟩ := exists_infraredCharacterization hd M'
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      ((aux_prop_growth_macro_energy_nativeSreg M').C * M'.delta ^ 2 * |Real.log M'.delta|) :=
    ⟨_, rfl⟩
  rw [← hκ] at hκ'
  have hlam : 0 ≤ 2 * (2 * Pexp) * t1 * Real.log 3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    have : (0 : ℝ) ≤ Pexp := by linarith
    positivity
  have hκ0 : 0 < κ := lt_of_le_of_lt hlam hκ'
  obtain ⟨Lm, hLmeas, hLtail, hLpre⟩ := aux_aux_macro_moment_bank_prefix M'
    (aux_prop_growth_macro_energy_nativeSreg M') (1 - ((d : ℝ) - t1) / 4) κ hδC' hα' hκ hκ0
    (r⁻¹ • z)
  have hA1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M').C *
      Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) := by
    have h1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M').C :=
      (aux_prop_growth_macro_energy_nativeSreg M').C_ge_one
    have h2 : 1 ≤ Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) :=
      Real.one_le_exp (by positivity)
    nlinarith
  have hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M').toMeasure ≤
      ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))) :=
    fun n => aux_aux_macro_moment_bank_eLpNorm_rpow_three_le _ (Lm n) t1 (2 * (2 * Pexp))
      (by linarith) _ (aux_aux_macro_moment_bank_lintegral_exp_le
        (chaosSampleLaw M').toMeasure (Lm n) (hLmeas n) _ κ _ hA1 hlam hκ' (hLtail n))
  -- the original global energy on `Q(z,r)`
  obtain ⟨Lg, Kg, Cg, hKg0, hKgmem, hKgnorm, -, hKgsrc, -⟩ :=
    hbank M Rm Sreg It H hH hδB z r hr hr1
  have hKgsrc' : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2 := by
    filter_upwards [hKgsrc] with om hom
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have h := hom N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have h3 : 1 ≤ (3 : ℝ) ^ (t1 * (Lg N om : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg ht10.le (Nat.cast_nonneg _))
    exact (le_mul_of_one_le_left (sobolevCoefficientForm_nonneg _ _) h3).trans h
  -- the residual reference factor
  obtain ⟨hRmeas, -, hRmem⟩ := aux_aux_macro_moment_bank_reference hd M' H' hH'
    (closedCube (r⁻¹ • z) 1 one_pos) (2 * (2 * Pexp)) (by linarith)
  have hmom := aux_prop_growth_macro_energy_Kfinal_moment M M' kk r t1
    (aux_aux_macro_energy_recurrence_Z (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d)
    Pexp hr (aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _) hP1 hT Lm hLmeas _ hX
    (aux_prop_growth_macro_energy_Rs H' z r) hRmeas _ le_rfl Kg (ENNReal.ofReal (Cg 0))
    (fun N => (hKgmem 0 N).aestronglyMeasurable) (fun N => hKgnorm 0 N)
  -- the common finite bound
  obtain ⟨Btot, hBtot⟩ : ∃ Btot : ℝ≥0∞, Btot =
      ENNReal.ofReal ((3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1)) * ENNReal.ofReal (Cg 0) +
        (ENNReal.ofReal (18 * aux_aux_macro_energy_recurrence_Z
              (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d * (3 : ℝ) ^ t1 *
              (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1))) *
            (eLpNorm (fun om => aux_prop_growth_macro_energy_env M kk om ^ 3)
                (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure *
              (ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
                  Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
                (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^
                  (1 / (2 * (2 * Pexp))) *
                eLpNorm (aux_prop_growth_macro_energy_Rs H' z r)
                  (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M').toMeasure)) +
          ENNReal.ofReal (18 * aux_aux_macro_energy_recurrence_Z
              (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d * (3 : ℝ) ^ t1 *
              (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1)) * ((r⁻¹) ^ d * (r⁻¹) ^ 2)) *
            (eLpNorm (fun om => aux_prop_growth_macro_energy_env M kk om ^ 6)
                (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure *
              (ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
                  Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
                (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^
                  (1 / (2 * (2 * Pexp))) * ENNReal.ofReal (Cg 0)))) := ⟨_, rfl⟩
  have hfin : Btot ≠ ⊤ := by
    have hE3 := (aux_prop_growth_macro_energy_memLp_env_pow M kk 3 (2 * Pexp) (by linarith)).2.ne
    have hE6 := (aux_prop_growth_macro_energy_memLp_env_pow M kk 6 (2 * Pexp) (by linarith)).2.ne
    have hBX : ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^
          (1 / (2 * (2 * Pexp))) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    have hR := hRmem.2.ne
    rw [hBtot]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hE3 (ENNReal.mul_ne_top hBX hR)),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top hE6 (ENNReal.mul_ne_top hBX ENNReal.ofReal_ne_top))⟩⟩
  refine ⟨aux_prop_growth_macro_energy_Kfinal M kk r t1
      (aux_aux_macro_energy_recurrence_Z (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d)
      Lm (aux_prop_growth_macro_energy_Rs H' z r) Kg, fun _ => Btot.toReal, ?_, ?_, ?_, ?_⟩
  · intro N om
    unfold aux_prop_growth_macro_energy_Kfinal
    have h1 : 0 ≤ (3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) * Kg N om := by
      have := hKg0 N om
      positivity
    have h2 : 0 ≤ (if kk ≤ N then
        aux_prop_growth_macro_energy_Kmid d
          (aux_aux_macro_energy_recurrence_Z (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d)
          t1 r (aux_prop_growth_macro_energy_env M kk om)
          (Lm (N - kk) (MacroAllCube.residualShift r kk om))
          (aux_prop_growth_macro_energy_Rs H' z r (MacroAllCube.residualShift r kk om)) (Kg N om)
        else 0) := by
      split_ifs
      · exact aux_prop_growth_macro_energy_Kmid_nonneg d
          (aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _) hr
          (aux_prop_growth_macro_energy_one_le_env M kk om) (Real.exp_pos _).le (hKg0 N om)
      · exact le_refl 0
    exact add_nonneg h1 h2
  · intro i N
    obtain ⟨hm, hb⟩ := hmom N
    refine ⟨hm, lt_of_le_of_lt ((eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal (hpsP i)) hm).trans (hb.trans (le_of_eq hBtot.symm)))
      (lt_top_iff_ne_top.2 hfin)⟩
  · intro i N
    obtain ⟨hm, hb⟩ := hmom N
    rw [ENNReal.ofReal_toReal hfin]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hpsP i)) hm).trans
      (hb.trans (le_of_eq hBtot.symm))
  · exact aux_prop_growth_macro_energy_ae_bound hd Cp hFE M M'
      (aux_prop_growth_macro_energy_nativeSreg M') t1 ht1 ht2 hδC' hα' H H' hH hH' htau z r hr
      hr1 kk hk3 hT hshift Lm hLpre Kg hKg0 hKgsrc'

end Paper
namespace Paper

/-- The all-cube macro-energy conclusion from paper lines 605--657. The proof
uses the paper's initial spatial rescaling and transfers the prefix and reference
inputs to the physical cube scale. -/
theorem prop_growth_macro_energy :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (t1 : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t1 → t1 < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (Kmac : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
            (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              Kmac N om * (Kf + Cphi) ^ 2 * rad ^ t1 := by
  intro d hd _ _ E P X S t1 k ps ht1 ht2 hps
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 < t1 := by linarith
  -- one exponent for all listed orders
  obtain ⟨Pexp, hPdef⟩ : ∃ Pexp : ℝ, Pexp = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => by linarith [hps i]
  have hP1 : 1 ≤ Pexp := by rw [hPdef]; linarith
  have hpsP : ∀ i, ps i ≤ Pexp := by
    intro i
    rw [hPdef]
    have := Finset.single_le_sum (f := ps) (fun j _ => by linarith [hps j]) (Finset.mem_univ i)
    linarith
  -- the original global-energy bank at the quadrupled order (thresholds before the model)
  obtain ⟨dB, hdB, hbank⟩ := aux_macro_moment_bank d hd E P X S t1 1
    (fun _ => 2 * (2 * Pexp)) ht1 ht2 (fun _ => by linarith)
  obtain ⟨dA, hdA, hthr⟩ := aux_aux_macro_moment_bank_threshold (d := d) t1 (2 * Pexp) ht1 ht2
    ht10.le (by linarith)
  obtain ⟨Cp, -, hFE⟩ := aux_aux_macro_energy_recurrence_finite_estimate (d := d) hd
  have hD0 := ResidualModel.residualDisorderFactor_pos d
  refine ⟨min dB (min (dA / ResidualModel.residualDisorderFactor d)
    (2 * ResidualModel.residualDisorderFactor d)⁻¹), lt_min hdB (lt_min (div_pos hdA hD0)
      (by positivity)), ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hr1
  have hδB : M.delta ≤ dB := hδ.trans (min_le_left _ _)
  have hδA : M.delta ≤ dA / ResidualModel.residualDisorderFactor d :=
    hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδD : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹ :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the residual scale and the bounded-dilation model `M_s`
  obtain ⟨kk, hk1, hk3⟩ := MacroAllCube.exists_residual_scale hr hr1
  obtain ⟨M', hM'⟩ : ∃ M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      M' = ResidualModel.residualModel M hk1.le hk3 hδD := ⟨_, rfl⟩
  have hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure := by
    rw [hM']; exact ResidualModel.measurePreserving_residualModel M r kk hk1.le hk3 hδD
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M'.P = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
    rw [hM']; exact ResidualModel.residualModel_tauSq M hk1.le hk3 hδD
  have hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤
        aux_prop_growth_macro_energy_env M kk om := by
    intro n om; rw [hM']; exact aux_prop_growth_macro_energy_shiftC_bounds M hk1.le hk3 hδD kk n om
  have hδ' : M'.delta ≤ dA := by
    rw [hM', ResidualModel.residualModel_delta]
    rw [le_div_iff₀ hD0] at hδA
    linarith
  -- the native regularity input of `M_s` and its thresholds
  obtain ⟨hδC', hα', hκ'⟩ := hthr M' (aux_prop_growth_macro_energy_nativeSreg M') hδ'
  obtain ⟨H', hH'⟩ := exists_infraredCharacterization hd M'
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      ((aux_prop_growth_macro_energy_nativeSreg M').C * M'.delta ^ 2 * |Real.log M'.delta|) :=
    ⟨_, rfl⟩
  rw [← hκ] at hκ'
  have hlam : 0 ≤ 2 * (2 * Pexp) * t1 * Real.log 3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    have : (0 : ℝ) ≤ Pexp := by linarith
    positivity
  have hκ0 : 0 < κ := lt_of_le_of_lt hlam hκ'
  obtain ⟨Lm, hLmeas, hLtail, hLpre⟩ := aux_aux_macro_moment_bank_prefix M'
    (aux_prop_growth_macro_energy_nativeSreg M') (1 - ((d : ℝ) - t1) / 4) κ hδC' hα' hκ hκ0
    (r⁻¹ • z)
  have hA1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M').C *
      Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) := by
    have h1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M').C :=
      (aux_prop_growth_macro_energy_nativeSreg M').C_ge_one
    have h2 : 1 ≤ Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) :=
      Real.one_le_exp (by positivity)
    nlinarith
  have hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M').toMeasure ≤
      ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))) :=
    fun n => aux_aux_macro_moment_bank_eLpNorm_rpow_three_le _ (Lm n) t1 (2 * (2 * Pexp))
      (by linarith) _ (aux_aux_macro_moment_bank_lintegral_exp_le
        (chaosSampleLaw M').toMeasure (Lm n) (hLmeas n) _ κ _ hA1 hlam hκ' (hLtail n))
  -- the original global energy on `Q(z,r)`
  obtain ⟨Lg, Kg, Cg, hKg0, hKgmem, hKgnorm, -, hKgsrc, -⟩ :=
    hbank M Rm Sreg It H hH hδB z r hr hr1
  have hKgsrc' : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2 := by
    filter_upwards [hKgsrc] with om hom
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have h := hom N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have h3 : 1 ≤ (3 : ℝ) ^ (t1 * (Lg N om : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg ht10.le (Nat.cast_nonneg _))
    exact (le_mul_of_one_le_left (sobolevCoefficientForm_nonneg _ _) h3).trans h
  -- the residual reference factor
  obtain ⟨hRmeas, -, hRmem⟩ := aux_aux_macro_moment_bank_reference hd M' H' hH'
    (closedCube (r⁻¹ • z) 1 one_pos) (2 * (2 * Pexp)) (by linarith)
  have hmom := aux_prop_growth_macro_energy_Kfinal_moment M M' kk r t1
    (aux_aux_macro_energy_recurrence_Z (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d)
    Pexp hr (aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _) hP1 hT Lm hLmeas _ hX
    (aux_prop_growth_macro_energy_Rs H' z r) hRmeas _ le_rfl Kg (ENNReal.ofReal (Cg 0))
    (fun N => (hKgmem 0 N).aestronglyMeasurable) (fun N => hKgnorm 0 N)
  -- the common finite bound
  obtain ⟨Btot, hBtot⟩ : ∃ Btot : ℝ≥0∞, Btot =
      ENNReal.ofReal ((3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1)) * ENNReal.ofReal (Cg 0) +
        (ENNReal.ofReal (18 * aux_aux_macro_energy_recurrence_Z
              (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d * (3 : ℝ) ^ t1 *
              (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1))) *
            (eLpNorm (fun om => aux_prop_growth_macro_energy_env M kk om ^ 3)
                (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure *
              (ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
                  Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
                (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^
                  (1 / (2 * (2 * Pexp))) *
                eLpNorm (aux_prop_growth_macro_energy_Rs H' z r)
                  (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M').toMeasure)) +
          ENNReal.ofReal (18 * aux_aux_macro_energy_recurrence_Z
              (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d * (3 : ℝ) ^ t1 *
              (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1)) * ((r⁻¹) ^ d * (r⁻¹) ^ 2)) *
            (eLpNorm (fun om => aux_prop_growth_macro_energy_env M kk om ^ 6)
                (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure *
              (ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
                  Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
                (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^
                  (1 / (2 * (2 * Pexp))) * ENNReal.ofReal (Cg 0)))) := ⟨_, rfl⟩
  have hfin : Btot ≠ ⊤ := by
    have hE3 := (aux_prop_growth_macro_energy_memLp_env_pow M kk 3 (2 * Pexp) (by linarith)).2.ne
    have hE6 := (aux_prop_growth_macro_energy_memLp_env_pow M kk 6 (2 * Pexp) (by linarith)).2.ne
    have hBX : ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^
          (1 / (2 * (2 * Pexp))) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    have hR := hRmem.2.ne
    rw [hBtot]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hE3 (ENNReal.mul_ne_top hBX hR)),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top hE6 (ENNReal.mul_ne_top hBX ENNReal.ofReal_ne_top))⟩⟩
  refine ⟨aux_prop_growth_macro_energy_Kfinal M kk r t1
      (aux_aux_macro_energy_recurrence_Z (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d)
      Lm (aux_prop_growth_macro_energy_Rs H' z r) Kg, fun _ => Btot.toReal, ?_, ?_, ?_, ?_⟩
  · intro N om
    unfold aux_prop_growth_macro_energy_Kfinal
    have h1 : 0 ≤ (3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) * Kg N om := by
      have := hKg0 N om
      positivity
    have h2 : 0 ≤ (if kk ≤ N then
        aux_prop_growth_macro_energy_Kmid d
          (aux_aux_macro_energy_recurrence_Z (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d)
          t1 r (aux_prop_growth_macro_energy_env M kk om)
          (Lm (N - kk) (MacroAllCube.residualShift r kk om))
          (aux_prop_growth_macro_energy_Rs H' z r (MacroAllCube.residualShift r kk om)) (Kg N om)
        else 0) := by
      split_ifs
      · exact aux_prop_growth_macro_energy_Kmid_nonneg d
          (aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _) hr
          (aux_prop_growth_macro_energy_one_le_env M kk om) (Real.exp_pos _).le (hKg0 N om)
      · exact le_refl 0
    exact add_nonneg h1 h2
  · intro i N
    obtain ⟨hm, hb⟩ := hmom N
    refine ⟨hm, lt_of_le_of_lt ((eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal (hpsP i)) hm).trans (hb.trans (le_of_eq hBtot.symm)))
      (lt_top_iff_ne_top.2 hfin)⟩
  · intro i N
    obtain ⟨hm, hb⟩ := hmom N
    rw [ENNReal.ofReal_toReal hfin]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hpsP i)) hm).trans
      (hb.trans (le_of_eq hBtot.symm))
  · exact aux_prop_growth_macro_energy_ae_bound hd Cp hFE M M'
      (aux_prop_growth_macro_energy_nativeSreg M') t1 ht1 ht2 hδC' hα' H H' hH hH' htau z r hr
      hr1 kk hk3 hT hshift Lm hLpre Kg hKg0 hKgsrc'

end Paper
