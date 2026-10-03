module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepStationaryForcing
public import Homogenization.Geometry.CubeMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-!
# Spatial realization of GMC stationary fields

This is the GMC counterpart of
`Algsuperdiff/Section3/Provider/Corrector/Realization.lean`.  The abstract
stationary Hilbert layer only needs measurable fixed translations.  The
finite-volume corrector argument also needs joint measurability in the space
and sample variables.  For the literal GMC carrier this follows from the
compact-open topology on `PotentialField`: composition is jointly continuous
when the intermediate Euclidean space is locally compact.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The frozen potential carrier uses the topology induced from two
compact-open continuous-map spaces.  Mathlib cannot infer this instance
through the custom topology declaration automatically. -/
noncomputable instance potentialFieldSecondCountable (d : ℕ) :
    SecondCountableTopology (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) := by
  exact TopologicalSpace.secondCountableTopology_induced
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) Subtype.val

namespace PotentialJointTranslation

private def shiftMap {d : ℕ} (z : Vec d) : C(Vec d, Vec d) :=
  ⟨fun x => x + z, continuous_id.add continuous_const⟩

private theorem continuous_shiftMap {d : ℕ} :
    Continuous (shiftMap (d := d)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_snd.add continuous_fst

/-- Translation is jointly continuous in the displacement and the potential.
This is stronger than the fixed-displacement continuity exposed by
`PotentialField.continuous_translate`. -/
theorem continuous_translate {d : ℕ} :
    Continuous fun zg : Vec d × SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate zg.1 zg.2 := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · have hcomp : Continuous fun zg :
        Vec d × SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          zg.2.1.1.comp (shiftMap zg.1) := by
      exact ContinuousMap.continuous_comp'.comp
        ((continuous_shiftMap.comp continuous_fst).prodMk
          ((continuous_subtype_val.comp continuous_snd).fst))
    simpa only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate,
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply,
      ContinuousMap.comp_apply, shiftMap] using! hcomp
  · have hcomp : Continuous fun zg :
        Vec d × SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          zg.2.1.2.comp (shiftMap zg.1) := by
      exact ContinuousMap.continuous_comp'.comp
        ((continuous_shiftMap.comp continuous_fst).prodMk
          ((continuous_subtype_val.comp continuous_snd).snd))
    simpa only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate,
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply,
      ContinuousMap.comp_apply, shiftMap] using! hcomp

end PotentialJointTranslation

/-- The literal translation action on the potential sequence is jointly
continuous. -/
theorem continuous_translatePotentialSequence {d : ℕ} :
    Continuous fun zω : Vec d × SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      translatePotentialSequence zω.1 zω.2 := by
  apply continuous_pi
  intro k
  simpa only [translatePotentialSequence, Function.comp_def] using
    (PotentialJointTranslation.continuous_translate (d := d)).comp
      (continuous_fst.prodMk ((continuous_apply k).comp continuous_snd))

/-- Joint measurability required by the spatial realization/Fubini route. -/
noncomputable instance potentialSampleMeasurableVAdd₂ (d : ℕ) :
    MeasurableVAdd₂ (Vec d) (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) where
  measurable_vadd := continuous_translatePotentialSequence.measurable

/-- The spatial realization of a stationary representative. -/
def realize {d : ℕ} {E : Type*} (X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) : E :=
  X (x +ᵥ ω)

@[simp] theorem realize_apply {d : ℕ} {E : Type*}
    (X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    realize X ω x = X (x +ᵥ ω) := rfl

/-- A measurable representative has a jointly measurable realization, in
the Fubini order `(sample, space)`. -/
theorem stronglyMeasurable_uncurry_realize {d : ℕ} {E : Type*}
    [TopologicalSpace E] {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E}
    (hX : StronglyMeasurable X) :
    StronglyMeasurable fun p : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d => realize X p.1 p.2 :=
  hX.comp_measurable (measurable_vadd.comp measurable_swap)

/-- A measurable representative has a measurable realization for every
sample. -/
theorem stronglyMeasurable_realize {d : ℕ} {E : Type*}
    [TopologicalSpace E] {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E}
    (hX : StronglyMeasurable X) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    StronglyMeasurable (realize X ω) :=
  hX.comp_measurable
    (measurable_vadd.comp (measurable_id.prodMk measurable_const))

/-- Stationarity transfers an expectation through a spatial realization. -/
theorem integral_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E) (x : Vec d) :
    ∫ ω, realize X ω x ∂M.P.toMeasure =
      ∫ ω, X ω ∂M.P.toMeasure := by
  letI := potentialSequenceVAddInvariant M
  exact (Stationary.measurePreserving_const_vadd
    (mu := M.P.toMeasure) x).integral_comp
      (measurableEmbedding_const_vadd x) X

/-- Stationarity transfers integrability through a spatial realization. -/
theorem integrable_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E]
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hX : Integrable X M.P.toMeasure) (x : Vec d) :
    Integrable (fun ω => realize X ω x) M.P.toMeasure := by
  letI := potentialSequenceVAddInvariant M
  exact ((Stationary.measurePreserving_const_vadd
    (mu := M.P.toMeasure) x).integrable_comp_emb
      (measurableEmbedding_const_vadd x)).2 hX

/-- Restricted volume on a triadic cube is finite. -/
theorem isFiniteMeasure_volume_restrict_cubeSet {d : ℕ}
    (Q : TriadicCube d) :
    IsFiniteMeasure (volume.restrict (cubeSet Q)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact volume_cubeSet_lt_top Q

/-- The pointwise pairing of two stationary `L²` representatives is
integrable. -/
theorem integrable_vecDot {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {X Y : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d}
    (hX : MemLp X 2 M.P.toMeasure) (hY : MemLp Y 2 M.P.toMeasure) :
    Integrable (fun ω => vecDot (X ω).toVec (Y ω).toVec) M.P.toMeasure := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hX.toLp X) (hY.toLp Y)).congr ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω hx hy
  rw [hx, hy, HilbertVec.inner_def]

/-- The realized pairing is integrable on sample space times a cube. -/
theorem integrable_prod_vecDot_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Q : TriadicCube d)
    {X Y : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d}
    (hXm : StronglyMeasurable X) (hYm : StronglyMeasurable Y)
    (hX : MemLp X 2 M.P.toMeasure) (hY : MemLp Y 2 M.P.toMeasure) :
    Integrable
      (fun p : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
        vecDot (realize X p.1 p.2).toVec (realize Y p.1 p.2).toVec)
      (M.P.toMeasure.prod (volume.restrict (cubeSet Q))) := by
  letI := potentialSequenceVAddInvariant M
  haveI := isFiniteMeasure_volume_restrict_cubeSet Q
  have hpair := integrable_vecDot M hX hY
  have hstrong : StronglyMeasurable fun p : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
      vecDot (realize X p.1 p.2).toVec (realize Y p.1 p.2).toVec := by
    have hinner : StronglyMeasurable fun p : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
        inner ℝ (realize X p.1 p.2) (realize Y p.1 p.2) :=
      (stronglyMeasurable_uncurry_realize hXm).inner
        (stronglyMeasurable_uncurry_realize hYm)
    simpa using hinner
  refine (integrable_prod_iff' hstrong.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine Filter.Eventually.of_forall fun x => ?_
    exact integrable_realize M hpair x
  · have hconst : ∀ x : Vec d,
        (∫ ω, ‖vecDot (realize X ω x).toVec (realize Y ω x).toVec‖
            ∂M.P.toMeasure) =
          ∫ ω, ‖vecDot (X ω).toVec (Y ω).toVec‖ ∂M.P.toMeasure :=
      fun x => integral_realize M
        (fun ω => ‖vecDot (X ω).toVec (Y ω).toVec‖) x
    refine (integrable_congr ?_).2
      (integrable_const (∫ ω, ‖vecDot (X ω).toVec (Y ω).toVec‖ ∂M.P.toMeasure))
    filter_upwards with x
    exact hconst x

/-- For almost every sample, a stationary `L²` representative realizes to
an honest spatial `L²` field on the cube. -/
theorem ae_memHilbertVectorL2_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Q : TriadicCube d)
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d}
    (hXm : StronglyMeasurable X) (hX : MemLp X 2 M.P.toMeasure) :
    ∀ᵐ ω ∂M.P.toMeasure,
      MemHilbertVectorL2 (cubeSet Q) (realize X ω) := by
  haveI := isFiniteMeasure_volume_restrict_cubeSet Q
  filter_upwards [(integrable_prod_vecDot_realize M Q hXm hXm hX hX).prod_right_ae]
      with ω hω
  refine (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_realize hXm ω).aestronglyMeasurable).2 (hω.congr ?_)
  filter_upwards with x
  exact (HilbertVec.inner_def _ _).symm.trans (real_inner_self_eq_norm_sq _)

/-- Expectation of a normalized cube pairing equals its stationary origin
pairing. -/
theorem integral_cubeAverage_vecDot_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Q : TriadicCube d)
    {X Y : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d}
    (hXm : StronglyMeasurable X) (hYm : StronglyMeasurable Y)
    (hX : MemLp X 2 M.P.toMeasure) (hY : MemLp Y 2 M.P.toMeasure) :
    ∫ ω, cubeAverage Q
        (fun x => vecDot (realize X ω x).toVec (realize Y ω x).toVec)
        ∂M.P.toMeasure =
      ∫ ω, vecDot (X ω).toVec (Y ω).toVec ∂M.P.toMeasure := by
  haveI := isFiniteMeasure_volume_restrict_cubeSet Q
  have hswap :
      ∫ ω, (∫ x,
          vecDot (realize X ω x).toVec (realize Y ω x).toVec
            ∂volume.restrict (cubeSet Q)) ∂M.P.toMeasure =
        ∫ x, (∫ ω,
          vecDot (realize X ω x).toVec (realize Y ω x).toVec
            ∂M.P.toMeasure) ∂volume.restrict (cubeSet Q) :=
    integral_integral_swap
      (integrable_prod_vecDot_realize M Q hXm hYm hX hY)
  have hconst : ∀ x : Vec d,
      (∫ ω, vecDot (realize X ω x).toVec (realize Y ω x).toVec
          ∂M.P.toMeasure) =
        ∫ ω, vecDot (X ω).toVec (Y ω).toVec ∂M.P.toMeasure :=
    fun x => integral_realize M
      (fun ω => vecDot (X ω).toVec (Y ω).toVec) x
  calc
    ∫ ω, cubeAverage Q
        (fun x => vecDot (realize X ω x).toVec (realize Y ω x).toVec)
        ∂M.P.toMeasure =
      ∫ ω, (cubeVolume Q)⁻¹ *
        (∫ x, vecDot (realize X ω x).toVec (realize Y ω x).toVec
          ∂volume.restrict (cubeSet Q)) ∂M.P.toMeasure := by
      simp only [cubeAverage]
    _ = (cubeVolume Q)⁻¹ *
        ∫ ω, (∫ x, vecDot (realize X ω x).toVec (realize Y ω x).toVec
          ∂volume.restrict (cubeSet Q)) ∂M.P.toMeasure := integral_const_mul _ _
    _ = (cubeVolume Q)⁻¹ *
        ∫ x, (∫ ω, vecDot (realize X ω x).toVec (realize Y ω x).toVec
          ∂M.P.toMeasure) ∂volume.restrict (cubeSet Q) := by rw [hswap]
    _ = (cubeVolume Q)⁻¹ *
        ∫ _x : Vec d, (∫ ω, vecDot (X ω).toVec (Y ω).toVec
          ∂M.P.toMeasure) ∂volume.restrict (cubeSet Q) := by simp only [hconst]
    _ = ∫ ω, vecDot (X ω).toVec (Y ω).toVec ∂M.P.toMeasure := by
      rw [integral_const, Measure.real_def, Measure.restrict_apply_univ,
        volume_cubeSet_toReal, smul_eq_mul,
        inv_mul_cancel_left₀ (cubeVolume_pos Q).ne']

/-- Quadratic specialization of the stationary product-average transfer. -/
theorem integral_cubeAverage_normSq_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Q : TriadicCube d)
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d}
    (hXm : StronglyMeasurable X) (hX : MemLp X 2 M.P.toMeasure) :
    ∫ ω, cubeAverage Q (fun x => ‖realize X ω x‖ ^ 2) ∂M.P.toMeasure =
      ∫ ω, ‖X ω‖ ^ 2 ∂M.P.toMeasure := by
  have hpt : ∀ v : HilbertVec d, vecDot v.toVec v.toVec = ‖v‖ ^ 2 :=
    fun v => (HilbertVec.inner_def v v).symm.trans (real_inner_self_eq_norm_sq v)
  simpa only [hpt] using
    integral_cubeAverage_vecDot_realize M Q hXm hXm hX hX

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
