module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryRealization

@[expose] public section

/-!
# Stationary transfer on finite-volume spatial sets

This specializes the Fubini layer of
`Algsuperdiff/Section3/Provider/Corrector/StationaryStrip.lean` to the literal
GMC potential-sequence carrier.  It is the measure-theoretic input for the
boundary-cutoff realization of stationary potential and solenoidal fields.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Joint integrability of a stationary scalar observable over a
finite-volume spatial set. -/
theorem integrable_prod_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ} (hgm : StronglyMeasurable g)
    (hg : Integrable g M.P.toMeasure) :
    Integrable (fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d => realize g q.1 q.2)
      (M.P.toMeasure.prod (volume.restrict S)) := by
  haveI : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hSfin
  have hjm : StronglyMeasurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
      realize g q.1 q.2 := stronglyMeasurable_uncurry_realize hgm
  refine (integrable_prod_iff' hjm.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x => integrable_realize M hg x
  · refine (integrable_congr ?_).2
      (integrable_const (∫ ω, ‖g ω‖ ∂M.P.toMeasure))
    filter_upwards with x
    exact integral_realize M (fun ω => ‖g ω‖) x

/-- Set-indexed stationary transfer. -/
theorem integral_setIntegral_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ} (hgm : StronglyMeasurable g)
    (hg : Integrable g M.P.toMeasure) :
    ∫ ω, (∫ x in S, realize g ω x) ∂M.P.toMeasure =
      (volume S).toReal * ∫ ω, g ω ∂M.P.toMeasure := by
  haveI : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hSfin
  have hswap :
      ∫ ω, (∫ x, realize g ω x ∂volume.restrict S) ∂M.P.toMeasure =
        ∫ x, (∫ ω, realize g ω x ∂M.P.toMeasure) ∂volume.restrict S :=
    integral_integral_swap (integrable_prod_realize M hSfin hgm hg)
  calc
    ∫ ω, (∫ x in S, realize g ω x) ∂M.P.toMeasure =
        ∫ x, (∫ ω, realize g ω x ∂M.P.toMeasure) ∂volume.restrict S :=
      hswap
    _ = ∫ _x, (∫ ω, g ω ∂M.P.toMeasure) ∂volume.restrict S := by
      simp only [integral_realize M]
    _ = (volume S).toReal * ∫ ω, g ω ∂M.P.toMeasure := by
      rw [integral_const, Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul]

/-- Integrability of the random set integral. -/
theorem integrable_setIntegral_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ} (hgm : StronglyMeasurable g)
    (hg : Integrable g M.P.toMeasure) :
    Integrable (fun ω => ∫ x in S, realize g ω x) M.P.toMeasure :=
  (integrable_prod_realize M hSfin hgm hg).integral_prod_left

/-- Transfer of the squared norm of a stationary `L²` field. -/
theorem integral_setIntegral_normSq_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E]
    {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) :
    ∫ ω, (∫ x in S, ‖realize X ω x‖ ^ 2) ∂M.P.toMeasure =
      (volume S).toReal * ∫ ω, ‖X ω‖ ^ 2 ∂M.P.toMeasure :=
  integral_setIntegral_realize M hSfin (hXm.norm.pow 2)
    ((memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX)

/-- Integrability of the random spatial squared norm on a finite-volume set. -/
theorem integrable_setIntegral_normSq_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E]
    {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) :
    Integrable (fun omega => ∫ x in S, ‖realize X omega x‖ ^ 2)
      M.P.toMeasure :=
  integrable_setIntegral_realize M hSfin (hXm.norm.pow 2)
    ((memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX)

/-- Per-sample spatial `L²` membership on a finite-volume set. -/
theorem ae_memLp_two_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E]
    {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) :
    ∀ᵐ ω ∂M.P.toMeasure,
      MemLp (realize (d := d) X ω) 2 (volume.restrict S) := by
  have hprod := integrable_prod_realize M hSfin (hXm.norm.pow 2)
    ((memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX)
  filter_upwards [hprod.prod_right_ae] with ω hω
  exact (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_realize hXm ω).aestronglyMeasurable).2 hω

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
