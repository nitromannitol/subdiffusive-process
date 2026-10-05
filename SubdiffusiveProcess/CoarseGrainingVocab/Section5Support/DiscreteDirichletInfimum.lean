module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletEnergyContinuity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.CellEnvelope

@[expose] public section

/-!
# The discrete Dirichlet minimum `Q_{R,pi}(p)`

`p.homogenized.coefficient.strict.decay` defines

```text
Q_{R,pi}(p) = min_{v in linear_p + (V_{R,pi} cap H_0^1(spx_0^pi))}
                (1/|spx|) sum_{T in T_{R,pi}} |T| (sup_{closure T} B_0) |grad v|_T|^2 ,
```

the minimum of a *cellwise* energy over the conforming piecewise-affine class.
The continuum minimum `dirichletInfOn` leaves the shape of `Q_{R,pi}` to its consumer, with one constraint: Step 3
(`p.homogenized.coefficient.strict.decay`) writes the minimizer as `v|_T = c_T + linear_{p_T}`
and then solves a Dirichlet problem on each cell with boundary data `v|_{∂T}`,
so **the per-cell slopes `p_T` must be individually visible**.  This file fixes
that shape.

* `IsCellwiseSlope S Dw q` says that the field `Dw` is the constant `q T` on the
  interior of every cell of the mesh `S`.  This is exactly the membership in
  the source's `V_{R,pi}` that (S2a) produces
  (`exists_kuhn_h10_approx`'s cellwise clause);
* **`KuhnCompetitor U S`** bundles an `H_0^1(U)` function with its slope
  assignment: the source's `v - linear_p` together with the family `(p_T)_T`;
* **`kuhnDiscreteEnergy B S U p q`** is the source's sum literally, with `|T|`
  read as `|U cap T|`, so that cells outside `U` contribute nothing;
* **`kuhnDirichletInf B S U p`** is `Q_{R,pi}(p)` (unnormalized): the infimum of
  that sum over the *slope set* `kuhnSlopeSet U S` of admissible slope
  assignments.  Writing the infimum over slopes rather than over functions makes
  the dependence on the coefficient enter **only** through the finitely many
  numbers `cellSup B T`, which is what the measurability obligation of the
  bundle report consumes.

The analytic content is one splitting lemma, `setIntegral_eq_sum_openCarrier`:
an integral over `U` splits over the cells because the half-open carriers cover
`U` and the cell boundaries are null (`Kuhn/ZeroExtension.lean`).  Everything
else is termwise comparison:

* `dirichletEnergyOn'_le_kuhnDiscreteEnergy`: `B <= sup_{closure T} B` gives the
  source's *"the continuum minimum is bounded above by `Q_{R,pi}(p)`"*
  (`p.homogenized.coefficient.strict.decay`), now with no integrability hypothesis on the envelope;
* `abs_kuhnDiscreteEnergy_sub_dirichletEnergyOn'_le`: the two-sided version, the
  cost of the cellwise upper approximation of `p.homogenized.coefficient.strict.decay` being the uniform
  envelope error of (S2b).

## Scope

* **Infimum, not minimum.**  `kuhnDirichletInf` is an `sInf`.  Attainment is
  *not* proved: the admissible slope set is the image of a finite-dimensional
  space of vertex data, so the direct method applies in principle, but the
  identification of that space is not carried out here.  What is proved is
  near-attainment, `exists_kuhnCompetitor_kuhnDiscreteEnergy_lt`, which is what
  an `eps`-argument in Step 3 consumes.
* **No normalization.**  The source divides by `|spx_0^pi|`; this file does not.
* Nothing here is probabilistic.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The conforming class and its slopes -/

/-- **Membership in `V_{R,pi}`, read on gradients.**  The field `Dw` is almost
everywhere the constant `q T` on the part of `U` inside every cell of `S`.

The almost-everywhere form is forced, not chosen: an `H^1` function determines
its weak gradient only up to a null set (`Sobolev/WeakDerivatives.lean`'s
`HasWeakPartialDerivOn.ae_eq`), so a pointwise clause would not survive the
change of representative that `MemH10` performs.  Every energy in sight is an
integral, so nothing is lost.  `isCellwiseSlope_of_forall_mem_openCarrier`
imports the pointwise clause that (S2a) produces. -/
def IsCellwiseSlope (S : Finset (KuhnCell d)) (U : Set (Vec d)) (Dw : Vec d → Vec d)
    (q : KuhnCell d → Vec d) : Prop :=
  ∀ T ∈ S, ∀ᵐ x ∂(volume.restrict (U ∩ T.openCarrier)), Dw x = q T

theorem isCellwiseSlope_of_forall_mem_openCarrier {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} {Dw : Vec d → Vec d} {q : KuhnCell d → Vec d}
    (hU : MeasurableSet U) (h : ∀ T ∈ S, ∀ x ∈ T.openCarrier, Dw x = q T) :
    IsCellwiseSlope S U Dw q := fun T hT =>
  (ae_restrict_iff' (hU.inter (isOpen_openCarrier T).measurableSet)).mpr
    (Filter.Eventually.of_forall fun x hx => h T hT x hx.2)

/-- Conformity is inherited by any a.e.-equal representative of the gradient. -/
theorem IsCellwiseSlope.congr {S : Finset (KuhnCell d)} {U : Set (Vec d)}
    {Dw Dw' : Vec d → Vec d} {q : KuhnCell d → Vec d}
    (h : IsCellwiseSlope S U Dw q)
    (hae : Dw' =ᵐ[volume.restrict U] Dw) : IsCellwiseSlope S U Dw' q := by
  intro T hT
  have hres : Dw' =ᵐ[volume.restrict (U ∩ T.openCarrier)] Dw :=
    ae_mono (Measure.restrict_mono Set.inter_subset_left le_rfl) hae
  filter_upwards [h T hT, hres] with x hx hx'
  rw [hx', hx]

/-- **A conforming competitor**: an element of `V_{R,pi} cap H_0^1(U)` together
with the family of its per-cell slopes `p_T`, which Step 3 of
`p.homogenized.coefficient.strict.decay` consumes individually. -/
structure KuhnCompetitor (U : Set (Vec d)) (S : Finset (KuhnCell d)) where
  /-- The `H_0^1(U)` correction `v - linear_p`. -/
  toH10Function : H10Function U
  /-- The per-cell slope `p_T` of `p.homogenized.coefficient.strict.decay`. -/
  slope : KuhnCell d → Vec d
  /-- The competitor is affine on every cell, with the recorded slope. -/
  isCellwiseSlope : IsCellwiseSlope S U toH10Function.toH1Function.grad slope

namespace KuhnCompetitor

variable {U : Set (Vec d)} {S : Finset (KuhnCell d)}

/-- The weak gradient of a conforming competitor. -/
def grad (c : KuhnCompetitor U S) : Vec d → Vec d :=
  c.toH10Function.toH1Function.grad

theorem grad_ae_eq_slope (c : KuhnCompetitor U S) {T : KuhnCell d} (hT : T ∈ S) :
    ∀ᵐ x ∂(volume.restrict (U ∩ T.openCarrier)), c.grad x = c.slope T :=
  c.isCellwiseSlope T hT

/-- The zero competitor, whose slopes all vanish: the affine function
`linear_p` itself. -/
instance : Zero (KuhnCompetitor U S) where
  zero := ⟨0, fun _ => 0, fun _ _ => Filter.Eventually.of_forall fun _ => rfl⟩

@[simp] theorem zero_slope (T : KuhnCell d) :
    (0 : KuhnCompetitor U S).slope T = 0 := rfl

end KuhnCompetitor

/-- **The admissible slope assignments.**  A subset of `KuhnCell d → Vec d`
depending only on `U` and the mesh -- in particular *not* on the coefficient. -/
def kuhnSlopeSet (U : Set (Vec d)) (S : Finset (KuhnCell d)) :
    Set (KuhnCell d → Vec d) :=
  {q | ∃ c : KuhnCompetitor U S, c.slope = q}

theorem kuhnSlopeSet_nonempty (U : Set (Vec d)) (S : Finset (KuhnCell d)) :
    (kuhnSlopeSet U S).Nonempty :=
  ⟨_, (0 : KuhnCompetitor U S), rfl⟩

/-! ## The discrete energy and the discrete minimum -/

/-- **`sum_T |T| (sup_{closure T} B) |p + p_T|^2`** of
`p.homogenized.coefficient.strict.decay`, with `|T|` read as `|U cap T|` so that cells
outside `U` contribute nothing. -/
def kuhnDiscreteEnergy (B : Vec d → ℝ) (S : Finset (KuhnCell d)) (U : Set (Vec d))
    (p : Vec d) (q : KuhnCell d → Vec d) : ℝ :=
  ∑ T ∈ S, volume.real (U ∩ T.openCarrier) * (cellSup B T * vecNormSq (p + q T))

/-- **`Q_{R,pi}(p)`** of `p.homogenized.coefficient.strict.decay`, unnormalized: the infimum
of the cellwise energy over the admissible slope assignments. -/
def kuhnDirichletInf (B : Vec d → ℝ) (S : Finset (KuhnCell d)) (U : Set (Vec d))
    (p : Vec d) : ℝ :=
  sInf (kuhnDiscreteEnergy B S U p '' kuhnSlopeSet U S)

theorem kuhnDiscreteEnergy_image_nonempty (B : Vec d → ℝ) (S : Finset (KuhnCell d))
    (U : Set (Vec d)) (p : Vec d) :
    (kuhnDiscreteEnergy B S U p '' kuhnSlopeSet U S).Nonempty :=
  (kuhnSlopeSet_nonempty U S).image _

theorem kuhnDiscreteEnergy_nonneg {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec d)
    (q : KuhnCell d → Vec d) : 0 ≤ kuhnDiscreteEnergy B S U p q := by
  refine Finset.sum_nonneg fun T _ => mul_nonneg measureReal_nonneg ?_
  refine mul_nonneg ?_ (vecNormSq_nonneg _)
  exact le_trans (hB0 (T.vertex 0))
    (le_cellSup T hB.continuousOn (T.vertex_mem_closedCarrier 0))

theorem bddBelow_kuhnDiscreteEnergy_image {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec d) :
    BddBelow (kuhnDiscreteEnergy B S U p '' kuhnSlopeSet U S) := by
  refine ⟨0, ?_⟩
  rintro E ⟨q, -, rfl⟩
  exact kuhnDiscreteEnergy_nonneg hB hB0 p q

/-- **The defining bound**: every conforming competitor dominates `Q_{R,pi}(p)`. -/
theorem kuhnDirichletInf_le {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec d)
    (c : KuhnCompetitor U S) :
    kuhnDirichletInf B S U p ≤ kuhnDiscreteEnergy B S U p c.slope :=
  csInf_le (bddBelow_kuhnDiscreteEnergy_image hB hB0 p) ⟨c.slope, ⟨c, rfl⟩, rfl⟩

theorem kuhnDirichletInf_nonneg {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec d) :
    0 ≤ kuhnDirichletInf B S U p := by
  refine le_csInf (kuhnDiscreteEnergy_image_nonempty B S U p) ?_
  rintro E ⟨q, -, rfl⟩
  exact kuhnDiscreteEnergy_nonneg hB hB0 p q

/-- **Near-attainment.**  `Q_{R,pi}(p)` is an infimum, and no minimizer is
claimed; what is available, and what an `eps`-argument in Step 3 consumes, is a
conforming competitor whose per-cell slopes realize the infimum up to `eps`. -/
theorem exists_kuhnCompetitor_kuhnDiscreteEnergy_lt (B : Vec d → ℝ)
    {S : Finset (KuhnCell d)} {U : Set (Vec d)} (p : Vec d) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ c : KuhnCompetitor U S,
      kuhnDiscreteEnergy B S U p c.slope < kuhnDirichletInf B S U p + eps := by
  obtain ⟨E, ⟨q, ⟨c, hc⟩, hqE⟩, hE⟩ :=
    exists_lt_of_csInf_lt (kuhnDiscreteEnergy_image_nonempty B S U p)
      (lt_add_of_pos_right _ heps)
  exact ⟨c, by rw [hc, hqE]; exact hE⟩

/-! ## Splitting an integral over the mesh -/

/-- Almost every point of a covered set lies in the interior of some cell: the
half-open carriers cover, and the cell boundaries are null. -/
theorem ae_eq_iUnion_inter_openCarrier {S : Finset (KuhnCell d)} {U : Set (Vec d)}
    (hcover : U ⊆ ⋃ T ∈ (S : Set (KuhnCell d)), T.carrier) :
    U =ᵐ[volume] ⋃ T ∈ (S : Set (KuhnCell d)), (U ∩ T.openCarrier) := by
  have hnull :
      volume (U \ ⋃ T ∈ (S : Set (KuhnCell d)), T.openCarrier) = 0 := by
    refine measure_mono_null (t := ⋃ T ∈ (S : Set (KuhnCell d)),
      (T.closedCarrier \ T.openCarrier)) ?_ ?_
    · rintro x ⟨hxU, hxout⟩
      obtain ⟨T, hT, hxT⟩ := Set.mem_iUnion₂.mp (hcover hxU)
      refine Set.mem_iUnion₂.mpr ⟨T, hT, T.carrier_subset_closedCarrier hxT, ?_⟩
      exact fun hop => hxout (Set.mem_iUnion₂.mpr ⟨T, hT, hop⟩)
    · exact (measure_biUnion_null_iff S.finite_toSet.countable).mpr
        fun T _ => volume_closedCarrier_diff_openCarrier T
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null ?_ hnull
    rintro x ⟨hxU, hx⟩
    refine ⟨hxU, fun hmem => hx ?_⟩
    obtain ⟨T, hT, hxT⟩ := Set.mem_iUnion₂.mp hmem
    exact Set.mem_iUnion₂.mpr ⟨T, hT, hxU, hxT⟩
  · refine measure_mono_null (t := (∅ : Set (Vec d))) ?_ measure_empty
    rintro x ⟨hmem, hxU⟩
    obtain ⟨T, hT, hxT⟩ := Set.mem_iUnion₂.mp hmem
    exact absurd hxT.1 hxU

/-- **The mesh splits the integral.**  An integral over a set covered by an
equal-scale mesh is the sum of the integrals over the (open) cells. -/
theorem setIntegral_eq_sum_openCarrier {S : Finset (KuhnCell d)} {U : Set (Vec d)}
    {s : ℤ} {f : Vec d → ℝ} (hU : MeasurableSet U)
    (hscale : ∀ T ∈ S, T.supportCube.scale = s)
    (hcover : U ⊆ ⋃ T ∈ (S : Set (KuhnCell d)), T.carrier)
    (hint : IntegrableOn f U volume) :
    (∫ x in U, f x) = ∑ T ∈ S, ∫ x in U ∩ T.openCarrier, f x := by
  classical
  rw [setIntegral_congr_set (ae_eq_iUnion_inter_openCarrier hcover)]
  refine integral_biUnion_finset S
    (fun T _ => hU.inter (isOpen_openCarrier T).measurableSet) ?_
    fun T _ => hint.mono_set Set.inter_subset_left
  intro T hT V hV hTV
  refine Disjoint.mono Set.inter_subset_right Set.inter_subset_right ?_
  exact disjoint_openCarrier_of_supportCube_scale_eq
    ((hscale T hT).trans (hscale V hV).symm) hTV

/-! ## The discrete energy against the continuum energy -/

/-- Bounded measurable weights against an integrable square are integrable; a
local version of `integrableOn_smul_vecNormSq_add_grad`, with the bound
required only on `U`. -/
theorem integrableOn_mul_of_integrableOn_vecNormSq {B : Vec d → ℝ} {U : Set (Vec d)}
    {F : Vec d → Vec d} {C : ℝ} (hU : MeasurableSet U) (hBmeas : Measurable B)
    (hBbd : ∀ x ∈ U, ‖B x‖ ≤ C)
    (hF : IntegrableOn (fun x => vecNormSq (F x)) U volume) :
    IntegrableOn (fun x => B x * vecNormSq (F x)) U volume :=
  hF.bdd_mul hBmeas.aestronglyMeasurable
    ((ae_restrict_iff' hU).mpr (Filter.Eventually.of_forall hBbd))

/-- On one cell of the mesh the competitor's energy integrand is a.e. constant. -/
theorem setIntegral_const_mul_vecNormSq_grad {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} {p : Vec d} {T : KuhnCell d} (hT : T ∈ S)
    (c : KuhnCompetitor U S) (a : ℝ) :
    (∫ x in U ∩ T.openCarrier, a * vecNormSq (p + c.grad x)) =
      volume.real (U ∩ T.openCarrier) * (a * vecNormSq (p + c.slope T)) := by
  rw [integral_congr_ae (g := fun _ => a * vecNormSq (p + c.slope T))
      (by filter_upwards [c.grad_ae_eq_slope hT] with x hx; rw [hx]),
    setIntegral_const, smul_eq_mul]

/-- **The paper's sum is the integral of the cellwise-constant weight.** -/
theorem kuhnDiscreteEnergy_eq_sum_setIntegral {B : Vec d → ℝ}
    {S : Finset (KuhnCell d)} {U : Set (Vec d)} {p : Vec d}
    (c : KuhnCompetitor U S) :
    kuhnDiscreteEnergy B S U p c.slope =
      ∑ T ∈ S, ∫ x in U ∩ T.openCarrier, cellSup B T * vecNormSq (p + c.grad x) :=
  Finset.sum_congr rfl fun T hT =>
    (setIntegral_const_mul_vecNormSq_grad hT c (cellSup B T)).symm

/-- **The continuum energy is dominated by the discrete one**
(`p.homogenized.coefficient.strict.decay`): termwise, `B <= sup_{closure T} B` on each cell.
Unlike `dirichletInfOn_le_kuhnEnvelope_energy` this needs no
integrability hypothesis on the envelope. -/
theorem dirichletEnergyOn'_le_kuhnDiscreteEnergy {B : Vec d → ℝ}
    {S : Finset (KuhnCell d)} {U : Set (Vec d)} {p : Vec d} {s : ℤ}
    (hU : MeasurableSet U) (hUfin : volume U ≠ ⊤)
    (hscale : ∀ T ∈ S, T.supportCube.scale = s)
    (hcover : U ⊆ ⋃ T ∈ (S : Set (KuhnCell d)), T.carrier) (hB : Continuous B)
    (c : KuhnCompetitor U S)
    (hint : IntegrableOn (fun x => B x * vecNormSq (p + c.grad x)) U volume) :
    dirichletEnergyOn' B U p c.grad ≤ kuhnDiscreteEnergy B S U p c.slope := by
  rw [dirichletEnergyOn', setIntegral_eq_sum_openCarrier hU hscale hcover hint,
    kuhnDiscreteEnergy]
  refine Finset.sum_le_sum fun T hT => ?_
  have hm : MeasurableSet (U ∩ T.openCarrier) :=
    hU.inter (isOpen_openCarrier T).measurableSet
  have hfin : volume (U ∩ T.openCarrier) ≠ ⊤ :=
    ne_top_of_le_ne_top hUfin (measure_mono Set.inter_subset_left)
  calc (∫ x in U ∩ T.openCarrier, B x * vecNormSq (p + c.grad x))
      ≤ ∫ _ in U ∩ T.openCarrier, cellSup B T * vecNormSq (p + c.slope T) := by
        refine integral_mono_ae (hint.mono_set Set.inter_subset_left)
          (integrableOn_const hfin) ?_
        filter_upwards [c.grad_ae_eq_slope hT, ae_restrict_mem hm] with x hx hxmem
        rw [hx]
        exact mul_le_mul_of_nonneg_right
          (le_cellSup T hB.continuousOn (T.openCarrier_subset_closedCarrier hxmem.2))
          (vecNormSq_nonneg _)
    _ = volume.real (U ∩ T.openCarrier) *
          (cellSup B T * vecNormSq (p + c.slope T)) := by
        rw [setIntegral_const, smul_eq_mul]

/-- **The two-sided cellwise comparison.**  The discrete energy differs from the
continuum energy of the same competitor by at most the uniform envelope error
`eta` of (S2b) times the `L^2` norm of the gradient.  This single estimate
carries both halves of the source's Step 2 argument. -/
theorem abs_kuhnDiscreteEnergy_sub_dirichletEnergyOn'_le {B : Vec d → ℝ}
    {S : Finset (KuhnCell d)} {U : Set (Vec d)} {p : Vec d} {s : ℤ} {eta : ℝ}
    (hU : MeasurableSet U) (hscale : ∀ T ∈ S, T.supportCube.scale = s)
    (hcover : U ⊆ ⋃ T ∈ (S : Set (KuhnCell d)), T.carrier)
    (hclose : ∀ T ∈ S, ∀ x ∈ T.openCarrier, |cellSup B T - B x| ≤ eta)
    (c : KuhnCompetitor U S)
    (hint : IntegrableOn (fun x => B x * vecNormSq (p + c.grad x)) U volume)
    (hnorm : IntegrableOn (fun x => vecNormSq (p + c.grad x)) U volume) :
    |kuhnDiscreteEnergy B S U p c.slope - dirichletEnergyOn' B U p c.grad| ≤
      eta * ∫ x in U, vecNormSq (p + c.grad x) := by
  rw [kuhnDiscreteEnergy_eq_sum_setIntegral c, dirichletEnergyOn',
    setIntegral_eq_sum_openCarrier hU hscale hcover hint,
    setIntegral_eq_sum_openCarrier hU hscale hcover hnorm,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun T hT => ?_)
  have hm : MeasurableSet (U ∩ T.openCarrier) :=
    hU.inter (isOpen_openCarrier T).measurableSet
  have hintT := hint.mono_set (Set.inter_subset_left (t := T.openCarrier))
  have hnormT := hnorm.mono_set (Set.inter_subset_left (t := T.openCarrier))
  have hcT : IntegrableOn
      (fun x => cellSup B T * vecNormSq (p + c.grad x)) (U ∩ T.openCarrier) volume :=
    hnormT.const_mul _
  rw [← integral_sub hcT hintT]
  calc |∫ x in U ∩ T.openCarrier,
          (cellSup B T * vecNormSq (p + c.grad x) - B x * vecNormSq (p + c.grad x))|
      ≤ ∫ x in U ∩ T.openCarrier,
          |cellSup B T * vecNormSq (p + c.grad x) - B x * vecNormSq (p + c.grad x)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in U ∩ T.openCarrier, eta * vecNormSq (p + c.grad x) := by
        refine setIntegral_mono_on (hcT.sub hintT).abs (hnormT.const_mul eta) hm
          fun x hx => ?_
        rw [← sub_mul, abs_mul, abs_of_nonneg (vecNormSq_nonneg _)]
        exact mul_le_mul_of_nonneg_right (hclose T hT x hx.2) (vecNormSq_nonneg _)
    _ = eta * ∫ x in U ∩ T.openCarrier, vecNormSq (p + c.grad x) :=
        integral_const_mul _ _

/-! ## The continuum minimum against the discrete minimum -/

/-- **The lower half of (S2c)**: the continuum Dirichlet minimum never exceeds
`Q_{R,pi}(p)`, at every mesh.  This is `p.homogenized.coefficient.strict.decay` and one half
of the convergence. -/
theorem dirichletInfOn_le_kuhnDirichletInf {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} {p : Vec d} {s : ℤ} {C : ℝ}
    [IsFiniteMeasure (volume.restrict U)] (hU : MeasurableSet U)
    (hUfin : volume U ≠ ⊤) (hscale : ∀ T ∈ S, T.supportCube.scale = s)
    (hcover : U ⊆ ⋃ T ∈ (S : Set (KuhnCell d)), T.carrier) (hB : Continuous B)
    (hB0 : ∀ x, 0 ≤ B x) (hBbd : ∀ x ∈ U, ‖B x‖ ≤ C) :
    dirichletInfOn B U p ≤ kuhnDirichletInf B S U p := by
  refine le_csInf (kuhnDiscreteEnergy_image_nonempty B S U p) ?_
  rintro E ⟨q, ⟨c, rfl⟩, rfl⟩
  have hnorm : IntegrableOn (fun x => vecNormSq (p + c.grad x)) U volume :=
    integrableOn_vecNormSq_add_grad c.toH10Function.toH1Function p
  have hint : IntegrableOn (fun x => B x * vecNormSq (p + c.grad x)) U volume :=
    integrableOn_mul_of_integrableOn_vecNormSq hU hB.measurable hBbd hnorm
  exact le_trans (dirichletInfOn_le hU hB0 c.toH10Function)
    (dirichletEnergyOn'_le_kuhnDiscreteEnergy hU hUfin hscale hcover hB c hint)

/-! ## Refinement of the mesh -/

/-- **A conforming competitor stays conforming on any refinement of the mesh.**
The slope on a fine cell is the slope of the coarse cell containing it, which
exists by `Kuhn/Cells.lean`'s `triadicSimplexPartition_refines_openCarrier`.
This is what makes the discrete class *grow* as the mesh is refined, and hence
what turns the existential mesh scale produced by (S2a) into a bound valid at
every finer scale. -/
def KuhnCompetitor.refineMesh {U : Set (Vec d)} {Q : TriadicCube d} {j j' : ℤ}
    (hj : j ≤ Q.scale) (hj' : j' ≤ j)
    (c : KuhnCompetitor U (triadicSimplexPartition Q j)) :
    KuhnCompetitor U (triadicSimplexPartition Q j') := by
  classical
  refine ⟨c.toH10Function,
    fun T => if h : ∃ V ∈ triadicSimplexPartition Q j, T.openCarrier ⊆ V.openCarrier
      then c.slope h.choose else 0, ?_⟩
  intro T hT
  have h : ∃ V ∈ triadicSimplexPartition Q j, T.openCarrier ⊆ V.openCarrier :=
    triadicSimplexPartition_refines_openCarrier Q hj hj' hT
  have hres : ∀ᵐ x ∂(volume.restrict (U ∩ T.openCarrier)),
      c.toH10Function.toH1Function.grad x = c.slope h.choose :=
    ae_mono (Measure.restrict_mono
      (Set.inter_subset_inter_right _ h.choose_spec.2) le_rfl)
      (c.grad_ae_eq_slope h.choose_spec.1)
  filter_upwards [hres] with x hx
  show c.toH10Function.toH1Function.grad x =
    (if h : ∃ V ∈ triadicSimplexPartition Q j, T.openCarrier ⊆ V.openCarrier
      then c.slope h.choose else 0)
  rw [dite_eq_left h]
  exact hx

@[simp] theorem KuhnCompetitor.refineMesh_toH10Function {U : Set (Vec d)}
    {Q : TriadicCube d} {j j' : ℤ} (hj : j ≤ Q.scale) (hj' : j' ≤ j)
    (c : KuhnCompetitor U (triadicSimplexPartition Q j)) :
    (c.refineMesh hj hj').toH10Function = c.toH10Function := rfl

@[simp] theorem KuhnCompetitor.refineMesh_grad {U : Set (Vec d)}
    {Q : TriadicCube d} {j j' : ℤ} (hj : j ≤ Q.scale) (hj' : j' ≤ j)
    (c : KuhnCompetitor U (triadicSimplexPartition Q j)) :
    (c.refineMesh hj hj').grad = c.grad := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
