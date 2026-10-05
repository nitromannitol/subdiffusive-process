module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SimplexSphereMaximum

@[expose] public section

/-!
# `q_R` as a number: the (g2) moment of the cellwise supremum

Define the discrete constant

```text
Q_{R,pi}(p) = min_{v in linear_p + (V_{R,pi} cap H_0^1(spx_0^pi))}
                (1/|spx|) sum_T |T| (sup_{closure T} B_0) |grad v|_T|^2,
q_R = max_pi sup_{|p| = 1} E[Q_{R,pi}(p)],
```

and the sentence that makes `q_R` finite is

> The affine competitor bounds `Q_{R,pi}(p)` by `|p|^2 sup_{spx_0^pi} B_0`,
> whose expectation is finite by Assumption (g2).

This file is that sentence.  Unlike the continuum bound of `MeanOneFubini.lean`
-- which needs no moment at all, because `E[int_U B_0] = |U|` -- the discrete
energy is weighted by the **cellwise supremum** `sup_{closure T} B_0`, and its
expectation is finite only by (g2).

The chain:

* `abs_apply_le_g2Observable_of_mem_closedBall` -- (g2) controls the potential
  on the *closed* unit cube, not only the open one.  The observable's own bound
  is stated on `openCubeSet`; a continuous function obeys a closed inequality on
  the closure, and `closure (openCubeSet Q) = closedBall`;
* `integrable_exp_g2Observable` -- `E[exp(g2Observable(g_0))] < infinity`.  The
  stretched-exponential exponent `sigma = 2` of (g2) dominates the linear one:
  `x <= delta^2/4 + (x/delta)^2` for every real `x`;
* `integrable_cellSup_shellFactor` -- **(g2) in the shape Step 2 uses it**:
  `E[sup_{closure T} B_0] < infinity` for every cell of the unit cube;
* `integrable_kuhnDirichletInf_shellFactor` -- hence `Q_{R,pi}(p)` is integrable,
  by the affine competitor;
* `qRSlope`, `qRCell` -- the discrete analogues of `qStarSlope` and `qStarCell`,
  with `qStarCell_le_qRCell` recording `q_* <= q_R`.

## Scope

* The cells are required to lie in the closed unit cube, which is where (g2)
  lives; `closedCarrier_subset_closedBall_of_mem_triadicSimplexPartition`
  supplies this for every mesh of `originCube d 0`.
* `qRCell` is a supremum, not a maximum: boundedness above is proved (that is
  what makes it a number), attainment is not needed for the comparisons here.
* The convergence `q_R -> q_*` is not proved here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open MeasureTheory Homogenization Homogenization.Book Kuhn
open _root_.SubdiffusiveProcess.Model

noncomputable section

variable {d : ℕ}

/-! ## (g2) on the closed unit cube -/

/-- The closure of an open triadic cube is the closed ball around its center. -/
theorem closure_openCubeSet (Q : TriadicCube d) :
    closure (openCubeSet Q) = Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
  rw [← ball_cubeCenter_eq_openCubeSet, closure_ball _ (ne_of_gt (cubeRadius_pos Q))]

/-- **(g2) on the closed unit cube.**  The observable of `(g2)` bounds the
potential on `openCubeSet (originCube d 0)`; the bound is a closed condition and
the field is continuous, so it extends to the closure.  Cells of a mesh of the
unit cube touch its boundary, so this extension is what the cellwise supremum
needs. -/
theorem abs_apply_le_g2Observable_of_mem_closedBall (g : PotentialField d)
    {x : Vec d}
    (hx : x ∈ Metric.closedBall (cubeCenter (originCube d 0))
      (cubeRadius (originCube d 0))) :
    |g x| ≤ _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g := by
  have hclosed : IsClosed {y : Vec d | |g y| ≤ _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g} :=
    isClosed_le (g.contDiff_one.continuous.abs) continuous_const
  have hsub : openCubeSet (originCube d 0) ⊆
      {y : Vec d | |g y| ≤ _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g} := fun y hy =>
    _root_.SubdiffusiveProcess.Model.PotentialField.abs_apply_le_g2Observable g hy
  have hclos := closure_minimal hsub hclosed
  rw [closure_openCubeSet] at hclos
  exact hclos hx

/-! ## The exponential moment of the `(g2)` observable -/

/-- **`E[exp(g2Observable(g_0))] < infinity`.**  The `Gamma_2` control of (g2)
dominates every linear exponential moment, because
`x <= delta^2/4 + (x/delta)^2`. -/
theorem integrable_exp_g2Observable (M : GMCModel d) :
    Integrable (fun omega : PotentialSample d =>
      Real.exp (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable (omega 0))) M.P.toMeasure := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  set E : PotentialField d → ℝ := _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable with hEdef
  set Z : PotentialField d → ℝ := fun g =>
    Real.exp ((M.delta⁻¹ * max (E g) 0) ^ (2 : ℝ)) with hZdef
  have hZint : Integrable Z (zeroPotentialLaw M.P).toMeasure := by
    simpa [hZdef, hEdef, SubdiffusiveProcess.OGammaLE] using M.G2.regularity_expectation.1
  have hmeasE : Measurable E := _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable
  have hmeas : Measurable fun g : PotentialField d => Real.exp (E g) := hmeasE.exp
  have hdom : ∀ g : PotentialField d,
      Real.exp (E g) ≤ Real.exp (M.delta ^ 2 / 4) * Z g := by
    intro g
    have hE0 : 0 ≤ E g := _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg g
    have hZg : Z g = Real.exp ((M.delta⁻¹ * E g) ^ (2 : ℕ)) := by
      simp only [hZdef, max_eq_left hE0]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hZg, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hexpand : M.delta ^ 2 / 4 + (M.delta⁻¹ * E g) ^ (2 : ℕ) - E g
        = (E g - M.delta ^ 2 / 2) ^ 2 / M.delta ^ 2 := by
      field_simp
      ring
    have h2 : 0 ≤ M.delta ^ 2 / 4 + (M.delta⁻¹ * E g) ^ (2 : ℕ) - E g := by
      rw [hexpand]; positivity
    linarith
  have hlaw : Integrable (fun g : PotentialField d => Real.exp (E g))
      (zeroPotentialLaw M.P).toMeasure := by
    refine (hZint.const_mul (Real.exp (M.delta ^ 2 / 4))).mono'
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hdom g
  have hmap : (zeroPotentialLaw M.P).toMeasure =
      Measure.map (fun omega : PotentialSample d => omega 0) M.P.toMeasure := by
    rw [zeroPotentialLaw, potentialMarginalLaw, ProbabilityMeasure.toMeasure_map]
  rw [hmap] at hlaw
  exact (integrable_map_measure hmeas.aestronglyMeasurable
    (measurable_potentialCoordinate 0).aemeasurable).1 hlaw

/-! ## The moment of the cellwise supremum -/

/-- **The mesh-uniform envelope of `B_0`.**  Every cell of every mesh of the
unit cube lies in the closed unit cube, so this single integrable random
variable dominates `sup_{closure T} B_0` at every scale simultaneously.  That
uniformity is what makes the modulus of `DiscreteSlopeModulus.lean` independent
of the mesh. -/
def shellEnvelope (M : GMCModel d) (omega : PotentialSample d) : ℝ :=
  Real.exp (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable (omega 0) - tauSq M.P)

theorem shellEnvelope_pos (M : GMCModel d) (omega : PotentialSample d) :
    0 < shellEnvelope M omega := Real.exp_pos _

theorem integrable_shellEnvelope (M : GMCModel d) :
    Integrable (shellEnvelope M) M.P.toMeasure := by
  refine ((integrable_exp_g2Observable M).const_mul
    (Real.exp (-tauSq M.P))).congr (Filter.Eventually.of_forall fun omega => ?_)
  show Real.exp (-tauSq M.P) * Real.exp (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable (omega 0)) =
    shellEnvelope M omega
  rw [shellEnvelope, ← Real.exp_add]
  ring_nf

/-- The cellwise supremum of `B_0` on a cell of the unit cube is dominated by
the exponential of the `(g2)` observable. -/
theorem cellSup_shellFactor_le (M : GMCModel d) (omega : PotentialSample d)
    {T : KuhnCell d}
    (hT : T.closedCarrier ⊆ Metric.closedBall (cubeCenter (originCube d 0))
      (cubeRadius (originCube d 0))) :
    cellSup (shellFactor M 0 omega) T ≤
      Real.exp (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable (omega 0) - tauSq M.P) := by
  refine csSup_le (T.closedCarrier_nonempty.image _) ?_
  rintro y ⟨x, hx, rfl⟩
  refine Real.exp_le_exp.mpr ?_
  have habs := abs_apply_le_g2Observable_of_mem_closedBall (omega 0) (hT hx)
  have hle : omega 0 x ≤ |omega 0 x| := le_abs_self _
  linarith

theorem cellSup_shellFactor_nonneg (M : GMCModel d) (omega : PotentialSample d)
    (T : KuhnCell d) : 0 ≤ cellSup (shellFactor M 0 omega) T :=
  le_trans (shellFactor_pos M 0 omega (T.vertex 0)).le
    (le_cellSup T (continuous_shellFactor M 0 omega).continuousOn
      (T.vertex_mem_closedCarrier 0))

theorem measurable_cellSup_shellFactor (M : GMCModel d) (T : KuhnCell d) :
    Measurable fun omega : PotentialSample d => cellSup (shellFactor M 0 omega) T :=
  measurable_cellSup T (fun omega => continuous_shellFactor M 0 omega)
    fun y => (measurable_shell_eval 0 y).sub measurable_const |>.exp

/-- **(g2) in the shape Step 2 consumes it**: `E[sup_{closure T} B_0]` is finite
on every cell of the unit cube.  This is the only place in the strict-decay
chain where a moment assumption is used. -/
theorem integrable_cellSup_shellFactor (M : GMCModel d) {T : KuhnCell d}
    (hT : T.closedCarrier ⊆ Metric.closedBall (cubeCenter (originCube d 0))
      (cubeRadius (originCube d 0))) :
    Integrable (fun omega : PotentialSample d => cellSup (shellFactor M 0 omega) T)
      M.P.toMeasure := by
  refine ((integrable_exp_g2Observable M).const_mul (Real.exp (-tauSq M.P))).mono'
    (measurable_cellSup_shellFactor M T).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (cellSup_shellFactor_nonneg M omega T)]
  refine le_trans (cellSup_shellFactor_le M omega hT) (le_of_eq ?_)
  rw [← Real.exp_add]
  ring_nf

/-! ## Integrability of the discrete minimum -/

/-- The affine competitor bounds the discrete minimum by the cellwise-supremum
sum:  -/
theorem kuhnDirichletInf_le_affine {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec d) :
    kuhnDirichletInf B S U p ≤
      ∑ T ∈ S, volume.real (U ∩ T.openCarrier) * (cellSup B T * vecNormSq p) := by
  have h := kuhnDirichletInf_le hB hB0 p (0 : KuhnCompetitor U S)
  rw [kuhnDiscreteEnergy] at h
  simpa using h

/-- **`Q_{R,pi}(p)` is integrable.**  Measurability is the measurability argument's
`measurable_kuhnDirichletInf`; finiteness is the affine competitor against
(g2). -/
theorem integrable_kuhnDirichletInf_shellFactor (M : GMCModel d)
    {S : Finset (KuhnCell d)}
    (hS : ∀ T ∈ S, T.closedCarrier ⊆ Metric.closedBall (cubeCenter (originCube d 0))
      (cubeRadius (originCube d 0)))
    (U : Set (Vec d)) (p : Vec d) :
    Integrable (fun omega : PotentialSample d =>
      kuhnDirichletInf (shellFactor M 0 omega) S U p) M.P.toMeasure := by
  classical
  have hmeas : Measurable fun omega : PotentialSample d =>
      kuhnDirichletInf (shellFactor M 0 omega) S U p :=
    measurable_kuhnDirichletInf (fun omega => continuous_shellFactor M 0 omega)
      (fun omega x => (shellFactor_pos M 0 omega x).le)
      fun T _ => measurable_cellSup_shellFactor M T
  have hdom : Integrable (fun omega : PotentialSample d =>
      ∑ T ∈ S, volume.real (U ∩ T.openCarrier) *
        (cellSup (shellFactor M 0 omega) T * vecNormSq p)) M.P.toMeasure := by
    refine integrable_finsetSum S fun T hT => ?_
    exact ((integrable_cellSup_shellFactor M (hS T hT)).mul_const
      (vecNormSq p)).const_mul _
  refine hdom.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (kuhnDirichletInf_nonneg
    (continuous_shellFactor M 0 omega) (fun x => (shellFactor_pos M 0 omega x).le) p)]
  exact kuhnDirichletInf_le_affine (continuous_shellFactor M 0 omega)
    (fun x => (shellFactor_pos M 0 omega x).le) p

/-! ## `q_R` -/

/-- **`E[Q_{R,pi}(p)]`**, normalized by
`|spx_0^pi|` as the source's `fint` is. -/
def qRSlope (M : GMCModel d) (S : Finset (KuhnCell d)) (T : KuhnCell d) (p : Vec d) : ℝ :=
  (volume T.openCarrier).toReal⁻¹ *
    ∫ omega, kuhnDirichletInf (shellFactor M 0 omega) S T.openCarrier p
      ∂M.P.toMeasure

theorem qRSlope_nonneg (M : GMCModel d) (S : Finset (KuhnCell d)) (T : KuhnCell d)
    (p : Vec d) : 0 ≤ qRSlope M S T p := by
  refine mul_nonneg (by positivity) (integral_nonneg fun omega => ?_)
  exact kuhnDirichletInf_nonneg (continuous_shellFactor M 0 omega)
    (fun x => (shellFactor_pos M 0 omega x).le) p

/-- The domination that makes `q_R` a number: on the unit sphere the discrete
constants are bounded by one `(g2)` expectation. -/
theorem qRSlope_le (M : GMCModel d) {S : Finset (KuhnCell d)}
    (hS : ∀ T ∈ S, T.closedCarrier ⊆ Metric.closedBall (cubeCenter (originCube d 0))
      (cubeRadius (originCube d 0)))
    (T : KuhnCell d) {p : Vec d} (hp : p ∈ vecUnitSphere d) :
    qRSlope M S T p ≤ (volume T.openCarrier).toReal⁻¹ *
      ∑ V ∈ S, volume.real (T.openCarrier ∩ V.openCarrier) *
        ∫ omega, cellSup (shellFactor M 0 omega) V ∂M.P.toMeasure := by
  have hp1 : vecNormSq p = 1 := hp
  have hint := integrable_kuhnDirichletInf_shellFactor M hS T.openCarrier p
  have hdom : Integrable (fun omega : PotentialSample d =>
      ∑ V ∈ S, volume.real (T.openCarrier ∩ V.openCarrier) *
        (cellSup (shellFactor M 0 omega) V * vecNormSq p)) M.P.toMeasure := by
    refine integrable_finsetSum S fun V hV => ?_
    exact ((integrable_cellSup_shellFactor M (hS V hV)).mul_const
      (vecNormSq p)).const_mul _
  have hle := integral_mono hint hdom fun omega =>
    kuhnDirichletInf_le_affine (continuous_shellFactor M 0 omega)
      (fun x => (shellFactor_pos M 0 omega x).le) p
  rw [integral_finsetSum S (fun V hV =>
    ((integrable_cellSup_shellFactor M (hS V hV)).mul_const (vecNormSq p)).const_mul _)]
    at hle
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine hle.trans (le_of_eq (Finset.sum_congr rfl fun V _ => ?_))
  rw [hp1, integral_const_mul, integral_mul_const]
  ring

/-- **`q_R(pi) = sup_{|p| = 1} E[Q_{R,pi}(p)]`**, the discrete analogue of
`qStarCell`. -/
def qRCell (M : GMCModel d) (S : Finset (KuhnCell d)) (T : KuhnCell d) : ℝ :=
  sSup (qRSlope M S T '' vecUnitSphere d)

theorem bddAbove_qRSlope_image (M : GMCModel d) {S : Finset (KuhnCell d)}
    (hS : ∀ T ∈ S, T.closedCarrier ⊆ Metric.closedBall (cubeCenter (originCube d 0))
      (cubeRadius (originCube d 0)))
    (T : KuhnCell d) : BddAbove (qRSlope M S T '' vecUnitSphere d) := by
  refine ⟨(volume T.openCarrier).toReal⁻¹ *
    ∑ V ∈ S, volume.real (T.openCarrier ∩ V.openCarrier) *
      ∫ omega, cellSup (shellFactor M 0 omega) V ∂M.P.toMeasure, ?_⟩
  rintro y ⟨p, hp, rfl⟩
  exact qRSlope_le M hS T hp

theorem qRSlope_le_qRCell (M : GMCModel d) {S : Finset (KuhnCell d)}
    (hS : ∀ T ∈ S, T.closedCarrier ⊆ Metric.closedBall (cubeCenter (originCube d 0))
      (cubeRadius (originCube d 0)))
    (T : KuhnCell d) {p : Vec d} (hp : p ∈ vecUnitSphere d) :
    qRSlope M S T p ≤ qRCell M S T :=
  le_csSup (bddAbove_qRSlope_image M hS T) ⟨p, hp, rfl⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
