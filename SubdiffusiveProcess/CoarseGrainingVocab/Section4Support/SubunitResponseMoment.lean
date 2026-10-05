module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.EllipticitySpecialization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

@[expose] public section

/-!
# Section 4 support: subunit response moments

This module composes the source-exact deterministic scalar response bound with
the absolute-cutoff grid moment.  The scale-`k` descendants of the centered
scale-`m` cube are the canonical Lean carrier for
`3^k Z^d ∩ cube_m` in `e.moment.bound.for.J.subunit`.

The deterministic/moment split mirrors
`Algsuperdiff/Section3/Provider/MultiscaleEstimate/HomogenizationInput.lean`:
first dominate every cell response by one parent-cube observable, then apply
the already-proved moment estimate only once.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The exact subunit response carrier in `e.moment.bound.for.J.subunit`.
The two `iSup`s are the source's supremum over `L ≥ m` and spatial maximum
over the scale-`k` grid inside `cube_m`; `paperScalarProbeMaxOn` is its
unit-sphere maximum. -/
noncomputable def subunitResponseObservable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ L : {L : ℕ // m ≤ L},
    ⨆ R : {R : TriadicCube d //
        R ∈ descendantsAtScale (originCube d (m : ℤ)) k},
      paperScalarProbeMaxOn (Ch02.cubeDomain R.1)
        (aCutoffCoeffOnData M L.1 omega (Ch02.cubeDomain R.1)).toCoeffOn
        (tailCoefficientCubeAverage M L.1 m omega)

private theorem ratio_add_inv_sub_two_nonneg {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    0 ≤ a / b + b / a - 2 := by
  have hr : 0 < a / b := div_pos ha hb
  have hid : a / b + b / a - 2 = ((a / b - 1) ^ 2) / (a / b) := by
    field_simp [ha.ne', hb.ne']
    ring
  rw [hid]
  exact div_nonneg (sq_nonneg _) hr.le

private theorem integrableOn_cutoff_tail_ratio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (U : Ch02.Domain d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    IntegrableOn (fun x =>
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          tailCoefficientCubeAverage M L m omega +
        tailCoefficientCubeAverage M L m omega /
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x - 2)
      (U : Set (Vec d)) := by
  have hcontinuous : Continuous (fun x =>
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          tailCoefficientCubeAverage M L m omega +
        tailCoefficientCubeAverage M L m omega /
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x - 2) := by
    exact ((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).div_const _).add
      (continuous_const.div
        (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega)
        (fun x => (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).ne')) |>.sub
          continuous_const
  exact (hcontinuous.continuousOn.integrableOn_compact
    U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set
      subset_closure

/-- Every subunit cell response is bounded by the single parent-cube ratio
observable.  The normalized spatial average costs no grid-cardinality factor:
each cell is contained in the parent and the integrand is nonnegative. -/
theorem subunitResponseObservable_le_subunitTailRatioObservable
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) {k : ℤ}
    (hk : k ≤ (m : ℤ)) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    subunitResponseObservable M m k omega ≤
      subunitTailRatioObservable M m omega := by
  unfold subunitResponseObservable
  apply iSup_le
  intro L
  apply iSup_le
  intro R
  let U : Ch02.Domain d := Ch02.cubeDomain R.1
  let f : Vec d → ℝ := fun x =>
    _root_.SubdiffusiveProcess.Model.aCutoff M L.1 omega x /
        tailCoefficientCubeAverage M L.1 m omega +
      tailCoefficientCubeAverage M L.1 m omega /
        _root_.SubdiffusiveProcess.Model.aCutoff M L.1 omega x - 2
  let B : ℝ≥0∞ := subunitTailRatioObservable M m omega
  have hdirect :
      paperScalarProbeMaxOn U
          (aCutoffCoeffOnData M L.1 omega U).toCoeffOn
          (tailCoefficientCubeAverage M L.1 m omega) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) * Ch02.average U f) := by
    exact paperScalarProbeMaxOn_cutoff_le_tail_ratio_energy
      M L.1 m U omega
  refine hdirect.trans ?_
  change ENNReal.ofReal ((1 / 2 : ℝ) * Ch02.average U f) ≤ B
  by_cases hBtop : B = ⊤
  · rw [hBtop]
    exact le_top
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact ratio_add_inv_sub_two_nonneg
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L.1 omega x)
      (tailCoefficientCubeAverage_pos M L.1 m omega)
  have hf_integrable : IntegrableOn f (U : Set (Vec d)) := by
    exact integrableOn_cutoff_tail_ratio M L.1 m U omega
  have hf_le : ∀ x ∈ (U : Set (Vec d)), f x ≤ B.toReal := by
    intro x hx
    have hxParent : x ∈ openCubeSet (originCube d (m : ℤ)) :=
      openCubeSet_subset_of_mem_descendantsAtScale hk R.2 hx
    have hpoint : ENNReal.ofReal |f x| ≤ B := by
      apply le_iSup_of_le L
      apply le_iSup_of_le
        (⟨x, hxParent⟩ : {y : Vec d //
          y ∈ openCubeSet (originCube d (m : ℤ))})
      exact le_rfl
    have hpoint' : ENNReal.ofReal (f x) ≤ B := by
      simpa [abs_of_nonneg (hf_nonneg x), f, B] using hpoint
    exact (ENNReal.ofReal_le_iff_le_toReal hBtop).mp hpoint'
  have hvol : (volume (U : Set (Vec d))).toReal ≠ 0 :=
    (Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U).ne'
  have havg_le : Ch02.average U f ≤ B.toReal :=
    volumeAverage_le_of_le_on U.measurableSet hf_integrable hvol hf_le
  have havg_nonneg : 0 ≤ Ch02.average U f :=
    volumeAverage_nonneg_of_nonneg_on U.measurableSet
      (fun x _ => hf_nonneg x)
  apply (ENNReal.ofReal_le_iff_le_toReal hBtop).2
  nlinarith

private theorem paperENNRealLpNorm_mono_internal
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {xi : ℝ} (hxi : 0 ≤ xi) {X Y : Omega → ℝ≥0∞}
    (hXY : ∀ omega, X omega ≤ Y omega) :
    paperENNRealLpNorm mu xi X ≤ paperENNRealLpNorm mu xi Y := by exact SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm_mono (Ω := Omega) (μ := mu) (ξ := xi) (hξ := hxi) (X := X) (Y := Y) (hXY := hXY)

/-- `e.moment.bound.for.J.subunit`, with
the manuscript's `3^k Z^d ∩ cube_m` represented by the scale-`k`
descendants of the centered scale-`m` cube. -/
theorem subunit_response_moment {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (xi delta1 s : ℝ) (m : ℕ) (k : ℤ),
        1 ≤ xi → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        0 < s → s ≤ 1 →
        4 * (d : ℝ) * s⁻¹ ≤ xi →
        xi ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
        k < 0 →
        paperENNRealLpNorm M.P.toMeasure xi
            (subunitResponseObservable M m k) ≤
          ENNReal.ofReal (C * delta1 * (3 : ℝ) ^ (s * (m : ℝ))) := by
  rcases subunit_tail_ratio_moment (d := d) with
    ⟨c, C, hc, hc1, hC, hmoment⟩
  refine ⟨c, C, hc, hc1, hC, ?_⟩
  intro M xi delta1 s m k hxi hdelta hdelta1 hs hs1 hxid hxic hk
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hkm : k ≤ (m : ℤ) := by
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast Nat.zero_le m
    exact hk.le.trans hm0
  calc
    paperENNRealLpNorm M.P.toMeasure xi
        (subunitResponseObservable M m k) ≤
      paperENNRealLpNorm M.P.toMeasure xi
        (subunitTailRatioObservable M m) :=
      paperENNRealLpNorm_mono_internal M.P.toMeasure
        (zero_le_one.trans hxi)
        (subunitResponseObservable_le_subunitTailRatioObservable
          M m hkm)
    _ ≤ ENNReal.ofReal (C * delta1 * (3 : ℝ) ^ (s * (m : ℝ))) :=
      hmoment M xi delta1 s m hxi hdelta hdelta1 hs hs1 hxid hxic

end

end SubdiffusiveProcess.CoarseGrainingVocab
