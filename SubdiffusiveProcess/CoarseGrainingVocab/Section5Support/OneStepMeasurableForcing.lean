module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMeasurableSolutionOperator
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellW1pPackaging
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.HilbertWeakMeasurability
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section

/-!
# Measurable `L²` forcing class for the one-step shell

The literal field `(exp(h)-1) p` is jointly measurable in the sample and
spatial variables.  Pairing its `L²` class with every fixed Hilbert-space
probe is therefore measurable by Fubini.  The countable Hilbert-basis result
in `HilbertWeakMeasurability` upgrades these scalar pairings to strong Borel
measurability of the `HilbertVectorL2`-valued forcing.  This avoids requiring
a second-countability instance on the global compact-open
continuous-function carrier.

-/

open MeasureTheory Homogenization Topology
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section



/-- The one-step suffix multiplier as a bundled continuous spatial field. -/
def oneStepMultiplierContinuousMap {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    C(Vec d, ℝ) where
  toFun := fun x => Real.exp
    (cutoffShellSum (n + h) (n : ℤ) x omega -
      (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1
  continuous_toFun := by
    exact (Real.continuous_exp.comp
      ((continuous_finsetSum _ fun k _ =>
        (omega k).1.1.continuous).sub continuous_const)).sub continuous_const

/-- The bundled multiplier represents the literal forcing multiplier. -/
@[simp] theorem oneStepMultiplierContinuousMap_apply {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) (hh : 0 < h) :
    oneStepMultiplierContinuousMap M n h omega x =
      oneStepMultiplierAt M n h x omega := by
  change Real.exp
      (cutoffShellSum (n + h) (n : ℤ) x omega -
        (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1 = _
  rw [oneStepMultiplierAt, cutoffRatioMinusOne_eq_exp_shell]
  · have hdiff : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
      push_cast
      ring
    rw [hdiff]
  · omega
  · exact_mod_cast Nat.lt_add_of_pos_right hh

/-- The literal shell multiplier is jointly measurable in the sample and the
spatial variable.  This avoids asking for a second-countability instance on
the global compact-open continuous-function carrier. -/
theorem measurable_oneStepMultiplierAt_uncurry {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) :
    Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      oneStepMultiplierAt M n h q.2 q.1 := by
  by_cases hh : 0 < h
  ·
    have hEvalRaw : Measurable
        (Function.uncurry fun x : Vec d =>
          fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => g x) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun g => g.1.1.continuous)
        (fun x => _root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x)
    have hEval : Measurable fun q :
        _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d => q.1 q.2 := by
      simpa only [Function.comp_apply] using! hEvalRaw.comp measurable_swap
    have hshell : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
        cutoffShellSum (n + h) (n : ℤ) q.2 q.1 := by
      unfold cutoffShellSum
      exact Finset.measurable_sum _ fun k _ =>
        hEval.comp
          (((_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k).comp
            measurable_fst).prodMk measurable_snd)
    have hraw : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
        Real.exp
          (cutoffShellSum (n + h) (n : ℤ) q.2 q.1 -
            (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1 :=
      (hshell.sub_const _).exp.sub_const _
    convert hraw using 1
    funext q
    rw [oneStepMultiplierAt, cutoffRatioMinusOne_eq_exp_shell]
    · congr 2
      push_cast
      ring
    · omega
    · exact_mod_cast Nat.lt_add_of_pos_right hh
  · have hz : h = 0 := Nat.eq_zero_of_not_pos hh
    subst h
    have heq : (fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
        oneStepMultiplierAt M n 0 q.2 q.1) = fun _ => (0 : ℝ) := by
      funext q
      simp [oneStepMultiplierAt, cutoffRatioMinusOne, aCutoffAtInt,
        show ¬ ((n : ℤ) < 0) by omega,
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n q.1 q.2).ne']
    rw [heq]
    exact measurable_const

section Cube

variable {d : ℕ}

/-- A continuous vector field is square-integrable on an open triadic cube. -/
theorem memVectorL2_openCubeSet_of_continuous (Q : TriadicCube d)
    {g : Vec d → Vec d} (hg : Continuous g) :
    MemVectorL2 (openCubeSet Q) g := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using!
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hcompact : IsCompact
      (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  have hsub : cubeSet Q ⊆
      Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q
  have hae : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ‖g x‖ ≤ C := by
    rw [volumeMeasureOn, ae_restrict_iff' (measurableSet_openCubeSet Q)]
    filter_upwards with x hx
    exact hC x (hsub (openCubeSet_subset_cubeSet Q hx))
  exact memLp_top_of_bound hg.aestronglyMeasurable C hae |>.mono_exponent le_top

/-- Open triadic cubes have finite restricted volume. -/
theorem isFiniteMeasure_volumeMeasureOn_openCubeSet (Q : TriadicCube d) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
  simpa [volumeMeasureOn] using!
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The `L²` forcing class associated with a continuous scalar multiplier. -/
def oneStepContinuousScalarForcingL2 (Q : TriadicCube d) (p : Vec d)
    (f : C(Vec d, ℝ)) : HilbertVectorL2 (openCubeSet Q) :=
  toHilbertVectorL2OfVecField
    (memVectorL2_openCubeSet_of_continuous Q (g := fun x => f x • p)
      (f.continuous.smul (continuous_const : Continuous fun _ : Vec d => p)))

/-- A pointwise bound on a cube controls the norm of its Hilbert `L²` class. -/
theorem norm_oneStepToHilbertVectorL2OfVecField_le_of_bound_on
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) {f : Vec d → Vec d} (hf : MemVectorL2 U f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ U, ‖f x‖ ≤ C) :
    ‖toHilbertVectorL2OfVecField hf‖ ≤
      ((volumeMeasureOn U) Set.univ).toReal ^ ((2 : ℝ)⁻¹) * ((d : ℝ) * C) := by
  have hae : ∀ᵐ x ∂(volumeMeasureOn U),
      ‖hilbertifyVecField f x‖ ≤ (d : ℝ) * C := by
    rw [volumeMeasureOn, ae_restrict_iff' hU]
    filter_upwards with x hx
    exact le_trans (HilbertVec.norm_ofVec_le_mul_norm (f x))
      (mul_le_mul_of_nonneg_left (hb x hx) (by positivity))
  have hnorm : ‖toHilbertVectorL2OfVecField hf‖ =
      (eLpNorm (hilbertifyVecField f) 2 (volumeMeasureOn U)).toReal := by
    rw [toHilbertVectorL2OfVecField, toHilbertVectorL2, Lp.norm_toLp]
  have hbound := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞))
    (memHilbertVectorL2_hilbertifyVecField hf).aestronglyMeasurable hae
  have hfin : ((volumeMeasureOn U) Set.univ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ *
      ENNReal.ofReal ((d : ℝ) * C) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity)
        (measure_ne_top (volumeMeasureOn U) Set.univ))
      ENNReal.ofReal_ne_top
  rw [hnorm]
  refine le_trans (ENNReal.toReal_mono hfin hbound) ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity)]
  norm_num

/-- Passage from a compact-open scalar multiplier to its vector `L²` forcing
class on a fixed cube is continuous. -/
theorem continuous_oneStepContinuousScalarForcingL2
    (Q : TriadicCube d) (p : Vec d) :
    Continuous (oneStepContinuousScalarForcingL2 Q p) := by
  obtain ⟨R, hR, hball⟩ := (isOpenBoundedConvexDomain_openCubeSet Q).2.1
  have hKcpt : IsCompact (Metric.closedBall (0 : Vec d) R) :=
    isCompact_closedBall _ _
  have hUK : openCubeSet Q ⊆ Metric.closedBall (0 : Vec d) R := by
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hR.le).2 fun i => by
      simpa [Real.norm_eq_abs] using! hball x hx i
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let A : ℝ :=
    ((volumeMeasureOn (openCubeSet Q)) Set.univ).toReal ^ ((2 : ℝ)⁻¹) *
      ((d : ℝ) * ‖p‖)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine UniformContinuous.continuous ?_
  rw [uniformContinuous_def]
  intro V hV
  obtain ⟨eps, heps, hepsV⟩ := Metric.mem_uniformity_dist.1 hV
  have hdelta : 0 < eps / (A + 1) := by positivity
  refine (ContinuousMap.mem_compactConvergence_entourage_iff _).2
    ⟨Metric.closedBall (0 : Vec d) R,
      {q : ℝ × ℝ | |q.1 - q.2| < eps / (A + 1)}, hKcpt, ?_, ?_⟩
  · simpa [Real.dist_eq] using! Metric.dist_mem_uniformity hdelta
  · rintro ⟨f, g⟩ hfg
    refine hepsV ?_
    have hf : MemVectorL2 (openCubeSet Q) (fun x => f x • p) :=
      memVectorL2_openCubeSet_of_continuous Q (f.continuous.smul continuous_const)
    have hg : MemVectorL2 (openCubeSet Q) (fun x => g x • p) :=
      memVectorL2_openCubeSet_of_continuous Q (g.continuous.smul continuous_const)
    have hpoint : ∀ x ∈ openCubeSet Q,
        ‖f x • p - g x • p‖ ≤ eps / (A + 1) * ‖p‖ := by
      intro x hx
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hfg x (hUK hx)).le (norm_nonneg p)
    have hstep :
        ‖oneStepContinuousScalarForcingL2 Q p f -
            oneStepContinuousScalarForcingL2 Q p g‖ ≤
          A * (eps / (A + 1)) := by
      have hsub : oneStepContinuousScalarForcingL2 Q p f -
          oneStepContinuousScalarForcingL2 Q p g =
          toHilbertVectorL2OfVecField (hf.sub hg) := by
        simpa only [oneStepContinuousScalarForcingL2] using!
          (toHilbertVectorL2OfVecField_sub hf hg).symm
      rw [hsub]
      refine le_trans
        (norm_oneStepToHilbertVectorL2OfVecField_le_of_bound_on
          (measurableSet_openCubeSet Q) (hf.sub hg) (by positivity) hpoint) ?_
      dsimp [A]
      ring_nf
      exact le_rfl
    have hfinal : A * (eps / (A + 1)) < eps := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hstep hfinal

/-- The exact literal one-step forcing as a measurable `L²` class. -/
def oneStepShellForcingL2
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    HilbertVectorL2 (openCubeSet Q) :=
  oneStepContinuousScalarForcingL2 Q p
    (oneStepMultiplierContinuousMap M n h omega)

/-- The measurable forcing class is definitionally the class of the literal
Sobolev datum used by the pointwise corrector construction. -/
theorem oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepShellForcingL2 M n h p Q omega =
      toHilbertVectorL2OfVecField
        ((oneStepShellForcingH1 M n h omega p Q hh).memVectorL2_toField_openCubeSet) := by
  change toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        (g := fun x => oneStepMultiplierContinuousMap M n h omega x • p)
        ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
          (continuous_const : Continuous fun _ : Vec d => p))) = _
  apply Lp.ext
  filter_upwards
    [coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        (g := fun x => oneStepMultiplierContinuousMap M n h omega x • p)
        ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
          (continuous_const : Continuous fun _ : Vec d => p))),
      coeFn_toHilbertVectorL2OfVecField
        ((oneStepShellForcingH1 M n h omega p Q hh).memVectorL2_toField_openCubeSet)]
    with x hx hy
  rw [hx, hy]
  change HilbertVec.ofVec
      (oneStepMultiplierContinuousMap M n h omega x • p) =
    HilbertVec.ofVec
      ((oneStepShellForcingH1 M n h omega p Q hh).toField x)
  rw [oneStepMultiplierContinuousMap_apply M n h omega x hh]
  rfl

/-- Every fixed Hilbert `L²` probe of a nonempty one-step forcing block is
measurable in the sample.  This scalar-probe form follows directly from joint
sample/space measurability and Fubini. -/
theorem measurable_inner_oneStepShellForcingL2
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (Y : HilbertVectorL2 (openCubeSet Q)) :
    Measurable fun omega =>
      inner ℝ (oneStepShellForcingL2 M n h p Q omega) Y := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hmult : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      oneStepMultiplierAt M n h q.2 q.1 :=
    measurable_oneStepMultiplierAt_uncurry M n h
  have hY : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      (Y : Vec d → HilbertVec d) q.2 :=
    (MeasureTheory.Lp.stronglyMeasurable Y).measurable.comp measurable_snd
  have hint : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      inner ℝ
        (oneStepMultiplierAt M n h q.2 q.1 • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) q.2) :=
    (hmult.smul_const (HilbertVec.ofVec p)).inner hY
  have hparam : Measurable fun omega =>
      ∫ x, inner ℝ
        (oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) x)
        ∂(volumeMeasureOn (openCubeSet Q)) :=
    hint.stronglyMeasurable.integral_prod_right'.measurable
  have heq : (fun omega =>
      inner ℝ (oneStepShellForcingL2 M n h p Q omega) Y) =
      fun omega =>
        ∫ x, inner ℝ
          (oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
          ((Y : Vec d → HilbertVec d) x)
          ∂(volumeMeasureOn (openCubeSet Q)) := by
    funext omega
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards
      [coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d => p)))]
      with x hx
    change inner ℝ
      ((toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d => p))) :
          Vec d → HilbertVec d) x) ((Y : Vec d → HilbertVec d) x) = _
    rw [hx]
    change inner ℝ
      (oneStepMultiplierContinuousMap M n h omega x • HilbertVec.ofVec p)
      ((Y : Vec d → HilbertVec d) x) = _
    rw [oneStepMultiplierContinuousMap_apply M n h omega x hh]
  rw [heq]
  exact hparam



theorem measurable_oneStepShellForcingL2
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    Measurable (oneStepShellForcingL2 M n h p Q) := by
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  exact measurable_of_forall_real_inner_right fun Y =>
    measurable_inner_oneStepShellForcingL2 M n h p Q hh Y

/-- Negation commutes with the plain-vector to Hilbert-`L²` realization. -/
theorem toHilbertVectorL2OfVecField_neg_oneStep
    {Q : TriadicCube d} {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    toHilbertVectorL2OfVecField hg.neg =
      -toHilbertVectorL2OfVecField hg := by
  apply Lp.ext
  filter_upwards
    [coeFn_toHilbertVectorL2OfVecField hg.neg,
      coeFn_toHilbertVectorL2OfVecField hg,
      Lp.coeFn_neg (toHilbertVectorL2OfVecField hg)]
    with x hneg hpos hminus
  rw [hneg]
  calc
    hilbertifyVecField (-g) x = -hilbertifyVecField g x := rfl
    _ = -((toHilbertVectorL2OfVecField hg :
        Vec d → HilbertVec d) x) := congrArg Neg.neg hpos.symm
    _ = ((-toHilbertVectorL2OfVecField hg :
        HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) x := hminus.symm

end Cube

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
