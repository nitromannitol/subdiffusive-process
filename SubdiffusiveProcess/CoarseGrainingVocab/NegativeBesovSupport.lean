module

public import SubdiffusiveProcess.CoarseGrainingVocab.ReciprocalLowerSupport
public import Homogenization.Book.Ch02.Theorems.Dilation
public import Homogenization.Book.Ch04.Theorems.PartitionAverageMoments.Rosenthal
public import Homogenization.Geometry.ScaleColoring
public import Homogenization.Probability.IndependentSums.MomentCalculus

@[expose] public section

/-!
# Measurable support for the cutoff negative-Besov observables

This file supplies the proof-carrying exact-circ integrability and
measurability prerequisites used by `l.aL.negative.Besov`.  The measurable
assembly follows the source construction literally: finitely many block means
at each descendant depth, followed by a countable sum over depths.

The color-class interface at the end supplies the probabilistic core used.  Its proof route is adapted from
`Algsuperdiff/Probability/ColoredAverage.lean`: isolate the estimate on each
independent color class before the finite partition is recombined.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book
open Homogenization.IndependentSums
open scoped BigOperators ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-! ## Exact-circ block integrability -/

/-- The forward cutoff ratio has the exact block-integrability certificate
required by the paper's circ negative-Besov norm.  This includes the
`n = -1` convention through `aCutoffAtInt`. -/
theorem cutoffRatio_circNegativeBesovIntegrable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Ch01.CircNegativeBesovIntegrable (originCube d (m : ℤ))
      (cutoffRatioMinusOne M m n omega) :=
  cutoffRatioExactCircIntegrable M m n omega

/-- The exponentially normalized inverse cutoff ratio has the exact
block-integrability certificate required by the paper's circ negative-Besov
norm.  This includes the `n = -1` convention through `aCutoffAtInt`. -/
theorem normalizedInverseCutoffRatio_circNegativeBesovIntegrable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Ch01.CircNegativeBesovIntegrable (originCube d (m : ℤ))
      (normalizedInverseCutoffRatioMinusOne M m n omega) :=
  inverseCutoffRatioExactCircIntegrable M m n omega

/-! ## Measurability of the countable exact-circ assembly -/

/-- A jointly measurable random field has measurable certified block means.
The proof certificate does not affect the value of the Bochner integral. -/
theorem measurable_exactCircBlockMean_of_uncurry {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] (R : TriadicCube d) (F : Omega → Vec d → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hI : ∀ omega, Integrable (F omega) (normalizedCubeMeasure R)) :
    Measurable (fun omega => exactCircBlockMean R (F omega) (hI omega)) := by
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

/-- Measurability of one finite descendant-depth average in the exact-circ
kernel. -/
theorem measurable_exactCircDepthAverage_of_uncurry {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] (Q : TriadicCube d) (p : ℝ)
    (F : Omega → Vec d → ℝ) (hF : Measurable (Function.uncurry F))
    (hI : ∀ omega, ExactCircIntegrable Q (F omega)) (j : ℕ) :
    Measurable (fun omega => exactCircDepthAverage Q p (F omega) (hI omega) j) := by
  unfold exactCircDepthAverage
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro R hR
  apply Measurable.pow_const
  apply Measurable.ennreal_ofReal
  simpa only [Real.norm_eq_abs] using
    (measurable_exactCircBlockMean_of_uncurry R.1 F hF
      (fun omega => (hI omega).block j R.1 R.2)).norm

/-- Measurability of one weighted descendant-depth term. -/
theorem measurable_exactCircDepthTerm_of_uncurry {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] (Q : TriadicCube d) (s p : ℝ)
    (F : Omega → Vec d → ℝ) (hF : Measurable (Function.uncurry F))
    (hI : ∀ omega, ExactCircIntegrable Q (F omega)) (j : ℕ) :
    Measurable (fun omega => exactCircDepthTerm Q s p (F omega) (hI omega) j) := by
  unfold exactCircDepthTerm
  exact measurable_const.mul
    ((measurable_exactCircDepthAverage_of_uncurry Q p F hF hI j).pow_const p⁻¹)

/-- Measurability of the paper's diagonal finite-exponent circ quantity. -/
theorem measurable_paperNegativeBesovCircDiagonal_of_uncurry
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (Q : TriadicCube d) (s p : ℝ) (F : Omega → Vec d → ℝ)
    (hF : Measurable (Function.uncurry F))
    (hI : ∀ omega, ExactCircIntegrable Q (F omega)) :
    Measurable
      (fun omega => paperNegativeBesovCircDiagonal Q s p (F omega) (hI omega)) := by
  unfold paperNegativeBesovCircDiagonal
  apply measurable_const.mul
  apply Measurable.pow_const
  apply Measurable.tsum
  intro j
  exact (measurable_exactCircDepthTerm_of_uncurry Q s p F hF hI j).pow_const p

/-- The forward cutoff-ratio negative-Besov observable is measurable in the
environment. -/
theorem measurable_cutoffRatioNegativeBesov {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ) (s p : ℝ) :
    Measurable (cutoffRatioNegativeBesov M m n s p) := by
  exact measurable_paperNegativeBesovCircDiagonal_of_uncurry
    (originCube d (m : ℤ)) s p (cutoffRatioMinusOne M m n)
    (measurable_cutoffRatioMinusOne_uncurry M m n)
    (cutoffRatioExactCircIntegrable M m n)

/-- The normalized inverse cutoff-ratio negative-Besov observable is
measurable in the environment. -/
theorem measurable_inverseCutoffRatioNegativeBesov {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ) (s p : ℝ) :
    Measurable (inverseCutoffRatioNegativeBesov M m n s p) := by
  exact measurable_paperNegativeBesovCircDiagonal_of_uncurry
    (originCube d (m : ℤ)) s p
    (normalizedInverseCutoffRatioMinusOne M m n)
    (by
      exact (measurable_const.mul
        ((measurable_aCutoffAtInt_uncurry M n).div
          (measurable_cutoff_uncurry M m))).sub measurable_const)
    (inverseCutoffRatioExactCircIntegrable M m n)

/-! ## Exact shell telescope and inverse-law reduction -/

/-- The `r`th fresh-shell term in the paper's cutoff telescoping identity. -/
noncomputable def cutoffFreshShellTerm {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m r : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) : ℝ :=
  _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
      _root_.SubdiffusiveProcess.Model.aCutoff M r omega x *
    (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)

/-- A fresh-shell telescoping integrand is continuous in space. -/
theorem continuous_cutoffFreshShellTerm {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m r : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Continuous (cutoffFreshShellTerm M m r omega) := by
  unfold cutoffFreshShellTerm
  exact ((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M m omega).div
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M r omega)
      (fun x => (_root_.SubdiffusiveProcess.Model.aCutoff_pos M r omega x).ne')).mul
    ((Real.continuous_exp.comp
      ((omega r).1.1.continuous.sub continuous_const)).sub continuous_const)

/-- a normalized fresh-shell block integral is
the normalized average of its integrals over any fixed descendant depth. -/
theorem integral_cutoffFreshShellTerm_eq_descendantsAverage_integral {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m r : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (Q : TriadicCube d) (depth : ℕ) :
    (∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure Q) =
      descendantsAverage Q depth (fun R =>
        ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure R) := by
  let f := cutoffFreshShellTerm M m r omega
  have hf : IntegrableOn f (cubeSet Q) volume :=
    ((ContinuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q))
      (continuous_cutoffFreshShellTerm M m r omega).continuousOn).mono_set
        (cubeSet_subset_closedBall Q))
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q depth f hf]
  congr 1
  funext R
  exact cubeAverage_eq_integral_normalizedCubeMeasure R f

/-- One cutoff is its predecessor times the fresh centered exponential shell,
including the source convention `a_(-1) = 1` at `r = 0`. -/
theorem aCutoff_eq_pred_mul_freshShell {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (r : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.aCutoff M r omega x =
      aCutoffAtInt M ((r : ℤ) - 1) omega x *
        Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
  cases r with
  | zero =>
      simp [_root_.SubdiffusiveProcess.Model.aCutoff, aCutoffAtInt]
  | succ r =>
      simp only [_root_.SubdiffusiveProcess.Model.aCutoff, Finset.sum_range_succ,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      rw [Real.exp_add]
      rw [aCutoffAtInt, ite_eq_right (by omega)]
      rw [Int.toNat_natCast]
      rw [_root_.SubdiffusiveProcess.Model.aCutoff, Finset.sum_range_succ]

/-- Each fresh-shell term is one difference in the cutoff-ratio telescope. -/
theorem cutoffFreshShellTerm_eq_telescope {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m r : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    cutoffFreshShellTerm M m r omega x =
      _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          aCutoffAtInt M ((r : ℤ) - 1) omega x -
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          aCutoffAtInt M (r : ℤ) omega x := by
  rw [cutoffFreshShellTerm]
  have hr := aCutoff_eq_pred_mul_freshShell M r omega x
  have hprev := aCutoffAtInt_pos M ((r : ℤ) - 1) omega x
  have hexp : 0 < Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) :=
    Real.exp_pos _
  have hcurr : aCutoffAtInt M (r : ℤ) omega x =
      _root_.SubdiffusiveProcess.Model.aCutoff M r omega x := by
    simp [aCutoffAtInt]
  rw [hcurr, hr]
  field_simp [hprev.ne', hexp.ne']

/-- `e.aL.negative.Besov.iden1`, pointwise and with the exceptional initial
shell included: the cutoff ratio is the finite sum of its fresh-shell
increments. -/
theorem cutoffRatioMinusOne_eq_sum_freshShellTerms {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) (hn : -1 ≤ n) (hnm : n < (m : ℤ)) :
    cutoffRatioMinusOne M m n omega x =
      ∑ r ∈ cutoffShellIndices m n, cutoffFreshShellTerm M m r omega x := by
  let F : ℕ → ℝ := fun r =>
    _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
      aCutoffAtInt M ((r : ℤ) - 1) omega x
  have hlower : (n + 1).toNat ≤ m + 1 := by omega
  have hinterval : cutoffShellIndices m n = Finset.Ico (n + 1).toNat (m + 1) := by
    unfold cutoffShellIndices
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hlowerPred : ((n + 1).toNat : ℤ) - 1 = n := by omega
  have htel := Finset.sum_Ico_sub (fun r => -F r) hlower
  have hsum : (∑ r ∈ Finset.Ico (n + 1).toNat (m + 1),
      (F r - F (r + 1))) = F (n + 1).toNat - F (m + 1) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htel
  rw [cutoffRatioMinusOne, hinterval]
  have hFleft : F (n + 1).toNat =
      _root_.SubdiffusiveProcess.Model.aCutoff M m omega x / aCutoffAtInt M n omega x := by
    dsimp [F]
    rw [hlowerPred]
  have hFright : F (m + 1) = 1 := by
    dsimp [F]
    norm_num
    rw [aCutoffAtInt, ite_eq_right (by omega)]
    exact div_self (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x).ne'
  calc
    _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          aCutoffAtInt M n omega x - 1 =
        F (n + 1).toNat - F (m + 1) := by
      rw [hFleft, hFright]
    _ = ∑ r ∈ Finset.Ico (n + 1).toNat (m + 1), (F r - F (r + 1)) :=
      hsum.symm
    _ = ∑ r ∈ Finset.Ico (n + 1).toNat (m + 1),
          cutoffFreshShellTerm M m r omega x := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [cutoffFreshShellTerm_eq_telescope]
      dsimp [F]
      congr 2
      norm_num

/-- Negating all shells turns the integer-indexed cutoff into its normalized
reciprocal, including the source convention `a_(-1) = 1`. -/
theorem aCutoffAtInt_negatePotentialSequence {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) (hn : -1 ≤ n) :
    aCutoffAtInt M n (negatePotentialSequence omega) x =
      Real.exp (-2 * (((n + 1 : ℤ) : ℝ)) *
        _root_.SubdiffusiveProcess.Model.tauSq M.P) *
          (aCutoffAtInt M n omega x)⁻¹ := by
  rcases eq_or_lt_of_le hn with rfl | hn0
  · simp [aCutoffAtInt]
  · have hnneg : ¬ n < 0 := by omega
    rw [aCutoffAtInt, ite_eq_right hnneg, aCutoffAtInt, ite_eq_right hnneg]
    rw [aCutoff_negatePotentialSequence M n.toNat omega x]
    congr 2
    have hncast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ n)
    push_cast
    rw [hncast]



theorem cutoffRatioMinusOne_negatePotentialSequence {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) (hn : -1 ≤ n) :
    cutoffRatioMinusOne M m n (negatePotentialSequence omega) x =
      normalizedInverseCutoffRatioMinusOne M m n omega x := by
  rw [cutoffRatioMinusOne, normalizedInverseCutoffRatioMinusOne,
    aCutoff_negatePotentialSequence M m omega x,
    aCutoffAtInt_negatePotentialSequence M n omega x hn]
  have hA := _root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x
  have hB := aCutoffAtInt_pos M n omega x
  have hEm : Real.exp
      (-2 * (m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≠ 0 :=
    (Real.exp_pos _).ne'
  have hEn : Real.exp
      (-2 * (((n + 1 : ℤ) : ℝ)) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≠ 0 :=
    (Real.exp_pos _).ne'
  congr 1
  field_simp [hA.ne', hB.ne', hEm, hEn]
  rw [← Real.exp_add]
  congr 2
  push_cast
  ring

/-- The full inverse negative-Besov observable is the forward observable after
shell negation. -/
theorem cutoffRatioNegativeBesov_negatePotentialSequence {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (s p : ℝ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hn : -1 ≤ n) :
    cutoffRatioNegativeBesov M m n s p (negatePotentialSequence omega) =
      inverseCutoffRatioNegativeBesov M m n s p omega := by
  unfold cutoffRatioNegativeBesov inverseCutoffRatioNegativeBesov
  congr 1
  funext x
  exact cutoffRatioMinusOne_negatePotentialSequence M m n omega x hn

/-- `e.inverse.symmetry.in.law` on the exact `ENNReal` moment carrier used by
the frozen Section-3 anchor. -/
theorem paperENNRealLpNorm_inverseCutoffRatioNegativeBesov_eq_forward {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (s p : ℝ) (hn : -1 ≤ n) :
    paperENNRealLpNorm M.P.toMeasure p
        (inverseCutoffRatioNegativeBesov M m n s p) =
      paperENNRealLpNorm M.P.toMeasure p
        (cutoffRatioNegativeBesov M m n s p) := by
  unfold paperENNRealLpNorm
  congr 1
  calc
    (∫⁻ omega, (inverseCutoffRatioNegativeBesov M m n s p omega) ^ p
        ∂M.P.toMeasure) =
        ∫⁻ omega, (cutoffRatioNegativeBesov M m n s p
          (negatePotentialSequence omega)) ^ p ∂M.P.toMeasure := by
      apply lintegral_congr
      intro omega
      rw [cutoffRatioNegativeBesov_negatePotentialSequence M m n s p omega hn]
    _ = ∫⁻ omega, (cutoffRatioNegativeBesov M m n s p omega) ^ p
          ∂Measure.map negatePotentialSequence M.P.toMeasure := by
      symm
      apply MeasureTheory.lintegral_map
      · exact (measurable_cutoffRatioNegativeBesov M m n s p).pow_const p
      · exact measurable_negatePotentialSequence
    _ = ∫⁻ omega, (cutoffRatioNegativeBesov M m n s p omega) ^ p
          ∂M.P.toMeasure := by
      rw [potentialSequenceLaw_negation M]

/-! ## Finite-range color-class decomposition -/

/-- Separation at the exact range in assumption G1. -/
def PotentialRangeSeparated {d : ℕ} (U V : Set (Vec d)) : Prop :=
  ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
    Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)

/-! The standard Chapter-4 coloring only separates its classes by distance
`1`. After a fresh shell is rescaled to shell zero, G1 requires the literal
range `sqrt d`; the source proof therefore needs a dimension-dependent (but
scale-independent) refinement of that coloring. -/

/-- Period of the fresh-shell coloring after rescaling scale `r - 1` cells to
scale `-1`. -/
noncomputable def freshShellColorPeriod (d : ℕ) : ℕ :=
  1 + Nat.ceil (3 * Real.sqrt (d : ℝ))

/-- Dimension-range color of a triadic cube. -/
abbrev FreshShellColor (d : ℕ) := Fin d → Fin (freshShellColorPeriod d)

theorem freshShellColorPeriod_pos (d : ℕ) : 0 < freshShellColorPeriod d := by
  simp [freshShellColorPeriod]

private theorem freshShellColorPeriod_int_pos (d : ℕ) :
    0 < (freshShellColorPeriod d : ℤ) := by
  exact_mod_cast freshShellColorPeriod_pos d

private theorem freshShellColorPeriod_int_ne_zero (d : ℕ) :
    (freshShellColorPeriod d : ℤ) ≠ 0 :=
  ne_of_gt (freshShellColorPeriod_int_pos d)

/-- Coordinatewise residue color with the dimension-range period. -/
noncomputable def cubeFreshShellColor {d : ℕ} (Q : TriadicCube d) :
    FreshShellColor d := fun i =>
  ⟨Int.toNat (Q.index i % (freshShellColorPeriod d : ℤ)), by
    have hnonneg : 0 ≤ Q.index i % (freshShellColorPeriod d : ℤ) :=
      Int.emod_nonneg _ (freshShellColorPeriod_int_ne_zero d)
    have hlt : Q.index i % (freshShellColorPeriod d : ℤ) <
        (freshShellColorPeriod d : ℤ) :=
      Int.emod_lt_of_pos _ (freshShellColorPeriod_int_pos d)
    rw [Int.toNat_lt hnonneg]
    exact hlt⟩

private theorem cubeFreshShellColor_eq_iff_modEq {d : ℕ}
    {R S : TriadicCube d} :
    cubeFreshShellColor R = cubeFreshShellColor S ↔
      ∀ i, R.index i ≡ S.index i [ZMOD (freshShellColorPeriod d : ℤ)] := by
  constructor
  · intro h i
    change R.index i % (freshShellColorPeriod d : ℤ) =
      S.index i % (freshShellColorPeriod d : ℤ)
    have hval :
        Int.toNat (R.index i % (freshShellColorPeriod d : ℤ)) =
          Int.toNat (S.index i % (freshShellColorPeriod d : ℤ)) := by
      simpa [cubeFreshShellColor] using
        congrArg Fin.val (congrArg (fun c : FreshShellColor d => c i) h)
    have hR : 0 ≤ R.index i % (freshShellColorPeriod d : ℤ) :=
      Int.emod_nonneg _ (freshShellColorPeriod_int_ne_zero d)
    have hS : 0 ≤ S.index i % (freshShellColorPeriod d : ℤ) :=
      Int.emod_nonneg _ (freshShellColorPeriod_int_ne_zero d)
    have hcast :
        (((Int.toNat (R.index i % (freshShellColorPeriod d : ℤ)) : ℕ) : ℤ)) =
          Int.toNat (S.index i % (freshShellColorPeriod d : ℤ)) := by
      exact_mod_cast hval
    simpa [Int.ModEq, Int.toNat_of_nonneg hR, Int.toNat_of_nonneg hS] using hcast
  · intro h
    funext i
    apply Fin.ext
    have hmod : R.index i % (freshShellColorPeriod d : ℤ) =
        S.index i % (freshShellColorPeriod d : ℤ) := by
      simpa [Int.ModEq] using h i
    exact_mod_cast congrArg Int.toNat hmod

private theorem index_add_freshShellColorPeriod_le_of_color_eq_of_lt {d : ℕ}
    {R S : TriadicCube d} {i : Fin d}
    (hcolor : cubeFreshShellColor R = cubeFreshShellColor S)
    (hlt : R.index i < S.index i) :
    R.index i + freshShellColorPeriod d ≤ S.index i := by
  have hmod : R.index i ≡ S.index i [ZMOD (freshShellColorPeriod d : ℤ)] :=
    (cubeFreshShellColor_eq_iff_modEq.mp hcolor) i
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨n, hn⟩
  have hperiod : 0 < (freshShellColorPeriod d : ℤ) :=
    freshShellColorPeriod_int_pos d
  have hprod : 0 < (freshShellColorPeriod d : ℤ) * n := by
    rw [← hn]
    exact sub_pos.mpr hlt
  have hnpos : 0 < n := by nlinarith
  nlinarith

private theorem three_mul_sqrt_le_freshShellColorPeriod_pred (d : ℕ) :
    3 * Real.sqrt (d : ℝ) ≤ (freshShellColorPeriod d : ℝ) - 1 := by
  have h := Nat.le_ceil (3 * Real.sqrt (d : ℝ))
  simpa [freshShellColorPeriod] using h

/-- Same-colored distinct scale-`-1` cubes meet G1's exact `sqrt d` range.
This is the geometric residue left implicit in the manuscript's `C(d)`
color-class partition. -/
theorem potentialRangeSeparated_of_cubeFreshShellColor_eq_of_scale_neg_one
    {d : ℕ} {R S : TriadicCube d}
    (hRscale : R.scale = -1) (hSscale : S.scale = -1)
    (hcolor : cubeFreshShellColor R = cubeFreshShellColor S) (hne : R ≠ S) :
    PotentialRangeSeparated (cubeSet R) (cubeSet S) := by
  have hindex : ∃ i, R.index i ≠ S.index i := by
    by_contra h
    push Not at h
    apply hne
    cases R with
    | mk r ri =>
        cases S with
        | mk s si =>
            simp only at hRscale hSscale h ⊢
            have hrs : r = s := hRscale.trans hSscale.symm
            subst s
            congr
            exact funext h
  rcases hindex with ⟨i, hi⟩
  intro x y hx hy
  have hscaleR : cubeScaleFactor R = (1 / 3 : ℝ) := by
    simp [cubeScaleFactor, hRscale]
  have hscaleS : cubeScaleFactor S = (1 / 3 : ℝ) := by
    simp [cubeScaleFactor, hSscale]
  have hperiod := three_mul_sqrt_le_freshShellColorPeriod_pred d
  have hsqrt : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hcoord : Real.sqrt (d : ℝ) ≤ |(x - y) i| := by
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have hgap :=
        index_add_freshShellColorPeriod_le_of_color_eq_of_lt hcolor hlt
      have hgapReal : (R.index i : ℝ) + freshShellColorPeriod d ≤
          (S.index i : ℝ) := by exact_mod_cast hgap
      have hx' := hx i
      have hy' := hy i
      rw [hscaleR] at hx'
      rw [hscaleS] at hy'
      have hsep : Real.sqrt (d : ℝ) < y i - x i := by nlinarith
      rw [Pi.sub_apply, abs_of_nonpos (by linarith)]
      linarith
    · have hgap :=
        index_add_freshShellColorPeriod_le_of_color_eq_of_lt hcolor.symm hgt
      have hgapReal : (S.index i : ℝ) + freshShellColorPeriod d ≤
          (R.index i : ℝ) := by exact_mod_cast hgap
      have hx' := hx i
      have hy' := hy i
      rw [hscaleR] at hx'
      rw [hscaleS] at hy'
      have hsep : Real.sqrt (d : ℝ) < x i - y i := by nlinarith
      rw [Pi.sub_apply, abs_of_nonneg (by linarith)]
      linarith
  rw [euclideanNorm_eq_norm_ofVec]
  exact hcoord.trans (by
    simpa using HilbertVec.abs_apply_le_norm (HilbertVec.ofVec (x - y)) i)

/-- The rescaled descendants in one fresh-shell color class satisfy G1's
range condition. -/
theorem potentialRangeSeparated_dilateCube_neg_shell_of_freshShellColor_eq
    {d : ℕ} {Q R S : TriadicCube d} {r : ℕ}
    (hR : R ∈ descendantsAtScale Q ((r : ℤ) - 1))
    (hS : S ∈ descendantsAtScale Q ((r : ℤ) - 1))
    (hcolor : cubeFreshShellColor R = cubeFreshShellColor S) (hne : R ≠ S) :
    PotentialRangeSeparated
      (cubeSet (Ch02.dilateCube (-(r : ℤ)) R))
      (cubeSet (Ch02.dilateCube (-(r : ℤ)) S)) := by
  apply potentialRangeSeparated_of_cubeFreshShellColor_eq_of_scale_neg_one
  · simp only [Ch02.dilateCube_scale, scale_eq_of_mem_descendantsAtScale hR]
    omega
  · simp only [Ch02.dilateCube_scale, scale_eq_of_mem_descendantsAtScale hS]
    omega
  · simpa [cubeFreshShellColor, Ch02.dilateCube] using! hcolor
  · intro h
    apply hne
    exact Ch02.dilateCube_injective (-(r : ℤ)) h

/-- The number of fresh-shell colors is bounded by the dimensional constant
`freshShellColorPeriod d ^ d`. -/
theorem card_image_cubeFreshShellColor_le {d : ℕ} (s : Finset (TriadicCube d)) :
    (s.image cubeFreshShellColor).card ≤ freshShellColorPeriod d ^ d := by
  have hsubset : s.image cubeFreshShellColor ⊆
      (Finset.univ : Finset (FreshShellColor d)) := fun _ _ ↦ Finset.mem_univ _
  calc
    (s.image cubeFreshShellColor).card ≤
        (Finset.univ : Finset (FreshShellColor d)).card :=
      Finset.card_le_card hsubset
    _ = freshShellColorPeriod d ^ d := by simp [FreshShellColor]

/-! ## Normalized-cube dilation for fresh-shell transport -/

/-- Measurable equivalence implementing the source dilation `x ↦ 3^k x`. -/
public noncomputable def triadicDilationEquiv {d : ℕ} (k : ℤ) :
    Vec d ≃ᵐ Vec d :=
  MeasurableEquiv.smul₀ (Ch02.triadicDilationFactor k)
    (Ch02.triadicDilationFactor_ne_zero k)

private theorem cubeVolume_dilateCube_eq {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    cubeVolume (Ch02.dilateCube k Q) =
      (Ch02.triadicDilationFactor k) ^ d * cubeVolume Q := by
  rw [cubeVolume_eq_scaleFactor_pow, Ch02.cubeScaleFactor_dilateCube,
    mul_pow, cubeVolume_eq_scaleFactor_pow]

/-- Normalized volume is exactly preserved when a triadic cube and its points
are dilated by the same triadic factor. -/
theorem measurePreserving_triadicDilationEquiv_normalizedCubeMeasure {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) :
    MeasurePreserving (triadicDilationEquiv (d := d) k)
      (normalizedCubeMeasure Q)
      (normalizedCubeMeasure (Ch02.dilateCube k Q)) := by
  let a : ℝ := Ch02.triadicDilationFactor k
  let T := triadicDilationEquiv (d := d) k
  have ha : 0 < a := Ch02.triadicDilationFactor_pos k
  have hT : (T : Vec d → Vec d) = fun x => a • x := rfl
  have hmap : Measure.map T (cubeMeasure Q) =
      ENNReal.ofReal ((a ^ d)⁻¹) • cubeMeasure (Ch02.dilateCube k Q) := by
    rw [cubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
      hT, map_smul_volume_restrict ha, Ch02.openCubeSet_dilateCube]
  have hvol : cubeVolume (Ch02.dilateCube k Q) = a ^ d * cubeVolume Q := by
    simpa only [a] using cubeVolume_dilateCube_eq k Q
  refine ⟨T.measurable, ?_⟩
  rw [normalizedCubeMeasure, normalizedCubeMeasure, Measure.map_smul _ T.measurable.aemeasurable, hmap,
    smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (cubeVolume_nonneg Q))]
  have hapow : 0 < a ^ d := pow_pos ha d
  rw [show (cubeVolume Q)⁻¹ * (a ^ d)⁻¹ =
      (a ^ d * cubeVolume Q)⁻¹ by field_simp [hapow.ne'], hvol]

/-- Integral change of variables for normalized triadic cube measure. -/
theorem integral_comp_triadicDilationEquiv_normalizedCubeMeasure {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) (f : Vec d → ℝ) :
    ∫ x, f (triadicDilationEquiv k x) ∂normalizedCubeMeasure Q =
      ∫ y, f y ∂normalizedCubeMeasure (Ch02.dilateCube k Q) := by
  exact (measurePreserving_triadicDilationEquiv_normalizedCubeMeasure k Q).integral_comp
    (triadicDilationEquiv k).measurableEmbedding f

private theorem potentialRangeSeparated_biUnion_right {d : ℕ}
    {ι : Type*} {U : Set (Vec d)} {V : ι → Set (Vec d)} {s : Finset ι}
    (h : ∀ i ∈ s, PotentialRangeSeparated U (V i)) :
    PotentialRangeSeparated U (⋃ i ∈ s, V i) := by
  intro x y hx hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨i, hi, hyi⟩ := hy
  exact h i hi hx hyi

/-- Potential-field local sigma algebras are monotone in the observation
region. -/
theorem potentialFieldLocalSigma_mono {d : ℕ} {U V : Set (Vec d)}
    (hUV : U ⊆ V) :
    _root_.SubdiffusiveProcess.Model.PotentialField.localSigma U ≤
      _root_.SubdiffusiveProcess.Model.PotentialField.localSigma V := by
  unfold _root_.SubdiffusiveProcess.Model.PotentialField.localSigma
  exact MeasurableSpace.comap_mono (Homogenization.localSigmaR_mono hUV)

/-- Every potential-field local sigma algebra is contained in the canonical
Borel sigma algebra. -/
theorem potentialFieldLocalSigma_le_borel {d : ℕ} (U : Set (Vec d)) :
    _root_.SubdiffusiveProcess.Model.PotentialField.localSigma U ≤
      (inferInstance : MeasurableSpace
        (_root_.SubdiffusiveProcess.Model.PotentialField d)) := by
  unfold _root_.SubdiffusiveProcess.Model.PotentialField.localSigma
  exact (MeasurableSpace.comap_mono (Homogenization.LocalSigmaR_le U)).trans
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_forgetPotential.comap_le



theorem measurable_eval_potentialFieldLocalSigma_of_mem_isOpen
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    {x : Vec d} (hx : x ∈ U) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
      (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U) _ (fun g => g x) := by
  obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  let radius : ℕ → ℝ := fun n => (rho / 2) * (1 / ((n : ℝ) + 1))
  let B : ℕ → Set (Vec d) := fun n => Metric.closedBall x (radius n)
  let A : ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun n g =>
    Homogenization.avgMat (B n)
      (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential g) i i
  have hradius_pos (n : ℕ) : 0 < radius n := by
    dsimp [radius]
    positivity
  have hradius_lt (n : ℕ) : radius n < rho := by
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num
    dsimp [radius]
    nlinarith
  have hBsub (n : ℕ) : B n ⊆ U :=
    (Metric.closedBall_subset_ball (hradius_lt n)).trans hball
  have hA_meas (n : ℕ) :
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U) _ (A n) := by
    have havg := Homogenization.measurable_avgMat
      (U := U) (B := B n) (isCompact_closedBall x (radius n))
      (measurableSet_closedBall : MeasurableSet (Metric.closedBall x (radius n))) (hBsub n)
    have hforget :
        @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d)
          (Homogenization.RegCoeffField d)
          (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U)
          (Homogenization.LocalSigmaR U)
          _root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential :=
      Measurable.of_comap_le le_rfl
    have hmatrix :
        @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d)
          (Homogenization.Mat d)
          (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U) _
          (fun g => Homogenization.avgMat (B n)
            (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential g)) :=
      havg.comp hforget
    have hrow :
        @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) (Fin d → ℝ)
          (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U) _
          (fun g => Homogenization.avgMat (B n)
            (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential g) i) :=
      (measurable_pi_apply i).comp hmatrix
    have hentry :
        @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
          (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U) _
          (fun g => Homogenization.avgMat (B n)
            (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential g) i i) :=
      (measurable_pi_apply i).comp hrow
    exact hentry
  refine @measurable_of_tendsto_metrizable
    (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
    (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U) _ _ _ _
    A (fun g => g x) hA_meas ?_
  rw [tendsto_pi_nhds]
  intro g
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨delta, hdelta, hcont⟩ :=
    Metric.continuousAt_iff.mp g.1.1.continuous.continuousAt eps heps
  have hradius_tendsto : Filter.Tendsto radius Filter.atTop (nhds 0) := by
    simpa [radius] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (rho / 2)
  have hevent : ∀ᶠ n in Filter.atTop, dist (radius n) 0 < delta :=
    hradius_tendsto.eventually (Metric.ball_mem_nhds 0 hdelta)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  refine ⟨N, fun n hn => ?_⟩
  have hrn_delta : radius n < delta := by
    have := hN n hn
    simpa [Real.dist_eq, abs_of_pos (hradius_pos n)] using this
  have hmu0 : volume (B n) ≠ 0 :=
    (Metric.measure_closedBall_pos volume x (hradius_pos n)).ne'
  have hmutop : volume (B n) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hint : IntegrableOn (fun y : Vec d => g y) (B n) volume :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall x (radius n))
      g.1.1.continuous.continuousOn
  obtain ⟨y, hyB, hyavg⟩ := MeasureTheory.exists_le_setAverage hmu0 hmutop hint
  obtain ⟨z, hzB, havgz⟩ := MeasureTheory.exists_setAverage_le hmu0 hmutop hint
  have hyclose : |g y - g x| < eps := by
    rw [← Real.dist_eq]
    apply hcont
    have : dist y x ≤ radius n := by simpa [B, Metric.mem_closedBall] using hyB
    exact this.trans_lt hrn_delta
  have hzclose : |g z - g x| < eps := by
    rw [← Real.dist_eq]
    apply hcont
    have : dist z x ≤ radius n := by simpa [B, Metric.mem_closedBall] using hzB
    exact this.trans_lt hrn_delta
  have hAeq : A n g = ⨍ y in B n, g y ∂volume := by
    change Homogenization.avgMat (B n)
      (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential g) i i = _
    rw [Homogenization.avgMat_entry_eq_setAverage]
    simp [_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential_apply,
      Homogenization.scalarMatrix, i]
  rw [hAeq, Real.dist_eq]
  rw [abs_lt]
  constructor <;> linarith [abs_lt.mp hyclose, abs_lt.mp hzclose]

private theorem measurableSet_biInter_potentialFieldLocalSigma_biUnion
    {d : ℕ} {ι : Type*} {U : ι → Set (Vec d)}
    {f : ι → Set (_root_.SubdiffusiveProcess.Model.PotentialField d)} {s : Finset ι}
    (hf : ∀ i ∈ s,
      @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialField d)
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (U i)) (f i)) :
    @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialField d)
      (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (⋃ i ∈ s, U i))
      (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hi_meas :
          @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialField d)
            (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma
              (⋃ j ∈ insert i s, U j)) (f i) :=
        (potentialFieldLocalSigma_mono hsubset_i) (f i) (hf i (by simp))
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hs_meas :
          @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialField d)
            (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma
              (⋃ j ∈ insert i s, U j)) (⋂ j ∈ s, f j) :=
        (potentialFieldLocalSigma_mono hsubset_s) (⋂ j ∈ s, f j)
          (ih fun j hj => hf j (by simp [hj]))
      simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas

/-- G1's two-region independence upgrades to mutual independence for every
pairwise range-separated finite family.  This is the finite-color-class
independence step used at source.

 the finite-union induction mirrors
`Algsuperdiff/Probability/ColoredAverage.lean` and
`Homogenization/Probability/Source/Coarse/Laws.lean`. -/
theorem iIndep_potentialFieldLocalSigma_of_G1 {d : ℕ} {ι : Type*}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {U : ι → Set (Vec d)}
    (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => PotentialRangeSeparated (U i) (U j)) :
    iIndep (fun i => _root_.SubdiffusiveProcess.Model.PotentialField.localSigma (U i))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  classical
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsep_union : PotentialRangeSeparated (U i) (⋃ j ∈ s, U j) := by
        apply potentialRangeSeparated_biUnion_right
        intro j hj
        exact hsep (by
          intro hij
          exact hi (hij ▸ hj))
      have hs_meas :
          @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialField d)
            (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (⋃ j ∈ s, U j))
            (⋂ j ∈ s, f j) :=
        measurableSet_biInter_potentialFieldLocalSigma_biUnion
          (U := U) (f := f) (s := s) fun j hj => hf j (by simp [hj])
      have h_inter :
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
              (f i ∩ ⋂ j ∈ s, f j) =
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure (f i) *
              (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
                (⋂ j ∈ s, f j) := by
        exact (Indep_iff
          (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (U i))
          (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (⋃ j ∈ s, U j))
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure).1
            (M.G1.range_dependence (U i) (⋃ j ∈ s, U j)
              (hU i) (Finset.measurableSet_biUnion s fun j _ => hU j) hsep_union)
            (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
            (⋂ j ∈ insert i s, f j) =
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
              (f i ∩ ⋂ j ∈ s, f j) := by simp
        _ = (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure (f i) *
              (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
                (⋂ j ∈ s, f j) := h_inter
        _ = (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure (f i) *
              ∏ j ∈ s,
                (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure (f j) := by
              rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s,
              (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure (f j) := by
              simp [Finset.prod_insert, hi]

/-- Local observables on a pairwise range-separated family are mutually
independent under the zero-layer law.  Supplying local measurability of the
weighted exponential block means specializes this theorem to the paper's
conditional color classes. -/
theorem iIndepFun_of_G1_of_potentialFieldLocal {d : ℕ} {ι : Type*}
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {U : ι → Set (Vec d)}
    {X : ∀ i, _root_.SubdiffusiveProcess.Model.PotentialField d → β i}
    (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => PotentialRangeSeparated (U i) (U j))
    (hX : ∀ i,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) (β i)
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (U i)) _ (X i)) :
    iIndepFun X (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  rw [iIndepFun_iff_iIndep, iIndep_iff]
  intro s f hf
  exact (iIndep_iff
    (fun i => _root_.SubdiffusiveProcess.Model.PotentialField.localSigma (U i))
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure).1
      (iIndep_potentialFieldLocalSigma_of_G1 M hU hsep) s
      (fun i hi => (Measurable.comap_le (hX i)) (f i) (hf i hi))

/-- A frozen coefficient weight paired with one centered exponential shell on
a block.  This is the conditional block variable in source. -/
noncomputable def frozenExponentialBlockMean {d : ℕ}
    (weight : Vec d → ℝ) (tau : ℝ) (R : TriadicCube d)
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  ∫ x, weight x * (Real.exp (g x - tau) - 1) ∂normalizedCubeMeasure R

/-- After marginal-law rescaling, an actual shell block is exactly the
zero-shell frozen block on the scale-`-1` dilated cube. -/
theorem integral_weight_mul_triadicScale_freshShell_eq_frozenBlock {d : ℕ}
    (weight : Vec d → ℝ) (tau : ℝ) (r : ℕ) (R : TriadicCube d)
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    (∫ x, weight x *
        (Real.exp
          (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale r g x - tau) - 1)
        ∂normalizedCubeMeasure R) =
      frozenExponentialBlockMean
        (fun y => weight (Ch02.dilateVec (r : ℤ) y)) tau
        (Ch02.dilateCube (-(r : ℤ)) R) g := by
  unfold frozenExponentialBlockMean
  let f : Vec d → ℝ := fun y =>
    weight (Ch02.dilateVec (r : ℤ) y) * (Real.exp (g y - tau) - 1)
  rw [← integral_comp_triadicDilationEquiv_normalizedCubeMeasure
    (-(r : ℤ)) R f]
  apply integral_congr_ae
  filter_upwards with x
  dsimp [f, triadicDilationEquiv]
  have hcancel : Ch02.dilateVec (r : ℤ)
      (Ch02.triadicDilationFactor (-(r : ℤ)) • x) = x := by
    exact Ch02.dilateVec_dilateVec_neg (r : ℤ) x
  have hscale : Ch02.triadicDilationFactor (-(r : ℤ)) • x =
      ((3 : ℝ) ^ r)⁻¹ • x := by
    ext i
    simp [Ch02.triadicDilationFactor, smul_eq_mul, zpow_neg]
  rw [hcancel, hscale]

/-- A continuous scalar field has every `L^p` moment on a normalized cube. -/
theorem memLp_normalizedCubeMeasure_of_continuous {d : ℕ}
    (R : TriadicCube d) (p : ℝ≥0∞) {f : Vec d → ℝ}
    (hf : Continuous f) : MemLp f p (normalizedCubeMeasure R) := by
  have hcompact : IsCompact (closure (cubeSet R)) :=
    (isBounded_cubeSet R).isCompact_closure
  rcases hcompact.bddAbove_image hf.norm.continuousOn with ⟨C, hC⟩
  have hcube : ∀ᵐ x ∂normalizedCubeMeasure R, x ∈ cubeSet R := by
    have hrestrict : ∀ᵐ x ∂volume.restrict (cubeSet R), x ∈ cubeSet R :=
      ae_restrict_mem (measurableSet_cubeSet R)
    simpa [normalizedCubeMeasure, cubeMeasure] using
      Measure.ae_smul_measure hrestrict
        (ENNReal.ofReal ((cubeVolume R)⁻¹))
  exact MemLp.of_bound hf.aestronglyMeasurable C <|
    hcube.mono fun x hx => hC ⟨x, subset_closure hx, rfl⟩

/-- Stationarity makes the zero-layer exponential moment independent of the
spatial evaluation point.  This is the expectation identity used to center
each conditional color-class summand in `e.condy.moment.bound`.

 source; the measure-map calculation is the
zero-layer specialization of the stationarity transport in
`AnnealedProviders.lean`. -/
theorem integral_exp_zeroPotential_apply {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (x : Vec d) :
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g x)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure =
      ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let F0 : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => Real.exp (g 0)
  have hF0 : Measurable F0 :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).exp
  calc
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g x) ∂mu0 =
        ∫ g, F0 (_root_.SubdiffusiveProcess.Model.PotentialField.translate x g) ∂mu0 := by
      apply integral_congr_ae
      filter_upwards with g
      simp [F0]
    _ = ∫ g, F0 g
          ∂Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate x) mu0 := by
      exact (integral_map
        (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate x).aemeasurable
        hF0.aestronglyMeasurable).symm
    _ = ∫ g, F0 g ∂mu0 := by rw [M.G1.stationary x]

/-- Every zero-layer exponential evaluation is integrable, again by exact
stationarity of the zero-shell law. -/
theorem integrable_exp_zeroPotential_apply {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (x : Vec d) :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.exp (g x))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let F0 : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => Real.exp (g 0)
  have hF0 : Measurable F0 :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).exp
  have hmap : Integrable F0
      (Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate x) mu0) := by
    rw [M.G1.stationary x]
    exact M.G4.exponential_integrable
  have hcomp := (integrable_map_measure hF0.aestronglyMeasurable
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate x).aemeasurable).1 hmap
  simpa [F0, Function.comp_def, mu0] using hcomp

/-- The definition of `tauSq`, together with its G4 positivity guard, centers
the exponential shell at every spatial point. -/
theorem integral_exp_sub_tauSq_zeroPotential_apply_eq_one {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (x : Vec d) :
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
        Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P)
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure = 1 := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let I : ℝ := ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0) ∂mu0
  have hIpos : 0 < I := by
    exact integral_exp_pos M.G4.exponential_integrable
  have hexpTau : Real.exp (_root_.SubdiffusiveProcess.Model.tauSq M.P) = I := by
    simpa [I, mu0, _root_.SubdiffusiveProcess.Model.tauSq] using Real.exp_log hIpos
  calc
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
        Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) ∂mu0 =
        Real.exp (-_root_.SubdiffusiveProcess.Model.tauSq M.P) *
          ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g x) ∂mu0 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with g
      rw [Real.exp_sub, Real.exp_neg]
      ring
    _ = Real.exp (-_root_.SubdiffusiveProcess.Model.tauSq M.P) * I := by
      rw [integral_exp_zeroPotential_apply M x]
    _ = 1 := by
      rw [Real.exp_neg, hexpTau]
      field_simp

/-- Raw G2 lognormal scale for one centered zero-shell exponential. -/
noncomputable def freshShellPointMomentScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℝ) : ℝ :=
  let A := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta
  2 * gammaMomentConst 2 * Real.sqrt (2 * p) *
    (A + |_root_.SubdiffusiveProcess.Model.tauSq M.P|) *
      Real.exp (p * A ^ 2 + |_root_.SubdiffusiveProcess.Model.tauSq M.P|)

theorem freshShellPointMomentScale_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {p : ℝ} (hp : 0 < p) :
    0 < freshShellPointMomentScale M p := by
  have hbase : 0 < 1 + Real.log 2 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hA : 0 < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta :=
    mul_pos (Real.rpow_pos_of_pos hbase _) M.shellPrefix.delta_pos
  unfold freshShellPointMomentScale
  exact mul_pos
    (mul_pos
      (mul_pos (mul_pos (by norm_num) (gammaMomentConst_pos (by norm_num)))
        (Real.sqrt_pos.mpr (by positivity)))
      (add_pos_of_pos_of_nonneg hA (abs_nonneg _)))
    (Real.exp_pos _)



theorem integral_abs_exp_zeroPotential_apply_sub_tauSq_rpow_root_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (x : Vec d)
    (p : ℝ) (hp : 1 ≤ p) :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        |Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ∧
      (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
          |Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
            ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
        freshShellPointMomentScale M p := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let A : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta
  let X : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => g 0
  let Phi : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g =>
    |Real.exp (g 0 - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
  have hbase : 0 < 1 + Real.log 2 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hA : 0 < A := mul_pos
    (Real.rpow_pos_of_pos hbase _) M.shellPrefix.delta_pos
  have hXm : AEMeasurable X mu0 :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).aemeasurable
  have hX : IsBigO mu0 (gammaSigma 2) X A := by
    have h := SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE
      (μ := mu0) (σ := 2) (A := M.delta)
      (X := fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => |g 0|)
      (by norm_num) M.shellPrefix.delta_pos (fun _ => abs_nonneg _)
      (ogammaLE_abs_zeroPotential_at_zero M)
    simpa [IsBigO, A] using h
  have horigin := integral_abs_exp_sub_const_sub_one_rpow_root_le
    (mu := mu0) (X := X) (A := A) (p := p)
    (b := _root_.SubdiffusiveProcess.Model.tauSq M.P) hA hp hXm hX
  have hPhi : Measurable Phi := by
    exact ((((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).sub
      measurable_const).exp.sub measurable_const).norm.pow_const p)
  have hstationary : Measure.map
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate x) mu0 = mu0 :=
    M.G1.stationary x
  have hPhiMap : Integrable Phi
      (Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate x) mu0) := by
    rw [hstationary]
    simpa [Phi, X] using horigin.1
  have hxInt : Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      |Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p) mu0 := by
    have hcomp := (integrable_map_measure hPhi.aestronglyMeasurable
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate x).aemeasurable).1 hPhiMap
    simpa [Phi, Function.comp_def] using hcomp
  refine ⟨hxInt, ?_⟩
  have heq :
      ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
          |Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p ∂mu0 =
        ∫ g, Phi g ∂mu0 := by
    calc
      ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
          |Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p ∂mu0 =
          ∫ g, Phi (_root_.SubdiffusiveProcess.Model.PotentialField.translate x g) ∂mu0 := by
        apply integral_congr_ae
        filter_upwards with g
        simp [Phi]
      _ = ∫ g, Phi g
          ∂Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate x) mu0 := by
        exact (integral_map
          (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate x).aemeasurable
          hPhi.aestronglyMeasurable).symm
      _ = ∫ g, Phi g ∂mu0 := by rw [hstationary]
  rw [heq]
  simpa [freshShellPointMomentScale, A, X, Phi] using horigin.2

/-- Power form of the preceding pointwise lognormal estimate. -/
theorem integral_abs_exp_zeroPotential_apply_sub_tauSq_rpow_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (x : Vec d)
    (p : ℝ) (hp : 1 ≤ p) :
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
        |Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ≤
      (freshShellPointMomentScale M p) ^ p := by
  let I : ℝ :=
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
      |Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let B : ℝ := freshShellPointMomentScale M p
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hI0 : 0 ≤ I := integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hB : 0 < B := freshShellPointMomentScale_pos M hp0
  have hroot : I ^ p⁻¹ ≤ B := by
    simpa [I, B] using
      (integral_abs_exp_zeroPotential_apply_sub_tauSq_rpow_root_le M x p hp).2
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hroot hp0.le
  calc
    I = (I ^ p⁻¹) ^ p := by
      rw [← Real.rpow_mul hI0]
      rw [inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    _ ≤ B ^ p := hpow

/-- The same centered lognormal moment bound on an actual shell coordinate.
Marginal scaling and stationarity have already been packaged in
`isBigO_gammaTwo_potentialCoordinate_apply`; no spatial-law identification is
needed for this pointwise estimate. -/
theorem integral_abs_exp_potentialCoordinate_apply_sub_tauSq_rpow_root_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (r : ℕ) (x : Vec d)
    (p : ℝ) (hp : 1 ≤ p) :
    Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        |Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p)
        M.P.toMeasure ∧
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
            ∂M.P.toMeasure) ^ p⁻¹ ≤ freshShellPointMomentScale M p := by
  let A : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta
  have hbase : 0 < 1 + Real.log 2 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hA : 0 < A :=
    mul_pos (Real.rpow_pos_of_pos hbase _) M.shellPrefix.delta_pos
  have hXm : AEMeasurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega r x) M.P.toMeasure :=
    ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r)).aemeasurable
  have h := integral_abs_exp_sub_const_sub_one_rpow_root_le
    (mu := M.P.toMeasure) (X := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega r x)
    (A := A) (p := p) (b := _root_.SubdiffusiveProcess.Model.tauSq M.P)
    hA hp hXm (isBigO_gammaTwo_potentialCoordinate_apply M r x)
  simpa [freshShellPointMomentScale, A] using h

/-- Power form of the actual-shell pointwise lognormal estimate. -/
theorem integral_abs_exp_potentialCoordinate_apply_sub_tauSq_rpow_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (r : ℕ) (x : Vec d)
    (p : ℝ) (hp : 1 ≤ p) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
          ∂M.P.toMeasure ≤ (freshShellPointMomentScale M p) ^ p := by
  let I : ℝ :=
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      |Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
        ∂M.P.toMeasure
  let B : ℝ := freshShellPointMomentScale M p
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hI0 : 0 ≤ I := integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hB : 0 < B := freshShellPointMomentScale_pos M hp0
  have hroot : I ^ p⁻¹ ≤ B := by
    simpa [I, B] using
      (integral_abs_exp_potentialCoordinate_apply_sub_tauSq_rpow_root_le
        M r x p hp).2
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hroot hp0.le
  calc
    I = (I ^ p⁻¹) ^ p := by
      rw [← Real.rpow_mul hI0, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    _ ≤ B ^ p := hpow

/-- Product-space moment bound for an actual fresh shell. -/
theorem integral_integral_abs_potentialCoordinate_freshShell_rpow_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (r : ℕ)
    (R : TriadicCube d) (p : ℝ) (hp : 1 ≤ p) :
    let nu := normalizedCubeMeasure R
    let E : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d → ℝ := fun q =>
      |Real.exp (q.1 r q.2 - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
    Integrable E (M.P.toMeasure.prod nu) ∧
      ∫ omega, (∫ x, E (omega, x) ∂nu) ∂M.P.toMeasure ≤
        (freshShellPointMomentScale M p) ^ p := by
  dsimp only
  let nu := normalizedCubeMeasure R
  let B := freshShellPointMomentScale M p
  let E : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d → ℝ := fun q =>
    |Real.exp (q.1 r q.2 - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
  let : IsProbabilityMeasure nu :=
    isProbabilityMeasure_iff.mpr (normalizedCubeMeasure_apply_univ R)
  have hraw : Measurable
      (Function.uncurry fun x : Vec d => fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega r x) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun omega => (omega r).1.1.continuous)
      (fun x => (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r))
  have hval : Measurable (fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d => q.1 r q.2) := by
    simpa only [Function.comp_def, Function.uncurry_apply_pair, Prod.swap_prod_mk] using! hraw.comp measurable_swap
  have hEmeas : Measurable E :=
    ((hval.sub measurable_const).exp.sub measurable_const).norm.pow_const p
  have hsectionInt (x : Vec d) : Integrable (fun omega => E (omega, x)) M.P.toMeasure := by
    simpa [E] using
      (integral_abs_exp_potentialCoordinate_apply_sub_tauSq_rpow_root_le
        M r x p hp).1
  have hsectionBound (x : Vec d) :
      ∫ omega, ‖E (omega, x)‖ ∂M.P.toMeasure ≤ B ^ p := by
    have hnonneg : ∀ omega, 0 ≤ E (omega, x) := fun omega =>
      Real.rpow_nonneg (abs_nonneg _) _
    calc
      ∫ omega, ‖E (omega, x)‖ ∂M.P.toMeasure =
          ∫ omega, E (omega, x) ∂M.P.toMeasure := by
        apply integral_congr_ae
        filter_upwards with omega
        exact Real.norm_of_nonneg (hnonneg omega)
      _ ≤ B ^ p := by
        simpa [E, B] using
          integral_abs_exp_potentialCoordinate_apply_sub_tauSq_rpow_le
            M r x p hp
  have houterMeas : AEStronglyMeasurable
      (fun x => ∫ omega, ‖E (omega, x)‖ ∂M.P.toMeasure) nu :=
    hEmeas.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have houterInt : Integrable
      (fun x => ∫ omega, ‖E (omega, x)‖ ∂M.P.toMeasure) nu :=
    (integrable_const (B ^ p)).mono' houterMeas
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact hsectionBound x)
  have hprod : Integrable E (M.P.toMeasure.prod nu) :=
    (integrable_prod_iff' hEmeas.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall hsectionInt, houterInt⟩
  refine ⟨hprod, ?_⟩
  calc
    ∫ omega, (∫ x, E (omega, x) ∂nu) ∂M.P.toMeasure =
        ∫ x, (∫ omega, E (omega, x) ∂M.P.toMeasure) ∂nu :=
      integral_integral_swap hprod
    _ ≤ ∫ _x, B ^ p ∂nu := by
      exact integral_mono hprod.integral_prod_right (integrable_const (B ^ p))
        (fun x => by
          calc
            ∫ omega, E (omega, x) ∂M.P.toMeasure =
                ∫ omega, ‖E (omega, x)‖ ∂M.P.toMeasure := by
              apply integral_congr_ae
              filter_upwards with omega
              exact (Real.norm_of_nonneg
                (Real.rpow_nonneg (abs_nonneg _) _)).symm
            _ ≤ B ^ p := hsectionBound x)
    _ = B ^ p := by simp



theorem integral_abs_potentialCoordinate_freshShell_block_rpow_root_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    (r : ℕ) (R : TriadicCube d) (p : ℝ) (hp : 2 ≤ p) :
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∫ x, weight x *
            (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
          ∂normalizedCubeMeasure R| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^ (2 : ℝ)⁻¹) *
        freshShellPointMomentScale M p := by
  let nu := normalizedCubeMeasure R
  let B := freshShellPointMomentScale M p
  let E : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d → ℝ := fun q =>
    Real.exp (q.1 r q.2 - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1
  let W : ℝ := (∫ x, |weight x| ^ (2 : ℕ) ∂nu) ^ (2 : ℝ)⁻¹
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    (∫ x, |E (omega, x)| ^ (2 : ℕ) ∂nu) ^ (2 : ℝ)⁻¹
  let K : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => ∫ x, |E (omega, x)| ^ p ∂nu
  let : IsProbabilityMeasure nu :=
    isProbabilityMeasure_iff.mpr (normalizedCubeMeasure_apply_univ R)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hhalf : 1 ≤ p / 2 := by linarith
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hraw : Measurable
      (Function.uncurry fun x : Vec d => fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega r x) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun omega => (omega r).1.1.continuous)
      (fun x => (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r))
  have hval : Measurable (fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d => q.1 r q.2) := by
    simpa only [Function.comp_def, Function.uncurry_apply_pair, Prod.swap_prod_mk] using! hraw.comp measurable_swap
  have hEmeas : Measurable E :=
    (hval.sub measurable_const).exp.sub measurable_const
  have hEcont (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Continuous (fun x => E (omega, x)) :=
    (Real.continuous_exp.comp
      ((omega r).1.1.continuous.sub continuous_const)).sub continuous_const
  have hproduct :=
    integral_integral_abs_potentialCoordinate_freshShell_rpow_le M r R p hp1
  have hKInt : Integrable K M.P.toMeasure := by
    simpa [K, E, nu] using hproduct.1.integral_prod_left
  have hKbound : ∫ omega, K omega ∂M.P.toMeasure ≤ B ^ p := by
    simpa [K, E, B, nu] using hproduct.2
  have hZpow_le (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Z omega ^ p ≤ K omega := by
    let A : Vec d → ℝ := fun x => |E (omega, x)| ^ (2 : ℕ)
    have hAcont : Continuous A := (hEcont omega).abs.pow 2
    have hAInt : Integrable A nu := by
      have hcompact : IntegrableOn A
          (Metric.closedBall (cubeCenter R) (cubeRadius R)) volume :=
        hAcont.continuousOn.integrableOn_compact
          (isCompact_closedBall (cubeCenter R) (cubeRadius R))
      exact (hcompact.mono_set (cubeSet_subset_closedBall R)).smul_measure
        ENNReal.ofReal_ne_top
    have hApInt : Integrable (fun x => A x ^ (p / 2)) nu := by
      have hcont : Continuous (fun x => A x ^ (p / 2)) :=
        (Real.continuous_rpow_const (by positivity)).comp hAcont
      have hcompact : IntegrableOn (fun x => A x ^ (p / 2))
          (Metric.closedBall (cubeCenter R) (cubeRadius R)) volume :=
        hcont.continuousOn.integrableOn_compact
          (isCompact_closedBall (cubeCenter R) (cubeRadius R))
      exact (hcompact.mono_set (cubeSet_subset_closedBall R)).smul_measure
        ENNReal.ofReal_ne_top
    have hjensen : (∫ x, A x ∂nu) ^ (p / 2) ≤
        ∫ x, A x ^ (p / 2) ∂nu :=
      (convexOn_rpow hhalf).map_integral_le
        (Real.continuous_rpow_const (by positivity)).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall fun x => by
          show 0 ≤ A x
          dsimp [A]
          positivity)
        hAInt hApInt
    calc
      Z omega ^ p = (∫ x, A x ∂nu) ^ (p / 2) := by
        dsimp [Z, A]
        rw [← Real.rpow_mul (integral_nonneg fun _ => by positivity)]
        congr 1
        ring
      _ ≤ ∫ x, A x ^ (p / 2) ∂nu := hjensen
      _ = K omega := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [A, K]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (abs_nonneg (E (omega, x)))]
        congr 1
        ring
  have hZmeas : Measurable Z := by
    dsimp [Z]
    exact (hEmeas.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
      |>.pow_const _
  have hZpInt : Integrable (fun omega => Z omega ^ p) M.P.toMeasure :=
    hKInt.mono' (hZmeas.pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by
          exact Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _) _)]
        exact hZpow_le omega)
  have hW0 : 0 ≤ W := Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  have hB0 : 0 ≤ B := (freshShellPointMomentScale_pos M hp0).le
  have hpoint (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
      |∫ x, weight x * E (omega, x) ∂nu| ^ p ≤ W ^ p * Z omega ^ p := by
    have hwMem : MemLp (fun x => |weight x|) (ENNReal.ofReal 2) nu :=
      (memLp_normalizedCubeMeasure_of_continuous R (ENNReal.ofReal 2) hweight).norm
    have hEMem : MemLp (fun x => |E (omega, x)|) (ENNReal.ofReal 2) nu :=
      (memLp_normalizedCubeMeasure_of_continuous R (ENNReal.ofReal 2)
        (hEcont omega)).norm
    have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => abs_nonneg (weight x))
      (Filter.Eventually.of_forall fun x => abs_nonneg (E (omega, x)))
      hwMem hEMem
    have habs : |∫ x, weight x * E (omega, x) ∂nu| ≤ W * Z omega := by
      calc
        |∫ x, weight x * E (omega, x) ∂nu| ≤
            ∫ x, |weight x * E (omega, x)| ∂nu := abs_integral_le_integral_abs
        _ = ∫ x, |weight x| * |E (omega, x)| ∂nu := by
          apply integral_congr_ae
          filter_upwards with x
          rw [abs_mul]
        _ ≤ W * Z omega := by simpa [W, Z] using hholder
    have hpow := Real.rpow_le_rpow (abs_nonneg _) habs hp0.le
    exact hpow.trans_eq (Real.mul_rpow hW0
      (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _))
  have hWp0 : 0 ≤ W ^ p := Real.rpow_nonneg hW0 _
  have hmajorInt : Integrable (fun omega => W ^ p * Z omega ^ p) M.P.toMeasure :=
    hZpInt.const_mul (W ^ p)
  have hZbound : ∫ omega, Z omega ^ p ∂M.P.toMeasure ≤ B ^ p :=
    (integral_mono hZpInt hKInt hZpow_le).trans hKbound
  have hblockMeas : Measurable
      (fun omega => ∫ x, weight x * E (omega, x) ∂nu) := by
    have hjoint : Measurable (fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d => weight q.2 * E q) :=
      (hweight.measurable.comp measurable_snd).mul hEmeas
    exact hjoint.stronglyMeasurable.integral_prod_right'.measurable
  have htargetInt : Integrable
      (fun omega => |∫ x, weight x * E (omega, x) ∂nu| ^ p) M.P.toMeasure :=
    hmajorInt.mono' (hblockMeas.norm.pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hpoint omega)
  have hmoment :
      ∫ omega, |∫ x, weight x * E (omega, x) ∂nu| ^ p ∂M.P.toMeasure ≤
        (W * B) ^ p := by
    calc
      ∫ omega, |∫ x, weight x * E (omega, x) ∂nu| ^ p ∂M.P.toMeasure ≤
          ∫ omega, W ^ p * Z omega ^ p ∂M.P.toMeasure :=
        integral_mono htargetInt hmajorInt hpoint
      _ = W ^ p * ∫ omega, Z omega ^ p ∂M.P.toMeasure := by
        rw [integral_const_mul]
      _ ≤ W ^ p * B ^ p := mul_le_mul_of_nonneg_left hZbound hWp0
      _ = (W * B) ^ p := (Real.mul_rpow hW0 hB0).symm
  have hI0 : 0 ≤
      ∫ omega, |∫ x, weight x * E (omega, x) ∂nu| ^ p ∂M.P.toMeasure :=
    integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hroot := Real.rpow_le_rpow hI0 hmoment (inv_nonneg.mpr hp0.le)
  calc
    (∫ omega, |∫ x, weight x *
        (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
        ∂normalizedCubeMeasure R| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
        ((W * B) ^ p) ^ p⁻¹ := by simpa [E, nu] using hroot
    _ = W * B := by
      rw [← Real.rpow_mul (mul_nonneg hW0 hB0),
        mul_inv_cancel₀ hp0.ne', Real.rpow_one]
    _ = ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^
          (2 : ℝ)⁻¹) * freshShellPointMomentScale M p := rfl

/-- Power form of the actual-shell frozen-weight block estimate. -/
theorem integral_abs_potentialCoordinate_freshShell_block_rpow_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    (r : ℕ) (R : TriadicCube d) (p : ℝ) (hp : 2 ≤ p) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∫ x, weight x *
            (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
          ∂normalizedCubeMeasure R| ^ p ∂M.P.toMeasure ≤
      (((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^
          (2 : ℝ)⁻¹) * freshShellPointMomentScale M p) ^ p := by
  let I : ℝ :=
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      |∫ x, weight x *
          (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
        ∂normalizedCubeMeasure R| ^ p ∂M.P.toMeasure
  let K : ℝ :=
    ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^
        (2 : ℝ)⁻¹) * freshShellPointMomentScale M p
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hI0 : 0 ≤ I := integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hK0 : 0 ≤ K := mul_nonneg
    (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _)
    (freshShellPointMomentScale_pos M hp0).le
  have hroot : I ^ p⁻¹ ≤ K := by
    simpa [I, K] using
      integral_abs_potentialCoordinate_freshShell_block_rpow_root_le
        M weight hweight r R p hp
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hroot hp0.le
  calc
    I = (I ^ p⁻¹) ^ p := by
      rw [← Real.rpow_mul hI0, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    _ ≤ K ^ p := hpow

/--  before the elementary maximum-to-sum and cell-mass
algebra: the sum of the conditional block moments is controlled cell by cell
by the frozen spatial `L²` masses. -/
theorem finsetSum_integral_abs_potentialCoordinate_freshShell_block_rpow_le
    {d : ℕ} {ι : Type*} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (weight : ι → Vec d → ℝ) (hweight : ∀ i, Continuous (weight i))
    (r : ℕ) (R : ι → TriadicCube d) (s : Finset ι)
    (p : ℝ) (hp : 2 ≤ p) :
    ∑ i ∈ s, ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∫ x, weight i x *
            (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
          ∂normalizedCubeMeasure (R i)| ^ p ∂M.P.toMeasure ≤
      ∑ i ∈ s,
        (((∫ x, |weight i x| ^ (2 : ℕ)
            ∂normalizedCubeMeasure (R i)) ^ (2 : ℝ)⁻¹) *
          freshShellPointMomentScale M p) ^ p := by
  exact Finset.sum_le_sum fun i _ ↦
    integral_abs_potentialCoordinate_freshShell_block_rpow_le
      M (weight i) (hweight i) r (R i) p hp

/-- Product-space `p`-integrability and the normalized spatial-moment bound
for one fresh shell.  This is the Fubini/Jensen input used before applying
the frozen-weight `L²` estimate. -/
theorem integral_integral_abs_freshShell_rpow_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (R : TriadicCube d)
    (p : ℝ) (hp : 1 ≤ p) :
    let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
    let nu := normalizedCubeMeasure R
    let E : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d → ℝ := fun q =>
      |Real.exp (q.1 q.2 - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
    Integrable E (mu0.prod nu) ∧
      ∫ g, (∫ x, E (g, x) ∂nu) ∂mu0 ≤
        (freshShellPointMomentScale M p) ^ p := by
  dsimp only
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let nu := normalizedCubeMeasure R
  let B := freshShellPointMomentScale M p
  let E : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d → ℝ := fun q =>
    |Real.exp (q.1 q.2 - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p
  let : IsProbabilityMeasure nu :=
    isProbabilityMeasure_iff.mpr (normalizedCubeMeasure_apply_univ R)
  have hval : Continuous
      (fun q : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d => q.1 q.2) :=
    (ContinuousEval.continuous_eval.comp
      (((continuous_subtype_val.comp continuous_fst).fst).prodMk
        continuous_snd))
  have hEmeas : Measurable E :=
    ((hval.measurable.sub measurable_const).exp.sub measurable_const).norm.pow_const p
  have hsectionInt (x : Vec d) : Integrable (fun g => E (g, x)) mu0 := by
    simpa [E, mu0] using
      (integral_abs_exp_zeroPotential_apply_sub_tauSq_rpow_root_le M x p hp).1
  have hsectionBound (x : Vec d) :
      ∫ g, ‖E (g, x)‖ ∂mu0 ≤ B ^ p := by
    have hnonneg : ∀ g, 0 ≤ E (g, x) := fun g =>
      Real.rpow_nonneg (abs_nonneg _) _
    calc
      ∫ g, ‖E (g, x)‖ ∂mu0 = ∫ g, E (g, x) ∂mu0 := by
        apply integral_congr_ae
        filter_upwards with g
        exact Real.norm_of_nonneg (hnonneg g)
      _ ≤ B ^ p := by
        simpa [E, B, mu0] using
          integral_abs_exp_zeroPotential_apply_sub_tauSq_rpow_le M x p hp
  have hBpow0 : 0 ≤ B ^ p :=
    Real.rpow_nonneg (freshShellPointMomentScale_pos M
      (lt_of_lt_of_le zero_lt_one hp)).le _
  have houterMeas : AEStronglyMeasurable
      (fun x => ∫ g, ‖E (g, x)‖ ∂mu0) nu :=
    hEmeas.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have houterInt : Integrable (fun x => ∫ g, ‖E (g, x)‖ ∂mu0) nu :=
    (integrable_const (B ^ p)).mono' houterMeas
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact hsectionBound x)
  have hprod : Integrable E (mu0.prod nu) :=
    (integrable_prod_iff' hEmeas.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall hsectionInt, houterInt⟩
  refine ⟨hprod, ?_⟩
  calc
    ∫ g, (∫ x, E (g, x) ∂nu) ∂mu0 =
        ∫ x, (∫ g, E (g, x) ∂mu0) ∂nu := integral_integral_swap hprod
    _ ≤ ∫ _x, B ^ p ∂nu := by
      exact integral_mono hprod.integral_prod_right (integrable_const (B ^ p))
        (fun x => by
          calc
            ∫ g, E (g, x) ∂mu0 = ∫ g, ‖E (g, x)‖ ∂mu0 := by
              apply integral_congr_ae
              filter_upwards with g
              exact (Real.norm_of_nonneg
                (Real.rpow_nonneg (abs_nonneg _) _)).symm
            _ ≤ B ^ p := hsectionBound x)
    _ = B ^ p := by simp

/-- `e.condiepees` before the source-constant absorption: a frozen weight is
measured in normalized spatial `L²`, while the fresh centered exponential is
controlled by the raw G2 lognormal scale. -/
theorem integral_abs_frozenExponentialBlockMean_tauSq_rpow_root_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (weight : Vec d → ℝ)
    (hweight : Continuous weight) (R : TriadicCube d)
    (p : ℝ) (hp : 2 ≤ p) :
    (∫ g, |frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
      ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^ (2 : ℝ)⁻¹) *
        freshShellPointMomentScale M p := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let nu := normalizedCubeMeasure R
  let B := freshShellPointMomentScale M p
  let E : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d → ℝ := fun q =>
    Real.exp (q.1 q.2 - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1
  let W : ℝ := (∫ x, |weight x| ^ (2 : ℕ) ∂nu) ^ (2 : ℝ)⁻¹
  let Z : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g =>
    (∫ x, |E (g, x)| ^ (2 : ℕ) ∂nu) ^ (2 : ℝ)⁻¹
  let K : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g =>
    ∫ x, |E (g, x)| ^ p ∂nu
  let : IsProbabilityMeasure nu :=
    isProbabilityMeasure_iff.mpr (normalizedCubeMeasure_apply_univ R)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hhalf : 1 ≤ p / 2 := by linarith
  have hval : Continuous
      (fun q : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d => q.1 q.2) :=
    (ContinuousEval.continuous_eval.comp
      (((continuous_subtype_val.comp continuous_fst).fst).prodMk
        continuous_snd))
  have hEcont : Continuous E :=
    (Real.continuous_exp.comp
      (hval.sub continuous_const)).sub continuous_const
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hproduct := integral_integral_abs_freshShell_rpow_le M R p hp1
  have hKInt : Integrable K mu0 := by
    simpa [K, E, mu0, nu] using hproduct.1.integral_prod_left
  have hKbound : ∫ g, K g ∂mu0 ≤ B ^ p := by
    simpa [K, E, B, mu0, nu] using hproduct.2
  have hZpow_le (g : _root_.SubdiffusiveProcess.Model.PotentialField d) : Z g ^ p ≤ K g := by
    let A : Vec d → ℝ := fun x => |E (g, x)| ^ (2 : ℕ)
    have hAcont : Continuous A := hEcont.comp (continuous_const.prodMk continuous_id) |>.abs.pow 2
    have hAInt : Integrable A nu := by
      have hcompact : IntegrableOn A
          (Metric.closedBall (cubeCenter R) (cubeRadius R)) volume :=
        hAcont.continuousOn.integrableOn_compact
          (isCompact_closedBall (cubeCenter R) (cubeRadius R))
      exact (hcompact.mono_set (cubeSet_subset_closedBall R)).smul_measure
        ENNReal.ofReal_ne_top
    have hApInt : Integrable (fun x => A x ^ (p / 2)) nu := by
      have hcont : Continuous (fun x => A x ^ (p / 2)) :=
        (Real.continuous_rpow_const (by positivity)).comp hAcont
      have hcompact : IntegrableOn (fun x => A x ^ (p / 2))
          (Metric.closedBall (cubeCenter R) (cubeRadius R)) volume :=
        hcont.continuousOn.integrableOn_compact
          (isCompact_closedBall (cubeCenter R) (cubeRadius R))
      exact (hcompact.mono_set (cubeSet_subset_closedBall R)).smul_measure
        ENNReal.ofReal_ne_top
    have hjensen : (∫ x, A x ∂nu) ^ (p / 2) ≤
        ∫ x, A x ^ (p / 2) ∂nu := by
      exact (convexOn_rpow hhalf).map_integral_le
        (Real.continuous_rpow_const (by positivity)).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall fun x => by
          show 0 ≤ A x
          dsimp [A]
          positivity)
        hAInt hApInt
    calc
      Z g ^ p = (∫ x, A x ∂nu) ^ (p / 2) := by
        dsimp [Z, A]
        rw [← Real.rpow_mul (integral_nonneg fun _ => by positivity)]
        congr 1
        ring
      _ ≤ ∫ x, A x ^ (p / 2) ∂nu := hjensen
      _ = K g := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [A, K]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (abs_nonneg (E (g, x)))]
        congr 1
        ring
  have hE2meas : Measurable (fun q => |E q| ^ (2 : ℕ)) :=
    (hEcont.abs.pow 2).measurable
  have hZmeas : Measurable Z := by
    dsimp [Z]
    exact (hE2meas.stronglyMeasurable.integral_prod_right'.measurable).pow_const _
  have hZpInt : Integrable (fun g => Z g ^ p) mu0 :=
    hKInt.mono' (hZmeas.pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by
          exact Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _) _)]
        exact hZpow_le g)
  have hW0 : 0 ≤ W := Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  have hB0 : 0 ≤ B := (freshShellPointMomentScale_pos M hp0).le
  have hpoint (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
      |frozenExponentialBlockMean weight
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p ≤ W ^ p * Z g ^ p := by
    have hwMem : MemLp (fun x => |weight x|) (ENNReal.ofReal 2) nu :=
      (memLp_normalizedCubeMeasure_of_continuous R (ENNReal.ofReal 2) hweight).norm
    have hEMem : MemLp (fun x => |E (g, x)|) (ENNReal.ofReal 2) nu :=
      (memLp_normalizedCubeMeasure_of_continuous R (ENNReal.ofReal 2)
        (hEcont.comp (continuous_const.prodMk continuous_id))).norm
    have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => abs_nonneg (weight x))
      (Filter.Eventually.of_forall fun x => abs_nonneg (E (g, x)))
      hwMem hEMem
    have habs : |frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ≤ W * Z g := by
      calc
        |frozenExponentialBlockMean weight
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ≤
            ∫ x, |weight x * E (g, x)| ∂nu := abs_integral_le_integral_abs
        _ = ∫ x, |weight x| * |E (g, x)| ∂nu := by
          apply integral_congr_ae
          filter_upwards with x
          rw [abs_mul]
        _ ≤ W * Z g := by simpa [W, Z] using hholder
    have hpow := Real.rpow_le_rpow (abs_nonneg _) habs hp0.le
    calc
      |frozenExponentialBlockMean weight
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p ≤
          (W * Z g) ^ p := hpow
      _ = W ^ p * Z g ^ p := Real.mul_rpow hW0 (Real.rpow_nonneg
        (integral_nonneg fun _ => by positivity) _)
  have hWp0 : 0 ≤ W ^ p := Real.rpow_nonneg hW0 _
  have hmajorInt : Integrable (fun g => W ^ p * Z g ^ p) mu0 :=
    hZpInt.const_mul (W ^ p)
  have hZbound : ∫ g, Z g ^ p ∂mu0 ≤ B ^ p :=
    (integral_mono hZpInt hKInt hZpow_le).trans hKbound
  have hblockMeas : Measurable (frozenExponentialBlockMean weight
      (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) := by
    have hjoint : Measurable
        (fun q : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d =>
          weight q.2 * E q) :=
      (hweight.measurable.comp measurable_snd).mul hEcont.measurable
    simpa [frozenExponentialBlockMean, E, nu] using!
      hjoint.stronglyMeasurable.integral_prod_right'.measurable
  have htargetMeas : AEStronglyMeasurable (fun g =>
      |frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p) mu0 :=
    (hblockMeas.norm.pow_const p).aestronglyMeasurable
  have htargetInt : Integrable (fun g =>
      |frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p) mu0 :=
    hmajorInt.mono' htargetMeas
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hpoint g)
  have hmoment :
      ∫ g, |frozenExponentialBlockMean weight
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p ∂mu0 ≤
        (W * B) ^ p := by
    calc
      ∫ g, |frozenExponentialBlockMean weight
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p ∂mu0 ≤
          ∫ g, W ^ p * Z g ^ p ∂mu0 :=
        integral_mono htargetInt hmajorInt hpoint
      _ = W ^ p * ∫ g, Z g ^ p ∂mu0 := by rw [integral_const_mul]
      _ ≤ W ^ p * B ^ p := mul_le_mul_of_nonneg_left hZbound hWp0
      _ = (W * B) ^ p := (Real.mul_rpow hW0 hB0).symm
  have hI0 : 0 ≤ ∫ g, |frozenExponentialBlockMean weight
      (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p ∂mu0 :=
    integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hroot := Real.rpow_le_rpow hI0 hmoment (inv_nonneg.mpr hp0.le)
  calc
    (∫ g, |frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p ∂mu0) ^ p⁻¹ ≤
        ((W * B) ^ p) ^ p⁻¹ := hroot
    _ = W * B := by
      rw [← Real.rpow_mul (mul_nonneg hW0 hB0)]
      rw [mul_inv_cancel₀ hp0.ne', Real.rpow_one]

/-- Power form of `integral_abs_frozenExponentialBlockMean_tauSq_rpow_root_le`.
It is the form needed before summing the actual cell moments in Rosenthal's
two terms. -/
theorem integral_abs_frozenExponentialBlockMean_tauSq_rpow_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (weight : Vec d → ℝ)
    (hweight : Continuous weight) (R : TriadicCube d)
    (p : ℝ) (hp : 2 ≤ p) :
    ∫ g, |frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ≤
      (((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^ (2 : ℝ)⁻¹) *
        freshShellPointMomentScale M p) ^ p := by
  let I : ℝ :=
    ∫ g, |frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let K : ℝ :=
    ((∫ x, |weight x| ^ (2 : ℕ) ∂normalizedCubeMeasure R) ^ (2 : ℝ)⁻¹) *
      freshShellPointMomentScale M p
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hI0 : 0 ≤ I := integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hK0 : 0 ≤ K := mul_nonneg
    (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _)
    (freshShellPointMomentScale_pos M hp0).le
  have hroot : I ^ p⁻¹ ≤ K := by
    simpa [I, K] using
      integral_abs_frozenExponentialBlockMean_tauSq_rpow_root_le
        M weight hweight R p hp
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hroot hp0.le
  calc
    I = (I ^ p⁻¹) ^ p := by
      rw [← Real.rpow_mul hI0, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    _ ≤ K ^ p := hpow


/-- Every frozen weighted block variable has the real `p`-integrability
required by the color-class Rosenthal theorem.  This is the spatial Jensen
half of `e.condiepees`; the sharper `L²` size estimate is kept separate. -/
theorem integrable_abs_frozenExponentialBlockMean_tauSq_rpow {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (weight : Vec d → ℝ)
    (hweight : Continuous weight) (R : TriadicCube d)
    (p : ℝ) (hp : 1 ≤ p) :
    Integrable (fun g =>
      |frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p)
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let nu := normalizedCubeMeasure R
  let B := freshShellPointMomentScale M p
  let F : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d → ℝ := fun q =>
    weight q.2 *
      (Real.exp (q.1 q.2 - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
  let H : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d → ℝ := fun q =>
    |F q| ^ p
  let : IsProbabilityMeasure nu :=
    isProbabilityMeasure_iff.mpr (normalizedCubeMeasure_apply_univ R)
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hval : Continuous
      (fun q : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d => q.1 q.2) :=
    (ContinuousEval.continuous_eval.comp
      (((continuous_subtype_val.comp continuous_fst).fst).prodMk
        continuous_snd))
  have hFmeas : Measurable F := by
    exact (hweight.measurable.comp measurable_snd).mul
      ((hval.measurable.sub measurable_const).exp.sub measurable_const)
  have hHmeas : Measurable H := by
    exact hFmeas.norm.pow_const p
  have hsectionInt (x : Vec d) : Integrable (fun g => H (g, x)) mu0 := by
    have hpoint :=
      (integral_abs_exp_zeroPotential_apply_sub_tauSq_rpow_root_le M x p hp).1
    have hmul := hpoint.const_mul (|weight x| ^ p)
    convert hmul using 1
    funext g
    dsimp [H, F]
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hsectionBound (x : Vec d) :
      ∫ g, ‖H (g, x)‖ ∂mu0 ≤ |weight x| ^ p * B ^ p := by
    have hnonneg : ∀ g, 0 ≤ H (g, x) := fun g =>
      Real.rpow_nonneg (abs_nonneg _) _
    calc
      ∫ g, ‖H (g, x)‖ ∂mu0 = ∫ g, H (g, x) ∂mu0 := by
        apply integral_congr_ae
        filter_upwards with g
        exact Real.norm_of_nonneg (hnonneg g)
      _ = |weight x| ^ p *
          ∫ g, |Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ^ p ∂mu0 := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with g
        dsimp [H, F]
        rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      _ ≤ |weight x| ^ p * B ^ p := by
        gcongr
        simpa [B] using
          integral_abs_exp_zeroPotential_apply_sub_tauSq_rpow_le M x p hp
  have hmajorInt : Integrable (fun x => |weight x| ^ p * B ^ p) nu := by
    have hcont : Continuous (fun x => |weight x| ^ p * B ^ p) :=
      ((Real.continuous_rpow_const hp0).comp hweight.abs).mul continuous_const
    have hcompact : IntegrableOn (fun x => |weight x| ^ p * B ^ p)
        (Metric.closedBall (cubeCenter R) (cubeRadius R)) volume :=
      hcont.continuousOn.integrableOn_compact
        (isCompact_closedBall (cubeCenter R) (cubeRadius R))
    have hcube : Integrable (fun x => |weight x| ^ p * B ^ p) (cubeMeasure R) :=
      hcompact.mono_set (cubeSet_subset_closedBall R)
    exact hcube.smul_measure ENNReal.ofReal_ne_top
  have houterMeas : AEStronglyMeasurable
      (fun x => ∫ g, ‖H (g, x)‖ ∂mu0) nu :=
    hHmeas.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have houterInt : Integrable (fun x => ∫ g, ‖H (g, x)‖ ∂mu0) nu :=
    hmajorInt.mono' houterMeas
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact hsectionBound x)
  have hHprod : Integrable H (mu0.prod nu) :=
    (integrable_prod_iff' hHmeas.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall hsectionInt, houterInt⟩
  have hrightInt : Integrable (fun g => ∫ x, H (g, x) ∂nu) mu0 :=
    hHprod.integral_prod_left
  have hblockMeas : Measurable (fun g => ∫ x, F (g, x) ∂nu) :=
    hFmeas.stronglyMeasurable.integral_prod_right'.measurable
  have htargetMeas : AEStronglyMeasurable (fun g =>
      |frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p) mu0 :=
    (by
      simpa [frozenExponentialBlockMean, F, nu] using
        (hblockMeas.norm.pow_const p).aestronglyMeasurable)
  refine hrightInt.mono' htargetMeas ?_
  filter_upwards with g
  have hFcont : Continuous (fun x => F (g, x)) := by
    exact hweight.mul
      ((Real.continuous_exp.comp
        (g.1.1.continuous.sub continuous_const)).sub continuous_const)
  have hFint : Integrable (fun x => F (g, x)) nu := by
    have hcompact : IntegrableOn (fun x => F (g, x))
        (Metric.closedBall (cubeCenter R) (cubeRadius R)) volume :=
      hFcont.continuousOn.integrableOn_compact
        (isCompact_closedBall (cubeCenter R) (cubeRadius R))
    have hcube : Integrable (fun x => F (g, x)) (cubeMeasure R) :=
      hcompact.mono_set (cubeSet_subset_closedBall R)
    exact hcube.smul_measure ENNReal.ofReal_ne_top
  have hHint : Integrable (fun x => H (g, x)) nu := by
    have hHcont : Continuous (fun x => H (g, x)) :=
      (Real.continuous_rpow_const hp0).comp hFcont.abs
    have hcompact : IntegrableOn (fun x => H (g, x))
        (Metric.closedBall (cubeCenter R) (cubeRadius R)) volume :=
      hHcont.continuousOn.integrableOn_compact
        (isCompact_closedBall (cubeCenter R) (cubeRadius R))
    have hcube : Integrable (fun x => H (g, x)) (cubeMeasure R) :=
      hcompact.mono_set (cubeSet_subset_closedBall R)
    exact hcube.smul_measure ENNReal.ofReal_ne_top
  have hnormInt : Integrable (fun x => |F (g, x)|) nu := by
    simpa [Real.norm_eq_abs] using hFint.norm
  have hjensen : (∫ x, |F (g, x)| ∂nu) ^ p ≤ ∫ x, H (g, x) ∂nu := by
    simpa [H, Function.comp_def] using
      (convexOn_rpow hp).map_integral_le
        (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall fun x => abs_nonneg (F (g, x)))
        hnormInt (by simpa [H, Function.comp_def] using hHint)
  have habsInt : |∫ x, F (g, x) ∂nu| ≤ ∫ x, |F (g, x)| ∂nu :=
    abs_integral_le_integral_abs
  have hpow := Real.rpow_le_rpow (abs_nonneg _) habsInt hp0
  change ‖|∫ x, F (g, x) ∂nu| ^ p‖ ≤ ∫ x, H (g, x) ∂nu
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact hpow.trans hjensen

/-- The frozen one-block variables supplied to the color-class Rosenthal
estimate are centered.  The proof also establishes the product integrability
needed for the Fubini interchange, rather than hiding it in a conditional-
expectation convention. -/
theorem integral_frozenExponentialBlockMean_tauSq_eq_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (weight : Vec d → ℝ)
    (hweight : Continuous weight) (R : TriadicCube d) :
    ∫ g, frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure = 0 := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let nu := normalizedCubeMeasure R
  let F : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d → ℝ := fun q =>
    weight q.2 *
      (Real.exp (q.1 q.2 - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
  have hval : Continuous
      (fun q : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d => q.1 q.2) :=
    (ContinuousEval.continuous_eval.comp
      (((continuous_subtype_val.comp continuous_fst).fst).prodMk
        continuous_snd))
  have hFmeas : Measurable F := by
    exact (hweight.measurable.comp measurable_snd).mul
      ((hval.measurable.sub measurable_const).exp.sub measurable_const)
  have hshiftInt (x : Vec d) : Integrable
      (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P)) mu0 := by
    have h := (integrable_exp_zeroPotential_apply M x).const_mul
      (Real.exp (-_root_.SubdiffusiveProcess.Model.tauSq M.P))
    convert h using 1
    funext g
    rw [Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
    ring
  have hsectionInt (x : Vec d) : Integrable (fun g => F (g, x)) mu0 := by
    have hcenter := (hshiftInt x).sub (integrable_const (1 : ℝ))
    have hmul := hcenter.const_mul (weight x)
    simpa [F] using hmul
  have hsectionNorm (x : Vec d) :
      ∫ g, ‖F (g, x)‖ ∂mu0 ≤ 2 * |weight x| := by
    let G : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g =>
      |weight x| *
        (Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) + 1)
    have hGint : Integrable G mu0 := by
      have h := ((hshiftInt x).add (integrable_const (1 : ℝ))).const_mul |weight x|
      simpa [G] using h
    have hpoint : ∀ g, ‖F (g, x)‖ ≤ G g := by
      intro g
      rw [Real.norm_eq_abs, abs_mul]
      dsimp [F, G]
      gcongr
      calc
        |Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ≤
            |Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P)| + |(1 : ℝ)| :=
          abs_sub _ _
        _ = Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) + 1 := by
          rw [abs_of_pos (Real.exp_pos _)]
          norm_num
    calc
      ∫ g, ‖F (g, x)‖ ∂mu0 ≤ ∫ g, G g ∂mu0 :=
        integral_mono (hsectionInt x).norm hGint hpoint
      _ = |weight x| *
          ((∫ g, Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) ∂mu0) + 1) := by
        rw [integral_const_mul, integral_add (hshiftInt x) (integrable_const (1 : ℝ))]
        simp
      _ = 2 * |weight x| := by
        rw [integral_exp_sub_tauSq_zeroPotential_apply_eq_one M x]
        ring
  have hweightInt : Integrable (fun x => 2 * |weight x|) nu := by
    have hcompact : IntegrableOn (fun x => 2 * |weight x|)
        (Metric.closedBall (cubeCenter R) (cubeRadius R)) volume :=
      (continuous_const.mul hweight.abs).continuousOn.integrableOn_compact
        (isCompact_closedBall (cubeCenter R) (cubeRadius R))
    have hcube : Integrable (fun x => 2 * |weight x|) (cubeMeasure R) := by
      exact hcompact.mono_set (cubeSet_subset_closedBall R)
    exact hcube.smul_measure ENNReal.ofReal_ne_top
  have houterMeas : AEStronglyMeasurable
      (fun x => ∫ g, ‖F (g, x)‖ ∂mu0) nu :=
    hFmeas.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have houterInt : Integrable (fun x => ∫ g, ‖F (g, x)‖ ∂mu0) nu :=
    hweightInt.mono' houterMeas
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact hsectionNorm x)
  have hprod : Integrable F (mu0.prod nu) :=
    (integrable_prod_iff' hFmeas.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall hsectionInt, houterInt⟩
  calc
    ∫ g, frozenExponentialBlockMean weight
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g ∂mu0 =
        ∫ g, ∫ x, F (g, x) ∂nu ∂mu0 := by rfl
    _ = ∫ x, ∫ g, F (g, x) ∂mu0 ∂nu := integral_integral_swap hprod
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with x
      have hcenter := (hshiftInt x).sub (integrable_const (1 : ℝ))
      calc
        ∫ g, F (g, x) ∂mu0 = weight x *
            ∫ g, (Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) ∂mu0 := by
          rw [← integral_const_mul]
        _ = weight x *
            ((∫ g, Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) ∂mu0) - 1) := by
          rw [integral_sub (hshiftInt x) (integrable_const (1 : ℝ))]
          simp
        _ = 0 := by
          rw [integral_exp_sub_tauSq_zeroPotential_apply_eq_one M x]
          ring

/-- The frozen weighted block mean is measurable for the canonical
potential-field sigma algebra. -/
theorem measurable_frozenExponentialBlockMean {d : ℕ}
    (weight : Vec d → ℝ) (hweight : Measurable weight)
    (tau : ℝ) (R : TriadicCube d) :
    Measurable (frozenExponentialBlockMean weight tau R) := by
  have hval : Continuous
      (fun q : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d => q.1 q.2) :=
    (ContinuousEval.continuous_eval.comp
      (((continuous_subtype_val.comp continuous_fst).fst).prodMk
        continuous_snd))
  have hintegrand : Measurable
      (fun q : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d =>
        weight q.2 * (Real.exp (q.1 q.2 - tau) - 1)) :=
    (hweight.comp measurable_snd).mul
      ((hval.measurable.sub measurable_const).exp.sub measurable_const)
  exact hintegrand.stronglyMeasurable.integral_prod_right'.measurable

private noncomputable def localInteriorCutoff {d : ℕ}
    (U : Set (Vec d)) (n : ℕ) (x : Vec d) : ℝ :=
  Metric.infDist x Uᶜ /
    (Metric.infDist x Uᶜ + 1 / ((n : ℝ) + 1))

private theorem continuous_localInteriorCutoff {d : ℕ}
    (U : Set (Vec d)) (n : ℕ) : Continuous (localInteriorCutoff U n) := by
  apply (Metric.continuous_infDist_pt Uᶜ).div
    ((Metric.continuous_infDist_pt Uᶜ).add continuous_const)
  intro x
  have hq : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have ha : 0 ≤ Metric.infDist x Uᶜ := Metric.infDist_nonneg
  exact (add_pos_of_nonneg_of_pos ha hq).ne'



theorem measurable_frozenExponentialBlockMean_localSigma
    {d : ℕ} [NeZero d]
    (weight : Vec d → ℝ) (hweight : Continuous weight)
    (tau : ℝ) (R : TriadicCube d) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
      (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (cubeSet R)) _
      (frozenExponentialBlockMean weight tau R) := by
  let U : Set (Vec d) := openCubeSet R
  let base : _root_.SubdiffusiveProcess.Model.PotentialField d → Vec d → ℝ := fun g x =>
    weight x * (Real.exp (g x - tau) - 1)
  let F : ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d → Vec d → ℝ := fun n g x =>
    localInteriorCutoff U n x * base g x
  have hUopen : IsOpen U := isOpen_openCubeSet R
  have hUsub : U ⊆ cubeSet R := openCubeSet_subset_cubeSet R
  have heval (x : Vec d) (hx : x ∈ U) :
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (cubeSet R)) _
        (fun g => g x) :=
    (measurable_eval_potentialFieldLocalSigma_of_mem_isOpen hUopen hx).mono
      (potentialFieldLocalSigma_mono hUsub) le_rfl
  have hF_section (n : ℕ) (x : Vec d) :
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (cubeSet R)) _
        (fun g => F n g x) := by
    by_cases hx : x ∈ U
    · exact measurable_const.mul
        (measurable_const.mul (((heval x hx).sub measurable_const).exp.sub measurable_const))
    · have hcut : localInteriorCutoff U n x = 0 := by
        simp [localInteriorCutoff, Metric.infDist_zero_of_mem (show x ∈ Uᶜ from hx)]
      simp [F, hcut]
  have hF_cont (n : ℕ) (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
      Continuous (F n g) := by
    exact (continuous_localInteriorCutoff U n).mul
      (hweight.mul
        ((Real.continuous_exp.comp
          (g.1.1.continuous.sub continuous_const)).sub continuous_const))
  have hF_joint (n : ℕ) :
      @Measurable
        (_root_.SubdiffusiveProcess.Model.PotentialField d × Vec d) ℝ
        ((_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (cubeSet R)).prod
          inferInstance) _
        (fun q => F n q.1 q.2) := by
    have hraw :
        @Measurable
          (Vec d × _root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
          ((inferInstance : MeasurableSpace (Vec d)).prod
            (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (cubeSet R))) _
          (Function.uncurry fun x g => F n g x) :=
      measurable_uncurry_of_continuous_of_measurable (fun g => hF_cont n g) (hF_section n)
    have hswap :
        @Measurable
          (_root_.SubdiffusiveProcess.Model.PotentialField d × Vec d)
          (Vec d × _root_.SubdiffusiveProcess.Model.PotentialField d)
          ((_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (cubeSet R)).prod
            inferInstance)
          ((inferInstance : MeasurableSpace (Vec d)).prod
            (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (cubeSet R)))
          Prod.swap := measurable_swap
    simpa only [Function.comp_def, Function.uncurry_apply_pair, Prod.swap_prod_mk] using! hraw.comp hswap
  have hFn_meas (n : ℕ) :
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (cubeSet R)) _
        (fun g => ∫ x, F n g x ∂normalizedCubeMeasure R) := by
    let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
      _root_.SubdiffusiveProcess.Model.PotentialField.localSigma (cubeSet R)
    exact (hF_joint n).stronglyMeasurable.integral_prod_right'.measurable
  refine @measurable_of_tendsto_metrizable
    (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
    (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (cubeSet R)) _ _ _ _
    (fun n g => ∫ x, F n g x ∂normalizedCubeMeasure R)
    (frozenExponentialBlockMean weight tau R) hFn_meas ?_
  rw [tendsto_pi_nhds]
  intro g
  have hbase_cont : Continuous (base g) :=
    hweight.mul ((Real.continuous_exp.comp
      (g.1.1.continuous.sub continuous_const)).sub continuous_const)
  have hbase_on : IntegrableOn (base g) (cubeSet R) volume := by
    exact (ContinuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter R) (cubeRadius R)) hbase_cont.continuousOn).mono_set
        (cubeSet_subset_closedBall R)
  have hbase_int : Integrable (base g) (normalizedCubeMeasure R) := by
    rw [normalizedCubeMeasure, cubeMeasure]
    exact hbase_on.smul_measure ENNReal.ofReal_ne_top
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => |base g x|)
  · intro n
    exact (hF_cont n g).aestronglyMeasurable
  · exact hbase_int.norm
  · intro n
    filter_upwards with x
    have ha : 0 ≤ Metric.infDist x Uᶜ := Metric.infDist_nonneg
    have hq : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hcut_nonneg : 0 ≤ localInteriorCutoff U n x := by
      exact div_nonneg ha (add_nonneg ha hq.le)
    have hcut_le : localInteriorCutoff U n x ≤ 1 := by
      rw [localInteriorCutoff, div_le_one (add_pos_of_nonneg_of_pos ha hq)]
      linarith
    change |localInteriorCutoff U n x * base g x| ≤ |base g x|
    rw [abs_mul, abs_of_nonneg hcut_nonneg]
    exact mul_le_of_le_one_left (abs_nonneg _) hcut_le
  · filter_upwards [ae_openCubeSet_normalizedCubeMeasure R] with x hx
    have hcomp : (Uᶜ).Nonempty := by
      apply Set.nonempty_compl.mpr
      intro hU
      apply NormedSpace.unbounded_univ (𝕜 := ℝ) (E := Vec d)
      simpa [U, hU] using isBounded_openCubeSet R
    have hxU : x ∈ U := by simpa [U] using hx
    have hxnot : x ∉ Uᶜ := by simpa using hxU
    have ha : 0 < Metric.infDist x Uᶜ :=
      ((hUopen.isClosed_compl).notMem_iff_infDist_pos hcomp).mp hxnot
    have hcut_tendsto :
        Filter.Tendsto (fun n => localInteriorCutoff U n x) Filter.atTop (nhds 1) := by
      have hq : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hnum : Filter.Tendsto (fun _ : ℕ => Metric.infDist x Uᶜ)
          Filter.atTop (nhds (Metric.infDist x Uᶜ)) := tendsto_const_nhds
      have hden : Filter.Tendsto
          (fun n : ℕ => Metric.infDist x Uᶜ + 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds (Metric.infDist x Uᶜ + 0)) :=
        tendsto_const_nhds.add hq
      have hdiv := hnum.div hden (by simpa using ha.ne')
      simpa [localInteriorCutoff, Pi.div_apply, div_self ha.ne'] using! hdiv
    change Filter.Tendsto
      (fun n => localInteriorCutoff U n x * base g x) Filter.atTop (nhds (base g x))
    simpa using hcut_tendsto.mul_const (base g x)

/-- Real-exponent Rosenthal on one G1 color class.  The only model-specific
input left to a consumer is locality of each weighted block mean in its own
observation region; mutual independence is derived here from G1.

 this is the one-class core of
`Algsuperdiff/Probability/ColoredAverage.lean`, using CoarseGraining's
real-exponent Rosenthal corollary. -/
theorem integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_of_G1_colorClass
    {d : ℕ} {ι : Type*} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    {X : ι → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ}
    {sI : Finset ι} (hsI : sI.Nonempty) {p : ℝ} (hp : 2 ≤ p)
    (hsep : Pairwise fun i j => PotentialRangeSeparated (U i) (U j))
    (hX_local : ∀ i,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (U i)) _ (X i))
    (hLp_int : ∀ i ∈ sI,
      Integrable (fun g => |X i g| ^ p)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
    (hmean : ∀ i ∈ sI,
      ∫ g, X i g ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure = 0) :
    (∫ g, |∑ i ∈ sI, X i g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
      2 * p *
          (∑ i ∈ sI,
            ∫ g, |X i g| ^ p
              ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt
            (∑ i ∈ sI, ProbabilityTheory.moment (X i) 2
              (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)) := by
  apply
    integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_polynomial_of_iIndepFun_of_integral_eq_zero
      hsI hp
      (iIndepFun_of_G1_of_potentialFieldLocal M hU hsep hX_local)
  · intro i
    exact (hX_local i).mono (potentialFieldLocalSigma_le_borel (U i)) le_rfl
  · exact hLp_int
  · exact hmean

/-- The complete one-color moment statement for the paper's frozen
exponential block variables.  Unlike the generic G1/Rosenthal theorem above,
this specialization has no locality premise: continuity of the frozen weights
and the continuous potential carrier discharge it internally. -/
theorem integral_abs_sum_frozenExponentialBlockMean_rpow_rpow_inv_le_of_G1_colorClass
    {d : ℕ} {ι : Type*} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : ι → TriadicCube d) (weight : ι → Vec d → ℝ)
    (hweight : ∀ i, Continuous (weight i)) (tau : ℝ)
    {sI : Finset ι} (hsI : sI.Nonempty) {p : ℝ} (hp : 2 ≤ p)
    (hsep : Pairwise fun i j =>
      PotentialRangeSeparated (cubeSet (R i)) (cubeSet (R j)))
    (hLp_int : ∀ i ∈ sI,
      Integrable (fun g => |frozenExponentialBlockMean (weight i) tau (R i) g| ^ p)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
    (hmean : ∀ i ∈ sI,
      ∫ g, frozenExponentialBlockMean (weight i) tau (R i) g
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure = 0) :
    (∫ g, |∑ i ∈ sI, frozenExponentialBlockMean (weight i) tau (R i) g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
      2 * p *
          (∑ i ∈ sI,
            ∫ g, |frozenExponentialBlockMean (weight i) tau (R i) g| ^ p
              ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt
            (∑ i ∈ sI, ProbabilityTheory.moment
              (frozenExponentialBlockMean (weight i) tau (R i)) 2
              (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)) := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let : NeZero d := ⟨by omega⟩
  apply integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_of_G1_colorClass
    M (U := fun i => cubeSet (R i))
    (X := fun i => frozenExponentialBlockMean (weight i) tau (R i))
    (fun i => measurableSet_cubeSet (R i)) hsI hp hsep
  · intro i
    exact measurable_frozenExponentialBlockMean_localSigma
      (weight i) (hweight i) tau (R i)
  · exact hLp_int
  · exact hmean

/-- The source-specialized one-color Rosenthal estimate at the actual GMC
normalization.  The centering hypotheses are discharged by G1 stationarity,
G4, and the definition of `tauSq`; consumers now supply only the quantitative
`p`-integrability input for the frozen weights. -/
theorem integral_abs_sum_frozenExponentialBlockMean_tauSq_rpow_rpow_inv_le_of_G1_colorClass
    {d : ℕ} {ι : Type*} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : ι → TriadicCube d) (weight : ι → Vec d → ℝ)
    (hweight : ∀ i, Continuous (weight i))
    {sI : Finset ι} (hsI : sI.Nonempty) {p : ℝ} (hp : 2 ≤ p)
    (hsep : Pairwise fun i j =>
      PotentialRangeSeparated (cubeSet (R i)) (cubeSet (R j)))
    (hLp_int : ∀ i ∈ sI,
      Integrable (fun g =>
        |frozenExponentialBlockMean (weight i)
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i) g| ^ p)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) :
    (∫ g, |∑ i ∈ sI, frozenExponentialBlockMean (weight i)
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i) g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
      2 * p *
          (∑ i ∈ sI,
            ∫ g, |frozenExponentialBlockMean (weight i)
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i) g| ^ p
              ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt
            (∑ i ∈ sI, ProbabilityTheory.moment
              (frozenExponentialBlockMean (weight i)
                (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i)) 2
              (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)) := by
  apply
    integral_abs_sum_frozenExponentialBlockMean_rpow_rpow_inv_le_of_G1_colorClass
      M R weight hweight (_root_.SubdiffusiveProcess.Model.tauSq M.P) hsI hp hsep hLp_int
  intro i hi
  exact integral_frozenExponentialBlockMean_tauSq_eq_zero M (weight i) (hweight i) (R i)

/-- Fully discharged one-color Rosenthal interface for the centered fresh
shell.  All integrability and centering obligations are consequences of the
model assumptions; only the scale-color separation remains at the call site. -/
theorem integral_abs_sum_frozenExponentialBlockMean_tauSq_rpow_rpow_inv_le
    {d : ℕ} {ι : Type*} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : ι → TriadicCube d) (weight : ι → Vec d → ℝ)
    (hweight : ∀ i, Continuous (weight i))
    {sI : Finset ι} (hsI : sI.Nonempty) {p : ℝ} (hp : 2 ≤ p)
    (hsep : Pairwise fun i j =>
      PotentialRangeSeparated (cubeSet (R i)) (cubeSet (R j))) :
    (∫ g, |∑ i ∈ sI, frozenExponentialBlockMean (weight i)
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i) g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
      2 * p *
          (∑ i ∈ sI,
            ∫ g, |frozenExponentialBlockMean (weight i)
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i) g| ^ p
              ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt
            (∑ i ∈ sI, ProbabilityTheory.moment
              (frozenExponentialBlockMean (weight i)
                (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i)) 2
              (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)) := by
  apply
    integral_abs_sum_frozenExponentialBlockMean_tauSq_rpow_rpow_inv_le_of_G1_colorClass
      M R weight hweight hsI hp hsep
  intro i hi
  exact integrable_abs_frozenExponentialBlockMean_tauSq_rpow
    M (weight i) (hweight i) (R i) p (le_trans (by norm_num) hp)

/-- Quantitative one-color form after substituting the frozen cell `L²`
sizes into both Rosenthal terms. -/
theorem integral_abs_sum_frozenExponentialBlockMean_tauSq_rpow_rpow_inv_le_weight
    {d : ℕ} {ι : Type*} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : ι → TriadicCube d) (weight : ι → Vec d → ℝ)
    (hweight : ∀ i, Continuous (weight i))
    {sI : Finset ι} (hsI : sI.Nonempty) {p : ℝ} (hp : 2 ≤ p)
    (hsep : Pairwise fun i j ↦
      PotentialRangeSeparated (cubeSet (R i)) (cubeSet (R j))) :
    (∫ g, |∑ i ∈ sI, frozenExponentialBlockMean (weight i)
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i) g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
      2 * p *
          (∑ i ∈ sI,
            (((∫ x, |weight i x| ^ (2 : ℕ) ∂normalizedCubeMeasure (R i)) ^
                  (2 : ℝ)⁻¹) * freshShellPointMomentScale M p) ^ p) ^ p⁻¹ +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt
            (∑ i ∈ sI,
              (((∫ x, |weight i x| ^ (2 : ℕ) ∂normalizedCubeMeasure (R i)) ^
                    (2 : ℝ)⁻¹) * freshShellPointMomentScale M 2) ^ (2 : ℕ))) := by
  have hbase :=
    integral_abs_sum_frozenExponentialBlockMean_tauSq_rpow_rpow_inv_le
      M R weight hweight hsI hp hsep
  have hsum_p :
      (∑ i ∈ sI,
          ∫ g, |frozenExponentialBlockMean (weight i)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i) g| ^ p
            ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ≤
        ∑ i ∈ sI,
          (((∫ x, |weight i x| ^ (2 : ℕ) ∂normalizedCubeMeasure (R i)) ^
                (2 : ℝ)⁻¹) * freshShellPointMomentScale M p) ^ p :=
    Finset.sum_le_sum fun i hi ↦
      integral_abs_frozenExponentialBlockMean_tauSq_rpow_le
        M (weight i) (hweight i) (R i) p hp
  have hroot_p := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i hi ↦ integral_nonneg fun _ ↦
      Real.rpow_nonneg (abs_nonneg _) _)
    hsum_p (inv_nonneg.mpr (le_trans (by norm_num) hp))
  have hsum_two :
      (∑ i ∈ sI, ProbabilityTheory.moment
          (frozenExponentialBlockMean (weight i)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i)) 2
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ≤
        ∑ i ∈ sI,
          (((∫ x, |weight i x| ^ (2 : ℕ) ∂normalizedCubeMeasure (R i)) ^
                (2 : ℝ)⁻¹) * freshShellPointMomentScale M 2) ^ (2 : ℕ) := by
    apply Finset.sum_le_sum
    intro i hi
    calc
      ProbabilityTheory.moment
          (frozenExponentialBlockMean (weight i)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i)) 2
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure =
          ∫ g, |frozenExponentialBlockMean (weight i)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) (R i) g| ^ (2 : ℕ)
            ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
        simp [ProbabilityTheory.moment]
      _ ≤ (((∫ x, |weight i x| ^ (2 : ℕ) ∂normalizedCubeMeasure (R i)) ^
              (2 : ℝ)⁻¹) * freshShellPointMomentScale M 2) ^ (2 : ℕ) :=
        by
          convert
            integral_abs_frozenExponentialBlockMean_tauSq_rpow_le
              M (weight i) (hweight i) (R i) 2 (by norm_num) using 1 <;>
            norm_num [Real.rpow_natCast]
  have hsqrt_two := Real.sqrt_le_sqrt hsum_two
  have hfirst := mul_le_mul_of_nonneg_left hroot_p (by positivity : 0 ≤ 2 * p)
  have hRB : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst,
      Homogenization.IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have hsecond := mul_le_mul_of_nonneg_left hsqrt_two
    (by positivity : 0 ≤ 4 * rosenthalBennettIntegralConst * Real.sqrt p)
  exact hbase.trans (add_le_add hfirst (by
    simpa [mul_assoc] using hsecond))

/-- Recombination of the paper's finitely many range-separated color
classes.  The right-hand side retains the actual moment of every frozen cell;
this is essential for the square-root descendant gain after the frozen
weight is integrated out.

 this follows the finite-color Minkowski and `biUnion` assembly in
`Homogenization/Book/Ch04/SourceDescendantMoments.lean` and mirrors
`Algsuperdiff/Section3/Provider/Stream/LayerPairColoredAverage.lean`. -/
theorem integral_abs_sum_frozenExponentialBlockMean_tauSq_rpow_rpow_inv_le_colors
    {d : ℕ} {κ : Type*} [DecidableEq κ]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (k : ℤ)
    (color : TriadicCube d → κ)
    (weight : TriadicCube d → Vec d → ℝ)
    (hweight : ∀ R, Continuous (weight R))
    {p : ℝ} (hp : 2 ≤ p)
    (hsep : ∀ c ∈ (descendantsAtScale Q k).image color,
      ((descendantsAtScale Q k).filter (fun R ↦ color R = c) :
        Set (TriadicCube d)).Pairwise fun R S ↦
          PotentialRangeSeparated (cubeSet R) (cubeSet S)) :
    (∫ g, |∑ R ∈ descendantsAtScale Q k,
        frozenExponentialBlockMean (weight R)
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
      ∑ c ∈ (descendantsAtScale Q k).image color,
        (2 * p *
            (∑ R ∈ (descendantsAtScale Q k).filter (fun R ↦ color R = c),
              ∫ g, |frozenExponentialBlockMean (weight R)
                (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
                ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt
              (∑ R ∈ (descendantsAtScale Q k).filter (fun R ↦ color R = c),
                ProbabilityTheory.moment
                  (frozenExponentialBlockMean (weight R)
                    (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) 2
                  (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure))) := by
  classical
  let colors : Finset κ := (descendantsAtScale Q k).image color
  let Y : κ → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun c g ↦
    ∑ R ∈ (descendantsAtScale Q k).filter (fun R ↦ color R = c),
      frozenExponentialBlockMean (weight R)
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have hclass_nonempty : ∀ c ∈ colors,
      ((descendantsAtScale Q k).filter (fun R ↦ color R = c)).Nonempty := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨R, hR, rfl⟩
    exact ⟨R, by simp [hR]⟩
  have hY_meas : ∀ c ∈ colors, Measurable (Y c) := by
    intro c hc
    dsimp [Y]
    exact Finset.measurable_sum _ fun R _ ↦
      measurable_frozenExponentialBlockMean (weight R) (hweight R).measurable
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R
  have hY_int : ∀ c ∈ colors, Integrable (fun g ↦ |Y c g| ^ p)
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
    intro c hc
    dsimp [Y]
    exact integrable_abs_finsetSum_rpow
      (μ := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
      (s := (descendantsAtScale Q k).filter (fun R ↦ color R = c))
      hp_one
      (fun R _ ↦ measurable_frozenExponentialBlockMean (weight R)
        (hweight R).measurable (_root_.SubdiffusiveProcess.Model.tauSq M.P) R)
      (fun R _ ↦ integrable_abs_frozenExponentialBlockMean_tauSq_rpow
        M (weight R) (hweight R) R p hp_one)
  have hY_bound : ∀ c ∈ colors,
      (∫ g, |Y c g| ^ p
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
        2 * p *
            (∑ R ∈ (descendantsAtScale Q k).filter (fun R ↦ color R = c),
              ∫ g, |frozenExponentialBlockMean (weight R)
                (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
                ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt
              (∑ R ∈ (descendantsAtScale Q k).filter (fun R ↦ color R = c),
                ProbabilityTheory.moment
                  (frozenExponentialBlockMean (weight R)
                    (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) 2
                  (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)) := by
    intro c hc
    let S : Finset (TriadicCube d) :=
      (descendantsAtScale Q k).filter (fun R ↦ color R = c)
    let R' : {R : TriadicCube d // R ∈ S} → TriadicCube d := fun R ↦ R.1
    let weight' : {R : TriadicCube d // R ∈ S} → Vec d → ℝ := fun R ↦ weight R.1
    have hattach : S.attach.Nonempty := by
      simpa [S] using hclass_nonempty c hc
    have hsep' : Pairwise fun (R T : {R : TriadicCube d // R ∈ S}) ↦
        PotentialRangeSeparated (cubeSet (R' R)) (cubeSet (R' T)) := by
      intro R T hRT
      apply hsep c hc R.2 T.2
      intro hval
      apply hRT
      exact Subtype.ext hval
    have hbound :=
      integral_abs_sum_frozenExponentialBlockMean_tauSq_rpow_rpow_inv_le
        M R' weight' (fun R ↦ hweight R.1) hattach hp hsep'
    dsimp [R', weight'] at hbound
    have hsum_block (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
        (∑ R ∈ S.attach, frozenExponentialBlockMean (weight R.1)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) R.1 g) =
          ∑ R ∈ S, frozenExponentialBlockMean (weight R)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g := by
      simpa using Finset.sum_attach (s := S) (f := fun R ↦
        frozenExponentialBlockMean (weight R)
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g)
    have hsum_p :
        (∑ R ∈ S.attach,
            ∫ g, |frozenExponentialBlockMean (weight R.1)
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) R.1 g| ^ p
              ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) =
          ∑ R ∈ S,
            ∫ g, |frozenExponentialBlockMean (weight R)
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
              ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      simpa using Finset.sum_attach (s := S) (f := fun R ↦
        ∫ g, |frozenExponentialBlockMean (weight R)
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
    have hsum_two :
        (∑ R ∈ S.attach, ProbabilityTheory.moment
            (frozenExponentialBlockMean (weight R.1)
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) R.1) 2
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) =
          ∑ R ∈ S, ProbabilityTheory.moment
            (frozenExponentialBlockMean (weight R)
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) 2
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      simpa using Finset.sum_attach (s := S) (f := fun R ↦
        ProbabilityTheory.moment
          (frozenExponentialBlockMean (weight R)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) 2
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
    simp_rw [hsum_block] at hbound
    rw [hsum_p, hsum_two] at hbound
    simpa [Y, S, R', weight'] using hbound
  have hsum :
      (∫ g, |∑ c ∈ colors, Y c g| ^ p
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ ≤
        ∑ c ∈ colors,
          (∫ g, |Y c g| ^ p
            ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ := by
    exact integral_abs_finsetSum_rpow_rpow_inv_le_sum
      (μ := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
      hp_one hY_meas hY_int
  have hsum_eq : (fun g ↦ ∑ c ∈ colors, Y c g) =
      fun g ↦ ∑ R ∈ descendantsAtScale Q k,
        frozenExponentialBlockMean (weight R)
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g := by
    funext g
    calc
      ∑ c ∈ colors, Y c g =
          ∑ c ∈ colors,
            ∑ R ∈ (descendantsAtScale Q k).filter (fun R ↦ color R = c),
            frozenExponentialBlockMean (weight R)
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g := by
        refine Finset.sum_congr rfl fun c hc ↦ ?_
        simp [Y]
      _ = ∑ R ∈ colors.biUnion
          (fun c ↦ (descendantsAtScale Q k).filter (fun R ↦ color R = c)),
          frozenExponentialBlockMean (weight R)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g := by
        symm
        exact Finset.sum_biUnion fun c hc c' hc' hne ↦ by
          change Disjoint
            ((descendantsAtScale Q k).filter (fun R ↦ color R = c))
            ((descendantsAtScale Q k).filter (fun R ↦ color R = c'))
          rw [Finset.disjoint_left]
          intro R hRc hRc'
          simp only [Finset.mem_filter] at hRc hRc'
          exact hne (hRc.2.symm.trans hRc'.2)
      _ = ∑ R ∈ descendantsAtScale Q k,
          frozenExponentialBlockMean (weight R)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g := by
        rw [show colors.biUnion
            (fun c ↦ (descendantsAtScale Q k).filter (fun R ↦ color R = c)) =
            descendantsAtScale Q k by
          ext R
          constructor
          · intro hR
            rcases Finset.mem_biUnion.mp hR with ⟨c, hc, hRc⟩
            exact (Finset.mem_filter.mp hRc).1
          · intro hR
            exact Finset.mem_biUnion.mpr
              ⟨color R, Finset.mem_image.mpr ⟨R, hR, rfl⟩, by simp [hR]⟩]
  calc
    (∫ g, |∑ R ∈ descendantsAtScale Q k,
        frozenExponentialBlockMean (weight R)
          (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ =
        (∫ g, |∑ c ∈ colors, Y c g| ^ p
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g ↦ by
        change
          |∑ R ∈ descendantsAtScale Q k,
              frozenExponentialBlockMean (weight R)
                (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p =
            |∑ c ∈ colors, Y c g| ^ p
        rw [congrFun hsum_eq g]
    _ ≤ ∑ c ∈ colors,
        (∫ g, |Y c g| ^ p
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ := hsum
    _ ≤ ∑ c ∈ colors,
        (2 * p *
            (∑ R ∈ (descendantsAtScale Q k).filter (fun R ↦ color R = c),
              ∫ g, |frozenExponentialBlockMean (weight R)
                (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p
                ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt
              (∑ R ∈ (descendantsAtScale Q k).filter (fun R ↦ color R = c),
                ProbabilityTheory.moment
                  (frozenExponentialBlockMean (weight R)
                    (_root_.SubdiffusiveProcess.Model.tauSq M.P) R) 2
                  (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure))) :=
      Finset.sum_le_sum fun c hc ↦ hY_bound c hc


/-! ## Actual-shell color recombination after marginal rescaling -/

/-- The complete finite-color Rosenthal bound for an actual shell coordinate.
The shell is transported to the zero law, every scale-`r-1` cell is dilated
to scale `-1`, and the dimension-range coloring supplies G1 separation. The
right side deliberately retains the cellwise frozen-weight moments for the
subsequent descendant-mass calculation. -/
theorem integral_abs_sum_potentialCoordinate_freshShell_rpow_root_le_colors
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (r : ℕ) (_hrQ : (r : ℤ) - 1 ≤ Q.scale)
    (weight : TriadicCube d → Vec d → ℝ)
    (hweight : ∀ R, Continuous (weight R)) {p : ℝ} (hp : 2 ≤ p) :
    let Q' := Ch02.dilateCube (-(r : ℤ)) Q
    let weight' : TriadicCube d → Vec d → ℝ := fun S y =>
      weight (Ch02.dilateCube (r : ℤ) S) (Ch02.dilateVec (r : ℤ) y)
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        |∑ R ∈ descendantsAtScale Q ((r : ℤ) - 1),
          ∫ x, weight R x *
              (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
            ∂normalizedCubeMeasure R| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      ∑ c ∈ (descendantsAtScale Q' (-1)).image cubeFreshShellColor,
        (2 * p *
            (∑ S ∈ (descendantsAtScale Q' (-1)).filter
                (fun S ↦ cubeFreshShellColor S = c),
              ∫ g, |frozenExponentialBlockMean (weight' S)
                (_root_.SubdiffusiveProcess.Model.tauSq M.P) S g| ^ p
                ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt
              (∑ S ∈ (descendantsAtScale Q' (-1)).filter
                  (fun S ↦ cubeFreshShellColor S = c),
                ProbabilityTheory.moment
                  (frozenExponentialBlockMean (weight' S)
                    (_root_.SubdiffusiveProcess.Model.tauSq M.P) S) 2
                  (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure))) := by
  dsimp only
  let Q' := Ch02.dilateCube (-(r : ℤ)) Q
  let weight' : TriadicCube d → Vec d → ℝ := fun S y =>
    weight (Ch02.dilateCube (r : ℤ) S) (Ch02.dilateVec (r : ℤ) y)
  let F : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g =>
    |∑ R ∈ descendantsAtScale Q ((r : ℤ) - 1),
      ∫ x, weight R x *
          (Real.exp (g x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
        ∂normalizedCubeMeasure R| ^ p
  have hdesc : descendantsAtScale Q' (-1) =
      (descendantsAtScale Q ((r : ℤ) - 1)).image
        (Ch02.dilateCube (-(r : ℤ))) := by
    have h := Ch02.descendantsAtScale_dilateCube
      (-(r : ℤ)) ((r : ℤ) - 1) Q
    have hscale : (r : ℤ) - 1 + -(r : ℤ) = -1 := by omega
    simpa only [Q', hscale] using h
  have hsum (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
      (∑ R ∈ descendantsAtScale Q ((r : ℤ) - 1),
        ∫ x, weight R x *
            (Real.exp
              (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale r g x -
                _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
          ∂normalizedCubeMeasure R) =
        ∑ S ∈ descendantsAtScale Q' (-1),
          frozenExponentialBlockMean (weight' S)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) S g := by
    rw [hdesc, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro R hR
      rw [integral_weight_mul_triadicScale_freshShell_eq_frozenBlock]
      simp only [weight', Ch02.dilateCube_dilateCube_neg]
    · intro R hR S hS heq
      exact Ch02.dilateCube_injective (-(r : ℤ)) heq
  have hFm : Measurable F := by
    have heq : F = fun g =>
        |∑ R ∈ descendantsAtScale Q ((r : ℤ) - 1),
          frozenExponentialBlockMean (weight R)
            (_root_.SubdiffusiveProcess.Model.tauSq M.P) R g| ^ p := by
      funext g
      rfl
    rw [heq]
    exact (Finset.measurable_sum _ fun R _ ↦
      measurable_frozenExponentialBlockMean (weight R) (hweight R).measurable
        (_root_.SubdiffusiveProcess.Model.tauSq M.P) R).norm.pow_const p
  have hlaw :
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, F (omega r) ∂M.P.toMeasure) =
        ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale r g)
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
    calc
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, F (omega r) ∂M.P.toMeasure) =
          ∫ g, F g
            ∂(_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P r).toMeasure := by
        rw [_root_.SubdiffusiveProcess.Model.potentialMarginalLaw,
          ProbabilityMeasure.toMeasure_map]
        exact (integral_map
          (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r).aemeasurable
          hFm.aestronglyMeasurable).symm
      _ = ∫ g, F g ∂Measure.map
            (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale r)
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
        rw [M.shellPrefix.marginal_scaling r, ProbabilityMeasure.toMeasure_map]
      _ = ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale r g)
            ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
        exact integral_map
          (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale r).aemeasurable
          hFm.aestronglyMeasurable
  have hlaw' :
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          |∑ R ∈ descendantsAtScale Q ((r : ℤ) - 1),
            ∫ x, weight R x *
                (Real.exp (omega r x - _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1)
              ∂normalizedCubeMeasure R| ^ p ∂M.P.toMeasure) =
        ∫ g, |∑ S ∈ descendantsAtScale Q' (-1),
            frozenExponentialBlockMean (weight' S)
              (_root_.SubdiffusiveProcess.Model.tauSq M.P) S g| ^ p
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
    change (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, F (omega r) ∂M.P.toMeasure) = _
    rw [hlaw]
    apply integral_congr_ae
    filter_upwards with g
    simp only [F, hsum g]
  rw [hlaw']
  apply integral_abs_sum_frozenExponentialBlockMean_tauSq_rpow_rpow_inv_le_colors
    M Q' (-1) cubeFreshShellColor weight'
  · intro S
    exact (hweight (Ch02.dilateCube (r : ℤ) S)).comp
      (by
        simpa only [Ch02.dilateVec, Pi.smul_apply, id_eq] using!
          (continuous_const.smul continuous_id :
            Continuous ((fun _ : Vec d => Ch02.triadicDilationFactor (r : ℤ)) • id)))
  · exact hp
  · intro c hc S hS T hT hne
    exact potentialRangeSeparated_of_cubeFreshShellColor_eq_of_scale_neg_one
      (scale_eq_of_mem_descendantsAtScale (Finset.mem_filter.mp hS).1)
      (scale_eq_of_mem_descendantsAtScale (Finset.mem_filter.mp hT).1)
      ((Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hT).2.symm) hne

/-! ## Conditioning on disjoint cutoff-index blocks -/

/-- The sigma-field generated by the potential shells in `I`. -/
@[instance_reducible]
def potentialShellIndexSigma {d : ℕ} (I : Set ℕ) : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  ⨆ k ∈ I, MeasurableSpace.comap (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) inferInstance

/-- A selected shell is measurable for its shell-index sigma-field. -/
theorem measurable_potentialCoordinate_shellIndexSigma {d : ℕ}
    {I : Set ℕ} {k : ℕ} (hk : k ∈ I) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (_root_.SubdiffusiveProcess.Model.PotentialField d)
      (potentialShellIndexSigma I) inferInstance (fun omega => omega k) :=
  Measurable.of_comap_le (le_iSup_of_le k <| le_iSup_of_le hk le_rfl)

/-- Every shell-index sigma-field is contained in the canonical sample
sigma-field. -/
theorem potentialShellIndexSigma_le_borel {d : ℕ} (I : Set ℕ) :
    potentialShellIndexSigma (d := d) I ≤
      (inferInstance : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d)) := by
  refine iSup_le fun k => iSup_le fun _ => ?_
  exact (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k).comap_le

/-- Disjoint cutoff-index blocks are independent.  This is the direct GMC
adaptation of `Algsuperdiff/Probability/IndexSigma.lean`. -/
theorem indep_potentialShellIndexSigma_of_disjoint {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {I J : Set ℕ}
    (hIJ : Disjoint I J) :
    Indep (potentialShellIndexSigma (d := d) I) (potentialShellIndexSigma J)
      M.P.toMeasure := by
  exact indep_iSup_of_disjoint
    (fun k => (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k).comap_le)
    M.shellPrefix.independent.iIndep hIJ

/-- Random-variable form of independence for disjoint cutoff-index blocks. -/
theorem indepFun_of_measurable_potentialShellIndexSigma_of_disjoint
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {I J : Set ℕ} (hIJ : Disjoint I J)
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {X : _root_.SubdiffusiveProcess.Model.PotentialSample d → α} {Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → β}
    (hX : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) α (potentialShellIndexSigma I) _ X)
    (hY : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) β (potentialShellIndexSigma J) _ Y) :
    IndepFun X Y M.P.toMeasure :=
  (IndepFun_iff_Indep X Y M.P.toMeasure).mpr
    (indep_of_indep_of_le_right
      (indep_of_indep_of_le_left
        (indep_potentialShellIndexSigma_of_disjoint M hIJ) hX.comap_le)
      hY.comap_le)

/-- The exact shell sum reads only its finite cutoff-index interval. -/
theorem measurable_cutoffShellSum_shellIndexSigma {d : ℕ}
    (m : ℕ) (n : ℤ) (x : Vec d) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (↑(cutoffShellIndices m n) : Set ℕ)) _
      (cutoffShellSum m n x) := by
  unfold cutoffShellSum
  apply Finset.measurable_sum
  intro k hk
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
    (measurable_potentialCoordinate_shellIndexSigma (I :=
      (↑(cutoffShellIndices m n) : Set ℕ)) hk)

/-- The full higher-cutoff ratio field is measurable with respect to exactly
the shells in `(n,m]`. -/
theorem measurable_cutoffRatioMinusOne_shellIndexSigma {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (hn : -1 ≤ n) (hnm : n < (m : ℤ)) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (Vec d → ℝ)
      (potentialShellIndexSigma (↑(cutoffShellIndices m n) : Set ℕ)) _
      (cutoffRatioMinusOne M m n) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    potentialShellIndexSigma (↑(cutoffShellIndices m n) : Set ℕ)
  apply Measurable.of_eval
  intro x
  have hsum := measurable_cutoffShellSum_shellIndexSigma (d := d) m n x
  have hexp : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (↑(cutoffShellIndices m n) : Set ℕ)) _
      (fun omega => Real.exp
        (cutoffShellSum m n x omega -
          (((m : ℤ) - n : ℤ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) :=
    (hsum.sub measurable_const).exp.sub measurable_const
  convert hexp using 1
  funext omega
  exact cutoffRatioMinusOne_eq_exp_shell M m n omega x hn hnm

/-- The paper's conditioning field `a_m a_{k+1}^{-1}-1` is independent of
the fresh shell `g_{k+1}`. -/
theorem indepFun_cutoffRatioMinusOne_freshShell {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m k : ℕ)
    (hkm : k + 1 < m) :
    IndepFun (cutoffRatioMinusOne M m (k + 1 : ℕ))
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega (k + 1)) M.P.toMeasure := by
  let I : Set ℕ := ↑(cutoffShellIndices m (k + 1 : ℕ))
  let J : Set ℕ := {k + 1}
  have hIJ : Disjoint I J := by
    rw [Set.disjoint_left]
    intro r hrI hrJ
    have hr_mem : r ∈ cutoffShellIndices m (k + 1 : ℕ) := hrI
    have hr_bounds := Finset.mem_Icc.mp hr_mem
    have hr_eq : r = k + 1 := Set.mem_singleton_iff.mp hrJ
    omega
  apply indepFun_of_measurable_potentialShellIndexSigma_of_disjoint M hIJ
  · exact measurable_cutoffRatioMinusOne_shellIndexSigma M m (k + 1 : ℕ)
      (by omega) (by exact_mod_cast hkm)
  · exact measurable_potentialCoordinate_shellIndexSigma (I := J) (by simp [J])

/-- Literal source form: the conditioning field `a_m a_{k+1}^{-1}` is
independent of `g_{k+1}`. -/
theorem indepFun_cutoffRatio_freshShell {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m k : ℕ)
    (hkm : k + 1 < m) :
    IndepFun
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => fun x =>
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M (k + 1) omega x)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega (k + 1)) M.P.toMeasure := by
  let addOne : (Vec d → ℝ) → (Vec d → ℝ) := fun f x => f x + 1
  have haddOne : Measurable addOne := by
    apply Measurable.of_eval
    intro x
    exact (measurable_pi_apply x).add measurable_const
  have h := (indepFun_cutoffRatioMinusOne_freshShell M m k hkm).comp
    haddOne measurable_id
  convert h using 1
  · funext omega x
    simp [addOne, cutoffRatioMinusOne, aCutoffAtInt,
      show ¬ (k : ℤ) + 1 < 0 by omega]
  · funext omega
    rfl

/-! ## Conditional-product and marginal-transport wrappers -/

/-- Integrated conditional-expectation wrapper for two independent random
variables.  It identifies an integral with a random frozen parameter and a
fresh variable with the iterated integral against their two marginal laws.
This is the Fubini form of conditioning used in the paper's color-class step;
it avoids choosing a version of `condExp` while retaining the exact identity
tested by every integrable joint observable. -/
theorem integral_indepFun_eq_integral_integral
    {Omega A B : Type*} [MeasurableSpace Omega] [MeasurableSpace A]
    [MeasurableSpace B] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W : Omega → A} {Y : Omega → B} (hW : Measurable W) (hY : Measurable Y)
    (hWY : IndepFun W Y mu) (H : A → B → ℝ)
    (hH : AEStronglyMeasurable (Function.uncurry H) ((mu.map W).prod (mu.map Y)))
    (hHint : Integrable (Function.uncurry H) ((mu.map W).prod (mu.map Y))) :
    ∫ omega, H (W omega) (Y omega) ∂mu =
      ∫ w, (∫ y, H w y ∂mu.map Y) ∂mu.map W := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map
    hW.aemeasurable hY.aemeasurable).mp hWY
  have hHpair : AEStronglyMeasurable (Function.uncurry H)
      (mu.map fun omega => (W omega, Y omega)) := by
    rw [hmap]
    exact hH
  calc
    ∫ omega, H (W omega) (Y omega) ∂mu =
        ∫ q, Function.uncurry H q ∂mu.map (fun omega => (W omega, Y omega)) := by
      rw [MeasureTheory.integral_map (hW.prodMk hY).aemeasurable hHpair]
      rfl
    _ = ∫ q, Function.uncurry H q ∂((mu.map W).prod (mu.map Y)) := by rw [hmap]
    _ = ∫ w, (∫ y, H w y ∂mu.map Y) ∂mu.map W :=
      MeasureTheory.integral_prod (Function.uncurry H) hHint

/-- Source-specialized conditioning identity for the frozen higher-cutoff
ratio and the fresh shell `g_(k+1)`.  This combines the shell-index
independence theorem with the integrated conditional-product wrapper. -/
theorem integral_cutoffRatio_freshShell_eq_integral_integral {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m k : ℕ) (hkm : k + 1 < m)
    (H : (Vec d → ℝ) → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ)
    (hH : AEStronglyMeasurable (Function.uncurry H)
      ((M.P.toMeasure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => fun x =>
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M (k + 1) omega x)).prod
        (M.P.toMeasure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega (k + 1)))))
    (hHint : Integrable (Function.uncurry H)
      ((M.P.toMeasure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => fun x =>
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M (k + 1) omega x)).prod
        (M.P.toMeasure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega (k + 1))))) :
    (∫ omega, H
        (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M (k + 1) omega x)
        (omega (k + 1)) ∂M.P.toMeasure) =
      ∫ weight,
        (∫ g, H weight g
          ∂M.P.toMeasure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega (k + 1)))
        ∂M.P.toMeasure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => fun x =>
          _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
            _root_.SubdiffusiveProcess.Model.aCutoff M (k + 1) omega x) := by
  let W : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → ℝ := fun omega x =>
    _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
      _root_.SubdiffusiveProcess.Model.aCutoff M (k + 1) omega x
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → _root_.SubdiffusiveProcess.Model.PotentialField d := fun omega => omega (k + 1)
  have hW : Measurable W := by
    apply Measurable.of_eval
    intro x
    have hcentered := (measurable_cutoffRatioMinusOne_uncurry M m (k + 1 : ℕ)).comp
      (measurable_id.prodMk (measurable_const : Measurable fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => x))
    have hadd : Measurable (fun omega => cutoffRatioMinusOne M m (k + 1 : ℕ) omega x + 1) :=
      hcentered.add measurable_const
    convert hadd using 1
    funext omega
    simp [W, cutoffRatioMinusOne, aCutoffAtInt,
      show ¬ (k : ℤ) + 1 < 0 by omega]
  have hY : Measurable Y := _root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate (k + 1)
  exact integral_indepFun_eq_integral_integral M.P.toMeasure hW hY
    (indepFun_cutoffRatio_freshShell M m k hkm) H hH hHint

/-! ## Continuous-weight conditioning

The preceding wrapper deliberately retains the manuscript's literal full
function-space carrier.  Its pointwise measurable structure does not make
variable evaluation jointly measurable.  Actual cutoff ratios are continuous,
so the following carrier records their true support; Carathéodory
joint-measurability is then available to block-integral consumers. -/

/-- Continuous spatial weights, with the measurable subtype structure induced
by point evaluations. -/
abbrev ContinuousWeight (d : ℕ) :=
  {f : Vec d → ℝ // Continuous f}

/-- The literal higher-cutoff ratio as a continuously valued random weight. -/
noncomputable def cutoffRatioContinuousWeight
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m r : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ContinuousWeight d :=
  ⟨fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
      _root_.SubdiffusiveProcess.Model.aCutoff M r omega x,
    (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M m omega).div
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M r omega)
      (fun x ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M r omega x).ne')⟩

/-- The continuous cutoff-ratio realization is measurable with respect to
exactly the higher-shell index block on which it depends. -/
theorem measurable_cutoffRatioContinuousWeight_shellIndexSigma
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m r : ℕ)
    (hrm : r < m) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (ContinuousWeight d)
      (potentialShellIndexSigma (↑(cutoffShellIndices m r) : Set ℕ)) _
      (cutoffRatioContinuousWeight M m r) := by
  apply Measurable.subtype_mk
  let addOne : (Vec d → ℝ) → (Vec d → ℝ) := fun f x ↦ f x + 1
  have haddOne : Measurable addOne := by
    apply Measurable.of_eval
    intro x
    exact (measurable_pi_apply x).add measurable_const
  have hcenter := measurable_cutoffRatioMinusOne_shellIndexSigma
    M m r (by omega) (by exact_mod_cast hrm)
  have h := haddOne.comp hcenter
  convert h using 1
  funext omega x
  simp [addOne, cutoffRatioMinusOne, aCutoffAtInt,
    show ¬ (r : ℤ) < 0 by omega]

/-- The continuously realized ratio is independent of its fresh shell. -/
theorem indepFun_cutoffRatioContinuousWeight_freshShell_at
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m r : ℕ)
    (hrm : r < m) :
    IndepFun (cutoffRatioContinuousWeight M m r)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r) M.P.toMeasure := by
  let I : Set ℕ := ↑(cutoffShellIndices m r)
  let J : Set ℕ := {r}
  have hIJ : Disjoint I J := by
    rw [Set.disjoint_left]
    intro k hkI hkJ
    have hk_mem : k ∈ cutoffShellIndices m r := hkI
    have hk_bounds := Finset.mem_Icc.mp hk_mem
    have hk_eq : k = r := Set.mem_singleton_iff.mp hkJ
    omega
  apply indepFun_of_measurable_potentialShellIndexSigma_of_disjoint M hIJ
  · exact measurable_cutoffRatioContinuousWeight_shellIndexSigma M m r hrm
  · exact measurable_potentialCoordinate_shellIndexSigma (I := J) (by simp [J])

/-- Conditioning identity on the actual continuous-weight carrier.  This is
the full-carrier wrapper above with only its defective outer carrier repaired;
the old source-facing statement is left unchanged. -/
theorem integral_cutoffRatioContinuousWeight_freshShell_eq_integral_integral
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m r : ℕ) (hrm : r < m)
    (H : ContinuousWeight d → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ)
    (hH : AEStronglyMeasurable (Function.uncurry H)
      ((M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)).prod
        (M.P.toMeasure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r))))
    (hHint : Integrable (Function.uncurry H)
      ((M.P.toMeasure.map (cutoffRatioContinuousWeight M m r)).prod
        (M.P.toMeasure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r)))) :
    (∫ omega, H (cutoffRatioContinuousWeight M m r omega) (omega r)
        ∂M.P.toMeasure) =
      ∫ weight,
        (∫ g, H weight g
          ∂M.P.toMeasure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r))
        ∂M.P.toMeasure.map (cutoffRatioContinuousWeight M m r) := by
  have hW : Measurable (cutoffRatioContinuousWeight M m r) :=
    (measurable_cutoffRatioContinuousWeight_shellIndexSigma M m r hrm).mono
      (potentialShellIndexSigma_le_borel
        (↑(cutoffShellIndices m r) : Set ℕ)) le_rfl
  have hY : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ omega r) :=
    _root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate r
  exact integral_indepFun_eq_integral_integral M.P.toMeasure hW hY
    (indepFun_cutoffRatioContinuousWeight_freshShell_at M m r hrm) H hH hHint

/-- Transport an integrable shell observable from coordinate `k` of the GMC
sample to the zero-shell law through the exact marginal scaling axiom. -/
theorem integral_potentialCoordinate_eq_integral_triadicScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ)
    (F : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ) (hF : Measurable F) :
    ∫ omega, F (omega k) ∂M.P.toMeasure =
      ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  calc
    ∫ omega, F (omega k) ∂M.P.toMeasure =
        ∫ g, F g ∂(_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure := by
      rw [_root_.SubdiffusiveProcess.Model.potentialMarginalLaw,
        ProbabilityMeasure.toMeasure_map]
      exact (MeasureTheory.integral_map
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k).aemeasurable
        hF.aestronglyMeasurable).symm
    _ = ∫ g, F g ∂Measure.map
          (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      rw [M.shellPrefix.marginal_scaling k, ProbabilityMeasure.toMeasure_map]
    _ = ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g)
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      rw [MeasureTheory.integral_map
        (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k).aemeasurable
        hF.aestronglyMeasurable]

end

end SubdiffusiveProcess.CoarseGrainingVocab
