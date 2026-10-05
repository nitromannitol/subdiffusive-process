module

public import SubdiffusiveProcess.CoarseGrainingVocab.RestrictedCoefficientSigma
public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GammaTwoEnvelope

@[expose] public section

/-!
# Local coefficient-ratio tails for the bounded-multiplier argument

This file isolates the probability-only part of the unit-scale Moser step in
`p.cutoff.Holder.bounded.multiplier`.  The analytic Moser estimate is not used.
For every translate of the unit cube, the oscillation of the *fixed cutoff*
shell sum is dominated by a cutoff-uniform `Gamma_2` envelope.  A raw union
bound over the unit cubes covering a translated scale-`m` cube then gives the
printed `exp (-1 / (delta^2 |log delta|^2))` exceptional probability.

The resulting event is expressed solely through coefficient ratios on the
intersections of the covering cubes with the ambient cube.  It is therefore
measurable in the frozen restricted coefficient sigma-field.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open Homogenization IndependentSums
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := PotentialSample d

/-- A cutoff-uniform majorant for the oscillation of the prefix
`sum_{k=0}^L omega_k` on the translated unit cube centered at `z`. -/
def fixedCutoffOscillationEnvelope {d : ℕ} (L : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  2 * ∑ k ∈ Finset.range (L + 1),
    translatedSmallShellEnvelope k (0 : ℤ) z omega

theorem fixedCutoffOscillationEnvelope_nonneg {d : ℕ} (L : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : 0 ≤ fixedCutoffOscillationEnvelope L z omega := by
  unfold fixedCutoffOscillationEnvelope
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ =>
    translatedSmallShellEnvelope_nonneg k (0 : ℤ) z omega)

theorem measurable_fixedCutoffOscillationEnvelope {d : ℕ} (L : ℕ)
    (z : Vec d) : Measurable (fixedCutoffOscillationEnvelope L z) := by
  unfold fixedCutoffOscillationEnvelope
  exact (Finset.measurable_sum _ fun k _ =>
    measurable_translatedSmallShellEnvelope k (0 : ℤ) z).const_mul 2

/-- The fixed prefix oscillation between any two points of a translated unit
cube is controlled by `fixedCutoffOscillationEnvelope`. -/
theorem cutoffShellSum_pair_sub_le_fixedCutoffOscillationEnvelope {d : ℕ}
    (L : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x y : Vec d}
    (hx : x ∈ translatedCube d 0 z) (hy : y ∈ translatedCube d 0 z) :
    (∑ k ∈ Finset.range (L + 1), omega k x) -
        (∑ k ∈ Finset.range (L + 1), omega k y) ≤
      fixedCutoffOscillationEnvelope L z omega := by
  have hx' : x - z ∈ openCubeSet (originCube d 0) := by
    rcases hx with ⟨u, hu, rfl⟩
    simpa [cube] using hu
  have hy' : y - z ∈ openCubeSet (originCube d 0) := by
    rcases hy with ⟨u, hu, rfl⟩
    simpa [cube] using hu
  have hpoint (w : Vec d) (hw : w - z ∈ openCubeSet (originCube d 0)) :
      |(∑ k ∈ Finset.range (L + 1), omega k w) -
          (∑ k ∈ Finset.range (L + 1), omega k z)| ≤
        ∑ k ∈ Finset.range (L + 1),
          translatedSmallShellEnvelope k (0 : ℤ) z omega := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k ∈ Finset.range (L + 1), (omega k w - omega k z)| ≤
          ∑ k ∈ Finset.range (L + 1), |omega k w - omega k z| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun k hk =>
        abs_shell_sub_le_translatedSmallShellEnvelope k (0 : ℤ)
          (by omega) z omega hw
  have hxBound := hpoint x hx'
  have hyBound := hpoint y hy'
  unfold fixedCutoffOscillationEnvelope
  calc
    (∑ k ∈ Finset.range (L + 1), omega k x) -
        (∑ k ∈ Finset.range (L + 1), omega k y) ≤
      |(∑ k ∈ Finset.range (L + 1), omega k x) -
          (∑ k ∈ Finset.range (L + 1), omega k z)| +
        |(∑ k ∈ Finset.range (L + 1), omega k y) -
          (∑ k ∈ Finset.range (L + 1), omega k z)| := by
      have htri := abs_sub_le
        (∑ k ∈ Finset.range (L + 1), omega k x)
        (∑ k ∈ Finset.range (L + 1), omega k z)
        (∑ k ∈ Finset.range (L + 1), omega k y)
      have htri' : |(∑ k ∈ Finset.range (L + 1), omega k x) -
          (∑ k ∈ Finset.range (L + 1), omega k y)| ≤
          |(∑ k ∈ Finset.range (L + 1), omega k x) -
            (∑ k ∈ Finset.range (L + 1), omega k z)| +
          |(∑ k ∈ Finset.range (L + 1), omega k y) -
            (∑ k ∈ Finset.range (L + 1), omega k z)| := by
        simpa only [abs_sub_comm
          (∑ k ∈ Finset.range (L + 1), omega k z)] using htri
      exact (le_abs_self _).trans htri'
    _ ≤ 2 * ∑ k ∈ Finset.range (L + 1),
        translatedSmallShellEnvelope k (0 : ℤ) z omega := by linarith

/-- Dimension-free scale constant for the translated fixed-prefix
oscillation. -/
def fixedCutoffOscillationConst : ℝ :=
  3 * gammaTriangleConst 2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹

theorem fixedCutoffOscillationConst_pos :
    0 < fixedCutoffOscillationConst := by
  unfold fixedCutoffOscillationConst
  exact mul_pos (mul_pos (by norm_num) gammaTriangleConst_pos)
    (Real.rpow_pos_of_pos (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _)

private theorem sum_range_geom_third_le (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 / 3 : ℝ) ^ k ≤ 3 / 2 := by
  rw [geom_sum_eq (by norm_num : (1 / 3 : ℝ) ≠ 1)]
  have hp : 0 ≤ (1 / 3 : ℝ) ^ N := by positivity
  calc
    ((1 / 3 : ℝ) ^ N - 1) / (1 / 3 - 1) =
        3 / 2 * (1 - (1 / 3 : ℝ) ^ N) := by ring
    _ ≤ 3 / 2 := by nlinarith

private theorem fixedCutoffOscillationScale_le {d : ℕ}
    (M : GMCModel d) (L : ℕ) :
    2 * (gammaTriangleConst 2 *
        ∑ k ∈ Finset.Icc 0 L, translatedSmallShellScale M k (0 : ℤ)) ≤
      fixedCutoffOscillationConst * M.delta := by
  have hterm (k : ℕ) : translatedSmallShellScale M k (0 : ℤ) =
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) * (1 / 3 : ℝ) ^ k := by
    unfold translatedSmallShellScale
    rw [show (0 : ℤ) - (k : ℤ) = -(k : ℤ) by omega,
      zpow_neg, zpow_natCast]
    simp only [one_div, inv_pow]
    ring
  have hgeom := sum_range_geom_third_le (L + 1)
  have hsets : Finset.Icc 0 L = Finset.range (L + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
    omega
  rw [hsets]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  unfold fixedCutoffOscillationConst
  have hbase : 0 ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta := by
    exact mul_nonneg (Real.rpow_nonneg (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _) M.shellPrefix.delta_pos.le
  have hgamma : 0 ≤ gammaTriangleConst 2 := gammaTriangleConst_pos.le
  nlinarith [mul_le_mul_of_nonneg_left hgeom hbase]

/-- The fixed-cutoff oscillation envelope has a `Gamma_2` scale bounded by a
constant times `delta`, uniformly in the cutoff and translate. -/
theorem isBigOWith_gammaTwo_fixedCutoffOscillationEnvelope {d : ℕ}
    (M : GMCModel d) (L : ℕ) (z : Vec d) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fixedCutoffOscillationEnvelope L z)
      (fixedCutoffOscillationConst * M.delta) := by
  have hbase := isBigOWith_gammaTwo_smallCubeShellSum M 0 L (0 : ℤ) z
    (Nat.zero_le L)
  have hmul := hbase.const_mul (by norm_num : (0 : ℝ) ≤ 2)
  have hform : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      2 * ∑ j ∈ Finset.Icc 0 L,
        translatedSmallShellEnvelope j (0 : ℤ) z omega) =
      fixedCutoffOscillationEnvelope L z := by
    funext omega
    unfold fixedCutoffOscillationEnvelope
    congr 2
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
    omega
  rw [hform] at hmul
  exact hmul.mono_scale (fixedCutoffOscillationScale_le M L)

/-- The local coefficient-ratio event on a translated unit cube. -/
def localCoefficientRatioGood {d : ℕ} (M : GMCModel d) (L : ℕ)
    (z : Vec d) (t : ℝ) : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  CoefficientRatioGood (aCutoff M L) (translatedCube d 0 z) (Real.exp t)

/-- The oscillation envelope implies the local coefficient-ratio event. -/
theorem mem_localCoefficientRatioGood_of_envelope_le {d : ℕ}
    (M : GMCModel d) (L : ℕ) (z : Vec d) {t : ℝ} {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (h : fixedCutoffOscillationEnvelope L z omega ≤ t) :
    omega ∈ localCoefficientRatioGood M L z t := by
  apply coefficientRatioGood_aCutoff_of_shellSum_oscillation M L omega
  intro x hx y hy
  exact (cutoffShellSum_pair_sub_le_fixedCutoffOscillationEnvelope
    L z omega hx hy).trans h

/-- One translated unit cube has the Gaussian tail furnished by `(g2)`, with
no independence input and uniformly in the fixed cutoff. -/
theorem measureReal_compl_localCoefficientRatioGood_le_exp {d : ℕ}
    (M : GMCModel d) (L : ℕ) (z : Vec d) {s : ℝ} (hs : 1 ≤ s) :
    M.P.toMeasure.real (localCoefficientRatioGood M L z
      (fixedCutoffOscillationConst * M.delta * s))ᶜ ≤
        Real.exp (-(s ^ (2 : ℝ))) := by
  have htail := (isBigOWith_gammaSigma_iff.mp
    (isBigOWith_gammaTwo_fixedCutoffOscillationEnvelope M L z)) hs
  let E := upperTailEvent (fixedCutoffOscillationEnvelope L z)
    (fixedCutoffOscillationConst * M.delta * s)
  refine (measureReal_mono (s₂ := E) ?_
    (measure_ne_top M.P.toMeasure E)).trans ?_
  · intro omega hbad
    change fixedCutoffOscillationConst * M.delta * s <
      fixedCutoffOscillationEnvelope L z omega
    by_contra hnot
    exact hbad (mem_localCoefficientRatioGood_of_envelope_le M L z
      (le_of_not_gt hnot))
  · simpa [E, absTailEvent, abs_of_nonneg
      (fixedCutoffOscillationEnvelope_nonneg L z _)] using htail

/-! ## The translated finite cover -/

/-- A unit covering cell, clipped to the ambient translated cube so that its
coefficient-ratio event sees only evaluations from the frozen window. -/
def boundedMultiplierCoverCell (d : ℕ) (m : ℤ) (z : Vec d)
    (p : Fin d → ℤ) : Set (Vec d) :=
  translatedCube d m z ∩
    translatedCube d 0 (z + physicalShellCoverCenter 0 p)

/-- Gaussian parameter used in the raw union bound.  Its first term pays for
the number of covering cells, while the second produces the printed
log-squared exceptional probability. -/
def boundedMultiplierCoverTailParameter {d : ℕ} (M : GMCModel d) (m : ℤ) : ℝ :=
  Real.sqrt (Real.log ((shellCoverShifts d m).card : ℝ)) +
    (M.delta * |Real.log M.delta|)⁻¹

/-- Logarithm of the allowed coefficient ratio on every clipped covering
cell. -/
def boundedMultiplierCoverOscillationThreshold {d : ℕ}
    (M : GMCModel d) (m : ℤ) : ℝ :=
  fixedCutoffOscillationConst * M.delta *
    boundedMultiplierCoverTailParameter M m

/-- The underlying `g2` envelope event on every unit covering cell.  Unlike
the coefficient-ratio image of this event, it retains the derivative data and
can therefore feed the maximal-derivative route. -/
def coveringFixedCutoffEnvelopeGood {d : ℕ} (M : GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d) : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  ⋂ p ∈ shellCoverShifts d m,
    {omega | fixedCutoffOscillationEnvelope L
      (z + physicalShellCoverCenter 0 p) omega ≤
        boundedMultiplierCoverOscillationThreshold M m}

@[simp] theorem mem_coveringFixedCutoffEnvelopeGood_iff {d : ℕ}
    {M : GMCModel d} {L : ℕ} {m : ℤ} {z : Vec d} {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d} :
    omega ∈ coveringFixedCutoffEnvelopeGood M L m z ↔
      ∀ p ∈ shellCoverShifts d m,
        fixedCutoffOscillationEnvelope L
          (z + physicalShellCoverCenter 0 p) omega ≤
            boundedMultiplierCoverOscillationThreshold M m := by
  simp [coveringFixedCutoffEnvelopeGood]

theorem measurableSet_coveringFixedCutoffEnvelopeGood {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    MeasurableSet (coveringFixedCutoffEnvelopeGood M L m z) := by
  unfold coveringFixedCutoffEnvelopeGood
  refine MeasurableSet.biInter (shellCoverShifts d m).countable_toSet
    fun p _hp => ?_
  exact measurableSet_le (measurable_fixedCutoffOscillationEnvelope L
    (z + physicalShellCoverCenter 0 p)) measurable_const

/-- The restricted-coefficient good event used by the unit-scale covering
argument. -/
def coveringCoefficientRatioGood {d : ℕ} (M : GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d) : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  ⋂ p ∈ shellCoverShifts d m,
    CoefficientRatioGood (aCutoff M L)
      (boundedMultiplierCoverCell d m z p)
      (Real.exp (boundedMultiplierCoverOscillationThreshold M m))

@[simp] theorem mem_coveringCoefficientRatioGood_iff {d : ℕ}
    {M : GMCModel d} {L : ℕ} {m : ℤ} {z : Vec d} {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d} :
    omega ∈ coveringCoefficientRatioGood M L m z ↔
      ∀ p ∈ shellCoverShifts d m,
        omega ∈ CoefficientRatioGood (aCutoff M L)
          (boundedMultiplierCoverCell d m z p)
          (Real.exp (boundedMultiplierCoverOscillationThreshold M m)) := by
  simp [coveringCoefficientRatioGood]

/-- The common envelope event simultaneously supplies the previously proved
restricted-coefficient ratio event. -/
theorem mem_coveringCoefficientRatioGood_of_envelopeGood {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hgood : omega ∈ coveringFixedCutoffEnvelopeGood M L m z) :
    omega ∈ coveringCoefficientRatioGood M L m z := by
  rw [mem_coveringCoefficientRatioGood_iff]
  intro p hp
  have henv := mem_coveringFixedCutoffEnvelopeGood_iff.1 hgood p hp
  have hlocal := mem_localCoefficientRatioGood_of_envelope_le M L
    (z + physicalShellCoverCenter 0 p) henv
  intro x hx y hy
  exact hlocal x hx.2 y hy.2

private theorem isOpen_translatedCube (d : ℕ) (m : ℤ) (z : Vec d) :
    IsOpen (translatedCube d m z) := by
  have hset : translatedCube d m z =
      (fun x : Vec d => x - z) ⁻¹' openCubeSet (originCube d m) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change u ∈ openCubeSet (originCube d m) at hu
      simpa using hu
    · intro hx
      refine ⟨x - z, ?_, ?_⟩
      · simpa [cube] using hx
      · ext i
        simp
  rw [hset]
  exact (isOpen_openCubeSet (originCube d m)).preimage
    (continuous_id.sub continuous_const)

/-- The cover good event is measurable in exactly the coefficient sigma-field
restricted to the ambient translated cube. -/
theorem measurableSet_coveringCoefficientRatioGood {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    MeasurableSet[restrictedCoefficientSigma (aCutoff M L)
      (translatedCube d m z)] (coveringCoefficientRatioGood M L m z) := by
  unfold coveringCoefficientRatioGood
  refine MeasurableSet.biInter (shellCoverShifts d m).countable_toSet
    fun p hp => ?_
  have hcellOpen : IsOpen (boundedMultiplierCoverCell d m z p) :=
    (isOpen_translatedCube d m z).inter
      (isOpen_translatedCube d 0 (z + physicalShellCoverCenter 0 p))
  have hlocal := measurableSet_coefficientRatioGood_aCutoff M L hcellOpen
    (Real.exp (boundedMultiplierCoverOscillationThreshold M m))
  exact restrictedCoefficientSigma_mono (aCutoff M L)
    (Set.inter_subset_left : boundedMultiplierCoverCell d m z p ⊆
      translatedCube d m z) _ hlocal

theorem measurableSet_compl_coveringCoefficientRatioGood {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    MeasurableSet[restrictedCoefficientSigma (aCutoff M L)
      (translatedCube d m z)] (coveringCoefficientRatioGood M L m z)ᶜ :=
  (measurableSet_coveringCoefficientRatioGood M L m z).compl

/-- Every point of the ambient translated cube belongs to one of the clipped
unit covering cells. -/
theorem exists_mem_boundedMultiplierCoverCell {d : ℕ} (m : ℤ) (z : Vec d)
    {x : Vec d} (hx : x ∈ translatedCube d m z) :
    ∃ p ∈ shellCoverShifts d m, x ∈ boundedMultiplierCoverCell d m z p := by
  rcases hx with ⟨u, hu, rfl⟩
  obtain ⟨p, hp, hup⟩ := exists_physicalShellCoverCenter_mem 0 m (by
    simpa [cube] using hu)
  refine ⟨p, by simpa using hp, ⟨⟨u, hu, rfl⟩, ?_⟩⟩
  refine ⟨u - physicalShellCoverCenter 0 p, ?_, ?_⟩
  · simpa [cube] using hup
  · ext i
    simp [physicalShellCoverCenter]

private theorem delta_mul_abs_log_le_one {d : ℕ} (M : GMCModel d) :
    M.delta * |Real.log M.delta| ≤ 1 := by
  have h := Real.abs_log_mul_self_lt M.delta M.shellPrefix.delta_pos
    (M.shellPrefix.delta_le_half.trans (by norm_num))
  have heq : M.delta * |Real.log M.delta| =
      |Real.log M.delta * M.delta| := by
    rw [abs_mul, abs_of_pos M.shellPrefix.delta_pos]
    ring
  rw [heq]
  exact h.le

private theorem one_le_boundedMultiplierCoverTailParameter {d : ℕ}
    (M : GMCModel d) (m : ℤ) :
    1 ≤ boundedMultiplierCoverTailParameter M m := by
  have hlog : Real.log M.delta < 0 := Real.log_neg M.shellPrefix.delta_pos
    (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hprod : 0 < M.delta * |Real.log M.delta| :=
    mul_pos M.shellPrefix.delta_pos (abs_pos.2 hlog.ne)
  have hinv : 1 ≤ (M.delta * |Real.log M.delta|)⁻¹ := by
    exact (one_le_inv₀ hprod).2 (delta_mul_abs_log_le_one M)
  exact hinv.trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))

private theorem full_local_good_implies_clipped_good {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (p : Fin d → ℤ)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d} {t : ℝ}
    (hgood : omega ∈ localCoefficientRatioGood M L
      (z + physicalShellCoverCenter 0 p) t) :
    omega ∈ CoefficientRatioGood (aCutoff M L)
      (boundedMultiplierCoverCell d m z p) (Real.exp t) := by
  intro x hx y hy
  exact hgood x hx.2 y hy.2

private theorem cover_union_tail_arithmetic {d : ℕ} (M : GMCModel d)
    (m : ℤ) :
    ((shellCoverShifts d m).card : ℝ) *
        Real.exp (-(boundedMultiplierCoverTailParameter M m ^ (2 : ℝ))) ≤
      Real.exp (-(M.delta * |Real.log M.delta|)⁻¹ ^ (2 : ℝ)) := by
  simp only [Real.rpow_two]
  let N : ℝ := ((shellCoverShifts d m).card : ℝ)
  let u : ℝ := (M.delta * |Real.log M.delta|)⁻¹
  have hNtwo : 2 ≤ (shellCoverShifts d m).card :=
    shellCoverShifts_card_ge_two M m
  have hNpos : 0 < N := by
    dsimp only [N]
    positivity
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by
    dsimp only [N]
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hNtwo))
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    exact inv_nonneg.mpr
      (mul_nonneg M.shellPrefix.delta_pos.le (abs_nonneg _))
  have hsqrtSq : Real.sqrt (Real.log N) ^ 2 = Real.log N :=
    Real.sq_sqrt hlogN
  have hexp : N = Real.exp (Real.log N) := (Real.exp_log hNpos).symm
  change N * Real.exp (-(Real.sqrt (Real.log N) + u) ^ 2) ≤
    Real.exp (-(u ^ 2))
  rw [hexp, ← Real.exp_add]
  rw [Real.log_exp]
  apply Real.exp_le_exp.2
  have hcross : 0 ≤ Real.sqrt (Real.log N) * u :=
    mul_nonneg (Real.sqrt_nonneg _) hu0
  calc
    Real.log N + -(Real.sqrt (Real.log N) + u) ^ 2 ≤
        Real.log N - (Real.sqrt (Real.log N) ^ 2 + u ^ 2) := by
      nlinarith
    _ = -(u ^ 2) := by rw [hsqrtSq]; ring

/-- The unshifted Gaussian union bound for the common envelope event.  This
is the route-independent maximal-derivative probability input; in particular
there is no additive constant from replacing `q` by `(q-1)_+`. -/
theorem measure_compl_coveringFixedCutoffEnvelopeGood_le {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    M.P.toMeasure (coveringFixedCutoffEnvelopeGood M L m z)ᶜ ≤
      ENNReal.ofReal
        (Real.exp (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) := by
  let S := shellCoverShifts d m
  let s := boundedMultiplierCoverTailParameter M m
  let A := fixedCutoffOscillationConst * M.delta
  let E : (Fin d → ℤ) → Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) := fun p =>
    upperTailEvent (fixedCutoffOscillationEnvelope L
      (z + physicalShellCoverCenter 0 p)) (A * s)
  have hsubset : (coveringFixedCutoffEnvelopeGood M L m z)ᶜ ⊆
      ⋃ p ∈ S, E p := by
    intro omega hbad
    have hnot : ¬ ∀ p ∈ S,
        fixedCutoffOscillationEnvelope L
          (z + physicalShellCoverCenter 0 p) omega ≤ A * s := by
      intro hall
      apply hbad
      exact mem_coveringFixedCutoffEnvelopeGood_iff.2 (by
        simpa [A, s, boundedMultiplierCoverOscillationThreshold] using hall)
    push Not at hnot
    obtain ⟨p, hpS, hpbad⟩ := hnot
    exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hpS, hpbad⟩⟩
  have hreal : M.P.toMeasure.real
      (coveringFixedCutoffEnvelopeGood M L m z)ᶜ ≤
      Real.exp (-(M.delta * |Real.log M.delta|)⁻¹ ^ (2 : ℝ)) := by
    calc
      M.P.toMeasure.real (coveringFixedCutoffEnvelopeGood M L m z)ᶜ ≤
          M.P.toMeasure.real (⋃ p ∈ S, E p) :=
        measureReal_mono hsubset (measure_ne_top M.P.toMeasure _)
      _ ≤ (S.card : ℝ) * Real.exp (-(s ^ (2 : ℝ))) := by
        exact Section6Anchored.measureReal_biUnion_upperTailEvent_le S
          (one_le_boundedMultiplierCoverTailParameter M m)
          (fun p _hp => by
            simpa [A, s] using
              isBigOWith_gammaTwo_fixedCutoffOscillationEnvelope M L
                (z + physicalShellCoverCenter 0 p))
      _ ≤ Real.exp (-(M.delta * |Real.log M.delta|)⁻¹ ^ (2 : ℝ)) := by
        simpa [S, s] using cover_union_tail_arithmetic M m
  apply (ENNReal.le_ofReal_iff_toReal_le
    (measure_ne_top M.P.toMeasure _)
    (Real.exp_pos _).le).2
  have hden : M.delta ^ 2 * |Real.log M.delta| ^ 2 =
      (M.delta * |Real.log M.delta|) ^ 2 := by ring
  rw [hden]
  have hrate : -(M.delta * |Real.log M.delta|)⁻¹ ^ (2 : ℝ) =
      -1 / (M.delta * |Real.log M.delta|) ^ 2 := by
    rw [Real.rpow_two, div_eq_mul_inv, inv_pow]
    ring
  rw [hrate] at hreal
  exact hreal

/-- **Printed probability bound for the restricted-coefficient event.**

This is the Moser-independent probability half: `(g2)` controls each
translated fixed-cutoff oscillation envelope and a raw finite union bound pays
for all cells.  No shell independence and no PDE regularity theorem is used. -/
theorem measure_compl_coveringCoefficientRatioGood_le {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    M.P.toMeasure (coveringCoefficientRatioGood M L m z)ᶜ ≤
      ENNReal.ofReal
        (Real.exp (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) := by
  let S := shellCoverShifts d m
  let s := boundedMultiplierCoverTailParameter M m
  let A := fixedCutoffOscillationConst * M.delta
  let E : (Fin d → ℤ) → Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) := fun p =>
    upperTailEvent (fixedCutoffOscillationEnvelope L
      (z + physicalShellCoverCenter 0 p)) (A * s)
  have hsubset : (coveringCoefficientRatioGood M L m z)ᶜ ⊆
      ⋃ p ∈ S, E p := by
    intro omega hbad
    have hnot : ¬ ∀ p ∈ S,
        omega ∈ CoefficientRatioGood (aCutoff M L)
          (boundedMultiplierCoverCell d m z p)
          (Real.exp (boundedMultiplierCoverOscillationThreshold M m)) := by
      intro hall
      apply hbad
      exact mem_coveringCoefficientRatioGood_iff.2 hall
    push Not at hnot
    obtain ⟨p, hpS, hpbad⟩ := hnot
    refine Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hpS, ?_⟩⟩
    change A * s < fixedCutoffOscillationEnvelope L
      (z + physicalShellCoverCenter 0 p) omega
    by_contra henvelope
    apply hpbad
    apply full_local_good_implies_clipped_good M L m z p
    apply mem_localCoefficientRatioGood_of_envelope_le M L _
    simpa [A, s, boundedMultiplierCoverOscillationThreshold] using
      (le_of_not_gt henvelope)
  have hreal : M.P.toMeasure.real
      (coveringCoefficientRatioGood M L m z)ᶜ ≤
      Real.exp (-(M.delta * |Real.log M.delta|)⁻¹ ^ (2 : ℝ)) := by
    calc
      M.P.toMeasure.real (coveringCoefficientRatioGood M L m z)ᶜ ≤
          M.P.toMeasure.real (⋃ p ∈ S, E p) :=
        measureReal_mono hsubset (measure_ne_top M.P.toMeasure _)
      _ ≤ ∑ p ∈ S, M.P.toMeasure.real (E p) :=
        measureReal_biUnion_finset_le S E
      _ ≤ ∑ _p ∈ S, Real.exp (-(s ^ (2 : ℝ))) := by
        apply Finset.sum_le_sum
        intro p hp
        have htail := isBigOWith_gammaSigma_iff.mp
          (isBigOWith_gammaTwo_fixedCutoffOscillationEnvelope M L
            (z + physicalShellCoverCenter 0 p))
          (one_le_boundedMultiplierCoverTailParameter M m)
        simpa [E, A, s, absTailEvent, abs_of_nonneg
          (fixedCutoffOscillationEnvelope_nonneg L
            (z + physicalShellCoverCenter 0 p) _)] using htail
      _ = (S.card : ℝ) * Real.exp (-(s ^ (2 : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.exp (-(M.delta * |Real.log M.delta|)⁻¹ ^ (2 : ℝ)) := by
        simpa [S, s] using cover_union_tail_arithmetic M m
  apply (ENNReal.le_ofReal_iff_toReal_le
    (measure_ne_top M.P.toMeasure _)
    (Real.exp_pos _).le).2
  have hden : M.delta ^ 2 * |Real.log M.delta| ^ 2 =
      (M.delta * |Real.log M.delta|) ^ 2 := by ring
  rw [hden]
  have hrate : -(M.delta * |Real.log M.delta|)⁻¹ ^ (2 : ℝ) =
      -1 / (M.delta * |Real.log M.delta|) ^ 2 := by
    rw [Real.rpow_two, div_eq_mul_inv, inv_pow]
    ring
  rw [hrate] at hreal
  exact hreal

/-- Existential packaging in the exact sigma-field/probability shape consumed
by the bounded-multiplier anchor.  Off `bad`, every clipped unit covering cell
has the coefficient ratio recorded by `coveringCoefficientRatioGood`. -/
theorem exists_restrictedBad_coveringCoefficientRatio {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    ∃ bad : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d),
      @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialSample d)
        (restrictedCoefficientSigma (aCutoff M L) (translatedCube d m z)) bad ∧
      M.P.toMeasure bad ≤ ENNReal.ofReal
        (Real.exp (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
      ∀ omega ∉ bad, omega ∈ coveringCoefficientRatioGood M L m z := by
  refine ⟨(coveringCoefficientRatioGood M L m z)ᶜ,
    measurableSet_compl_coveringCoefficientRatioGood M L m z,
    measure_compl_coveringCoefficientRatioGood_le M L m z, ?_⟩
  intro omega homega
  simpa using homega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
