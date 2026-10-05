module

public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRange
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRestrictionSymmetry
public import SubdiffusiveProcess.CoarseGrainingVocab.RestrictionContinuousBridge
public import Homogenization.Book.Ch04.Theorems.DilationLaw

@[expose] public section

/-!
# Canonical range normalization of a finite GMC cutoff

The cutoff at level `L` has literal local range `sqrt(d) * 3^L`.  A canonical
least triadic depth leaves room for two fixed open thickenings and converts
that range into CoarseGraining's exact unit-range restriction law.

 mirrors
`Algsuperdiff/Section3/Cutoff/RangeNormalization.lean` and
`Algsuperdiff/Section3/Cutoff/NormalizedStructuralLaw.lean`, using the finite
GMC shell join proved in `ACutoffRange.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization MeasureTheory Metric ProbabilityTheory Homogenization.Book
open scoped Pointwise

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Literal range of the level-`L` GMC cutoff. -/
def aCutoffNaturalRange (d L : ℕ) : ℝ :=
  Real.sqrt (d : ℝ) * (3 : ℝ) ^ L



def aCutoffBridgeEpsilon : ℝ := 1 / 4

theorem aCutoffBridgeEpsilon_pos : 0 < aCutoffBridgeEpsilon := by
  norm_num [aCutoffBridgeEpsilon]

@[simp]
theorem one_sub_two_mul_aCutoffBridgeEpsilon :
    1 - 2 * aCutoffBridgeEpsilon = 1 / 2 := by
  norm_num [aCutoffBridgeEpsilon]

private theorem exists_aCutoffNormalizationDepth (d L : ℕ) :
    ∃ k : ℕ, 2 * aCutoffNaturalRange d L < (3 : ℝ) ^ k :=
  pow_unbounded_of_one_lt _ (by norm_num)

/-- Least normalization depth leaving strict room for both thickenings. -/
noncomputable def aCutoffNormalizationDepth (d L : ℕ) : ℕ :=
  Nat.find (by
    exact exists_aCutoffNormalizationDepth d L :
    ∃ k : ℕ, 2 * aCutoffNaturalRange d L < (3 : ℝ) ^ k)

theorem aCutoffNormalizationDepth_spec (d L : ℕ) :
    2 * aCutoffNaturalRange d L <
      (3 : ℝ) ^ aCutoffNormalizationDepth d L :=
  Nat.find_spec (exists_aCutoffNormalizationDepth d L)

theorem aCutoffNormalizationDepth_strict_slack (d L : ℕ) :
    aCutoffNaturalRange d L <
      (3 : ℝ) ^ aCutoffNormalizationDepth d L *
        (1 - 2 * aCutoffBridgeEpsilon) := by
  rw [one_sub_two_mul_aCutoffBridgeEpsilon]
  nlinarith [aCutoffNormalizationDepth_spec d L]

private theorem vecNorm_smul {d : ℕ} (c : ℝ) (v : Vec d) :
    Homogenization.Book.Ch02.vecNorm (c • v) =
      |c| * Homogenization.Book.Ch02.vecNorm v := by
  change ‖(WithLp.toLp 2 (c • v) : EuclideanSpace ℝ (Fin d))‖ =
    |c| * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖
  have h : (WithLp.toLp 2 (c • v) : EuclideanSpace ℝ (Fin d)) =
      c • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) := by
    ext i
    rfl
  rw [h, norm_smul, Real.norm_eq_abs]

private theorem aCutoff_range_on_scaled_thickenings (d L k : ℕ)
    (U V : Set (Vec d)) (hUV : AreUnitSeparated U V)
    (hslack : aCutoffNaturalRange d L < (3 : ℝ) ^ k *
      (1 - 2 * aCutoffBridgeEpsilon)) :
    ∀ ⦃x y : Vec d⦄,
      x ∈ ((3 : ℝ) ^ k) • thickening aCutoffBridgeEpsilon U →
      y ∈ ((3 : ℝ) ^ k) • thickening aCutoffBridgeEpsilon V →
      aCutoffNaturalRange d L ≤ Homogenization.Book.Ch02.vecNorm (x - y) := by
  rintro x y ⟨x0, hx0, rfl⟩ ⟨y0, hy0, rfl⟩
  have hscale : 0 < (3 : ℝ) ^ k := by positivity
  have hgap := one_sub_two_mul_lt_vecNorm_sub_of_mem_thickenings
    (d := d) hUV (epsilon := aCutoffBridgeEpsilon) hx0 hy0
  have hstrict : aCutoffNaturalRange d L <
      Homogenization.Book.Ch02.vecNorm
        (((3 : ℝ) ^ k) • x0 - (3 : ℝ) ^ k • y0) := by
    rw [← smul_sub, vecNorm_smul, abs_of_pos hscale]
    exact hslack.trans (mul_lt_mul_of_pos_left hgap hscale)
  exact hstrict.le

theorem aux_dedup_d176_continuous_aCutoffRegCoeffField_entry {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (i j : Fin d) :
    Continuous (fun x : Vec d => aCutoffRegCoeffField M L omega x i j) := by
  have hmat : Continuous (fun x : Vec d =>
      scalarMatrix (d := d) (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x)) :=
    (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).smul continuous_const
  exact (continuous_apply j).comp ((continuous_apply i).comp hmat)

private theorem continuous_aCutoffRegCoeffField_entry {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (i j : Fin d) :
    Continuous (fun x : Vec d => aCutoffRegCoeffField M L omega x i j) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d176_continuous_aCutoffRegCoeffField_entry (d := d) (M := M) (L := L) (omega := omega) (i := i) (j := j)

/-- The canonically normalized finite-cutoff law has exact unit-range
restriction dependence. -/
theorem aCutoffNormalization_unitRangeDependentLaw {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    Ch04.RestrictionUnitRangeDependentLaw
      (Ch04.restrictionScaleNormalizedLaw
        (aCutoffNormalizationDepth d L) (aCutoffRestrictionLaw M L)) := by
  let : NeZero d := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  intro U V hU hV hUV
  let k : ℕ := aCutoffNormalizationDepth d L
  let r : ℝ := (3 : ℝ) ^ k
  let S : Set (Vec d) := thickening aCutoffBridgeEpsilon U
  let T : Set (Vec d) := thickening aCutoffBridgeEpsilon V
  have hr : r ≠ 0 := by
    dsimp [r]
    positivity
  have hS : IsOpen S := isOpen_thickening
  have hT : IsOpen T := isOpen_thickening
  have hrS : IsOpen (r • S) := by
    rw [← Set.image_smul]
    exact ((Homeomorph.smulOfNeZero r hr).isOpen_image).2 hS
  have hrT : IsOpen (r • T) := by
    rw [← Set.image_smul]
    exact ((Homeomorph.smulOfNeZero r hr).isOpen_image).2 hT
  have hsep : ∀ ⦃x y : Vec d⦄, x ∈ r • S → y ∈ r • T →
      aCutoffNaturalRange d L ≤ Homogenization.Book.Ch02.vecNorm (x - y) := by
    simpa only [r, S, T] using
      aCutoff_range_on_scaled_thickenings d L k U V hUV
        (by simpa [k] using aCutoffNormalizationDepth_strict_slack d L)
  let A : _root_.SubdiffusiveProcess.Model.PotentialSample d → RegCoeffField d := fun omega =>
    rescaleReg k (aCutoffRegCoeffField M L omega)
  have hAmeas : Measurable A :=
    (measurable_rescaleReg k).comp (measurable_aCutoffRegCoeffField M L)
  have hAcont : ∀ omega i j,
      Continuous (fun x : Vec d => A omega x i j) := by
    intro omega i j
    exact (continuous_aCutoffRegCoeffField_entry M L omega i j).comp
      (continuous_const_smul ((3 : ℝ) ^ k))
  have hlocalSource := indep_aCutoffRegCoeffField_local_of_separation
    M L (r • S) (r • T) hrS hrT hsep
  have hA_local_S : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (RegCoeffField d)
      ((LocalSigmaR (r • S)).comap (aCutoffRegCoeffField M L))
      (LocalSigmaR S) A := by
    exact (measurable_smulReg_local r hr S).comp
      (Measurable.of_comap_le le_rfl)
  have hA_local_T : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (RegCoeffField d)
      ((LocalSigmaR (r • T)).comap (aCutoffRegCoeffField M L))
      (LocalSigmaR T) A := by
    exact (measurable_smulReg_local r hr T).comp
      (Measurable.of_comap_le le_rfl)
  have hlocal : Indep (MeasurableSpace.comap A (LocalSigmaR S))
      (MeasurableSpace.comap A (LocalSigmaR T)) M.P.toMeasure :=
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hlocalSource hA_local_S.comap_le)
      hA_local_T.comap_le
  have hbridge := indep_restrictionSigmaR_map_of_indep_localSigmaR_thickenings
    A hAmeas hAcont U V hU hV aCutoffBridgeEpsilon
      aCutoffBridgeEpsilon_pos hlocal
  have hmap : Measure.map A M.P.toMeasure =
      Ch04.restrictionScaleNormalizedLaw k (aCutoffRestrictionLaw M L) := by
    rw [Ch04.restrictionScaleNormalizedLaw_eq_map_rescaleReg,
      aCutoffRestrictionLaw_eq_map,
      Measure.map_map (measurable_rescaleReg k)
        (measurable_aCutoffRegCoeffField M L)]
    rfl
  simpa [A, k, S, T] using hmap ▸ hbridge

/-- The canonically normalized GMC cutoff law satisfies the complete Chapter-4
structural package. -/
theorem aCutoffNormalization_structuralLaw {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    Ch04.RestrictionStructuralLaw
      (Ch04.restrictionScaleNormalizedLaw
        (aCutoffNormalizationDepth d L) (aCutoffRestrictionLaw M L)) where
  stationary :=
    Ch04.RestrictionStationaryLaw.scaleNormalized
      (aCutoffRestrictionLaw_stationary M L) (aCutoffNormalizationDepth d L)
  unit_range := aCutoffNormalization_unitRangeDependentLaw M L
  isotropic :=
    Ch04.RestrictionIsotropicLaw.scaleNormalized
      (aCutoffRestrictionLaw_isotropic M L) (aCutoffNormalizationDepth d L)
  adjoint_invariant :=
    Ch04.RestrictionAdjointInvariantLaw.scaleNormalized
      (aCutoffRestrictionLaw_adjoint_invariant M L)
      (aCutoffNormalizationDepth d L)

end

end SubdiffusiveProcess.CoarseGrainingVocab
