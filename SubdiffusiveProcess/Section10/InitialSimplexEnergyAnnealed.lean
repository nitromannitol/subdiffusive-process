module

public import SubdiffusiveProcess.Section10.InitialSimplexEnergyGluing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeanOneFubini
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SimplexGapStrict
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixVariational

@[expose] public section

/-!
# The actual GMC annealed packing inequality

This module applies the finite gluing supplier to `aCutoff M L`. The expected
energy on each packed domain can then be evaluated at any earlier cutoff:
the established prefix Jensen comparison reinserts the omitted independent
mean-one layers. The affine remainder has exactly its volume as expected
coefficient integral. No assumed energy bound or random minimizer selection
is used.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Expected affine Dirichlet energy of the actual cutoff matrix. -/
def expectedAffineDirichletEnergy (M : GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p : Vec d) : ℝ :=
  ∫ omega, vecDot p (matVecMul (randomAMatrix M L U omega) p) ∂M.P.toMeasure

/-- The scale-ell simplex appearing in `lim:lem-strict-decay`. -/
def initialSimplex (ell : ℕ) (pi : Equiv.Perm (Fin d)) : Kuhn.KuhnCell d :=
  ⟨originCube d (ell : ℤ), pi⟩

/-- The actual expected simplex energy to initialize retained-prefix induction. -/
def initialSimplexExpectedEnergy (M : GMCModel d) (ell : ℕ)
    (pi : Equiv.Perm (Fin d)) (p : Vec d) : ℝ :=
  expectedAffineDirichletEnergy M ell (kuhnCellDomain (initialSimplex ell pi)) p

/-- Integrability of the actual affine quadratic energy, without a half factor. -/
theorem integrable_affineDirichletEnergy (M : GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p : Vec d) :
    Integrable (fun omega => vecDot p (matVecMul (randomAMatrix M L U omega) p))
      M.P.toMeasure := by
  convert (integrable_randomAMatrix_quadratic M L U p).const_mul 2 using 1
  funext omega
  ring

/-- The actual expected energy is the annealed matrix quadratic form. -/
theorem expectedAffineDirichletEnergy_eq_abar (M : GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p : Vec d) :
    expectedAffineDirichletEnergy M L U p = vecDot p (matVecMul (abar M L U) p) := by
  have h := integral_randomAMatrix_quadratic M L U p
  rw [integral_const_mul] at h
  change (1 / 2 : ℝ) * expectedAffineDirichletEnergy M L U p = _ at h
  linarith

/-- The continuum minimum is the unnormalized actual matrix quadratic energy. -/
theorem dirichletInfOn_aCutoff_eq_volume_mul (M : GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (omega : PotentialSample d) (p : Vec d) :
    dirichletInfOn (aCutoff M L omega) (U : Set (Vec d)) p =
      (volume (U : Set (Vec d))).toReal *
        vecDot p (matVecMul (randomAMatrix M L U omega) p) := by
  have h := vecDot_aMatrix_eq_dirichletInfOn (aCutoffCoeffOnData M L omega U)
    (fun x => (Real.exp_pos _).le) p
  change vecDot p (matVecMul (randomAMatrix M L U omega) p) = _ at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (volume_toReal_pos U).ne', one_mul]

/-- Integrability of the unnormalized continuum minimum at the actual cutoff. -/
theorem integrable_dirichletInfOn_aCutoff (M : GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p : Vec d) :
    Integrable (fun omega => dirichletInfOn (aCutoff M L omega)
      (U : Set (Vec d)) p) M.P.toMeasure := by
  simp_rw [dirichletInfOn_aCutoff_eq_volume_mul]
  exact (integrable_affineDirichletEnergy M L U p).const_mul _

/-- Fubini and mean-one normalization of the actual cutoff on any bounded set. -/
theorem integral_setIntegral_aCutoff (M : GMCModel d) (L : ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    ∫ omega, (∫ x in U, aCutoff M L omega x) ∂M.P.toMeasure =
      (volume U).toReal := by
  simp_rw [aCutoff_eq_layerCoefficient]
  exact integral_setIntegral_layerCoefficient M (Finset.range (L + 1)) hU hUb

/-- The same spatial integral is integrable in the genuine GMC law. -/
theorem integrable_setIntegral_aCutoff (M : GMCModel d) (L : ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    Integrable (fun omega => ∫ x in U, aCutoff M L omega x) M.P.toMeasure := by
  simp_rw [aCutoff_eq_layerCoefficient]
  exact integrable_setIntegral_layerCoefficient M (Finset.range (L + 1)) hU hUb

/-- Reinserting the independent mean-one omitted prefix layers can only reduce
expected Dirichlet energy. This is a theorem about the actual GMC cutoffs. -/
theorem expectedAffineDirichletEnergy_antitone_cutoff (M : GMCModel d)
    (U : Ch02.Domain d) {n L : ℕ} (hnL : n ≤ L) (p : Vec d) :
    expectedAffineDirichletEnergy M L U p ≤ expectedAffineDirichletEnergy M n U p := by
  rw [expectedAffineDirichletEnergy_eq_abar, expectedAffineDirichletEnergy_eq_abar]
  rcases eq_or_lt_of_le hnL with rfl | hnL
  · exact le_refl _
  · have h := matLoewnerLE_abar_cutoff M U hnL p
    linarith

/-- Actual GMC expected energy on a finite disjoint packing with affine
remainder. Each packed domain may use its own earlier cutoff `n i`. All
remaining premises are geometric or index bounds. -/
theorem expectedAffineDirichletEnergy_le_packing
    {ι : Type*} [DecidableEq ι] (M : GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (S : Finset ι) (V : ι → Ch02.Domain d) (n : ι → ℕ)
    (hsub : ∀ i ∈ S, (V i : Set (Vec d)) ⊆ U)
    (hdisj : (S : Set ι).PairwiseDisjoint (fun i => (V i : Set (Vec d))))
    (hn : ∀ i ∈ S, n i ≤ L) (p : Vec d) :
    expectedAffineDirichletEnergy M L U p ≤
      (∑ i ∈ S, (volume (V i : Set (Vec d))).toReal /
        (volume (U : Set (Vec d))).toReal * expectedAffineDirichletEnergy M (n i) (V i) p) +
      (volume (packingRemainder (U : Set (Vec d)) S
        (fun i => (V i : Set (Vec d))))).toReal /
        (volume (U : Set (Vec d))).toReal * vecNormSq p := by
  classical
  let R := packingRemainder (U : Set (Vec d)) S (fun i => (V i : Set (Vec d)))
  have hRmeas : MeasurableSet R :=
    U.measurableSet.diff (S.measurableSet_biUnion (fun i _ => (V i).measurableSet))
  have hRb : Bornology.IsBounded R := U.isDomain.isBoundedDomain.isBounded.subset diff_subset
  have hintR : Integrable (fun omega => ∫ x in R, aCutoff M L omega x * vecNormSq p)
      M.P.toMeasure := by
    simp_rw [integral_mul_const]
    exact (integrable_setIntegral_aCutoff M L hRmeas hRb).mul_const _
  have hintS : Integrable (fun omega => ∑ i ∈ S,
      dirichletInfOn (aCutoff M L omega) (V i : Set (Vec d)) p) M.P.toMeasure :=
    integrable_finset_sum S (fun i _ => integrable_dirichletInfOn_aCutoff M L (V i) p)
  have hle := integral_mono (integrable_dirichletInfOn_aCutoff M L U p)
    (hintS.add hintR) (fun omega =>
      dirichletInfOn_le_packing_add_affine_remainder U S V hsub hdisj
        (continuous_aCutoff M L omega) (fun _ => Real.exp_pos _) p)
  have hS : (∫ omega, (∑ i ∈ S,
      dirichletInfOn (aCutoff M L omega) (V i : Set (Vec d)) p) ∂M.P.toMeasure) =
      ∑ i ∈ S, (volume (V i : Set (Vec d))).toReal *
        expectedAffineDirichletEnergy M L (V i) p := by
    rw [integral_finset_sum S (fun i _ => integrable_dirichletInfOn_aCutoff M L (V i) p)]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [dirichletInfOn_aCutoff_eq_volume_mul]
    exact integral_const_mul _ _
  have hrest : (∫ omega, (∫ x in R, aCutoff M L omega x * vecNormSq p)
      ∂M.P.toMeasure) = (volume R).toReal * vecNormSq p := by
    simp_rw [integral_mul_const]
    rw [integral_setIntegral_aCutoff M L hRmeas hRb]
  simp only [Pi.add_apply] at hle
  rw [integral_add hintS hintR, hS, hrest] at hle
  simp_rw [dirichletInfOn_aCutoff_eq_volume_mul] at hle
  rw [integral_const_mul] at hle
  have hle' := mul_le_mul_of_nonneg_left hle
    (inv_nonneg.mpr (volume_toReal_pos U).le)
  change (volume (U : Set (Vec d))).toReal⁻¹ *
      ((volume (U : Set (Vec d))).toReal * expectedAffineDirichletEnergy M L U p) ≤ _ at hle'
  rw [← mul_assoc, inv_mul_cancel₀ (volume_toReal_pos U).ne', one_mul] at hle'
  calc
    expectedAffineDirichletEnergy M L U p ≤
        (∑ i ∈ S, (volume (V i : Set (Vec d))).toReal /
          (volume (U : Set (Vec d))).toReal * expectedAffineDirichletEnergy M L (V i) p) +
          (volume R).toReal / (volume (U : Set (Vec d))).toReal * vecNormSq p := by
      convert hle' using 1
      rw [mul_add, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [div_eq_mul_inv]
        ring
      · rw [div_eq_mul_inv]
        ring
    _ ≤ _ := add_le_add (Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left
        (expectedAffineDirichletEnergy_antitone_cutoff M (V i) (hn i hi) p)
        (div_nonneg ENNReal.toReal_nonneg (volume_toReal_pos U).le))) (le_refl _)

end
end SubdiffusiveProcess.Section10
