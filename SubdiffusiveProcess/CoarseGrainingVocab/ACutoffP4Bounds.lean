import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4Envelope
import Homogenization.Book.Ch04.Theorems.WidetildeTheta
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Representatives
import Homogenization.Deterministic.CoarsePoincare.Setup.UniformBounds

/-!
# Samplewise coarse-ellipticity bounds for a GMC cutoff

The local lognormal envelope supplies explicit ellipticity witnesses on every
triadic cube.  This file mirrors
`Algsuperdiff/Section3/Cutoff/P4Bounds.lean`, with both ellipticity legs random
because the GMC cutoff has no deterministic molecular floor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Set Homogenization Homogenization.Book
open scoped BigOperators

noncomputable section


private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem exists_nat_openOriginCube_of_isCompact {K : Set (Vec d)}
    (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ openCubeSet (originCube d (n : ℤ)) := by
  let g : Vec d → ℝ := fun x => 2 * ∑ i : Fin d, |x i|
  have hg : Continuous g := continuous_const.mul
    (continuous_finset_sum Finset.univ (fun i _ => (continuous_apply i).abs))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, ?_⟩
  intro x hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hxi : |x i| ≤ ∑ j : Fin d, |x j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  have hgx : |g x| ≤ C := hC x hx
  have hsum_nn : 0 ≤ ∑ j : Fin d, |x j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg (x j)
  have hsum : 2 * ∑ j : Fin d, |x j| ≤ C := by
    simpa [g, abs_of_nonneg hsum_nn] using hgx
  have hpow : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ n := by simp
  rw [hpow]
  have hb : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by linarith
  rw [abs_lt] at hb
  exact ⟨by linarith [hb.1], hb.2⟩

/-- Least nonnegative origin-cube scale containing the closure of `Q`. -/
noncomputable def aCutoffCubeOriginCoverDepth (Q : TriadicCube d) : ℕ :=
  by
    classical
    exact Nat.find (exists_nat_openOriginCube_of_isCompact
      ((isBounded_openCubeSet Q).isCompact_closure))

noncomputable def aCutoffCubeOriginCoverScale (Q : TriadicCube d) : ℤ :=
  (aCutoffCubeOriginCoverDepth Q : ℤ)

omit [NeZero d] in
theorem closure_subset_aCutoffCubeOriginCover (Q : TriadicCube d) :
    closure (openCubeSet Q) ⊆
      openCubeSet (originCube d (aCutoffCubeOriginCoverScale Q)) :=
  by
    classical
    exact Nat.find_spec (exists_nat_openOriginCube_of_isCompact
      ((isBounded_openCubeSet Q).isCompact_closure))

omit [NeZero d] in
theorem openCubeSet_subset_aCutoffCubeOriginCover (Q : TriadicCube d) :
    openCubeSet Q ⊆
      openCubeSet (originCube d (aCutoffCubeOriginCoverScale Q)) :=
  subset_closure.trans (closure_subset_aCutoffCubeOriginCover Q)

/-- Explicit coefficient data whose ellipticity witnesses are measurable
functions of the local lognormal envelope. -/
noncomputable def aCutoffEnvelopeCoeffOnData
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d)
    (Q : TriadicCube d) :
    ScalarCoeffOnData (Ch02.cubeDomain Q)
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) where
  lam := Real.exp (-aCutoffCubeLogEnvelope M L
    (aCutoffCubeOriginCoverScale Q) omega)
  Lam := Real.exp (aCutoffCubeLogEnvelope M L
    (aCutoffCubeOriginCoverScale Q) omega)
  lam_pos := Real.exp_pos _
  lam_le_Lam := Real.exp_le_exp.mpr (by
    linarith [aCutoffCubeLogEnvelope_nonneg M L
      (aCutoffCubeOriginCoverScale Q) omega])
  aeStronglyMeasurable := by
    intro i j
    simpa only [Ch02.cubeDomain_coe] using
      (aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)).aeStronglyMeasurable i j
  aeBounds := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact ⟨exp_neg_aCutoffCubeLogEnvelope_le_aCutoff M L _ omega
      (openCubeSet_subset_aCutoffCubeOriginCover Q hx),
      aCutoff_le_exp_aCutoffCubeLogEnvelope M L _ omega
        (openCubeSet_subset_aCutoffCubeOriginCover Q hx)⟩

/-- Compatible triadic family with the literal cutoff as representative. -/
noncomputable def aCutoffEnvelopeScalarTriadicCoeffData
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d) :
    ScalarTriadicCoeffData (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) where
  onCube Q := aCutoffEnvelopeCoeffOnData M L omega Q

/-- Compatible triadic family with the literal cutoff as representative. -/
noncomputable def aCutoffEnvelopeTriadicCoeffFamily
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d) :
    Ch02.TriadicCoeffFamily d :=
  (aCutoffEnvelopeScalarTriadicCoeffData M L omega).toTriadicCoeffFamily

omit [NeZero d] in
theorem aCutoff_canonicalFamily_aeeq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d) :
    Ch02.TriadicCoeffFamily.AEEq
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (aCutoffRegCoeffField M L omega)
        (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega))
      (aCutoffEnvelopeTriadicCoeffFamily M L omega) := by
  intro Q
  change aCutoffRegCoeffField M L omega =ᵐ[volumeMeasureOn
    (Ch02.cubeDomain Q : Set (Vec d))] scalarCoeffField
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
  exact Filter.Eventually.of_forall fun x => by
    simp [aCutoffRegCoeffField, scalarCoeffField]

private theorem maxDescendantBMatrixNormAtScale_le_envelope
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d)
    (Q : TriadicCube d) (n : ℕ) :
    Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ))
      (aCutoffEnvelopeTriadicCoeffFamily M L omega) ≤
      4 * (d : ℝ) *
        Real.exp (3 * aCutoffCubeLogEnvelope M L
          (aCutoffCubeOriginCoverScale Q) omega) := by
  let F := aCutoffEnvelopeTriadicCoeffFamily M L omega
  let A : CoeffField d := Internal.Ch02.BookCh02.pointwiseCoeffField
    (Ch02.cubeDomain Q) (F.coeffOn Q)
  let Z := aCutoffCubeLogEnvelope M L (aCutoffCubeOriginCoverScale Q) omega
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := sub_le_self _ (by positivity)
  have hEll : IsEllipticFieldOn (Real.exp (-Z)) (Real.exp Z)
      (openCubeSet Q) A := by
    simpa [A, F, Z, aCutoffEnvelopeTriadicCoeffFamily,
      aCutoffEnvelopeCoeffOnData, ScalarCoeffOnData.toCoeffOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using Ch02.pointwiseCoeffField_openCube_descendant_data
      Q (F.coeffOn Q)
  calc
    Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F ≤
        maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) A :=
      Ch02.maxDescendantBMatrixNormAtScale_le_maxDescendantBBlockNormAtScale F Q hk
    _ ≤ 4 * (d : ℝ) * (Real.exp (-Z))⁻¹ * (Real.exp Z) ^ 2 := by
      simpa [A] using
        maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
          Q A hEll hData n
    _ = 4 * (d : ℝ) * Real.exp (3 * Z) := by
      rw [← Real.exp_neg, neg_neg, pow_two]
      have hexp : Real.exp (3 * Z) =
          Real.exp Z * Real.exp Z * Real.exp Z := by
        rw [show 3 * Z = Z + Z + Z by ring, Real.exp_add, Real.exp_add]
      rw [hexp]
      ring

private theorem maxDescendantSigmaStarInvMatrixNormAtScale_le_envelope
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d)
    (Q : TriadicCube d) (n : ℕ) :
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ))
      (aCutoffEnvelopeTriadicCoeffFamily M L omega) ≤
      4 * (d : ℝ) * Real.exp (aCutoffCubeLogEnvelope M L
        (aCutoffCubeOriginCoverScale Q) omega) := by
  let F := aCutoffEnvelopeTriadicCoeffFamily M L omega
  let A : CoeffField d := Internal.Ch02.BookCh02.pointwiseCoeffField
    (Ch02.cubeDomain Q) (F.coeffOn Q)
  let Z := aCutoffCubeLogEnvelope M L (aCutoffCubeOriginCoverScale Q) omega
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := sub_le_self _ (by positivity)
  have hEll : IsEllipticFieldOn (Real.exp (-Z)) (Real.exp Z)
      (openCubeSet Q) A := by
    simpa [A, F, Z, aCutoffEnvelopeTriadicCoeffFamily,
      aCutoffEnvelopeCoeffOnData, ScalarCoeffOnData.toCoeffOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using Ch02.pointwiseCoeffField_openCube_descendant_data
      Q (F.coeffOn Q)
  calc
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F ≤
        maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) A :=
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
        F Q hk
    _ ≤ 4 * (d : ℝ) * (Real.exp (-Z))⁻¹ := by
      simpa [A] using
        maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
          Q A hEll hData n
    _ = 4 * (d : ℝ) * Real.exp Z := by rw [← Real.exp_neg, neg_neg]

private theorem tsum_geometricWeight_one_mul_le_const
    {H : ℕ → ℝ} {s C : ℝ} (hs : 0 < s)
    (hH_nonneg : ∀ n, 0 ≤ H n) (hH_le : ∀ n, H n ≤ C) :
    (∑' n, Ch02.geometricWeight s 1 n * H n) ≤ C := by
  have hs1 : 0 < s * (1 : ℝ) := by simpa using hs
  have hsumH := summable_geometricWeight_mul_of_nonneg_of_le
    (s := s) (q := 1) (C := C) hs1 hH_nonneg hH_le
  have hsumC := (summable_geometricWeight (s := s) (q := 1) hs1).mul_right C
  calc
    (∑' n, Ch02.geometricWeight s 1 n * H n) ≤
        ∑' n, Ch02.geometricWeight s 1 n * C :=
      Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hH_le n)
        (geometricWeight_nonneg n hs1.le)) hsumH hsumC
    _ = C := by
      rw [tsum_mul_right]
      simpa [Ch02.geometricWeight_eq_old] using
        congrArg (fun x : ℝ => x * C) (tsum_geometricWeight_eq_one hs1)

/-- Upper Chapter 4 coarse observable controlled by the local log envelope. -/
theorem LambdaSqCoeffField_le_aCutoffCubeLogEnvelope
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    Ch04.LambdaSqCoeffField Q s (.finite 1) (aCutoffRegCoeffField M L omega) ≤
      4 * (d : ℝ) * Real.exp (3 * aCutoffCubeLogEnvelope M L
        (aCutoffCubeOriginCoverScale Q) omega) := by
  let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  let F := aCutoffEnvelopeTriadicCoeffFamily M L omega
  have hAEEq :
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (aCutoffRegCoeffField M L omega) hlocal).AEEq F := by
    simpa [hlocal, F] using aCutoff_canonicalFamily_aeeq M L omega
  let C := 4 * (d : ℝ) * Real.exp (3 * aCutoffCubeLogEnvelope M L
    (aCutoffCubeOriginCoverScale Q) omega)
  have hnonneg : ∀ n : ℕ, 0 ≤ Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
      Q (Q.scale - (n : ℤ)) (aCutoffRegCoeffField M L omega) := by
    intro n
    rw [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dif_pos hlocal,
      Ch02.maxDescendantBMatrixNormAtScale_eq_ofAEEq hAEEq]
    exact Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F
  have hbound : ∀ n : ℕ, Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
      Q (Q.scale - (n : ℤ)) (aCutoffRegCoeffField M L omega) ≤ C := by
    intro n
    rw [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dif_pos hlocal,
      Ch02.maxDescendantBMatrixNormAtScale_eq_ofAEEq hAEEq]
    exact maxDescendantBMatrixNormAtScale_le_envelope M L omega Q n
  calc
    Ch04.LambdaSqCoeffField Q s (.finite 1) (aCutoffRegCoeffField M L omega) ≤
        ∑' n, Ch02.geometricWeight s 1 n *
          Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) (aCutoffRegCoeffField M L omega) :=
      Ch04.LambdaSqCoeffField_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale
        Q _ hs
    _ ≤ C := tsum_geometricWeight_one_mul_le_const hs hnonneg hbound

/-- Lower inverse Chapter 4 coarse observable controlled by the same envelope. -/
theorem lambdaSqCoeffField_inv_le_aCutoffCubeLogEnvelope
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    (Ch04.lambdaSqCoeffField Q s (.finite 1) (aCutoffRegCoeffField M L omega))⁻¹ ≤
      4 * (d : ℝ) * Real.exp (aCutoffCubeLogEnvelope M L
        (aCutoffCubeOriginCoverScale Q) omega) := by
  let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  let F := aCutoffEnvelopeTriadicCoeffFamily M L omega
  have hAEEq :
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (aCutoffRegCoeffField M L omega) hlocal).AEEq F := by
    simpa [hlocal, F] using aCutoff_canonicalFamily_aeeq M L omega
  let C := 4 * (d : ℝ) * Real.exp (aCutoffCubeLogEnvelope M L
    (aCutoffCubeOriginCoverScale Q) omega)
  have hnonneg : ∀ n : ℕ, 0 ≤
      Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
        (Q.scale - (n : ℤ)) (aCutoffRegCoeffField M L omega) := by
    intro n
    rw [Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale,
      dif_pos hlocal, Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_eq_ofAEEq hAEEq]
    exact Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F
  have hbound : ∀ n : ℕ,
      Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
        (Q.scale - (n : ℤ)) (aCutoffRegCoeffField M L omega) ≤ C := by
    intro n
    rw [Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale,
      dif_pos hlocal, Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_eq_ofAEEq hAEEq]
    exact maxDescendantSigmaStarInvMatrixNormAtScale_le_envelope M L omega Q n
  calc
    (Ch04.lambdaSqCoeffField Q s (.finite 1) (aCutoffRegCoeffField M L omega))⁻¹ ≤
        ∑' n, Ch02.geometricWeight s 1 n *
          Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) (aCutoffRegCoeffField M L omega) :=
      Ch04.lambdaSqCoeffField_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
        Q _ hs
    _ ≤ C := tsum_geometricWeight_one_mul_le_const hs hnonneg hbound

end

end SubdiffusiveProcess.CoarseGrainingVocab
