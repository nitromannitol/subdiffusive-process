module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
public import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity
public import Homogenization.CoarseGraining.ResponseIdentities.Homogeneity

@[expose] public section

/-!
# Infrared cutoff comparison provider

This module implements the eight-line source proof of
`lemma:infrared.approx.cutoffs`: field-level cutoff-ratio sensitivity is
transported to the primal and dual coarse matrices using the source-exact
general sensitivity estimate and CoarseGraining's exact scalar homogeneity.

D-013 provenance: the Superdiffusion `Section3/Provider` tree was searched
for an infrared cutoff-comparison provider.  Its closest homogeneity lanes
(`Homogenization/ObservationScaleFiniteCoverDepth.lean` and
`Homogenization/CombineIntegerDownscale.lean`) use the same Chapter 2 matrix
scaling package, but no analogue has this theorem's two cutoff-ratio moment
assembly.  The proof therefore follows the GMC manuscript directly.
-/


open MeasureTheory Homogenization Homogenization.Book Homogenization.IndependentSums
open scoped ENNReal Matrix.Norms.L2Operator MatrixOrder

namespace SubdiffusiveProcess.Providers.Section3

open SubdiffusiveProcess.CoarseGrainingVocab

variable {d : ℕ}

private theorem scalarRatioLInf_le_of_ae_bound
    {U : Ch02.Domain d} {a b : Homogenization.Vec d → ℝ} {W : ℝ}
    (hW0 : 0 ≤ W)
    (h : ∀ᵐ x ∂volumeMeasureOn (U : Set (Homogenization.Vec d)), |a x / b x - 1| ≤ W) :
    scalarRatioLInf U a b ≤ W := by
  unfold scalarRatioLInf
  rw [SubdiffusiveProcess.RawLp.eLpNorm_top_exponent]
  have hess : eLpNormEssSup (fun x => a x / b x - 1)
      (volumeMeasureOn (U : Set (Homogenization.Vec d))) ≤ ENNReal.ofReal W :=
    eLpNormEssSup_le_of_ae_bound (by simpa [Real.norm_eq_abs] using h)
  calc
    (eLpNormEssSup (fun x => a x / b x - 1)
        (volumeMeasureOn (U : Set (Homogenization.Vec d)))).toReal ≤
        (ENNReal.ofReal W).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    _ = W := ENNReal.toReal_ofReal hW0

private theorem finite_scalarSensitivityError_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ) (k : ℤ)
    (hnm : n < m) (U : Ch02.Domain d)
    (hU : (U : Set (Homogenization.Vec d)) ⊆ openCubeSet (originCube d k))
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {W : ℝ}
    (hW0 : 0 ≤ W)
    (hfwd : cutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal W)
    (hinv : inverseCutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal W) :
    scalarSensitivityError U
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega)
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) ≤ W := by
  apply max_le
  · apply scalarRatioLInf_le_of_ae_bound hW0
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    have hpoint : ENNReal.ofReal
        |cutoffRatioMinusOne M m (n : ℤ) omega x| ≤
        cutoffRatioLinfty M m n k omega := by
      have hcast : ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) = ((m - n : ℕ) : ℝ) := by
        exact_mod_cast (show (m : ℤ) - n = (m - n : ℕ) by omega)
      unfold cutoffRatioLinfty
      calc
        ENNReal.ofReal |cutoffRatioMinusOne M m (n : ℤ) omega x| =
            ENNReal.ofReal |Real.exp (cutoffShellSum m (n : ℤ) x omega -
              ((m - n : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1| := by
          rw [cutoffRatioMinusOne_eq_exp_shell M m (n : ℤ) omega x
            (by omega) (by omega), hcast]
        _ ≤ ⨆ y : {x : Homogenization.Vec d //
            x ∈ openCubeSet (originCube d k)},
              ENNReal.ofReal
                |Real.exp (cutoffShellSum m (n : ℤ) y.1 omega -
                  ((m - n : ℕ) : ℝ) *
                    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1| :=
          le_iSup (fun y : {x : Homogenization.Vec d //
            x ∈ openCubeSet (originCube d k)} =>
              ENNReal.ofReal
                |Real.exp (cutoffShellSum m (n : ℤ) y.1 omega -
                  ((m - n : ℕ) : ℝ) *
                    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1|)
            (⟨x, hU hx⟩ : {x : Homogenization.Vec d //
              x ∈ openCubeSet (originCube d k)})
    have hreal := (ENNReal.ofReal_le_ofReal_iff hW0).mp
      (hpoint.trans hfwd)
    simpa only [cutoffRatioMinusOne, aCutoffAtInt,
      if_neg (not_lt.mpr (Int.natCast_nonneg n)), Int.toNat_natCast] using! hreal
  · apply scalarRatioLInf_le_of_ae_bound hW0
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    have hpoint : ENNReal.ofReal
        |inverseCutoffRatioMinusOne M m (n : ℤ) omega x| ≤
        inverseCutoffRatioLinfty M m n k omega := by
      have hcast : ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) = ((m - n : ℕ) : ℝ) := by
        exact_mod_cast (show (m : ℤ) - n = (m - n : ℕ) by omega)
      unfold inverseCutoffRatioLinfty
      calc
        ENNReal.ofReal |inverseCutoffRatioMinusOne M m (n : ℤ) omega x| =
            ENNReal.ofReal |Real.exp (-cutoffShellSum m (n : ℤ) x omega +
              ((m - n : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1| := by
          rw [inverseCutoffRatioMinusOne_eq_exp_shell M m (n : ℤ) omega x
            (by omega) (by omega), hcast]
        _ ≤ ⨆ y : {x : Homogenization.Vec d //
            x ∈ openCubeSet (originCube d k)},
              ENNReal.ofReal
                |Real.exp (-cutoffShellSum m (n : ℤ) y.1 omega +
                  ((m - n : ℕ) : ℝ) *
                    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1| :=
          le_iSup (fun y : {x : Homogenization.Vec d //
            x ∈ openCubeSet (originCube d k)} =>
              ENNReal.ofReal
                |Real.exp (-cutoffShellSum m (n : ℤ) y.1 omega +
                  ((m - n : ℕ) : ℝ) *
                    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1|)
            (⟨x, hU hx⟩ : {x : Homogenization.Vec d //
              x ∈ openCubeSet (originCube d k)})
    have hreal := (ENNReal.ofReal_le_ofReal_iff hW0).mp
      (hpoint.trans hinv)
    simpa only [inverseCutoffRatioMinusOne, aCutoffAtInt,
      if_neg (not_lt.mpr (Int.natCast_nonneg n)), Int.toNat_natCast] using! hreal

private theorem finite_matrix_deviations_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ) (k : ℤ)
    (hnm : n < m) (U : Ch02.Domain d)
    (hU : (U : Set (Homogenization.Vec d)) ⊆ openCubeSet (originCube d k))
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {W : ℝ}
    (hW0 : 0 ≤ W)
    (hfwd : cutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal W)
    (hinv : inverseCutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal W) :
    normalizedMatrixDeviation
        (randomAStarMatrix M m U omega) (randomAStarMatrix M n U omega) 1 ≤ W ∧
      normalizedMatrixDeviation
        (randomAMatrix M m U omega) (randomAMatrix M n U omega) 1 ≤ W ∧
      normalizedMatrixDeviation
        (randomAStarMatrix M n U omega) (randomAStarMatrix M m U omega) 1 ≤ W ∧
      normalizedMatrixDeviation
        (randomAMatrix M n U omega) (randomAMatrix M m U omega) 1 ≤ W := by
  let hm := aCutoffCoeffOnData M m omega U
  let hn := aCutoffCoeffOnData M n omega U
  have herr := finite_scalarSensitivityError_le M m n k hnm U hU omega
    hW0 hfwd hinv
  have hmn := normalized_aStarMatrix_and_aMatrix_deviation_le hm hn
  have hnm' := normalized_aStarMatrix_and_aMatrix_deviation_le hn hm
  have herr' : scalarSensitivityError U
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega) ≤ W := by
    simpa [scalarSensitivityError, max_comm] using herr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hm, hn, normalizedMatrixDeviation, randomAStarMatrix] using
      hnm'.1.trans herr'
  · simpa [hm, hn, normalizedMatrixDeviation, randomAMatrix] using
      hnm'.2.trans herr'
  · simpa [hm, hn, normalizedMatrixDeviation, randomAStarMatrix] using
      hmn.1.trans herr
  · simpa [hm, hn, normalizedMatrixDeviation, randomAMatrix] using
      hmn.2.trans herr

private theorem paperTwoTermLpObservable_le_add
    {Omega : Type*} {p : ℝ} (hp : 1 ≤ p) (X Y : Omega → ℝ)
    (omega : Omega) :
    paperTwoTermLpObservable p X Y omega ≤
      max (X omega) 0 + max (Y omega) 0 := by
  unfold paperTwoTermLpObservable
  simpa [one_div] using Real.rpow_add_rpow_le_add
    (le_max_right (X omega) 0) (le_max_right (Y omega) 0) hp

private theorem anchored_cutoff_ratio_eq_exp_shell_sub
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) (hnL : n < L)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : Homogenization.Vec d) :
    let c := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0
    c⁻¹ * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x =
      Real.exp (cutoffShellSum L (n : ℤ) 0 omega -
        cutoffShellSum L (n : ℤ) x omega) := by
  dsimp only
  have hx := cutoff_log_ratio_eq M L (n : ℤ) omega x (by omega) (by omega)
  have h0 := cutoff_log_ratio_eq M L (n : ℤ) omega 0 (by omega) (by omega)
  rw [if_neg (by omega : ¬(n : ℤ) < 0)] at hx h0
  simp only [Int.toNat_natCast] at hx h0
  simp only [SubdiffusiveProcess.Frozen.Assumptions.aCutoff, div_eq_mul_inv]
  field_simp
  simp only [← Real.exp_add]
  congr 1
  linarith

private theorem anchored_inverse_cutoff_ratio_eq_exp_shell_sub
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) (hnL : n < L)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : Homogenization.Vec d) :
    let c := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
        (c⁻¹ * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x) =
      Real.exp (cutoffShellSum L (n : ℤ) x omega -
        cutoffShellSum L (n : ℤ) 0 omega) := by
  dsimp only
  have hx := cutoff_log_ratio_eq M L (n : ℤ) omega x (by omega) (by omega)
  have h0 := cutoff_log_ratio_eq M L (n : ℤ) omega 0 (by omega) (by omega)
  rw [if_neg (by omega : ¬(n : ℤ) < 0)] at hx h0
  simp only [Int.toNat_natCast] at hx h0
  simp only [SubdiffusiveProcess.Frozen.Assumptions.aCutoff, div_eq_mul_inv]
  field_simp
  simp only [← Real.exp_add]
  congr 1
  linarith

private theorem abs_exp_sub_one_le_exp_abs_sub_one (t : ℝ) :
    |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht))]
  · have ht0 : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht0, abs_of_nonpos (sub_nonpos.mpr
      (Real.exp_le_one_iff.mpr ht0))]
    have hpos := Real.add_one_le_exp t
    have hneg := Real.add_one_le_exp (-t)
    nlinarith

private theorem anchored_scalarSensitivityError_le_oscillation
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) (hnL : n < L)
    (k : ℤ) (U : Ch02.Domain d)
    (hU : (U : Set (Homogenization.Vec d)) ⊆ openCubeSet (originCube d k))
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    let c := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0
    scalarSensitivityError U
        (fun x => c⁻¹ * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) ≤
      Real.exp (cubeOscillation k
        (fun x => cutoffShellSum L (n : ℤ) x omega)) - 1 := by
  dsimp only
  let f : Homogenization.Vec d → ℝ :=
    fun x => cutoffShellSum L (n : ℤ) x omega
  have hf : Continuous f := by
    dsimp [f, cutoffShellSum]
    fun_prop
  have hzero : (0 : Homogenization.Vec d) ∈ openCubeSet (originCube d k) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
    simp only [Pi.zero_apply]
    constructor <;> nlinarith
  have hR0 : 0 ≤ Real.exp (cubeOscillation k f) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (cubeOscillation_nonneg k f))
  apply max_le
  · apply scalarRatioLInf_le_of_ae_bound hR0
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    have hdiff : |f 0 - f x| ≤ cubeOscillation k f := by
      rw [abs_le]
      constructor
      · have h := sub_le_cubeOscillation_of_continuous k hf (hU hx) hzero
        linarith
      · exact sub_le_cubeOscillation_of_continuous k hf hzero (hU hx)
    rw [anchored_cutoff_ratio_eq_exp_shell_sub M L n hnL omega x]
    exact (abs_exp_sub_one_le_exp_abs_sub_one _).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr hdiff) 1)
  · apply scalarRatioLInf_le_of_ae_bound hR0
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    have hdiff : |f x - f 0| ≤ cubeOscillation k f := by
      rw [abs_le]
      constructor
      · have h := sub_le_cubeOscillation_of_continuous k hf hzero (hU hx)
        linarith
      · exact sub_le_cubeOscillation_of_continuous k hf (hU hx) hzero
    rw [anchored_inverse_cutoff_ratio_eq_exp_shell_sub M L n hnL omega x]
    exact (abs_exp_sub_one_le_exp_abs_sub_one _).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr hdiff) 1)

-- The certificate construction is the provider-local public analogue of the
-- private helper already used by `Sensitivity.lean`.
private noncomputable def scalarCoeffOnData_const_mul
    {U : Ch02.Domain d} {a : Homogenization.Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) {c : ℝ} (hc : 0 < c) :
    ScalarCoeffOnData U (fun x => c * a x) where
  lam := c * ha.lam
  Lam := c * ha.Lam
  lam_pos := mul_pos hc ha.lam_pos
  lam_le_Lam := mul_le_mul_of_nonneg_left ha.lam_le_Lam hc.le
  aeStronglyMeasurable := by
    intro i j
    have h := (ha.aeStronglyMeasurable i j).const_smul c
    convert h using 1
    funext x
    by_cases hx : x ∈ (U : Set (Homogenization.Vec d))
    · simp [restrictCoeffField, hx, scalarCoeffField, scalarMatrix, mul_assoc]
    · simp [restrictCoeffField, hx, scalarCoeffField]
  aeBounds := by
    filter_upwards [ha.aeBounds] with x hx
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hc.le,
      mul_le_mul_of_nonneg_left hx.2 hc.le⟩

private theorem scaled_aMatrices_eq
    {U : Ch02.Domain d} {a : Homogenization.Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) {c : ℝ} (hc : 0 < c) :
    let hca := scalarCoeffOnData_const_mul ha hc
    aMatrix U hca.toCoeffOn = c • aMatrix U ha.toCoeffOn ∧
      aStarMatrix U hca.toCoeffOn = c • aStarMatrix U ha.toCoeffOn := by
  dsimp only
  let hca := scalarCoeffOnData_const_mul ha hc
  have hscaled : Ch02.CoeffOn.AEScaled c ha.toCoeffOn hca.toCoeffOn := by
    exact Filter.Eventually.of_forall fun x => by
      ext i j
      simp [hca, scalarCoeffOnData_const_mul, ScalarCoeffOnData.toCoeffOn,
        scalarCoeffField, scalarMatrix, mul_assoc]
  have hscaleTheory := Ch02.responseSubadditivityAndScalingTheory U ha.toCoeffOn
  have hsigma := hscaleTheory.sigma_homogeneous hc hscaled
  have hstar := hscaleTheory.sigmaStar_homogeneous hc hscaled
  have hTa := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hTca := Ch02.responseSymmetricDirichletNeumannTheory U hca.toCoeffOn hca.isSymmetric
  constructor
  · change Ch02.aCoarse U hca.toCoeffOn = c • Ch02.aCoarse U ha.toCoeffOn
    rw [hTca.derived_matrices.1, hTa.derived_matrices.1]
    exact hsigma
  · change Ch02.aStarCoarse U hca.toCoeffOn = c • Ch02.aStarCoarse U ha.toCoeffOn
    rw [hTca.derived_matrices.2.1, hTa.derived_matrices.2.1]
    exact hstar

private theorem reverse_anchored_scalarSensitivityError_le_oscillation
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) (hnL : n < L)
    (k : ℤ) (U : Ch02.Domain d)
    (hU : (U : Set (Homogenization.Vec d)) ⊆ openCubeSet (originCube d k))
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    let c := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0
    scalarSensitivityError U
        (fun x => c * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) ≤
      Real.exp (cubeOscillation k
        (fun x => cutoffShellSum L (n : ℤ) x omega)) - 1 := by
  dsimp only
  let f : Homogenization.Vec d → ℝ :=
    fun x => cutoffShellSum L (n : ℤ) x omega
  have hf : Continuous f := by
    dsimp [f, cutoffShellSum]
    fun_prop
  have hzero : (0 : Homogenization.Vec d) ∈ openCubeSet (originCube d k) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
    simp only [Pi.zero_apply]
    constructor <;> nlinarith
  have hc : 0 < SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0 := div_pos
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n omega 0)
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega 0)
  have hR0 : 0 ≤ Real.exp (cubeOscillation k f) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (cubeOscillation_nonneg k f))
  apply max_le
  · apply scalarRatioLInf_le_of_ae_bound hR0
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    have hdiff : |f x - f 0| ≤ cubeOscillation k f := by
      rw [abs_le]
      constructor
      · have h := sub_le_cubeOscillation_of_continuous k hf hzero (hU hx)
        linarith
      · exact sub_le_cubeOscillation_of_continuous k hf (hU hx) hzero
    rw [show (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0) *
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x =
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
          ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0)⁻¹ *
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x) by field_simp]
    rw [anchored_inverse_cutoff_ratio_eq_exp_shell_sub M L n hnL omega x]
    exact (abs_exp_sub_one_le_exp_abs_sub_one _).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr hdiff) 1)
  · apply scalarRatioLInf_le_of_ae_bound hR0
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    have hdiff : |f 0 - f x| ≤ cubeOscillation k f := by
      rw [abs_le]
      constructor
      · have h := sub_le_cubeOscillation_of_continuous k hf (hU hx) hzero
        linarith
      · exact sub_le_cubeOscillation_of_continuous k hf hzero (hU hx)
    rw [show SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x /
          ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0) *
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) =
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0)⁻¹ *
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x by field_simp]
    rw [anchored_cutoff_ratio_eq_exp_shell_sub M L n hnL omega x]
    exact (abs_exp_sub_one_le_exp_abs_sub_one _).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr hdiff) 1)

private theorem cutoffSensitivityAt_le_oscillation
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) (hnL : n < L)
    (k : ℤ) (U : Ch02.Domain d)
    (hU : (U : Set (Homogenization.Vec d)) ⊆ openCubeSet (originCube d k))
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    cutoffSensitivityForwardAt M L n U omega ≤
        2 * (Real.exp (cubeOscillation k
          (fun x => cutoffShellSum L (n : ℤ) x omega)) - 1) ∧
      cutoffSensitivityReverseAt M L n U omega ≤
        2 * (Real.exp (cubeOscillation k
          (fun x => cutoffShellSum L (n : ℤ) x omega)) - 1) := by
  let c := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 /
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0
  have hc : 0 < c := div_pos
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n omega 0)
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega 0)
  let hnData := aCutoffCoeffOnData M n omega U
  let hLData := aCutoffCoeffOnData M L omega U
  let hnScaled := scalarCoeffOnData_const_mul hnData (inv_pos.mpr hc)
  let hLScaled := scalarCoeffOnData_const_mul hLData hc
  have hnScale := scaled_aMatrices_eq hnData (inv_pos.mpr hc)
  have hLScale := scaled_aMatrices_eq hLData hc
  have hforward := normalized_aStarMatrix_and_aMatrix_deviation_le hnScaled hLData
  have hreverse := normalized_aStarMatrix_and_aMatrix_deviation_le hLScaled hnData
  have herrF := anchored_scalarSensitivityError_le_oscillation
    M L n hnL k U hU omega
  have herrR := reverse_anchored_scalarSensitivityError_le_oscillation
    M L n hnL k U hU omega
  constructor
  · unfold cutoffSensitivityForwardAt
    dsimp only
    have hs :
        normalizedMatrixDeviation (randomAStarMatrix M L U omega)
            (randomAStarMatrix M n U omega) c ≤
              Real.exp (cubeOscillation k
                (fun x => cutoffShellSum L (n : ℤ) x omega)) - 1 ∧
          normalizedMatrixDeviation (randomAMatrix M L U omega)
            (randomAMatrix M n U omega) c ≤
              Real.exp (cubeOscillation k
                (fun x => cutoffShellSum L (n : ℤ) x omega)) - 1 := by
      constructor
      · simpa [hnScaled, hnData, hLData, normalizedMatrixDeviation,
          randomAStarMatrix, hnScale.2, c, smul_eq_mul, mul_assoc] using
          hforward.1.trans herrF
      · simpa [hnScaled, hnData, hLData, normalizedMatrixDeviation,
          randomAMatrix, hnScale.1, c, smul_eq_mul, mul_assoc] using
          hforward.2.trans herrF
    linarith [hs.1, hs.2]
  · unfold cutoffSensitivityReverseAt
    dsimp only
    have hcinv : (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0 /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0)⁻¹ = c := by
      dsimp [c]
      field_simp
    have hs :
        normalizedMatrixDeviation (randomAStarMatrix M n U omega)
            (randomAStarMatrix M L U omega)
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0 /
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0) ≤
              Real.exp (cubeOscillation k
                (fun x => cutoffShellSum L (n : ℤ) x omega)) - 1 ∧
          normalizedMatrixDeviation (randomAMatrix M n U omega)
            (randomAMatrix M L U omega)
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0 /
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0) ≤
              Real.exp (cubeOscillation k
                (fun x => cutoffShellSum L (n : ℤ) x omega)) - 1 := by
      constructor
      · simpa [hLScaled, hnData, hLData, normalizedMatrixDeviation,
          randomAStarMatrix, hLScale.2, c, hcinv, smul_eq_mul, mul_assoc] using
          hreverse.1.trans herrR
      · simpa [hLScaled, hnData, hLData, normalizedMatrixDeviation,
          randomAMatrix, hLScale.1, c, hcinv, smul_eq_mul, mul_assoc] using
          hreverse.2.trans herrR
    linarith [hs.1, hs.2]


private theorem scalarSensitivityError_self_eq_zero
    {U : Ch02.Domain d} {a : Homogenization.Vec d → ℝ}
    (ha : ∀ x, 0 < a x) : scalarSensitivityError U a a = 0 := by
  apply le_antisymm
  · apply max_le
    all_goals
      apply scalarRatioLInf_le_of_ae_bound (le_refl 0)
      exact Filter.Eventually.of_forall fun x => by
        rw [div_self (ha x).ne', sub_self, abs_zero]
  · exact scalarSensitivityError_nonneg U a a

private theorem cutoffSensitivityAt_self_le_zero
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (U : Ch02.Domain d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    cutoffSensitivityForwardAt M n n U omega ≤ 0 ∧
      cutoffSensitivityReverseAt M n n U omega ≤ 0 := by
  let hn := aCutoffCoeffOnData M n omega U
  have herr := scalarSensitivityError_self_eq_zero (U := U)
    (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n omega x)
  have hs := normalized_aStarMatrix_and_aMatrix_deviation_le hn hn
  have hstar : normalizedMatrixDeviation
      (randomAStarMatrix M n U omega) (randomAStarMatrix M n U omega) 1 ≤ 0 := by
    simpa [hn, normalizedMatrixDeviation, randomAStarMatrix, herr] using hs.1
  have hmat : normalizedMatrixDeviation
      (randomAMatrix M n U omega) (randomAMatrix M n U omega) 1 ≤ 0 := by
    simpa [hn, normalizedMatrixDeviation, randomAMatrix, herr] using hs.2
  constructor
  · unfold cutoffSensitivityForwardAt
    dsimp only
    rw [div_self (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n omega 0).ne']
    linarith
  · unfold cutoffSensitivityReverseAt
    dsimp only
    rw [div_self (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n omega 0).ne']
    linarith

private theorem cutoffSensitivitySups_le_two_mul_representative
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (k : ℤ)
    (U : Ch02.Domain d)
    (hU : (U : Set (Homogenization.Vec d)) ⊆ openCubeSet (originCube d k))
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {W : ℝ}
    (hW0 : 0 ≤ W)
    (hfield : cutoffRatioOscillationSup n k omega ≤ ENNReal.ofReal W) :
    cutoffSensitivityForwardSup M n U omega ≤ ENNReal.ofReal (2 * W) ∧
      cutoffSensitivityReverseSup M n U omega ≤ ENNReal.ofReal (2 * W) := by
  have at_bound (L : {L : ℕ // n ≤ L}) :
      ENNReal.ofReal (cutoffSensitivityForwardAt M L.1 n U omega) ≤
          ENNReal.ofReal (2 * W) ∧
        ENNReal.ofReal (cutoffSensitivityReverseAt M L.1 n U omega) ≤
          ENNReal.ofReal (2 * W) := by
    by_cases hLn : L.1 = n
    · rw [hLn]
      have hself := cutoffSensitivityAt_self_le_zero M n U omega
      constructor <;> apply ENNReal.ofReal_le_ofReal
      · exact hself.1.trans (mul_nonneg (by norm_num) hW0)
      · exact hself.2.trans (mul_nonneg (by norm_num) hW0)
    · have hnL : n < L.1 := lt_of_le_of_ne L.2 (Ne.symm hLn)
      have hAt := cutoffSensitivityAt_le_oscillation M L.1 n hnL k U hU omega
      let R := Real.exp (cubeOscillation k
        (fun x => cutoffShellSum L.1 (n : ℤ) x omega)) - 1
      have hRfield : ENNReal.ofReal R ≤ cutoffRatioOscillationSup n k omega := by
        unfold cutoffRatioOscillationSup R
        exact le_iSup_of_le L.1 (le_iSup (fun _h : n ≤ L.1 =>
          ENNReal.ofReal (Real.exp (cubeOscillation k
            (fun x => cutoffShellSum L.1 (n : ℤ) x omega)) - 1)) L.2)
      have htwo : ENNReal.ofReal (2 * R) ≤ ENNReal.ofReal (2 * W) := by
        calc
          ENNReal.ofReal (2 * R) = ENNReal.ofReal 2 * ENNReal.ofReal R := by
            rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
          _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal W :=
            mul_le_mul_of_nonneg_left (hRfield.trans hfield) bot_le
          _ = ENNReal.ofReal (2 * W) := by
            rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      exact ⟨(ENNReal.ofReal_le_ofReal hAt.1).trans htwo,
        (ENNReal.ofReal_le_ofReal hAt.2).trans htwo⟩
  constructor
  · unfold cutoffSensitivityForwardSup
    exact iSup_le fun L => (at_bound L).1
  · unfold cutoffSensitivityReverseSup
    exact iSup_le fun L => (at_bound L).2

private theorem paperENNRealLpNorm_le_of_ae_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} {W : Omega → ℝ}
    (hW0 : ∀ omega, 0 ≤ W omega)
    (hWint : Integrable (fun omega => W omega ^ p) mu)
    (hXW : ∀ᵐ omega ∂mu, X omega ≤ ENNReal.ofReal (W omega)) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p X ≤
      ENNReal.ofReal ((∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by
  have hp0 : 0 ≤ p := hp.le
  have hinv0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  have hpow : ∀ᵐ omega ∂mu,
      X omega ^ p ≤ ENNReal.ofReal (W omega ^ p) := by
    filter_upwards [hXW] with omega homega
    calc
      X omega ^ p ≤ (ENNReal.ofReal (W omega)) ^ p :=
        ENNReal.rpow_le_rpow homega hp0
      _ = ENNReal.ofReal (W omega ^ p) :=
        ENNReal.ofReal_rpow_of_nonneg (hW0 omega) hp0
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm
  calc
    (∫⁻ omega, X omega ^ p ∂mu) ^ p⁻¹ ≤
        (∫⁻ omega, ENNReal.ofReal (W omega ^ p) ∂mu) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow (lintegral_mono_ae hpow) hinv0
    _ = (ENNReal.ofReal (∫ omega, W omega ^ p ∂mu)) ^ p⁻¹ := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hWint
        (Filter.Eventually.of_forall fun omega =>
          Real.rpow_nonneg (hW0 omega) p)]
    _ = ENNReal.ofReal ((∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun omega =>
        Real.rpow_nonneg (hW0 omega) p) hinv0]

private theorem paperENNRealLpNorm_le_two_mul_of_ae_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} {W : Omega → ℝ}
    (hW0 : ∀ omega, 0 ≤ W omega)
    (hWint : Integrable (fun omega => W omega ^ p) mu)
    (hXW : ∀ᵐ omega ∂mu, X omega ≤ ENNReal.ofReal (2 * W omega)) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p X ≤
      ENNReal.ofReal (2 * (∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by
  let W2 : Omega → ℝ := fun omega => 2 * W omega
  have hW20 : ∀ omega, 0 ≤ W2 omega := fun omega =>
    mul_nonneg (by norm_num) (hW0 omega)
  have hpowfun : (fun omega => W2 omega ^ p) =
      fun omega => 2 ^ p * W omega ^ p := by
    funext omega
    exact Real.mul_rpow (by norm_num) (hW0 omega)
  have hW2int : Integrable (fun omega => W2 omega ^ p) mu := by
    rw [hpowfun]
    exact hWint.const_mul (2 ^ p)
  have hmain := paperENNRealLpNorm_le_of_ae_le hp hW20 hW2int (by
    simpa [W2] using hXW)
  have hI0 : 0 ≤ ∫ omega, W omega ^ p ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hW0 omega) p
  have hroot : (∫ omega, W2 omega ^ p ∂mu) ^ p⁻¹ =
      2 * (∫ omega, W omega ^ p ∂mu) ^ p⁻¹ := by
    rw [hpowfun, integral_const_mul, Real.mul_rpow
      (Real.rpow_nonneg (by norm_num) p) hI0,
      ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
      mul_inv_cancel₀ hp.ne', Real.rpow_one]
  rwa [hroot] at hmain

private theorem paperLpNorm_le_of_ae_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p : ℝ} (hp : 0 < p) {X W : Omega → ℝ}
    (hW0 : ∀ omega, 0 ≤ W omega)
    (hWint : Integrable (fun omega => W omega ^ p) mu)
    (hXW : ∀ᵐ omega ∂mu, |X omega| ≤ W omega) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperLpNorm mu p X ≤
      ENNReal.ofReal ((∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperLpNorm
  have hpne : ENNReal.ofReal p ≠ 0 := by simp [hp]
  have heLp := SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral
    (p := ENNReal.ofReal p) hpne ENNReal.ofReal_ne_top X mu
  have hpow : ∀ᵐ omega ∂mu,
      ‖X omega‖ₑ ^ (ENNReal.ofReal p).toReal ≤
        ENNReal.ofReal (W omega ^ p) := by
    filter_upwards [hXW] with omega homega
    calc
      ‖X omega‖ₑ ^ (ENNReal.ofReal p).toReal =
          ENNReal.ofReal |X omega| ^ p := by
        rw [ENNReal.toReal_ofReal hp.le, Real.enorm_eq_ofReal_abs]
      _ = ENNReal.ofReal (|X omega| ^ p) :=
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (X omega)) hp.le
      _ ≤ ENNReal.ofReal (W omega ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow (abs_nonneg _) homega hp.le
  calc
    SubdiffusiveProcess.RawLp.eLpNorm X (ENNReal.ofReal p) mu =
        (∫⁻ omega, ‖X omega‖ₑ ^ (ENNReal.ofReal p).toReal ∂mu) ^
          (1 / (ENNReal.ofReal p).toReal) := heLp
    _ = (∫⁻ omega, ‖X omega‖ₑ ^ (ENNReal.ofReal p).toReal ∂mu) ^ p⁻¹ := by
      rw [ENNReal.toReal_ofReal hp.le, one_div]
    _ ≤
        (∫⁻ omega, ENNReal.ofReal (W omega ^ p) ∂mu) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow (lintegral_mono_ae hpow) (inv_nonneg.mpr hp.le)
    _ = (ENNReal.ofReal (∫ omega, W omega ^ p ∂mu)) ^ p⁻¹ := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hWint
        (Filter.Eventually.of_forall fun omega =>
          Real.rpow_nonneg (hW0 omega) p)]
    _ = ENNReal.ofReal ((∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun omega =>
        Real.rpow_nonneg (hW0 omega) p) (inv_nonneg.mpr hp.le)]

private theorem paperLpNorm_le_two_mul_of_ae_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p : ℝ} (hp : 0 < p) {X W : Omega → ℝ}
    (hW0 : ∀ omega, 0 ≤ W omega)
    (hWint : Integrable (fun omega => W omega ^ p) mu)
    (hXW : ∀ᵐ omega ∂mu, |X omega| ≤ 2 * W omega) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperLpNorm mu p X ≤
      ENNReal.ofReal (2 * (∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by
  let W2 : Omega → ℝ := fun omega => 2 * W omega
  have hW20 : ∀ omega, 0 ≤ W2 omega := fun omega =>
    mul_nonneg (by norm_num) (hW0 omega)
  have hpowfun : (fun omega => W2 omega ^ p) =
      fun omega => 2 ^ p * W omega ^ p := by
    funext omega
    exact Real.mul_rpow (by norm_num) (hW0 omega)
  have hW2int : Integrable (fun omega => W2 omega ^ p) mu := by
    rw [hpowfun]
    exact hWint.const_mul (2 ^ p)
  have hmain := paperLpNorm_le_of_ae_le hp hW20 hW2int (by
    simpa only [W2] using hXW)
  have hI0 : 0 ≤ ∫ omega, W omega ^ p ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hW0 omega) p
  have hroot : (∫ omega, W2 omega ^ p ∂mu) ^ p⁻¹ =
      2 * (∫ omega, W omega ^ p ∂mu) ^ p⁻¹ := by
    rw [hpowfun, integral_const_mul, Real.mul_rpow
      (Real.rpow_nonneg (by norm_num) p) hI0,
      ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
      mul_inv_cancel₀ hp.ne', Real.rpow_one]
  rwa [hroot] at hmain


/-- The original finite/anchored callers use cutoffs and a proof-local scalar c.
Their continuity supplies both actual ratio measurability witnesses independently. -/

private noncomputable def infraredApproxConst (d : ℕ) : ℝ :=
  1 + 8 * gammaMomentConst 2 * Real.sqrt 2 * shellSensitivityConst d +
    shellSensitivityConst d ^ 2 +
    4 * finiteFieldMomentConst d + finiteFieldMomentExpConst d

private theorem finiteFieldConst_nonneg (d : ℕ) : 0 ≤ finiteFieldConst d := by
  unfold finiteFieldConst coveredLowBlockConst
  exact mul_nonneg (gammaTriangleConst_pos (σ := 2)).le
    (add_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) smallCubeBlockConst_pos.le)
      smallCubeBlockConst_pos.le)

private theorem finiteFieldMomentConst_nonneg (d : ℕ) :
    0 ≤ finiteFieldMomentConst d := by
  unfold finiteFieldMomentConst
  have hlog : 0 ≤ Real.log 2 / 2 := by positivity
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (gammaMomentConst_pos (by norm_num)).le)
      (Real.sqrt_nonneg 2))
    (add_nonneg (finiteFieldConst_nonneg d) hlog)

private theorem finiteFieldMomentExpConst_nonneg (d : ℕ) :
    0 ≤ finiteFieldMomentExpConst d := by
  unfold finiteFieldMomentExpConst
  have hlog : 0 ≤ Real.log 2 / 2 := by positivity
  positivity

private theorem infraredLeading_nonneg (d : ℕ) :
    0 ≤ 8 * gammaMomentConst 2 * Real.sqrt 2 * shellSensitivityConst d := by
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (gammaMomentConst_pos (by norm_num)).le)
      (Real.sqrt_nonneg 2))
    (shellSensitivityConst_pos d).le

private theorem infraredApproxConst_pos (d : ℕ) : 0 < infraredApproxConst d := by
  unfold infraredApproxConst
  have hlead := infraredLeading_nonneg d
  have hsquare : 0 ≤ shellSensitivityConst d ^ 2 := sq_nonneg _
  have hF := finiteFieldMomentConst_nonneg d
  have hE := finiteFieldMomentExpConst_nonneg d
  nlinarith

private theorem infraredApproxConst_prefactor_large (d : ℕ) :
    8 * gammaMomentConst 2 * Real.sqrt 2 * shellSensitivityConst d ≤
      infraredApproxConst d := by
  unfold infraredApproxConst
  have hg := (gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2)).le
  have hs := (shellSensitivityConst_pos d).le
  have hF := finiteFieldMomentConst_nonneg d
  have hE := finiteFieldMomentExpConst_nonneg d
  nlinarith [sq_nonneg (shellSensitivityConst d)]

private theorem infraredApproxConst_shell_sq_large (d : ℕ) :
    shellSensitivityConst d ^ 2 ≤ infraredApproxConst d := by
  unfold infraredApproxConst
  have hK := infraredLeading_nonneg d
  have hF := finiteFieldMomentConst_nonneg d
  have hE := finiteFieldMomentExpConst_nonneg d
  linarith

private theorem infraredApproxConst_finite_prefactor_large (d : ℕ) :
    4 * finiteFieldMomentConst d ≤ infraredApproxConst d := by
  unfold infraredApproxConst
  have hK := infraredLeading_nonneg d
  have hS : 0 ≤ shellSensitivityConst d ^ 2 := sq_nonneg _
  have hE := finiteFieldMomentExpConst_nonneg d
  linarith

private theorem infraredApproxConst_finite_exp_large (d : ℕ) :
    finiteFieldMomentExpConst d ≤ infraredApproxConst d := by
  unfold infraredApproxConst
  have hK := infraredLeading_nonneg d
  have hS : 0 ≤ shellSensitivityConst d ^ 2 := sq_nonneg _
  have hF := finiteFieldMomentConst_nonneg d
  linarith

theorem infrared_approx_cutoffs {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (k : ℤ)
        (xi : ℝ) (U : Ch02.Domain d),
        1 ≤ xi →
        (U : Set (Homogenization.Vec d)) ⊆
          Homogenization.openCubeSet (Homogenization.originCube d k) →
        paperENNRealLpNorm M.P.toMeasure xi
              (cutoffSensitivityForwardSup M n U) +
            paperENNRealLpNorm M.P.toMeasure xi
              (cutoffSensitivityReverseSup M n U) ≤
          ENNReal.ofReal
            (C * Real.sqrt xi * M.delta *
              Real.rpow 3 ((k : ℝ) - n) *
              Real.exp (C * xi * M.delta ^ 2 *
                Real.rpow 3 (2 * ((k : ℝ) - n)))) ∧
        ∀ m : ℕ, n < m →
          paperLpNorm M.P.toMeasure xi
              (paperTwoTermLpObservable xi
                (fun omega => normalizedMatrixDeviation
                  (randomAStarMatrix M m U omega) (randomAStarMatrix M n U omega) 1)
                (fun omega => normalizedMatrixDeviation
                  (randomAMatrix M m U omega) (randomAMatrix M n U omega) 1)) +
            paperLpNorm M.P.toMeasure xi
              (paperTwoTermLpObservable xi
                (fun omega => normalizedMatrixDeviation
                  (randomAStarMatrix M n U omega) (randomAStarMatrix M m U omega) 1)
                (fun omega => normalizedMatrixDeviation
                  (randomAMatrix M n U omega) (randomAMatrix M m U omega) 1)) ≤
            ENNReal.ofReal (C * Real.sqrt xi * M.delta *
                (Real.sqrt ((m - n : ℕ) : ℝ) + max ((k : ℝ) - n) 0) *
              Real.exp (C * xi * M.delta ^ 2 *
                (((m - n : ℕ) : ℝ) + (max ((k : ℝ) - n) 0) ^ 2))) := by
  refine ⟨infraredApproxConst d, infraredApproxConst_pos d, ?_⟩
  intro M n k xi U hxi hU
  have hxiPos : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hxi0 : 0 ≤ xi := hxiPos.le
  have hsqrtXi0 : 0 ≤ Real.sqrt xi := Real.sqrt_nonneg _
  have hdelta0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  constructor
  · let W : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega =>
      Real.exp (sensitivityFieldRepresentative n k omega) - 1
    obtain ⟨hWint, hWroot, hWdom⟩ :=
      infraredhom_approx_cutoffs_large_waves_field M n k xi hxi
    have hW0 : ∀ omega, 0 ≤ W omega := fun omega =>
      sub_nonneg.mpr (Real.one_le_exp
        (sensitivityFieldRepresentative_nonneg n k omega))
    have hsups : ∀ᵐ omega ∂M.P.toMeasure,
        cutoffSensitivityForwardSup M n U omega ≤ ENNReal.ofReal (2 * W omega) ∧
          cutoffSensitivityReverseSup M n U omega ≤ ENNReal.ofReal (2 * W omega) := by
      filter_upwards [hWdom] with omega homega
      exact cutoffSensitivitySups_le_two_mul_representative
        M n k U hU omega (hW0 omega) homega
    have hfwd := paperENNRealLpNorm_le_two_mul_of_ae_le hxiPos hW0 hWint
      (hsups.mono fun omega h => h.1)
    have hrev := paperENNRealLpNorm_le_two_mul_of_ae_le hxiPos hW0 hWint
      (hsups.mono fun omega h => h.2)
    let Iroot := (∫ omega, W omega ^ xi ∂M.P.toMeasure) ^ xi⁻¹
    let A := shellSensitivityConst d * M.delta * (3 : ℝ) ^ (k - (n : ℤ))
    let B := 2 * gammaMomentConst 2 * Real.sqrt (2 * xi) * A *
      Real.exp (xi * A ^ 2)
    have hIroot0 : 0 ≤ Iroot := Real.rpow_nonneg (integral_nonneg fun omega =>
      Real.rpow_nonneg (hW0 omega) xi) _
    have hB : Iroot ≤ B := by simpa [Iroot, B, A, W] using hWroot
    have hmoment :
        paperENNRealLpNorm M.P.toMeasure xi (cutoffSensitivityForwardSup M n U) +
            paperENNRealLpNorm M.P.toMeasure xi (cutoffSensitivityReverseSup M n U) ≤
          ENNReal.ofReal (4 * B) := by
      calc
        _ ≤ ENNReal.ofReal (2 * Iroot) + ENNReal.ofReal (2 * Iroot) :=
          add_le_add hfwd hrev
        _ = ENNReal.ofReal (4 * Iroot) := by
          rw [← ENNReal.ofReal_add
            (mul_nonneg (by norm_num) hIroot0)
            (mul_nonneg (by norm_num) hIroot0)]
          congr 1
          ring
        _ ≤ ENNReal.ofReal (4 * B) := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hB (by norm_num))
    refine hmoment.trans (ENNReal.ofReal_le_ofReal ?_)
    let r : ℝ := (3 : ℝ) ^ (k - (n : ℤ))
    have hr0 : 0 ≤ r := (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le
    have hrEq : Real.rpow 3 ((k : ℝ) - n) = r := by
      have hcast : ((k : ℝ) - n) = ((k - (n : ℤ) : ℤ) : ℝ) := by norm_num
      rw [hcast]
      change (3 : ℝ) ^ ((k - (n : ℤ) : ℤ) : ℝ) = r
      rw [Real.rpow_intCast]
    have hr2Eq : Real.rpow 3 (2 * ((k : ℝ) - n)) = r ^ 2 := by
      rw [show 2 * ((k : ℝ) - n) = ((k : ℝ) - n) * 2 by ring]
      change (3 : ℝ) ^ (((k : ℝ) - n) * 2) = r ^ 2
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      change Real.rpow (Real.rpow 3 ((k : ℝ) - n)) 2 = r ^ 2
      rw [hrEq]
      exact Real.rpow_natCast r 2
    have hsqrt : Real.sqrt (2 * xi) = Real.sqrt 2 * Real.sqrt xi := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    let P := Real.sqrt xi * M.delta * r
    have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg hsqrtXi0 hdelta0) hr0
    have hExpBase0 : 0 ≤ xi * M.delta ^ 2 * r ^ 2 := by positivity
    have hK := infraredApproxConst_prefactor_large d
    have hE := infraredApproxConst_shell_sq_large d
    have hC0 := (infraredApproxConst_pos d).le
    have hexp : Real.exp (shellSensitivityConst d ^ 2 *
        (xi * M.delta ^ 2 * r ^ 2)) ≤
        Real.exp (infraredApproxConst d *
          (xi * M.delta ^ 2 * r ^ 2)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hE hExpBase0
    change 4 * B ≤ _
    rw [hrEq, hr2Eq]
    calc
      4 * B =
          (8 * gammaMomentConst 2 * Real.sqrt 2 * shellSensitivityConst d) *
            P * Real.exp (shellSensitivityConst d ^ 2 *
              (xi * M.delta ^ 2 * r ^ 2)) := by
        dsimp [B, A, P, r]
        rw [hsqrt]
        ring_nf
      _ ≤ infraredApproxConst d * P *
          Real.exp (shellSensitivityConst d ^ 2 *
            (xi * M.delta ^ 2 * r ^ 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hK hP0) (Real.exp_pos _).le
      _ ≤ infraredApproxConst d * P *
          Real.exp (infraredApproxConst d *
            (xi * M.delta ^ 2 * r ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hC0 hP0)
      _ = infraredApproxConst d * Real.sqrt xi * M.delta * r *
          Real.exp (infraredApproxConst d * xi * M.delta ^ 2 * r ^ 2) := by
        dsimp [P]
        ring_nf
  · intro m hnm
    obtain ⟨W, hWmeas, hW0, hWint, hWroot, hWfwd, hWinv⟩ :=
      aman_Linfty_moments_source_bound M m n k hnm xi hxi
    have hdev : ∀ omega,
        normalizedMatrixDeviation
            (randomAStarMatrix M m U omega) (randomAStarMatrix M n U omega) 1 ≤ W omega ∧
          normalizedMatrixDeviation
            (randomAMatrix M m U omega) (randomAMatrix M n U omega) 1 ≤ W omega ∧
          normalizedMatrixDeviation
            (randomAStarMatrix M n U omega) (randomAStarMatrix M m U omega) 1 ≤ W omega ∧
          normalizedMatrixDeviation
            (randomAMatrix M n U omega) (randomAMatrix M m U omega) 1 ≤ W omega :=
      fun omega => finite_matrix_deviations_le M m n k hnm U hU omega
        (hW0 omega) (hWfwd omega) (hWinv omega)
    let Xforward := paperTwoTermLpObservable xi
      (fun omega => normalizedMatrixDeviation
        (randomAStarMatrix M m U omega) (randomAStarMatrix M n U omega) 1)
      (fun omega => normalizedMatrixDeviation
        (randomAMatrix M m U omega) (randomAMatrix M n U omega) 1)
    let Xreverse := paperTwoTermLpObservable xi
      (fun omega => normalizedMatrixDeviation
        (randomAStarMatrix M n U omega) (randomAStarMatrix M m U omega) 1)
      (fun omega => normalizedMatrixDeviation
        (randomAMatrix M n U omega) (randomAMatrix M m U omega) 1)
    have hXforward : ∀ omega, |Xforward omega| ≤ 2 * W omega := by
      intro omega
      have hnonneg : 0 ≤ Xforward omega := by
        dsimp [Xforward, paperTwoTermLpObservable]
        positivity
      rw [abs_of_nonneg hnonneg]
      calc
        Xforward omega ≤
            max (normalizedMatrixDeviation
              (randomAStarMatrix M m U omega) (randomAStarMatrix M n U omega) 1) 0 +
            max (normalizedMatrixDeviation
              (randomAMatrix M m U omega) (randomAMatrix M n U omega) 1) 0 :=
          paperTwoTermLpObservable_le_add hxi _ _ omega
        _ ≤ W omega + W omega := add_le_add
          (by rw [max_eq_left (by
            unfold normalizedMatrixDeviation
            exact Ch02.matrixOperatorNorm_nonneg _)]; exact (hdev omega).1)
          (by rw [max_eq_left (by
            unfold normalizedMatrixDeviation
            exact Ch02.matrixOperatorNorm_nonneg _)]; exact (hdev omega).2.1)
        _ = 2 * W omega := by ring
    have hXreverse : ∀ omega, |Xreverse omega| ≤ 2 * W omega := by
      intro omega
      have hnonneg : 0 ≤ Xreverse omega := by
        dsimp [Xreverse, paperTwoTermLpObservable]
        positivity
      rw [abs_of_nonneg hnonneg]
      calc
        Xreverse omega ≤
            max (normalizedMatrixDeviation
              (randomAStarMatrix M n U omega) (randomAStarMatrix M m U omega) 1) 0 +
            max (normalizedMatrixDeviation
              (randomAMatrix M n U omega) (randomAMatrix M m U omega) 1) 0 :=
          paperTwoTermLpObservable_le_add hxi _ _ omega
        _ ≤ W omega + W omega := add_le_add
          (by rw [max_eq_left (by
            unfold normalizedMatrixDeviation
            exact Ch02.matrixOperatorNorm_nonneg _)]; exact (hdev omega).2.2.1)
          (by rw [max_eq_left (by
            unfold normalizedMatrixDeviation
            exact Ch02.matrixOperatorNorm_nonneg _)]; exact (hdev omega).2.2.2)
        _ = 2 * W omega := by ring
    have hLpForward := paperLpNorm_le_two_mul_of_ae_le hxiPos hW0 hWint
      (Filter.Eventually.of_forall hXforward)
    have hLpReverse := paperLpNorm_le_two_mul_of_ae_le hxiPos hW0 hWint
      (Filter.Eventually.of_forall hXreverse)
    let Iroot := (∫ omega, W omega ^ xi ∂M.P.toMeasure) ^ xi⁻¹
    let S := Real.sqrt ((m - n : ℕ) : ℝ) + max 0 ((k : ℝ) - n)
    let Q := ((m - n : ℕ) : ℝ) + (max 0 ((k : ℝ) - n)) ^ 2
    let B := finiteFieldMomentConst d * Real.sqrt xi * M.delta * S *
      Real.exp (finiteFieldMomentExpConst d * xi * M.delta ^ 2 * Q)
    have hIroot0 : 0 ≤ Iroot := Real.rpow_nonneg (integral_nonneg fun omega =>
      Real.rpow_nonneg (hW0 omega) xi) _
    have hIB : Iroot ≤ B := by simpa [Iroot, B, S, Q] using hWroot
    have hmoment : paperLpNorm M.P.toMeasure xi Xforward +
        paperLpNorm M.P.toMeasure xi Xreverse ≤ ENNReal.ofReal (4 * B) := by
      calc
        _ ≤ ENNReal.ofReal (2 * Iroot) + ENNReal.ofReal (2 * Iroot) :=
          add_le_add hLpForward hLpReverse
        _ = ENNReal.ofReal (4 * Iroot) := by
          rw [← ENNReal.ofReal_add
            (mul_nonneg (by norm_num) hIroot0)
            (mul_nonneg (by norm_num) hIroot0)]
          congr 1
          ring
        _ ≤ ENNReal.ofReal (4 * B) := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hIB (by norm_num))
    change paperLpNorm M.P.toMeasure xi Xforward +
      paperLpNorm M.P.toMeasure xi Xreverse ≤ _
    refine hmoment.trans (ENNReal.ofReal_le_ofReal ?_)
    have hS0 : 0 ≤ S := add_nonneg (Real.sqrt_nonneg _) (le_max_left _ _)
    have hQ0 : 0 ≤ Q := add_nonneg (by positivity) (sq_nonneg _)
    have hP0 : 0 ≤ Real.sqrt xi * M.delta * S := by positivity
    have hExpBase0 : 0 ≤ xi * M.delta ^ 2 * Q := by positivity
    have hK := infraredApproxConst_finite_prefactor_large d
    have hE := infraredApproxConst_finite_exp_large d
    have hC0 := (infraredApproxConst_pos d).le
    have hexp : Real.exp (finiteFieldMomentExpConst d *
        (xi * M.delta ^ 2 * Q)) ≤
        Real.exp (infraredApproxConst d * (xi * M.delta ^ 2 * Q)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hE hExpBase0
    calc
      4 * B = (4 * finiteFieldMomentConst d) *
          (Real.sqrt xi * M.delta * S) *
            Real.exp (finiteFieldMomentExpConst d *
              (xi * M.delta ^ 2 * Q)) := by
        dsimp [B]
        ring_nf
      _ ≤ infraredApproxConst d * (Real.sqrt xi * M.delta * S) *
          Real.exp (finiteFieldMomentExpConst d *
            (xi * M.delta ^ 2 * Q)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hK hP0) (Real.exp_pos _).le
      _ ≤ infraredApproxConst d * (Real.sqrt xi * M.delta * S) *
          Real.exp (infraredApproxConst d *
            (xi * M.delta ^ 2 * Q)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hC0 hP0)
      _ = infraredApproxConst d * Real.sqrt xi * M.delta *
          (Real.sqrt ((m - n : ℕ) : ℝ) + max ((k : ℝ) - n) 0) *
          Real.exp (infraredApproxConst d * xi * M.delta ^ 2 *
            (((m - n : ℕ) : ℝ) + (max ((k : ℝ) - n) 0) ^ 2)) := by
        dsimp [S, Q]
        rw [max_comm 0 ((k : ℝ) - n)]
        ring_nf

end SubdiffusiveProcess.Providers.Section3
