module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMixedCutoffPatching
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteVolumeAssembly
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Averages

@[expose] public section

/-!
# Concrete finite-volume primal one-step assembly

This file inserts the literal mixed-cutoff source-cell patch into the random
Dirichlet coarse matrix.  It is the samplewise variational part of
paper label `l.one.step.upper`; no measurability of the selected cell minimizers
is used.
-/

open MeasureTheory Homogenization
open Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Common pointwise ellipticity data for one cutoff on a finite descendant
partition.  The witness is used only to form deterministic cell minimizers;
no measurable selection from this carrier is ever integrated. -/
structure OneStepDescendantEllipticityData
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L j : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (Q : TriadicCube d) where
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  isElliptic : ∀ R ∈ descendantsAtDepth Q j,
    IsEllipticFieldOn lam Lam (openCubeSet R)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))

/-- The compactness package in `OneStepConcreteCellCarrier` supplies the
finite-partition ellipticity data at every sample. -/
noncomputable def oneStepDescendantEllipticityData
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L j : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (Q : TriadicCube d) :
    OneStepDescendantEllipticityData M L j omega Q :=
  Classical.choice <| by
    obtain ⟨lam, Lam, hlam, hEll⟩ :=
      exists_isEllipticFieldOn_aCutoff_descendants (j := j) M L omega Q
    exact ⟨⟨lam, Lam, hlam, hEll⟩⟩

/-- The high-cutoff random Dirichlet quadratic is bounded by the normalized
sum of the principal, mixed, and oscillatory selected cell energies. -/
theorem half_randomAMatrix_le_mixedCutoff_selectedCellEnergies
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamLow LamLow (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)))
    (hHigh : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamHigh LamHigh (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega))) :
    let P := fun S ↦
      oneStepDirichletCellMeanField M n h p Q S omega hh
    let F := fun S ↦
      oneStepDirichletCellFluctuationField M n h p Q S omega hh
    let aLow := scalarCoeffField
      (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
    let aHigh := scalarCoeffField
      (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)
    (1 / 2 : ℝ) * vecDot p
        (matVecMul (randomAMatrix M (n + h)
          (Homogenization.Book.Ch02.cubeDomain Q) omega) p) ≤
      descendantsAverage Q j (fun R ↦
        if hR : R ∈ descendantsAtDepth Q j then
          let principal := oneStepSelectedDirichletCell aLow P hLow
            (oneStepDirichletCellMeanField_memVectorL2_of_descendant
              M n h p Q omega hh) R hR
          let oscillatory := oneStepSelectedDirichletCell aHigh F hHigh
            (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
              M n h p Q omega hh) R hR
          (1 / 2 : ℝ) * volumeAverage (openCubeSet R) (fun x ↦
              vecDot (principal.field x)
                (matVecMul (aHigh x) (principal.field x))) +
            volumeAverage (openCubeSet R) (fun x ↦
              vecDot (principal.field x)
                (matVecMul (aHigh x) (oscillatory.field x))) +
            (1 / 2 : ℝ) * volumeAverage (openCubeSet R) (fun x ↦
              vecDot (oscillatory.field x)
                (matVecMul (aHigh x) (oscillatory.field x)))
        else 0) := by
  dsimp only
  let aLow := scalarCoeffField
    (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
  let aHigh := scalarCoeffField
    (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)
  let P := fun S ↦ oneStepDirichletCellMeanField M n h p Q S omega hh
  let F := fun S ↦ oneStepDirichletCellFluctuationField M n h p Q S omega hh
  let patches := oneStepSelectedMixedCutoffDirichletPatchList Q j aLow aHigh
    P F hLow hHigh
      (oneStepDirichletCellMeanField_memVectorL2_of_descendant
        M n h p Q omega hh)
      (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
        M n h p Q omega hh)
  let w := oneStepTriadicDirichletSolution M n h p Q omega hh
  have hvar := vecDot_aMatrix_le_patchedCompetitorEnergy
    (aCutoffCoeffOnData M (n + h) omega
      (Homogenization.Book.Ch02.cubeDomain Q))
    (fun x ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (n + h) omega x).le)
    p w patches
  have hvarHalf := mul_le_mul_of_nonneg_left hvar (by norm_num : (0 : ℝ) ≤ 1 / 2)
  change (1 / 2 : ℝ) * vecDot p
      (matVecMul (randomAMatrix M (n + h)
        (Homogenization.Book.Ch02.cubeDomain Q) omega) p) ≤ _
  rw [show randomAMatrix M (n + h)
      (Homogenization.Book.Ch02.cubeDomain Q) omega =
        aMatrix (Homogenization.Book.Ch02.cubeDomain Q)
          (aCutoffCoeffOnData M (n + h) omega
            (Homogenization.Book.Ch02.cubeDomain Q)).toCoeffOn by rfl]
  refine hvarHalf.trans_eq ?_
  let energy : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x *
      vecNormSq (p + (oneStepPatchedCompetitor w patches).toH1Function.grad x)
  have henergyInt : IntegrableOn energy (openCubeSet Q) := by
    obtain ⟨lam, Lam, hlam, hEll⟩ :=
      exists_isEllipticFieldOn_aCutoff_descendants (j := 0)
        M (n + h) omega Q
    have hEllQ : IsEllipticFieldOn lam Lam (openCubeSet Q) aHigh := by
      exact hEll Q (by simp)
    have htotal : MemVectorL2 (openCubeSet Q)
        (fun x ↦ p + (oneStepPatchedCompetitor w patches).toH1Function.grad x) := by
      let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
        isFiniteMeasure_volumeMeasureOn_openCubeSet Q
      exact (MeasureTheory.memLp_const p).add
        (oneStepPatchedCompetitor w patches).toH1Function.grad_memVectorL2
    have hflux := memVectorL2_matVecMul_of_isEllipticFieldOn hEllQ htotal
    have hint := integrableOn_vecDot_of_memVectorL2 htotal hflux
    refine hint.congr ?_
    filter_upwards with x
    dsimp only [energy, aHigh, scalarCoeffField]
    rw [matVecMul_scalarMatrix, vecDot_smul_right]
    rfl
  have hpartition :=
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j energy
        (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr henergyInt)
  unfold dirichletEnergyOn'
  change (1 / 2 : ℝ) *
      ((volume (openCubeSet Q)).toReal⁻¹ *
        ∫ x in openCubeSet Q, energy x ∂volume) = _
  have hnormalized :
      (volume (openCubeSet Q)).toReal⁻¹ *
          ∫ x in openCubeSet Q, energy x ∂volume =
        cubeAverage Q energy := by
    unfold cubeAverage
    rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet,
      volume_openCubeSet_toReal]
  rw [hnormalized, hpartition]
  unfold descendantsAverage
  have hdistribute :
      (1 / 2 : ℝ) *
          (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth Q j, cubeAverage R energy) =
        (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j,
            (1 / 2 : ℝ) * cubeAverage R energy) := by
    calc
      (1 / 2 : ℝ) *
            (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtDepth Q j, cubeAverage R energy) =
          ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ((1 / 2 : ℝ) *
              ∑ R ∈ descendantsAtDepth Q j, cubeAverage R energy) := by
            ring
      _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth Q j,
              (1 / 2 : ℝ) * cubeAverage R energy := by
            rw [Finset.mul_sum]
  rw [hdistribute]
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  rw [dite_eq_left hR]
  let principal := oneStepSelectedDirichletCell aLow P hLow
    (oneStepDirichletCellMeanField_memVectorL2_of_descendant
      M n h p Q omega hh) R hR
  let oscillatory := oneStepSelectedDirichletCell aHigh F hHigh
    (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
      M n h p Q omega hh) R hR
  have hlocal : ∀ᵐ x ∂volume.restrict (cubeSet R),
      energy x =
        vecDot (principal.field x + oscillatory.field x)
          (matVecMul (aHigh x) (principal.field x + oscillatory.field x)) := by
    have hmem : ∀ᵐ x ∂volume.restrict (cubeSet R), x ∈ openCubeSet R := by
      rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
      exact ae_restrict_mem (measurableSet_openCubeSet R)
    filter_upwards [hmem] with x hx
    have hslope := oneStepDirichlet_mixedCutoff_patchedTotalSlope_eq_of_mem
      M n h p Q omega hh aLow aHigh hLow hHigh R hR hx
    dsimp only [energy]
    rw [hslope]
    dsimp only [aHigh, scalarCoeffField]
    rw [matVecMul_scalarMatrix, vecDot_smul_right]
    rfl
  have hsplit : ∀ x,
      (1 / 2 : ℝ) * vecDot (principal.field x + oscillatory.field x)
          (matVecMul (aHigh x) (principal.field x + oscillatory.field x)) =
        (1 / 2 : ℝ) * vecDot (principal.field x)
            (matVecMul (aHigh x) (principal.field x)) +
          vecDot (principal.field x)
            (matVecMul (aHigh x) (oscillatory.field x)) +
          (1 / 2 : ℝ) * vecDot (oscillatory.field x)
            (matVecMul (aHigh x) (oscillatory.field x)) := by
    intro x
    exact oneStep_half_quadratic_add_eq (aHigh x)
      (scalarMatrix_isSymm _) _ _
  let fp : Vec d → ℝ := fun x ↦ vecDot (principal.field x)
    (matVecMul (aHigh x) (principal.field x))
  let fm : Vec d → ℝ := fun x ↦ vecDot (principal.field x)
    (matVecMul (aHigh x) (oscillatory.field x))
  let fo : Vec d → ℝ := fun x ↦ vecDot (oscillatory.field x)
    (matVecMul (aHigh x) (oscillatory.field x))
  have hpMem : MemVectorL2 (openCubeSet R) principal.field :=
    (oneStepDirichletCellMeanField_memVectorL2_of_descendant
      M n h p Q omega hh R hR).add
        principal.correction.toH1Function.grad_memVectorL2
  have hoMem : MemVectorL2 (openCubeSet R) oscillatory.field :=
    (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
      M n h p Q omega hh R hR).add
        oscillatory.correction.toH1Function.grad_memVectorL2
  have hpFlux := memVectorL2_matVecMul_of_isEllipticFieldOn
    (hHigh R hR) hpMem
  have hoFlux := memVectorL2_matVecMul_of_isEllipticFieldOn
    (hHigh R hR) hoMem
  have hfpOpen : IntegrableOn fp (openCubeSet R) :=
    integrableOn_vecDot_of_memVectorL2 hpMem hpFlux
  have hfmOpen : IntegrableOn fm (openCubeSet R) :=
    integrableOn_vecDot_of_memVectorL2 hpMem hoFlux
  have hfoOpen : IntegrableOn fo (openCubeSet R) :=
    integrableOn_vecDot_of_memVectorL2 hoMem hoFlux
  have hfp : IntegrableOn fp (cubeSet R) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hfpOpen
  have hfm : IntegrableOn fm (cubeSet R) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hfmOpen
  have hfo : IntegrableOn fo (cubeSet R) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hfoOpen
  have hcubeEq : cubeAverage R (fun x ↦ (1 / 2 : ℝ) * energy x) =
      cubeAverage R (fun x ↦
        ((1 / 2 : ℝ) * fp x + fm x) + (1 / 2 : ℝ) * fo x) := by
    unfold cubeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hlocal] with x hx
    rw [hx, hsplit]
  rw [show (1 / 2 : ℝ) * cubeAverage R energy =
      cubeAverage R (fun x ↦ (1 / 2 : ℝ) * energy x) by
        rw [cubeAverage_const_mul]]
  rw [hcubeEq,
    cubeAverage_add_of_integrableOn R
      (fun x ↦ (1 / 2 : ℝ) * fp x + fm x)
      (fun x ↦ (1 / 2 : ℝ) * fo x)
      ((hfp.const_mul _).add hfm) (hfo.const_mul _),
    cubeAverage_add_of_integrableOn R
      (fun x ↦ (1 / 2 : ℝ) * fp x) fm (hfp.const_mul _) hfm,
    cubeAverage_const_mul, cubeAverage_const_mul]
  rw [← oneStep_volumeAverage_openCubeSet_eq_cubeAverage R fp,
    ← oneStep_volumeAverage_openCubeSet_eq_cubeAverage R fm,
    ← oneStep_volumeAverage_openCubeSet_eq_cubeAverage R fo]

/-- Spatial Cauchy--Schwarz for the mixed-cutoff selected fields.  The
principal correction is selected with the lower coefficient, while both
energies and the cross term are evaluated with the higher coefficient. -/
theorem abs_oneStepSelectedDirichletCell_mixedCutoff_le_sqrt_energies
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamLow LamLow (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)))
    (hHigh : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamHigh LamHigh (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)))
    (hR : R ∈ descendantsAtDepth Q j) :
    let aLow := scalarCoeffField
      (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
    let aHigh := scalarCoeffField
      (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)
    let P := fun S ↦ oneStepDirichletCellMeanField M n h p Q S omega hh
    let F := fun S ↦
      oneStepDirichletCellFluctuationField M n h p Q S omega hh
    let principal := oneStepSelectedDirichletCell aLow P hLow
      (oneStepDirichletCellMeanField_memVectorL2_of_descendant
        M n h p Q omega hh) R hR
    let oscillatory := oneStepSelectedDirichletCell aHigh F hHigh
      (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
        M n h p Q omega hh) R hR
    |volumeAverage (openCubeSet R) (fun x ↦
        vecDot (principal.field x)
          (matVecMul (aHigh x) (oscillatory.field x)))| ≤
      Real.sqrt (volumeAverage (openCubeSet R) (fun x ↦
        vecDot (principal.field x)
          (matVecMul (aHigh x) (principal.field x)))) *
      Real.sqrt (volumeAverage (openCubeSet R) (fun x ↦
        vecDot (oscillatory.field x)
          (matVecMul (aHigh x) (oscillatory.field x)))) := by
  dsimp only
  let aLow := scalarCoeffField
    (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
  let aHigh := scalarCoeffField
    (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)
  let P := fun S ↦ oneStepDirichletCellMeanField M n h p Q S omega hh
  let F := fun S ↦
    oneStepDirichletCellFluctuationField M n h p Q S omega hh
  let principal := oneStepSelectedDirichletCell aLow P hLow
    (oneStepDirichletCellMeanField_memVectorL2_of_descendant
      M n h p Q omega hh) R hR
  let oscillatory := oneStepSelectedDirichletCell aHigh F hHigh
    (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
      M n h p Q omega hh) R hR
  have hpMem : MemVectorL2 (openCubeSet R) principal.field :=
    (oneStepDirichletCellMeanField_memVectorL2_of_descendant
      M n h p Q omega hh R hR).add
        principal.correction.toH1Function.grad_memVectorL2
  have hoMem : MemVectorL2 (openCubeSet R) oscillatory.field :=
    (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
      M n h p Q omega hh R hR).add
        oscillatory.correction.toH1Function.grad_memVectorL2
  have hpFlux := memVectorL2_matVecMul_of_isEllipticFieldOn
    (hHigh R hR) hpMem
  have hoFlux := memVectorL2_matVecMul_of_isEllipticFieldOn
    (hHigh R hR) hoMem
  have hCross : IntegrableOn (fun x ↦
      vecDot (principal.field x) (matVecMul (aHigh x) (oscillatory.field x)))
      (openCubeSet R) := integrableOn_vecDot_of_memVectorL2 hpMem hoFlux
  have hPrincipal : IntegrableOn (fun x ↦
      vecDot (principal.field x) (matVecMul (aHigh x) (principal.field x)))
      (openCubeSet R) := integrableOn_vecDot_of_memVectorL2 hpMem hpFlux
  have hOscillatory : IntegrableOn (fun x ↦
      vecDot (oscillatory.field x) (matVecMul (aHigh x) (oscillatory.field x)))
      (openCubeSet R) := integrableOn_vecDot_of_memVectorL2 hoMem hoFlux
  apply abs_volumeAverage_openCubeSet_matrix_cross_le_sqrt_energies
    R aHigh principal.field oscillatory.field
  · exact integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hCross)
  · exact integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hPrincipal)
  · exact integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hOscillatory)
  · exact Filter.Eventually.of_forall fun _ ↦ scalarMatrix_isSymm _
  · exact Filter.Eventually.of_forall fun x v ↦ by
      dsimp only [aHigh, scalarCoeffField]
      rw [matVecMul_scalarMatrix, vecDot_smul_right]
      exact mul_nonneg (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (n + h) omega x).le
        (vecNormSq_nonneg v)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
