module

public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
public import SubdiffusiveProcess.Paper.inputs_Sf_besov_finite
public import SubdiffusiveProcess.Paper.inputs_Sf_besov_embedding
public import SubdiffusiveProcess.Paper.inputs_classical_e4_interpolation
public import SubdiffusiveProcess.Paper.inputs_classical_e4_rellich
public import SubdiffusiveProcess.Paper.inputs_classical_e4_extension
public import SubdiffusiveProcess.Paper.inputs_classical_e4_zero_extension
public import SubdiffusiveProcess.Paper.inputs_classical_e4_h1_finite
public import SubdiffusiveProcess.Paper.inputs_classical_e4_trace

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem inputs_Sf_witness (d : ℕ) (hd : 2 ≤ d) :
    Nonempty (SobolevFoundationalInput d hd) := by
  let halfOrder : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  obtain ⟨cExt, hcExt, hExt⟩ :=
    inputs_classical_e4_extension d hd threeQuarterOrder
  obtain ⟨cInterp, hcInterp, hInterp⟩ :=
    inputs_classical_e4_interpolation d hd threeQuarterOrder halfOrder (by
      norm_num [halfOrder, threeQuarterOrder])
  obtain ⟨cZero, hcZero, hZero⟩ :=
    inputs_classical_e4_zero_extension d hd threeQuarterOrder (by
      norm_num [threeQuarterOrder])
  let cCommon := max cExt (max cInterp cZero)
  have hcExtLe : cExt ≤ cCommon := by
    exact le_max_left _ _
  have hcInterpLe : cInterp ≤ cCommon := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hcZeroLe : cZero ≤ cCommon := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  let CB : ℝ → ℝ := fun s =>
    if hs : s ∈ Set.Ioo (0 : ℝ) (1 / 4) then
      Classical.choose (inputs_Sf_besov_embedding d hd s hs)
    else 1
  let CT : ℝ → ℝ := fun beta =>
    if hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1 then
      Classical.choose (inputs_classical_e4_trace d hd beta hbeta)
    else 1
  let bSem : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ℝ → DomainL2 (centeredCube z r hr) → ℝ := fun z r hr t v =>
    r ^ (-t) * (iSup fun j : ℕ =>
      Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) t 2
        (fun x => v (fun i : Fin d => z i + r * x i))
        (inputs_poincare_positive_integrable d hd z r hr v) j).toReal
  refine ⟨{
    C := cCommon
    C_pos := lt_of_lt_of_le hcExt (le_max_left _ _)
    CBesov := CB
    CBesov_pos := ?_
    besovSeminorm := bSem
    besovSeminorm_nonneg := ?_
    positive_integrable := ?_
    besovSeminorm_eq := ?_
    besov_finite_H1 := ?_
    h1_fractional_finite := ?_
    besov_embedding := ?_
    extension := ?_
    interpolation := ?_
    compactEmbedding := ?_
    zeroExtension := ?_
    CTrace := CT
    CTrace_pos := ?_
    traceRightInverse := ?_
  }⟩
  · intro s hs
    dsimp [CB]
    rw [dif_pos hs]
    exact (Classical.choose_spec (inputs_Sf_besov_embedding d hd s hs)).1
  · intro z r hr t v
    dsimp [bSem]
    positivity
  · intro z r hr v
    exact inputs_poincare_positive_integrable d hd z r hr v
  · intro z r hr t ht v
    rfl
  · intro z r hr t ht u
    exact inputs_Sf_besov_finite d hd z r hr t ht u
  · intro z r hr u
    exact inputs_classical_e4_h1_finite d hd threeQuarterOrder z r hr u
  · intro s hs z r hr hr1 v hfinite
    dsimp [CB, bSem]
    rw [dif_pos hs]
    exact (Classical.choose_spec (inputs_Sf_besov_embedding d hd s hs)).2
      z r hr hr1 v hfinite
  · intro z r hr hr1 v hv
    obtain ⟨V, hV, hnorm⟩ := hExt z r hr hr1 v hv
    refine ⟨V, hV, ?_⟩
    have hSq : 0 ≤ cubeFractionalSqNorm hd z r hr threeQuarterOrder v := by
      have hvol := centeredCube_volume_pos z hr
      unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
      positivity
    exact le_trans hnorm (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcExtLe hSq))
  · intro z r hr hr1 v hv
    have h := hInterp z r hr hr1 v hv
    have hvol : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      centeredCube_volume_pos z hr
    have hbound :
        Real.sqrt (cubeFractionalSqNorm hd z r hr halfOrder v) ≤
          cInterp * (‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
            (1 / 3 : ℝ) *
          Real.sqrt (cubeFractionalSqNorm hd z r hr threeQuarterOrder v) ^ (2 / 3 : ℝ) := by
      convert h.2 using 1; norm_num [halfOrder, threeQuarterOrder]
    calc
      Real.sqrt (cubeFractionalSqNorm hd z r hr halfOrder v) ≤
          cInterp * (‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
            (1 / 3 : ℝ) *
          Real.sqrt (cubeFractionalSqNorm hd z r hr threeQuarterOrder v) ^ (2 / 3 : ℝ) := hbound
      _ ≤ cCommon * (‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
            (1 / 3 : ℝ) *
          Real.sqrt (cubeFractionalSqNorm hd z r hr threeQuarterOrder v) ^ (2 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hcInterpLe (by positivity)
        · positivity
  · intro z r hr hr1 v B hfinite hbound
    exact inputs_classical_e4_rellich d hd threeQuarterOrder z r hr v B hfinite hbound
  · intro z r hr hr1 v
    obtain ⟨V, hV, hzero, hnorm⟩ := hZero z r hr hr1 v
    refine ⟨V, hV, hzero, ?_⟩
    have hSq : 0 ≤ cubeFractionalSqNorm hd z r hr threeQuarterOrder (v : SobolevData _).1 := by
      have hvol := centeredCube_volume_pos z hr
      unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
      positivity
    exact le_trans hnorm (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcZeroLe hSq))
  · intro beta
    by_cases hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1
    · dsimp [CT]
      rw [dif_pos hbeta]
      exact (Classical.choose_spec (inputs_classical_e4_trace d hd beta hbeta)).1
    · dsimp [CT]
      rw [dif_neg hbeta]
      norm_num
  · intro beta hbeta z r hr hr1 G hG
    dsimp [CT]
    rw [dif_pos hbeta]
    exact (Classical.choose_spec (inputs_classical_e4_trace d hd beta hbeta)).2
      z r hr hr1 G hG

end Paper

