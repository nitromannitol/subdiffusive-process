module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeBesovForcing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveWeakSolutionAlgebra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveContraction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMeasure
@[expose] public section

/-!
# Weighted torsion comparison from the half-order Besov test

The weighted equation has forcing b, and the comparison equation has forcing
one. Their difference is tested against itself with the same cube-volume
normalization as the Besov pairing.
-/

set_option autoImplicit false
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory Filter
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A half-order bound for b - 1 controls the normalized torsion energy difference. -/
theorem goodCube_torsion_comparison_of_half_besov_bound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    {lam Lam B : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) (scalarCoeffField b))
    (hbL2 : MemL2On (openCubeSet Q) b)
    (h1 : MemL2On (openCubeSet Q) (fun _ : Vec d => (1 : ℝ)))
    (hg : MemLp (fun x => b x - 1) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : cubeBesovCircNorm Q (1 / 2) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => b x - 1) ≤ B)
    (e w : H10Function (openCubeSet Q))
    (he : IsMassiveWeakSolutionOn b b 0 (openCubeSet Q) e.toH1Function (fun _ => 1))
    (hw : IsMassiveWeakSolutionOn b (fun _ => 1) 0 (openCubeSet Q) w.toH1Function (fun _ => 1)) :
    Real.sqrt (volumeAverage (openCubeSet Q) (fun x =>
      b x * vecNormSq ((e - w).toH1Function.grad x))) ≤
      (2 * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * weightedLocalSobolevEnergyConstant d) *
        B * cubeBesovScaleWeight (-1 / 2) Q *
        Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹) := by
  have hrhoMeas : AEStronglyMeasurable (fun _ : Vec d => (1 : ℝ))
      (volume.restrict (openCubeSet Q)) := aestronglyMeasurable_const
  have hrhoBdd : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
      |(fun _ : Vec d => (1 : ℝ)) x| ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun _ => by simp
  have he' : IsMassiveWeakSolutionOn b (fun _ : Vec d => (1 : ℝ)) 0 (openCubeSet Q)
      e.toH1Function b := by
    intro phi
    have h := he phi
    simp only [zero_mul, mul_one, one_mul] at h ⊢
    exact h
  have hsub := IsMassiveWeakSolutionOn.sub (c := b) (rho := fun _ : Vec d => (1 : ℝ))
    (mu := 0) (rhoMax := (1 : ℝ)) hEll hrhoMeas hrhoBdd hbL2 h1 he' hw
  have hsol : IsMassiveWeakSolutionOn b (fun _ : Vec d => (1 : ℝ)) 0 (openCubeSet Q)
      (e - w).toH1Function (fun x => b x - 1) := hsub
  have henergy := massive_energy_identity_of_isMassiveWeakSolutionOn
    (c := b) (rho := fun _ : Vec d => (1 : ℝ)) (mu := 0) (u := e - w)
    (f := fun x => b x - 1) hsol
  simp only [zero_mul, zero_add, one_mul] at henergy
  have hLpos : 0 < Ch02.lambdaSq Q (1 / 2) (.finite 1) A :=
    Ch02.lambdaSq_pos Q A (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num [Ch02.MultiscaleExponent.IsAdmissible] :
        (Ch02.MultiscaleExponent.finite 1).IsAdmissible)
  have hlamInv : 0 ≤ (Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ :=
    inv_nonneg.2 (le_of_lt hLpos)
  have hKle : 0 ≤ 2 * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * weightedLocalSobolevEnergyConstant d := by
    have hc : 0 < weightedLocalSobolevEnergyConstant d :=
      weightedLocalSobolevEnergyConstant_pos d
    have hp : 0 < (2 : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) :=
      mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) ((d : ℝ) + 1 / 2))
    exact le_of_lt (mul_pos hp hc)
  have hsz : 0 ≤ cubeBesovScaleWeight (-1 / 2) Q := cubeBesovScaleWeight_nonneg (-1 / 2) Q
  have hRnonneg : 0 ≤ (2 * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * weightedLocalSobolevEnergyConstant d) *
      B * cubeBesovScaleWeight (-1 / 2) Q *
      Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹) :=
    mul_nonneg (mul_nonneg (mul_nonneg hKle hB) hsz) (Real.sqrt_nonneg _)
  have hSnorm : volumeAverage (openCubeSet Q) (fun x =>
      b x * vecNormSq ((e - w).toH1Function.grad x)) =
      cubeAverage Q (fun x => (b x - 1) * (e - w).toH1Function.toFun x) := by
    simp only [volumeAverage, weightedSobolev_cubeAverage_open]
    rw [volume_openCubeSet_toReal Q]
    exact congrArg (fun J : ℝ => (cubeVolume Q)⁻¹ * J) henergy
  have hconv : volumeAverage (openCubeSet Q) (fun x =>
      b x * vecDot ((e - w).toH1Function.grad x) ((e - w).toH1Function.grad x)) =
      volumeAverage (openCubeSet Q) (fun x =>
        b x * vecNormSq ((e - w).toH1Function.grad x)) := by
    rfl
  have hpair := goodCube_half_besov_pairing_le_energy Q A b hb (fun x => b x - 1) hg (e - w)
  rw [hconv, hSnorm] at hpair
  set T : ℝ := cubeAverage Q (fun x => (b x - 1) * (e - w).toH1Function.toFun x) with hT
  have hTbound : |T| ≤
      (2 * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * weightedLocalSobolevEnergyConstant d) * B *
        cubeBesovScaleWeight (-1 / 2) Q *
        Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ * T) :=
    le_trans hpair (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hKle) hsz)
      (Real.sqrt_nonneg ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ * T)))
  rw [Real.sqrt_mul hlamInv T] at hTbound
  rw [← mul_assoc] at hTbound
  rw [hSnorm]
  rcases lt_or_ge T 0 with hneg | hle
  · have hs0 : Real.sqrt T = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [hs0]
    exact hRnonneg
  · rw [abs_of_nonneg hle] at hTbound
    have hsq : T = (Real.sqrt T) ^ 2 := (Real.sq_sqrt hle).symm
    rcases eq_or_lt_of_le (Real.sqrt_nonneg T) with h0 | hpos
    · rw [← h0]
      exact hRnonneg
    · have hmul : Real.sqrt T * Real.sqrt T ≤
          (2 * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * weightedLocalSobolevEnergyConstant d) * B *
            cubeBesovScaleWeight (-1 / 2) Q *
            Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹) * Real.sqrt T := by
        rw [← pow_two, ← hsq]
        exact hTbound
      exact le_of_mul_le_mul_right hmul hpos

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
