import SubdiffusiveProcess.Paper.lem_neumann_error_load_bound
import SubdiffusiveProcess.Sobolev.LoadApproximation
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.AffineResponses
import SubdiffusiveProcess.Sobolev.AffineMeanZero
import SubdiffusiveProcess.Main.CubeNegativeL2Norm
import SubdiffusiveProcess.Lane4.Carriers

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_neumann_error_energy :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (a : PositiveCoefficient (unitNeumannCube d)) (K Cload eps : ℝ)
    (L L' : meanZeroSobolevGraph (unitNeumannCube d) →L[ℝ] ℝ),
    0 < Cload → 0 < eps → eps < 1 / 8 →
    (∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          (v : SobolevData (unitNeumannCube d)).1 ≤
        K * sobolevCoefficientForm a
          (v : SobolevData (unitNeumannCube d))
          (v : SobolevData (unitNeumannCube d))) →
    (∀ z : meanZeroSobolevGraph (unitNeumannCube d),
      |(L - L') z| ≤ Cload * eps ^ (1 / 4 : ℝ) *
        Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
          one_pos threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1)) →
    responseForm (meanZeroResponseSpace hP) a
        (responseSolution (meanZeroResponseSpace hP) a L -
          responseSolution (meanZeroResponseSpace hP) a L')
        (responseSolution (meanZeroResponseSpace hP) a L -
          responseSolution (meanZeroResponseSpace hP) a L') ≤
      Cload ^ 2 * K * eps ^ (1 / 2 : ℝ)
    := by
  intro d hd _ _ hP a K Cload eps L L' hCload heps heps8 hcoercive hload
  let S := meanZeroResponseSpace hP
  have hresp (z : meanZeroSobolevGraph (unitNeumannCube d)) :
      responseForm S a z z =
        sobolevCoefficientForm a (z : SobolevData (unitNeumannCube d))
          (z : SobolevData (unitNeumannCube d)) := by
    rfl
  have hfrac_nonneg (z : meanZeroSobolevGraph (unitNeumannCube d)) :
      0 ≤ cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
        threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1 := by
    unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
    positivity
  have hΩ : Bornology.IsBounded (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    rw [unitNeumannCube]
    exact centeredCube_isBounded _ one_pos
  have hvol : 0 < volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    rw [unitNeumannCube]
    exact centeredCube_volume_pos _ one_pos
  let p : Fin d → ℝ := fun _ => 1
  have hp_sq : 0 < ∑ i : Fin d, p i * p i := by
    have hdpos : 0 < d := by omega
    have h0 : Fin d := ⟨0, hdpos⟩
    apply Finset.sum_pos'
    · intro i hi
      simp [p]
    · exact ⟨h0, Finset.mem_univ _, by simp [p]⟩
  let v : meanZeroSobolevGraph (unitNeumannCube d) :=
    meanZeroAffineSobolev hΩ hvol.ne' p
  have hv_ne : v ≠ 0 := by
    intro hv
    have hvload := affineNeumannLoad_meanZeroAffineSobolev hΩ hvol.ne' p p
    rw [show v = meanZeroAffineSobolev hΩ hvol.ne' p from rfl] at hv
    rw [hv] at hvload
    simp only [map_zero] at hvload
    have hprod : 0 < volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) *
        (∑ i : Fin d, p i * p i) := mul_pos hvol hp_sq
    linarith
  have henergy_pos : 0 < responseForm S a v v := by
    have henergy_ne : responseForm S a v v ≠ 0 := by
      intro hz
      exact hv_ne ((responseForm_self_eq_zero_iff S a v).mp hz)
    exact lt_of_le_of_ne (responseForm_nonneg S a v) (Ne.symm henergy_ne)
  have hK : 0 ≤ K := by
    by_contra hK
    have hKneg : K < 0 := lt_of_not_ge hK
    have hbound : cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
        threeQuarterOrder (v : SobolevData (unitNeumannCube d)).1 ≤
        K * responseForm S a v v := by
      calc
        _ ≤ K * sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
            (v : SobolevData (unitNeumannCube d)) := hcoercive v
        _ = K * responseForm S a v v := by rw [hresp v]
    have hright : K * responseForm S a v v < 0 :=
      mul_neg_of_neg_of_pos hKneg henergy_pos
    linarith [hfrac_nonneg v]
  let δ : ℝ := Cload * Real.sqrt K * eps ^ (1 / 4 : ℝ)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hsqrt_bound (z : meanZeroSobolevGraph (unitNeumannCube d)) :
      Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
        threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1) ≤
        Real.sqrt K * Real.sqrt (responseForm S a z z) := by
    have hz' : cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
        threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1 ≤
        K * responseForm S a z z := by
      calc
        _ ≤ K * sobolevCoefficientForm a (z : SobolevData (unitNeumannCube d))
            (z : SobolevData (unitNeumannCube d)) := hcoercive z
        _ = K * responseForm S a z z := by rw [hresp z]
    calc
      _ ≤ Real.sqrt (K * responseForm S a z z) :=
        Real.sqrt_le_sqrt hz'
      _ = Real.sqrt K * Real.sqrt (responseForm S a z z) := by
        rw [Real.sqrt_mul hK]
  have hload' : ∀ z : meanZeroSobolevGraph (unitNeumannCube d),
      |(L - L') z| ≤ δ * Real.sqrt (responseForm S a z z) := by
    intro z
    have hzload := hload z
    have hzsqrt := hsqrt_bound z
    have hcoef : 0 ≤ Cload * eps ^ (1 / 4 : ℝ) := by positivity
    dsimp [δ]
    calc
      |(L - L') z| ≤ Cload * eps ^ (1 / 4 : ℝ) *
          Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
            one_pos threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1) := hzload
      _ ≤ Cload * eps ^ (1 / 4 : ℝ) *
          (Real.sqrt K * Real.sqrt (responseForm S a z z)) :=
        mul_le_mul_of_nonneg_left hzsqrt hcoef
      _ = (Cload * Real.sqrt K * eps ^ (1 / 4 : ℝ)) *
          Real.sqrt (responseForm S a z z) := by ring
  have henergy := responseSolution_energy_difference_le S a L L' δ hload'
  have heps_rpow : (eps ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = eps ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul heps.le]
    congr 1
    norm_num
  dsimp [δ] at henergy ⊢
  simp only [mul_pow, Real.sq_sqrt hK, heps_rpow] at henergy
  simpa [S] using henergy

end Paper

