import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CubeNegativeL2Norm
import SubdiffusiveProcess.Main.HalfFractionalOrder
import SubdiffusiveProcess.Sobolev.BoundaryEnergy
import SubdiffusiveProcess.Sobolev.FoldDiscounts
import SubdiffusiveProcess.Sobolev.LoadApproximation
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.AffineResponses
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.CoarseGrainingVocab.Core
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.lem_neumann_error_load_bound
import SubdiffusiveProcess.Paper.lem_neumann_error_energy
import SubdiffusiveProcess.Paper.lem_neumann_error_volume_measurable
import SubdiffusiveProcess.Paper.lem_neumann_error_moment_assembly
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.lem_load
import SubdiffusiveProcess.Paper.lane4_cells_above_wavelength
import SubdiffusiveProcess.Paper.lane4_astar_removing_H
import SubdiffusiveProcess.Paper.lem_infrared

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

lemma aux_lem_neumann_error_load_scaling
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (a : PositiveCoefficient (unitNeumannCube d)) (K Cload eps : ℝ)
    (L L' : meanZeroSobolevGraph (unitNeumannCube d) →L[ℝ] ℝ)
    (hCload : 0 < Cload) (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (hcoercive : ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          (v : SobolevData (unitNeumannCube d)).1 ≤
        K * sobolevCoefficientForm a
          (v : SobolevData (unitNeumannCube d))
          (v : SobolevData (unitNeumannCube d)))
    (hload : ∀ z : meanZeroSobolevGraph (unitNeumannCube d),
      |(L - L') z| ≤ Cload * eps ^ (1 / 4 : ℝ) *
        Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
          one_pos threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1)) :
    0 ≤ K ∧ ∃ δ : ℝ, 0 ≤ δ ∧
      (∀ z : meanZeroSobolevGraph (unitNeumannCube d),
        |(L - L') z| ≤ δ * Real.sqrt (responseForm (meanZeroResponseSpace hP) a z z)) ∧
      δ = Cload * Real.sqrt K * eps ^ (1 / 4 : ℝ) := by
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
      _ ≤ Real.sqrt (K * responseForm S a z z) := Real.sqrt_le_sqrt hz'
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
  exact ⟨hK, δ, hδ_nonneg, by simpa [S] using hload', rfl⟩

lemma aux_lem_neumann_error_energy_triangle
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ x y, F x y = F y x)
    (hnonneg : ∀ x, 0 ≤ F x x) (u w : V) :
    F (u - w) (u - w) ≤ 2 * F u u + 2 * F w w := by
  have hplus := hnonneg (u + w)
  have hplus_expand : F (u + w) (u + w) =
      (F u u + F u w) + (F w u + F w w) := by
    calc
      F (u + w) (u + w) = (F u + F w) (u + w) := by
            exact congrArg (fun f : V →L[ℝ] ℝ => f (u + w)) (map_add F u w)
      _ = F u (u + w) + F w (u + w) :=
        ContinuousLinearMap.add_apply _ _ _
      _ = (F u u + F u w) + (F w u + F w w) := by
        exact congrArg₂ (· + ·) (map_add (F u) u w) (map_add (F w) u w)
  have hminus_expand : F (u - w) (u - w) =
      (F u u - F u w) - F w u + F w w := by
    calc
      F (u - w) (u - w) = (F u - F w) (u - w) := by
            exact congrArg (fun f : V →L[ℝ] ℝ => f (u - w)) (map_sub F u w)
      _ = F u (u - w) - F w (u - w) :=
        ContinuousLinearMap.sub_apply _ _ _
      _ = (F u u - F u w) - (F w u - F w w) := by
        exact congrArg₂ (· - ·) (map_sub (F u) u w) (map_sub (F w) u w)
      _ = (F u u - F u w) - F w u + F w w := by ring
  rw [hplus_expand] at hplus
  rw [hsymm w u] at hplus
  have hcross : -2 * F u w ≤ F u u + F w w := by
    linarith [hplus]
  rw [hminus_expand]
  rw [hsymm w u]
  linarith [hcross]

lemma aux_lem_neumann_error_sqrt_bound {A B δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hB_le : B ≤ 2 * A + 2 * δ ^ (2 : ℕ)) :
    Real.sqrt B ≤ 2 * (Real.sqrt A + δ) := by
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hAs := Real.sq_sqrt hA
    have hBs := Real.sq_sqrt hB
    have hprod : 0 ≤ Real.sqrt A * δ :=
      mul_nonneg (Real.sqrt_nonneg _) hδ
    nlinarith [hB_le, sq_nonneg (Real.sqrt A - δ)]

lemma aux_lem_neumann_error_error_arith {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    6 * x * y + 4 * x ^ 2 ≤ 8 * x * y + 64 * x ^ 2 := by
  nlinarith [mul_nonneg hx hy, sq_nonneg x]

lemma aux_lem_neumann_error_scale_arith {A B C t : ℝ}
    (ht : 0 ≤ t)
    (h : A ≤ B + 2 * C ^ 2 * t) :
    A ≤ B + 2 * (8 * C) ^ 2 * t := by
  have hcoef : 2 * C ^ 2 ≤ 2 * (8 * C) ^ 2 := by
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hcoef ht
  exact h.trans (by
    convert add_le_add_left hh B using 1 <;> ring)

lemma aux_lem_neumann_error_pointwise
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (a : PositiveCoefficient (unitNeumannCube d)) (K Cload eps : ℝ)
    (L L' : meanZeroSobolevGraph (unitNeumannCube d) →L[ℝ] ℝ)
    (hCload : 0 < Cload) (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (hcoercive : ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          (v : SobolevData (unitNeumannCube d)).1 ≤
        K * sobolevCoefficientForm a
          (v : SobolevData (unitNeumannCube d))
          (v : SobolevData (unitNeumannCube d)))
    (hload : ∀ z : meanZeroSobolevGraph (unitNeumannCube d),
      |(L - L') z| ≤ Cload * eps ^ (1 / 4 : ℝ) *
        Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
          one_pos threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1)) :
    0 ≤ K ∧
    responseForm (meanZeroResponseSpace hP) a
        (responseSolution (meanZeroResponseSpace hP) a L -
          responseSolution (meanZeroResponseSpace hP) a L')
        (responseSolution (meanZeroResponseSpace hP) a L -
          responseSolution (meanZeroResponseSpace hP) a L') ≤
      Cload ^ 2 * K * eps ^ (1 / 2 : ℝ) ∧
    |inverseResponse (meanZeroResponseSpace hP) a L -
        inverseResponse (meanZeroResponseSpace hP) a L'| ≤
      (8 * Cload) * eps ^ (1 / 4 : ℝ) * Real.sqrt K *
          Real.sqrt (inverseResponse (meanZeroResponseSpace hP) a L) +
        (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * K ∧
    inverseResponse (meanZeroResponseSpace hP) a L' ≤
      2 * inverseResponse (meanZeroResponseSpace hP) a L +
        2 * (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * K := by
  let S := meanZeroResponseSpace hP
  have henergy := lem_neumann_error_energy d hd hP a K Cload eps L L'
    hCload heps heps8 hcoercive hload
  obtain ⟨hK, δ, hδ, hload', hδeq⟩ :=
    aux_lem_neumann_error_load_scaling hd hP a K Cload eps L L'
      hCload heps heps8 hcoercive hload
  have henergy' : responseForm S a
        (responseSolution S a L - responseSolution S a L')
        (responseSolution S a L - responseSolution S a L') ≤
      Cload ^ 2 * K * eps ^ (1 / 2 : ℝ) := by
    simpa [S] using henergy
  have hinv := inverseResponse_load_difference_le S a L L' δ hδ hload'
  have htri := aux_lem_neumann_error_energy_triangle
    (responseForm S a) (responseForm_symm S a) (responseForm_nonneg S a)
    (responseSolution S a L)
    (responseSolution S a L - responseSolution S a L')
  have hV_raw : inverseResponse S a L' ≤
      2 * inverseResponse S a L + 2 * Cload ^ 2 * eps ^ (1 / 2 : ℝ) * K := by
    have htri' : inverseResponse S a L' ≤
        2 * inverseResponse S a L +
          2 * responseForm S a (responseSolution S a L - responseSolution S a L')
            (responseSolution S a L - responseSolution S a L') := by
      change responseForm S a (responseSolution S a L') (responseSolution S a L') ≤ _
      simpa only [sub_sub_cancel] using htri
    calc
      _ ≤ 2 * inverseResponse S a L +
          2 * responseForm S a (responseSolution S a L - responseSolution S a L')
            (responseSolution S a L - responseSolution S a L') := htri'
      _ ≤ 2 * inverseResponse S a L +
          2 * (Cload ^ 2 * K * eps ^ (1 / 2 : ℝ)) := by
        gcongr
      _ = 2 * inverseResponse S a L + 2 * Cload ^ 2 * eps ^ (1 / 2 : ℝ) * K := by
        ring
  have hδsq : δ ^ (2 : ℕ) = Cload ^ 2 * K * eps ^ (1 / 2 : ℝ) := by
    have heps_rpow : (eps ^ (1 / 4 : ℝ)) ^ (2 : ℕ) =
        eps ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul heps.le]
      congr 1
      norm_num
    rw [hδeq]
    simp only [mul_pow, Real.sq_sqrt hK, heps_rpow]
  have hV_raw' : inverseResponse S a L' ≤
      2 * inverseResponse S a L + 2 * δ ^ (2 : ℕ) := by
    calc
      _ ≤ 2 * inverseResponse S a L + 2 * Cload ^ 2 * eps ^ (1 / 2 : ℝ) * K := hV_raw
      _ = 2 * inverseResponse S a L + 2 * δ ^ (2 : ℕ) := by
        rw [hδsq]
        ring
  have hsqrtV : Real.sqrt (inverseResponse S a L') ≤
      2 * (Real.sqrt (inverseResponse S a L) + δ) :=
    aux_lem_neumann_error_sqrt_bound (inverseResponse_nonneg S a L)
      (inverseResponse_nonneg S a L') hδ hV_raw'
  have hD : |inverseResponse S a L - inverseResponse S a L'| ≤
      (8 * Cload) * eps ^ (1 / 4 : ℝ) * Real.sqrt K *
          Real.sqrt (inverseResponse S a L) +
        (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * K := by
    calc
      _ ≤ 2 * δ * (Real.sqrt (inverseResponse S a L) +
          Real.sqrt (inverseResponse S a L')) := hinv
      _ ≤ 2 * δ * (Real.sqrt (inverseResponse S a L) +
          2 * (Real.sqrt (inverseResponse S a L) + δ)) := by
        gcongr
      _ = 6 * δ * Real.sqrt (inverseResponse S a L) + 4 * δ ^ 2 := by ring
      _ ≤ 8 * δ * Real.sqrt (inverseResponse S a L) + 64 * δ ^ 2 :=
        aux_lem_neumann_error_error_arith hδ (Real.sqrt_nonneg _)
      _ = (8 * Cload) * eps ^ (1 / 4 : ℝ) * Real.sqrt K *
            Real.sqrt (inverseResponse S a L) +
          (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * K := by
        have hfirst : 8 * δ * Real.sqrt (inverseResponse S a L) =
            (8 * Cload) * eps ^ (1 / 4 : ℝ) * Real.sqrt K *
              Real.sqrt (inverseResponse S a L) := by
          rw [hδeq]
          ring
        have hsecond : 64 * δ ^ 2 =
            (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * K := by
          rw [hδsq]
          ring
        rw [hfirst, hsecond]
  have hV_scaled : inverseResponse S a L' ≤
      2 * inverseResponse S a L +
        2 * (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * K := by
    have hV_raw' : inverseResponse S a L' ≤
        2 * inverseResponse S a L +
          2 * Cload ^ 2 * (eps ^ (1 / 2 : ℝ) * K) := by
      simpa only [mul_assoc] using hV_raw
    have htmp := aux_lem_neumann_error_scale_arith
      (A := inverseResponse S a L') (B := 2 * inverseResponse S a L)
      (C := Cload) (t := eps ^ (1 / 2 : ℝ) * K)
      (mul_nonneg (Real.rpow_nonneg heps.le _) hK) hV_raw'
    simpa only [mul_assoc] using htmp
  exact ⟨hK, henergy', by simpa [S] using hD, by simpa [S] using hV_scaled⟩

lemma aux_lem_neumann_error_all_pointwise
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (aFun : BilateralField d → PositiveCoefficient (unitNeumannCube d))
    (L : meanZeroSobolevGraph (unitNeumannCube d) →L[ℝ] ℝ)
    (L' : BilateralField d → meanZeroSobolevGraph (unitNeumannCube d) →L[ℝ] ℝ)
    (Kcoerc : BilateralField d → ℝ) (Cload eps : ℝ)
    (hCload : 0 < Cload) (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (hcoercive : ∀ (x : BilateralField d)
      (v : meanZeroSobolevGraph (unitNeumannCube d)),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          (v : SobolevData (unitNeumannCube d)).1 ≤
        Kcoerc x * sobolevCoefficientForm (aFun x)
          (v : SobolevData (unitNeumannCube d))
          (v : SobolevData (unitNeumannCube d)))
    (hload : ∀ (x : BilateralField d)
      (z : meanZeroSobolevGraph (unitNeumannCube d)),
      |(L - L' x) z| ≤ Cload * eps ^ (1 / 4 : ℝ) *
        Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
          one_pos threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1)) :
    ∀ x, 0 ≤ Kcoerc x ∧
      responseForm (meanZeroResponseSpace hP) (aFun x)
          (responseSolution (meanZeroResponseSpace hP) (aFun x) L -
            responseSolution (meanZeroResponseSpace hP) (aFun x) (L' x))
          (responseSolution (meanZeroResponseSpace hP) (aFun x) L -
            responseSolution (meanZeroResponseSpace hP) (aFun x) (L' x)) ≤
        Cload ^ 2 * Kcoerc x * eps ^ (1 / 2 : ℝ) ∧
      |inverseResponse (meanZeroResponseSpace hP) (aFun x) L -
          inverseResponse (meanZeroResponseSpace hP) (aFun x) (L' x)| ≤
        (8 * Cload) * eps ^ (1 / 4 : ℝ) * Real.sqrt (Kcoerc x) *
            Real.sqrt (inverseResponse (meanZeroResponseSpace hP) (aFun x) L) +
          (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * Kcoerc x ∧
      inverseResponse (meanZeroResponseSpace hP) (aFun x) (L' x) ≤
        2 * inverseResponse (meanZeroResponseSpace hP) (aFun x) L +
          2 * (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * Kcoerc x := by
  intro x
  exact aux_lem_neumann_error_pointwise hd hP (aFun x) (Kcoerc x) Cload eps
    L (L' x) hCload heps heps8 (hcoercive x) (hload x)

abbrev aux_lem_neumann_error_load_type
    (d : ℕ) (hd : 2 ≤ d) (Cload : ℝ) : Prop :=
  ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
    (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
    ∀ (fL2 : ℕ → BilateralField d → DomainL2 (unitNeumannCube d)),
      (∀ N om, ((fL2 N om : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
          faceBump rho pvec eps)) →
      ∀ (N : ℕ) (om : BilateralField d) (z : meanZeroSobolevGraph (unitNeumannCube d)),
        |(((affineNeumannLoad pvec).comp
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
          ((sobolevVolumeLoad (fL2 N om)).comp
            (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL)) z| ≤
          Cload * eps ^ (1 / 4 : ℝ) *
            Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
              one_pos threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1)

abbrev aux_lem_neumann_error_assembly_type
    (p Bcoerc Bresponse Cload Cerr Cunif : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ],
    ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
    ∀ (K Y V D : Ω → ℝ),
      (∀ x, 0 ≤ K x) → (∀ x, 0 ≤ Y x) → (∀ x, 0 ≤ V x) →
      (∀ x, |D x| ≤ Cload * eps ^ (1 / 4 : ℝ) * Real.sqrt (K x) *
        Real.sqrt (Y x) + Cload ^ 2 * eps ^ (1 / 2 : ℝ) * K x) →
      (∀ x, V x ≤ 2 * Y x + 2 * Cload ^ 2 * eps ^ (1 / 2 : ℝ) * K x) →
      AEStronglyMeasurable D μ → AEStronglyMeasurable V μ →
      MemLp K (ENNReal.ofReal (4 * p)) μ →
      eLpNorm K (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal Bcoerc →
      MemLp Y (ENNReal.ofReal (4 * p)) μ →
      eLpNorm Y (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal Bresponse →
      eLpNorm D (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) ∧
      eLpNorm V (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cunif

lemma aux_lem_neumann_error_model
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (p : ℝ) (Bcoerc Bresponse Cload Cerr Cunif : ℝ)
    (hCload : 0 < Cload)
    (A : aux_lem_neumann_error_assembly_type p Bcoerc Bresponse (8 * Cload) Cerr Cunif)
    (_S : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (hload_bound : aux_lem_neumann_error_load_type d hd Cload)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (_Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hIH : InfraredCharacterization M H) (hdelta : M.delta ≤ 1) :
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
      (Kcoerc : ℕ → BilateralField d → ℝ),
      (∀ N om, ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
            (v : SobolevData (unitNeumannCube d)).1 ≤
          Kcoerc N om * sobolevCoefficientForm
            (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
            (v : SobolevData (unitNeumannCube d))
            (v : SobolevData (unitNeumannCube d))) →
      (∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (4 * p))
        (chaosSampleLaw M).toMeasure) →
      (∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * p))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Bcoerc) →
      (∀ N, MemLp (fun om' => inverseResponse (meanZeroResponseSpace hP)
        (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
        ((affineNeumannLoad pvec).comp
          (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))
        (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure) →
      (∀ N, eLpNorm (fun om' => inverseResponse (meanZeroResponseSpace hP)
        (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
        ((affineNeumannLoad pvec).comp
          (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))
        (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Bresponse) →
    ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
    ∀ (fL2 : ℕ → BilateralField d → DomainL2 (unitNeumannCube d)),
      (∀ N om, ((fL2 N om : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
          faceBump rho pvec eps)) →
    ∀ (N : ℕ) (om : BilateralField d),
      (responseForm (meanZeroResponseSpace hP)
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          (responseSolution (meanZeroResponseSpace hP)
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
              ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
            responseSolution (meanZeroResponseSpace hP)
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
              ((sobolevVolumeLoad (fL2 N om)).comp
                (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))
          (responseSolution (meanZeroResponseSpace hP)
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
              ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
            responseSolution (meanZeroResponseSpace hP)
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
              ((sobolevVolumeLoad (fL2 N om)).comp
                (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL)) ≤
        (8 * Cload) ^ 2 * Kcoerc N om * eps ^ (1 / 2 : ℝ)) ∧
      eLpNorm (fun om' => inverseResponse (meanZeroResponseSpace hP)
          (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
          ((affineNeumannLoad pvec).comp
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
        inverseResponse (meanZeroResponseSpace hP)
          (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
          ((sobolevVolumeLoad (fL2 N om')).comp
            (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) ∧
      eLpNorm (fun om' => inverseResponse (meanZeroResponseSpace hP)
          (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
          ((sobolevVolumeLoad (fL2 N om')).comp
            (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cunif := by
  intro rho hrho hrho_nonneg hrho_support hrho_int pvec hpvec hP Kcoerc hcoerc
    hKmem hKbound hYmem hYbound eps heps heps8 fL2 hfL2 N om
  let S := meanZeroResponseSpace hP
  let L : meanZeroSobolevGraph (unitNeumannCube d) →L[ℝ] ℝ :=
    (affineNeumannLoad pvec).comp
      (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))
  let aFun : BilateralField d → PositiveCoefficient (unitNeumannCube d) :=
    fun om' => cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos
  let L' : BilateralField d → meanZeroSobolevGraph (unitNeumannCube d) →L[ℝ] ℝ :=
    fun om' => (sobolevVolumeLoad (fL2 N om')).comp
      (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL
  let Y : BilateralField d → ℝ := fun om' => inverseResponse S (aFun om') L
  let V : BilateralField d → ℝ := fun om' => inverseResponse S (aFun om') (L' om')
  let D : BilateralField d → ℝ := fun om' => Y om' - V om'
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  obtain ⟨Lg, hLg, hLg_meas⟩ := lem_neumann_error_volume_measurable d M H hIH hP fL2
    (faceBump rho pvec eps) (by intro N' om'; exact hfL2 N' om') N
  have hY_mem : MemLp Y (ENNReal.ofReal (4 * p)) μ := by
    simpa [Y, aFun, S, μ] using hYmem N
  have hY_bound : eLpNorm Y (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal Bresponse := by
    simpa [Y, aFun, S, μ] using hYbound N
  have hK_mem : MemLp (Kcoerc N) (ENNReal.ofReal (4 * p)) μ := by
    simpa [μ] using hKmem N
  have hK_bound : eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal Bcoerc := by
    simpa [μ] using hKbound N
  have hV_meas : AEStronglyMeasurable V μ := by
    apply hLg_meas.aestronglyMeasurable.congr
    exact Filter.Eventually.of_forall (fun om' => by
      dsimp [V, aFun, L', S]
      rw [hLg om'])
  have hY_meas : AEStronglyMeasurable Y μ := hY_mem.aestronglyMeasurable
  have hD_meas : AEStronglyMeasurable D μ := by simpa [D] using hY_meas.sub hV_meas
  have hY_nonneg : ∀ x, 0 ≤ Y x := fun x => inverseResponse_nonneg S (aFun x) L
  have hV_nonneg : ∀ x, 0 ≤ V x := fun x => inverseResponse_nonneg S (aFun x) (L' x)
  have hcoercive_all : ∀ (x : BilateralField d)
      (v : meanZeroSobolevGraph (unitNeumannCube d)),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
      one_pos threeQuarterOrder (v : SobolevData (unitNeumannCube d)).1 ≤
    Kcoerc N x * sobolevCoefficientForm (aFun x) (v : SobolevData (unitNeumannCube d))
      (v : SobolevData (unitNeumannCube d)) := by
    intro x v
    simpa [aFun] using hcoerc N x v
  have hload_all : ∀ x z, |(L - L' x) z| ≤ Cload * eps ^ (1 / 4 : ℝ) *
      Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
        threeQuarterOrder (z : SobolevData (unitNeumannCube d)).1) := by
    intro x z
    simpa [L, L'] using hload_bound rho hrho hrho_nonneg hrho_support hrho_int
      pvec hpvec eps heps heps8 fL2 hfL2 N x z
  have hdirect := aux_lem_neumann_error_all_pointwise hd hP aFun L L' (Kcoerc N)
    Cload eps hCload heps heps8 hcoercive_all hload_all
  have hK : ∀ x, 0 ≤ Kcoerc N x := fun x => (hdirect x).1
  have hD : ∀ x, |D x| ≤ (8 * Cload) * eps ^ (1 / 4 : ℝ) * Real.sqrt (Kcoerc N x) *
      Real.sqrt (Y x) + (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * Kcoerc N x := by
    intro x
    simpa [D, Y, V] using (hdirect x).2.2.1
  have hV : ∀ x, V x ≤ 2 * Y x + 2 * (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * Kcoerc N x := by
    intro x
    simpa [V, Y] using (hdirect x).2.2.2
  have hasm := A (BilateralField d) μ eps heps heps8
    (Kcoerc N) Y V D hK hY_nonneg hV_nonneg hD hV hD_meas hV_meas
    hK_mem hK_bound hY_mem hY_bound
  refine ⟨?_, ?_, ?_⟩
  · have hpnt := (hdirect om).2.1
    have hc : Cload ^ 2 ≤ (8 * Cload) ^ 2 := by nlinarith [sq_nonneg Cload]
    calc
      _ ≤ Cload ^ 2 * Kcoerc N om * eps ^ (1 / 2 : ℝ) := hpnt
      _ ≤ (8 * Cload) ^ 2 * Kcoerc N om * eps ^ (1 / 2 : ℝ) := by
        have hh := mul_le_mul_of_nonneg_right hc (hK om)
        have he := Real.rpow_nonneg heps.le (1 / 2 : ℝ)
        convert mul_le_mul_of_nonneg_right hh he using 1 <;> ring
  · change eLpNorm D (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ))
    exact hasm.1
  · change eLpNorm V (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cunif
    exact hasm.2






theorem lem_neumann_error :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_S : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (p : ℝ), 1 ≤ p →
  ∀ (Bcoerc Bresponse : ℝ),
    0 ≤ Bcoerc → 0 ≤ Bresponse →
    ∃ (delta0 K Cerr Cunif : ℝ),
      0 < delta0 ∧ 0 < K ∧ 0 < Cerr ∧ 0 < Cunif ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
      (Kcoerc : ℕ → BilateralField d → ℝ),
      (∀ N om, ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
            (v : SobolevData (unitNeumannCube d)).1 ≤
          Kcoerc N om *
            sobolevCoefficientForm
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
              (v : SobolevData (unitNeumannCube d))
              (v : SobolevData (unitNeumannCube d))) →
      -- `K_N` has moments of order `4p`: the paper's standing reduction of `δ`
      (∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure) →
      (∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * p))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Bcoerc) →
      -- `y_N = E_N^Q(v_N) = Y_N^Q(p)` has moments of order `4p`: the second half of the
      -- same reduction.  `y_N` is the response of the **affine** load `L_p`, not of the
      
      (∀ N, MemLp (fun om' =>
          inverseResponse (meanZeroResponseSpace hP)
            (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
            ((affineNeumannLoad pvec).comp
              (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))
        (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure) →
      (∀ N, eLpNorm (fun om' =>
          inverseResponse (meanZeroResponseSpace hP)
            (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
            ((affineNeumannLoad pvec).comp
              (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))
        (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Bresponse) →
    ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
    ∀ (fL2 : ℕ → BilateralField d → DomainL2 (unitNeumannCube d)),
      (∀ N om, ((fL2 N om : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
          faceBump rho pvec eps)) →
    ∀ (N : ℕ) (om : BilateralField d),
      (responseForm (meanZeroResponseSpace hP)
            (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
            (responseSolution (meanZeroResponseSpace hP)
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                ((affineNeumannLoad pvec).comp
                  (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
              responseSolution (meanZeroResponseSpace hP)
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                ((sobolevVolumeLoad (fL2 N om)).comp
                  (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))
            (responseSolution (meanZeroResponseSpace hP)
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                ((affineNeumannLoad pvec).comp
                  (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
              responseSolution (meanZeroResponseSpace hP)
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                ((sobolevVolumeLoad (fL2 N om)).comp
                  (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL)) ≤
        K * Kcoerc N om * eps ^ (1 / 2 : ℝ)) ∧
      eLpNorm (fun om' =>
          inverseResponse (meanZeroResponseSpace hP)
              (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
              ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
            inverseResponse (meanZeroResponseSpace hP)
              (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
              ((sobolevVolumeLoad (fL2 N om')).comp
                (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) ∧
      eLpNorm (fun om' =>
          inverseResponse (meanZeroResponseSpace hP)
            (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
            ((sobolevVolumeLoad (fL2 N om')).comp
              (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cunif := by
  intro d hd _ _ E _P _S p hp Bcoerc Bresponse hBcoerc hBresponse
  let hload := lem_neumann_error_load_bound d hd _S
  let Cload : ℝ := Classical.choose hload
  have hload_spec := Classical.choose_spec hload
  have hCload : 0 < Cload := hload_spec.1
  have hload_bound : aux_lem_neumann_error_load_type d hd Cload := by
    change aux_lem_neumann_error_load_type d hd (Classical.choose hload)
    exact hload_spec.2
  let hasm0 := lem_neumann_error_moment_assembly p Bcoerc Bresponse (8 * Cload) hp
    hBcoerc hBresponse (by positivity)
  let Cerr : ℝ := Classical.choose hasm0
  have hasm1 := Classical.choose_spec hasm0
  let Cunif : ℝ := Classical.choose hasm1
  have hasm2 := Classical.choose_spec hasm1
  have hCerr : 0 < Cerr := by
    change 0 < Classical.choose hasm0
    exact hasm2.1
  have hCunif : 0 < Cunif := by
    change 0 < Classical.choose hasm1
    exact hasm2.2.1
  have hassemble : aux_lem_neumann_error_assembly_type p Bcoerc Bresponse
      (8 * Cload) Cerr Cunif := by
    change aux_lem_neumann_error_assembly_type p Bcoerc Bresponse
      (8 * Cload) (Classical.choose hasm0) (Classical.choose hasm1)
    exact hasm2.2.2
  refine ⟨1, (8 * Cload) ^ 2, Cerr, Cunif, by norm_num, ?_, hCerr, hCunif, ?_⟩
  · positivity
  · intro M _Rm H hIH hdelta
    exact aux_lem_neumann_error_model d hd p Bcoerc Bresponse Cload Cerr Cunif
      hCload hassemble _S hload_bound M _Rm H hIH hdelta

end Paper
