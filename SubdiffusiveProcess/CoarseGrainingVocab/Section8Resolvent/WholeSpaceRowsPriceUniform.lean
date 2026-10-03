/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCarrierLegs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellPrice

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The scale-only constants -/

/-- The cell-independent factor of the price constant `P` of
`mesoscopicCrossPriceEnergyOn_openCubeSet_of_massive_datum`. -/
def mesoscopicDatumPriceConstP [NeZero d] (Q : TriadicCube d) (s : ℝ) : ℝ :=
  2 * (3 : ℝ) ^ ((d : ℝ) + s) *
    ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
      Ch03.poincareDiscountFactor s (.finite 1) * Real.sqrt 2) *
    ((Book.Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
        Ch03.poincareDiscountFactor s (.finite 1))) *
    (cubeScaleFactor Q) ^ (1 - 2 * s)

/-- The cell-independent factor of the price constant `R` of
`mesoscopicCrossPriceEnergyOn_openCubeSet_of_massive_datum`. -/
def mesoscopicDatumPriceConstR [NeZero d] (Q : TriadicCube d) (s : ℝ) : ℝ :=
  4 * (3 : ℝ) ^ ((d : ℝ) + s) *
    ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
      Ch03.poincareDiscountFactor s (.finite 1) * Real.sqrt 2) *
    cubeBesovScaleWeight s Q

/-- The price constant `P`, with the three cell-dependent slots exposed: the
upper ellipticity factor `U`, the lower one `L` and the sup norm `X` of the
cutoff field. -/
def mesoscopicDatumPriceP [NeZero d] (Q : TriadicCube d) (s U L X B : ℝ) : ℝ :=
  mesoscopicDatumPriceConstP Q s *
    (U * L * (2 * cubeScaleFactor Q * B + 3 * X))

/-- The price constant `R`, with the two cell-dependent slots exposed. -/
def mesoscopicDatumPriceR [NeZero d] (Q : TriadicCube d) (s U X B : ℝ) : ℝ :=
  mesoscopicDatumPriceConstR Q s * (U * (5 * cubeScaleFactor Q * B + 7 * X))

/-! ## 2. The factorization is the constant P-231 displays -/

/-- `mesoscopicDatumPriceP` is exactly the first constant of
`mesoscopicCrossPriceEnergyOn_openCubeSet_of_massive_datum`. -/
theorem mesoscopicDatumPriceP_eq [NeZero d] (Q : TriadicCube d)
    (s U L X B : ℝ) :
    mesoscopicDatumPriceP Q s U L X B =
      2 * ((3 : ℝ) ^ ((d : ℝ) + s) *
        ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
          (Ch03.poincareDiscountFactor s (.finite 1) * U) * Real.sqrt 2) *
        ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
            (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
            (Ch03.poincareDiscountFactor s (.finite 1) * L))) *
        (2 * cubeScaleFactor Q * B + 3 * X) *
          (cubeScaleFactor Q) ^ (1 - 2 * s)) := by
  rw [mesoscopicDatumPriceP, mesoscopicDatumPriceConstP]
  ring

/-- `mesoscopicDatumPriceR` is exactly the second constant of
`mesoscopicCrossPriceEnergyOn_openCubeSet_of_massive_datum`. -/
theorem mesoscopicDatumPriceR_eq [NeZero d] (Q : TriadicCube d)
    (s U X B : ℝ) :
    mesoscopicDatumPriceR Q s U X B =
      2 * (2 * ((3 : ℝ) ^ ((d : ℝ) + s) *
        ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
          (Ch03.poincareDiscountFactor s (.finite 1) * U) * Real.sqrt 2) *
        (2 * (2 * cubeScaleFactor Q * B + 3 * X) * cubeBesovScaleWeight s Q +
          cubeBesovScaleWeight s Q *
            (cubeScaleFactor Q * B + X)))) := by
  rw [mesoscopicDatumPriceR, mesoscopicDatumPriceConstR]
  ring

/-! ## 3. Nonnegativity and monotonicity -/

theorem cubeScaleFactor_pos' (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  rw [cubeScaleFactor]
  exact zpow_pos (by norm_num) _

theorem poincareDiscountFactor_nonneg_one {s : ℝ} (hs0 : 0 < s) :
    0 ≤ Ch03.poincareDiscountFactor s (.finite 1) := by
  dsimp [Ch03.poincareDiscountFactor]
  exact Real.rpow_nonneg (geometricDiscount_pos (by linarith : 0 < s * 1)).le _

theorem mesoscopicDatumPriceConstP_nonneg [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs0 : 0 < s) : 0 ≤ mesoscopicDatumPriceConstP Q s := by
  have h1 : 0 ≤ Ch03.poincareDiscountFactor s (.finite 1) :=
    poincareDiscountFactor_nonneg_one hs0
  have h2 : 0 ≤ cubeBesovScaleWeight (-s) Q := cubeBesovScaleWeight_nonneg (-s) Q
  have h3 : 0 ≤ Book.Ch01.Legacy.fullVectorPoincareConstant Q :=
    Book.Ch01.Legacy.fullVectorPoincareConstant_nonneg Q
  have h4 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have h5 : (0 : ℝ) ≤ (cubeScaleFactor Q) ^ (1 - 2 * s) :=
    Real.rpow_nonneg (cubeScaleFactor_pos' Q).le _
  rw [mesoscopicDatumPriceConstP]
  positivity

theorem mesoscopicDatumPriceConstR_nonneg [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs0 : 0 < s) : 0 ≤ mesoscopicDatumPriceConstR Q s := by
  have h1 : 0 ≤ Ch03.poincareDiscountFactor s (.finite 1) :=
    poincareDiscountFactor_nonneg_one hs0
  have h2 : 0 ≤ cubeBesovScaleWeight (-s) Q := cubeBesovScaleWeight_nonneg (-s) Q
  have h6 : 0 ≤ cubeBesovScaleWeight s Q := cubeBesovScaleWeight_nonneg s Q
  have h4 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [mesoscopicDatumPriceConstR]
  positivity

/-- **Monotonicity of the price constant `P` in the three cell-dependent
slots.** -/
theorem mesoscopicDatumPriceP_le [NeZero d] {Q : TriadicCube d}
    {s U L X B U' L' X' : ℝ} (hs0 : 0 < s) (hB : 0 ≤ B)
    (hU0 : 0 ≤ U) (hL0 : 0 ≤ L) (hX0 : 0 ≤ X)
    (hU : U ≤ U') (hL : L ≤ L') (hX : X ≤ X') :
    mesoscopicDatumPriceP Q s U L X B ≤ mesoscopicDatumPriceP Q s U' L' X' B := by
  have hK := mesoscopicDatumPriceConstP_nonneg Q hs0
  have hsf : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hbase : (0 : ℝ) ≤ 2 * cubeScaleFactor Q * B + 3 * X := by positivity
  have hstep : U * L * (2 * cubeScaleFactor Q * B + 3 * X) ≤
      U' * L' * (2 * cubeScaleFactor Q * B + 3 * X') := by
    have h1 : U * L ≤ U' * L' :=
      mul_le_mul hU hL hL0 (le_trans hU0 hU)
    have h2 : 2 * cubeScaleFactor Q * B + 3 * X ≤
        2 * cubeScaleFactor Q * B + 3 * X' := by linarith
    exact mul_le_mul h1 h2 hbase (le_trans (mul_nonneg hU0 hL0) h1)
  rw [mesoscopicDatumPriceP, mesoscopicDatumPriceP]
  exact mul_le_mul_of_nonneg_left hstep hK

/-- **Monotonicity of the price constant `R` in the two cell-dependent
slots.** -/
theorem mesoscopicDatumPriceR_le [NeZero d] {Q : TriadicCube d}
    {s U X B U' X' : ℝ} (hs0 : 0 < s) (hB : 0 ≤ B)
    (hU0 : 0 ≤ U) (hX0 : 0 ≤ X) (hU : U ≤ U') (hX : X ≤ X') :
    mesoscopicDatumPriceR Q s U X B ≤ mesoscopicDatumPriceR Q s U' X' B := by
  have hK := mesoscopicDatumPriceConstR_nonneg Q hs0
  have hsf : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hbase : (0 : ℝ) ≤ 5 * cubeScaleFactor Q * B + 7 * X := by positivity
  have hstep : U * (5 * cubeScaleFactor Q * B + 7 * X) ≤
      U' * (5 * cubeScaleFactor Q * B + 7 * X') := by
    have h2 : 5 * cubeScaleFactor Q * B + 7 * X ≤
        5 * cubeScaleFactor Q * B + 7 * X' := by linarith
    exact mul_le_mul hU h2 hbase (le_trans hU0 hU)
  rw [mesoscopicDatumPriceR, mesoscopicDatumPriceR]
  exact mul_le_mul_of_nonneg_left hstep hK

/-! ## 4. The scale-only constants really are scale-only -/

/-- Two price cells of the same scale carry the same constant `P` factor. -/
theorem mesoscopicDatumPriceConstP_priceCell [NeZero d] (k : ℤ)
    (m m' : Fin d → ℤ) (s : ℝ) :
    mesoscopicDatumPriceConstP (priceCell d k m) s =
      mesoscopicDatumPriceConstP (priceCell d k m') s := rfl

/-- Two price cells of the same scale carry the same constant `R` factor. -/
theorem mesoscopicDatumPriceConstR_priceCell [NeZero d] (k : ℤ)
    (m m' : Fin d → ℤ) (s : ℝ) :
    mesoscopicDatumPriceConstR (priceCell d k m) s =
      mesoscopicDatumPriceConstR (priceCell d k m') s := rfl

/-- The price constants of two cells of the same scale agree once the three
cell-dependent slots are fixed; combined with `mesoscopicDatumPriceP_le` this is
the uniformity needed by
`mesoscopicCrossPriceEnergyOn_priceIndexBox_uniform`. -/
theorem mesoscopicDatumPriceP_priceCell [NeZero d] (k : ℤ)
    (m m' : Fin d → ℤ) (s U L X B : ℝ) :
    mesoscopicDatumPriceP (priceCell d k m) s U L X B =
      mesoscopicDatumPriceP (priceCell d k m') s U L X B := rfl

/-- The `R` analogue of `mesoscopicDatumPriceP_priceCell`. -/
theorem mesoscopicDatumPriceR_priceCell [NeZero d] (k : ℤ)
    (m m' : Fin d → ℤ) (s U X B : ℝ) :
    mesoscopicDatumPriceR (priceCell d k m) s U X B =
      mesoscopicDatumPriceR (priceCell d k m') s U X B := rfl

/-! ## 5. P-231's per-cell price, in the factored constants -/



theorem mesoscopicCrossPriceEnergyOn_openCubeSet_of_massive_datum_factored
    [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d} {a chi : Vec d → ℝ}
    {lam Lam : ℝ}
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (hAfam : ∀ S : TriadicCube d,
      (afam.coeffOn S).toCoeffField = (afam.coeffOn Q).toCoeffField)
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hs3 : 3 * s ≤ 1)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hforced : Ch03.IsForcedEquation Q afam u g)
    (hreg : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j, Ch03.ForceBesovRegularity R s g)
    (hGlobalBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hlam : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j,
      (lambdaSq R (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹)
    {T Clift B : ℝ} (hT : 0 < T)
    (huLp : MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hGnn : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g)
    (hdatum : cubeBesovPositiveVectorSeminormTwo Q s g ≤
      Clift * (cubeScaleFactor Q * (|T⁻¹| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)))
    (hbal : (lambdaSq Q (s / 2) (.finite 2)
        ((afam.coeffOn Q).toCoeffField))⁻¹ * cubeScaleFactor Q ^ 2 ≤ T)
    (ξ : Vec d → Vec d)
    (hξdef : ξ = fun x => fun i => chi x * (fderiv ℝ chi x) (basisVec i))
    (hB : 0 ≤ B)
    (hξLp : MemLp ξ (∞ : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξsmooth : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGnonneg : 0 ≤ (Book.Ch01.Legacy.fullVectorPoincareConstant Q *
        (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ∑ j : Fin d, Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x j))
    (hNnonneg : 0 ≤ ∑ i : Fin d,
      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => a x * u.grad x i)) :
    MesoscopicCrossPriceEnergyOn a (openCubeSet Q) (openCubeSet Q) u.toFun
      u.grad chi T
      (mesoscopicDatumPriceP Q s
        (Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1))
        (Ch03.poincareLowerEllipticityFactor Q afam s (.finite 1))
        (cubeLpNorm Q ∞ ξ) B)
      (mesoscopicDatumPriceR Q s
        (Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1))
        (cubeLpNorm Q ∞ ξ) B)
      (4 * (correctorEnergyConstant d s * Clift ^ 2 / 4)) := by
  rw [mesoscopicDatumPriceP_eq, mesoscopicDatumPriceR_eq]
  exact mesoscopicCrossPriceEnergyOn_openCubeSet_of_massive_datum haSymm
    hAfam hA hapos hEll hs0 hs1 hs3 hforced hreg hGlobalBdd hlam hT huLp
    hGnn hdatum hbal ξ hξdef hB hξLp hξsmooth hderiv hGnonneg hNnonneg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
