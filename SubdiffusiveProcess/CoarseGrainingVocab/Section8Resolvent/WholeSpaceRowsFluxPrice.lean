import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsFluxPoincare
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsMesoscopicSplit




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book.Ch03
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The flux conversion -/



theorem sum_circNegativeBesovNorm_flux_le_of_isForcedEquation [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d} {a : Vec d → ℝ} {lam Lam : ℝ}
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (hAfam : ∀ S : TriadicCube d,
      (afam.coeffOn S).toCoeffField = (afam.coeffOn Q).toCoeffField)
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hforced : Ch03.IsForcedEquation Q afam u g)
    (hreg : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j, Ch03.ForceBesovRegularity R s g)
    (hGlobalBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hlam : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j,
      (lambdaSq R (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹) :
    ∑ i : Fin d, Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x) i) ≤
      ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
          (Ch03.poincareDiscountFactor s (.finite 1) *
            Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1)) *
          Real.sqrt 2) *
        Real.sqrt
          (cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
            correctorEnergyConstant d s *
              (lambdaSq Q (s / 2) (.finite 2)
                ((afam.coeffOn Q).toCoeffField))⁻¹ *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  classical
  set A : CoeffField d := (afam.coeffOn Q).toCoeffField with hAdef
  set F : Vec d → Vec d := fun x => matVecMul (A x) (u.grad x) with hFdef
  set Ea : ℝ := cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) with hEadef
  set X : ℝ := correctorEnergyConstant d s *
    (lambdaSq Q (s / 2) (.finite 2) A)⁻¹ *
    (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 with hXdef
  -- the flux clause at `q = 1`
  have hbase := scaleNormalizedNegativeBesovVectorNorm_flux_le_of_isForcedEquation
    (Q := Q) (afam := afam) (a := a) (lam := lam) (Lam := Lam) (q := 1)
    haSymm hAfam hA hapos hEll hs0 hs1 le_rfl hforced hreg hGlobalBdd hlam
  
  have hguCubeQ : MemVectorL2 (cubeSet Q) u.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using u.grad_memVectorL2
  have hEllQ : IsEllipticFieldOn lam Lam (cubeSet Q) A := hEll
  have hFmemCube : MemVectorL2 (cubeSet Q) F :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllQ hguCubeQ
  have hFmemOpen : MemVectorL2 (openCubeSet Q) F := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hFmemCube
  have hFLp : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q hFmemOpen
  have hbdd : BddAbove (Set.range fun N : ℕ =>
      Ch03.negativeBesovVectorPartialNormFinite Q s 1 N F) := by
    simpa [Ch03.negativeBesovVectorPartialNormFinite,
      cubeBesovNegativeVectorPartialSeminorm, Real.rpow_one] using
      cubeBesovNegativeVectorPartialSeminorm_bddAbove_of_memLp Q hs0 F hFLp
  
  have hcomp : ∀ i : Fin d,
      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => F x i) ≤
        cubeBesovScaleWeight (-s) Q *
          Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) F := by
    intro i
    have hb := circNegativeBesovNorm_component_le_paperNegativeBesovVectorNorm
      Q hs0 F i hbdd
    refine hb.trans (le_of_eq ?_)
    have hpaper : SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
        Q s (Ch02.MultiscaleExponent.finite 1) F =
        s * Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) F := by
      simp [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm,
        Real.rpow_one]
    rw [hpaper]
    field_simp
  have hsum : ∑ i : Fin d,
      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => F x i) ≤
      (d : ℝ) * (cubeBesovScaleWeight (-s) Q *
        Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) F) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcomp i)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  -- assemble
  have hwnn : 0 ≤ cubeBesovScaleWeight (-s) Q :=
    Real.rpow_nonneg (le_of_lt (by unfold cubeScaleFactor; positivity)) _
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hstep : (d : ℝ) * (cubeBesovScaleWeight (-s) Q *
      Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) F) ≤
      (d : ℝ) * (cubeBesovScaleWeight (-s) Q *
        (Ch03.poincareDiscountFactor s (.finite 1) *
          Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1) *
            Real.sqrt (2 * Ea + 2 * correctorEnergyConstant d s *
              (lambdaSq Q (s / 2) (.finite 2) A)⁻¹ *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbase hwnn) hdnn
  refine hsum.trans (hstep.trans (le_of_eq ?_))
  have hsq : Real.sqrt (2 * Ea + 2 * correctorEnergyConstant d s *
      (lambdaSq Q (s / 2) (.finite 2) A)⁻¹ *
      (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) =
      Real.sqrt 2 * Real.sqrt (Ea + X) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [hXdef]
    ring
  rw [hsq]
  ring

/-! ## The scale at which the conversion is usable -/



theorem top_scale_datum_price_incompatible_with_contraction_smallness
    {t lamq Lam ell eta P R Gam Sc : ℝ}
    (ht : 0 < t) (hlamq : 0 < lamq) (hell : 0 < ell)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hcond : t * lamq ≤ ell ^ 2)
    (hlamq_le : lamq ≤ Lam)
    (hP : 1 ≤ P) (hGam : 0 ≤ Gam)
    (hSc : ell ^ 2 / (lamq * t) ≤ Sc)
    (hR : Lam / ell ^ 2 ≤ R ^ 2) :
    ¬ (81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 * (Gam + Sc) * t ≤ eta ^ 4) := by
  intro hsmall
  have hlt : (0 : ℝ) < lamq * t := mul_pos hlamq ht
  have hell2 : (0 : ℝ) < ell ^ 2 := by positivity
  set y : ℝ := ell ^ 2 / (lamq * t) with hydef
  have hy0 : 0 < y := div_pos hell2 hlt
  have hy1 : 1 ≤ y := by
    rw [hydef, le_div_iff₀ hlt]
    nlinarith
  have hGS : y ≤ Gam + Sc := by linarith
  have hGSpos : 0 < Gam + Sc := lt_of_lt_of_le hy0 hGS
  have hPGS : y ≤ P * (Gam + Sc) := by nlinarith
  have hPGS2 : y ^ 2 ≤ (P * (Gam + Sc)) ^ 2 := by nlinarith
  have hRlow : lamq / ell ^ 2 ≤ R ^ 2 := by
    refine le_trans ?_ hR
    gcongr
  have hRpos : (0 : ℝ) < lamq / ell ^ 2 := div_pos hlamq hell2
  -- the product bound
  have hprod : 81 * y ^ 2 * (lamq / ell ^ 2) * y * t ≤
      81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 * (Gam + Sc) * t := by
    have h1 : 81 * y ^ 2 ≤ 81 * (P * (Gam + Sc)) ^ 2 := by linarith
    have h2 : (0 : ℝ) ≤ 81 * y ^ 2 := by positivity
    have h3 : 0 ≤ (81 : ℝ) * (P * (Gam + Sc)) ^ 2 := by positivity
    have h4 : 81 * y ^ 2 * (lamq / ell ^ 2) ≤
        81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 :=
      mul_le_mul h1 hRlow hRpos.le h3
    have h5 : 0 ≤ 81 * y ^ 2 * (lamq / ell ^ 2) := by positivity
    have h6 : 81 * y ^ 2 * (lamq / ell ^ 2) * y ≤
        81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 * (Gam + Sc) :=
      mul_le_mul h4 hGS hy0.le (by positivity)
    exact mul_le_mul_of_nonneg_right h6 ht.le
  have hid : 81 * y ^ 2 * (lamq / ell ^ 2) * y * t = 81 * y ^ 2 := by
    rw [hydef]
    field_simp
  rw [hid] at hprod
  have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
  have heta4 : eta ^ 4 ≤ 1 := pow_le_one₀ heta0.le heta1
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
