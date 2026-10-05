module

public import SubdiffusiveProcess.Caccioppoli.Boundary
public import SubdiffusiveProcess.Caccioppoli.ExactDatum
@[expose] public section

namespace SubdiffusiveProcess.Caccioppoli
open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open Homogenization hiding Vec Mat TriadicCube
open Homogenization.Book.Ch03
open scoped ENNReal
noncomputable section
theorem source_boundary_caccioppoli {d : ℕ} [NeZero d] (_hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s t : ℝ), 0 < s → s < 1 → 0 < t → t < (1 / 2 : ℝ) → s + t < 1 →
        ∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0),
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
          ∀ u : Homogenization.H1Function
              (Homogenization.openCubeSet (Homogenization.originCube d 0)),
          ∀ (gF Hh : PaperPositiveSobolevField (Homogenization.originCube d 0) (2 * t)
              Homogenization.FiniteLpExponent.two)
            (hh : Homogenization.H1Function
              (Homogenization.openCubeSet (Homogenization.originCube d 0))),
            Hh.toField = hh.grad →
            Homogenization.cubeAverage (Homogenization.originCube d 0) hh.toFun = 0 →
            Homogenization.Book.Ch03.ABK26.IsForcedEquation (Homogenization.originCube d 0)
              (a.coeffOn (Homogenization.originCube d 0)) u gF.toField →
            Homogenization.Book.Ch01.LocalizedZeroTraceFunctionOn
              (Ch02.cubeDomain (Homogenization.originCube d 0) : Set (Vec d))
              (Homogenization.Book.Ch03.openCubeAtScale x
                ((Homogenization.originCube d 0).scale - 1))
              (fun y => u.toFun y - hh.toFun y) →
            Ch03.localizedCoeffEnergyValue
                (Ch03.caccioppoliCoreSet (Homogenization.originCube d 0) x)
                (a.coeffOn (Homogenization.originCube d 0)) u ≤
              Real.rpow (C / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
                Real.rpow
                  (LambdaDefault (Homogenization.originCube d 0) s a /
                    lambdaDefault (Homogenization.originCube d 0) t a)
                  ((s + (1 - s - t)) / (1 - s - t)) *
                (lambdaDefault (Homogenization.originCube d 0) t a *
                    Homogenization.cubeLpNorm (Homogenization.originCube d 0) (2 : ℝ≥0∞)
                      u.toFun ^ 2 +
                  t ^ (-11 : ℤ) * (lambdaDefault (Homogenization.originCube d 0) t a)⁻¹ *
                    gF.norm.toReal ^ 2 +
                  t ^ (-3 : ℤ) * LambdaDefault (Homogenization.originCube d 0) t a *
                    Hh.norm.toReal ^ 2) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_boundary_caccioppoli_with_datum d
  let D := caccioppoliExactDatumConstant d
  let Dh := (d : ℝ) + D
  let K := max 1 (max (D ^ 2) (Dh ^ 2))
  let C := (Real.exp 2 * K) ^ 2 * C₀
  have hD : 0 < D := caccioppoliExactDatumConstant_pos d
  have hK : 1 ≤ K := le_max_left _ _
  have hDK : D ^ 2 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hDhK : Dh ^ 2 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 0 < C := mul_pos (sq_pos_of_pos
    (mul_pos (Real.exp_pos 2) (lt_of_lt_of_le zero_lt_one hK))) hC₀
  refine ⟨C, hC, ?_⟩
  intro s t hs hs1 ht hth hst x hx a hsymm u gF Hh hh hgrad hmean heq htrace
  cases gF with
  | firstOrder hr hp G => exfalso; linarith only [hr, hth]
  | fractional rF hrF F =>
    cases Hh with
    | firstOrder hr hp G => exfalso; linarith only [hr, hth]
    | fractional rH hrH Hh =>
      let Q : Homogenization.TriadicCube d := originCube d 0
      let g : Homogenization.Vec d → Homogenization.Vec d := fun y => -F.toField y
      have hpublic : IsForcedEquation Q a u g := by
        intro phi
        have h := heq phi
        change (∫ y in openCubeSet (originCube d 0),
          vecDot (matVecMul ((a.coeffOn (originCube d 0)).toCoeffField y)
            (u.grad y)) (phi.toH1Function.grad y)) =
          ∫ y in openCubeSet (originCube d 0), vecDot (g y) (phi.toH1Function.grad y)
        calc
          _ = -(∫ y in openCubeSet (originCube d 0),
            vecDot (F.toField y) (phi.toH1Function.grad y)) := by simpa using! h
          _ = _ := by
            rw [← MeasureTheory.integral_neg]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            exact (vecDot_neg_left (F.toField y) (phi.toH1Function.grad y)).symm
      have hg : ForceBesovRegularity Q (2 * t) g := by
        simpa [Q, g, hrF] using!
          ((cubeEuclideanWspField_forceSobolevRegularity rF (negCubeEuclideanWspField F)).toForceBesovRegularity
            rF.2.1 rF.2.2.le)
      have hhreg : ForceBesovRegularity Q (2 * t) hh.grad := by
        change Hh.toField = hh.grad at hgrad
        rw [← hgrad]
        simpa [Q, hrH] using!
          ((cubeEuclideanWspField_forceSobolevRegularity rH Hh).toForceBesovRegularity
            rH.2.1 rH.2.2.le)
      have hmean' : volumeAverage (openCubeSet Q) hh.toFun = 0 := by
        rw [volumeAverage_openCubeSet_eq_cubeAverage]
        exact hmean
      have hraw := hb u hh 0 hsymm hpublic htrace hmean'
        hs hs1 ht hth hst hx hg hhreg
      simp only [sub_zero] at hraw
      rw [normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq
        Q u.toFun u.memL2_normalizedCubeMeasure] at hraw
      have hscale : Q.scale = 0 := rfl
      rw [hscale] at hraw
      simp only [Int.cast_zero, mul_zero] at hraw
      have hthree : Real.rpow 3 (0 : ℝ) = 1 := Real.rpow_zero 3
      rw [hthree, mul_one] at hraw
      let L := Ch02.lambdaS Q t a
      let Lt := Ch02.LambdaS Q t a
      let T := Ch02.ThetaRatio Q s t a
      let X := L * cubeLpNorm Q 2 u.toFun ^ 2
      let Nf := (paperFractionalFullNorm Q rF FiniteLpExponent.two F.toField).toReal ^ 2
      let Nh := (paperFractionalFullNorm Q rH FiniteLpExponent.two Hh.toField).toReal ^ 2
      let BF := Real.rpow t (-11 : ℝ) * L⁻¹ * Nf
      let BH := Real.rpow t (-3 : ℝ) * Lt * Nh
      have hL : 0 < L := Ch02.lambdaSq_finite_pos Q a ht (by norm_num)
      have hLt : 0 ≤ Lt := Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num)
      have hX : 0 ≤ X := mul_nonneg hL.le (sq_nonneg _)
      have hBF : 0 ≤ BF := mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _)
        (inv_nonneg.mpr hL.le)) (sq_nonneg _)
      have hBH : 0 ≤ BH := mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) hLt) (sq_nonneg _)
      have hf := besov_neg_sq_le_paperFractionalFullNorm d ht rF hrF F
      have hhprice := positiveBesov_full_sq_le_paperNorm d ht hth rH hrH Hh
      have hfinside : Real.rpow t (-10 : ℝ) * Real.rpow L (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 ≤ K * BF := by
        have h0 := normalized_square_budget (t := t) (k := 10) (M := D ^ 2) (L := L⁻¹) (N := Nf) ht (sq_nonneg D)
          (inv_nonneg.mpr hL.le) (sq_nonneg _) (by simpa only [D, Q, g, Nf] using! hf)
        have h0' : Real.rpow t (-10 : ℝ) * Real.rpow L (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 ≤ D ^ 2 * BF := by
          have hLinvEq : Real.rpow L (-1 : ℝ) = L⁻¹ := Real.rpow_neg_one L
          simpa only [BF, hLinvEq, show -(10 + 1 : ℝ) = -11 by norm_num, mul_assoc] using! h0
        exact h0'.trans (mul_le_mul_of_nonneg_right hDK hBF)
      have hhinside : Real.rpow t (-2 : ℝ) * Lt *
          scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) hh.grad ^ 2 ≤ K * BH := by
        have h0 := normalized_square_budget (t := t) (k := 2) (M := Dh ^ 2) (L := Lt) (N := Nh) ht (sq_nonneg Dh)
          hLt (sq_nonneg _) (by simpa only [Dh, D, Q, Nh] using! hhprice)
        change Hh.toField = hh.grad at hgrad
        rw [hgrad] at h0
        have h0' : Real.rpow t (-2 : ℝ) * Lt *
            scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) hh.grad ^ 2 ≤ Dh ^ 2 * BH := by
          simpa only [BH, show -(2 + 1 : ℝ) = -3 by norm_num, mul_assoc] using! h0
        exact h0'.trans (mul_le_mul_of_nonneg_right hDhK hBH)
      have hinside : L * cubeLpNorm Q 2 u.toFun ^ 2 +
          Real.rpow t (-10 : ℝ) * Real.rpow L (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 +
          Real.rpow t (-2 : ℝ) * Lt *
            scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) hh.grad ^ 2 ≤
          K * (X + BF + BH) := by
        have hU : X ≤ K * X := by simpa only [one_mul] using! mul_le_mul_of_nonneg_right hK hX
        simpa only [mul_add, X] using! add_le_add (add_le_add hU hfinside) hhinside
      let H₀ := Real.rpow (C₀ / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
        Real.rpow s (-(2 * s / (1 - s - t)))
      let H := Real.rpow (C / (1 - s - t)) (2 + 4 * s / (1 - s - t))
      have hT : 0 ≤ T := Ch02.ThetaRatio_nonneg Q a hs ht
      have hP : 0 ≤ caccioppoliWithRHSPrefactor C₀ Q a s t :=
        caccioppoliWithRHSPrefactor_nonneg hC₀.le hs ht hst
      have hhead : K * H₀ ≤ H := entropy_and_constant_absorption hC₀ hK hs hs1 ht hth hst
      have htail : 0 ≤ Real.rpow T ((1 - t) / (1 - s - t)) * (X + BF + BH) :=
        mul_nonneg (Real.rpow_nonneg hT _) (add_nonneg (add_nonneg hX hBF) hBH)
      calc
        _ ≤ caccioppoliWithRHSPrefactor C₀ Q a s t * (K * (X + BF + BH)) :=
          hraw.trans (mul_le_mul_of_nonneg_left hinside hP)
        _ = (K * H₀) * (Real.rpow T ((1 - t) / (1 - s - t)) * (X + BF + BH)) := by
          dsimp [caccioppoliWithRHSPrefactor, H₀, T]
          ring
        _ ≤ H * (Real.rpow T ((1 - t) / (1 - s - t)) * (X + BF + BH)) :=
          mul_le_mul_of_nonneg_right hhead htail
        _ = _ := by
          have he : s + (1 - s - t) = 1 - t := by ring
          have hfPow : Real.rpow t (-11 : ℝ) = t ^ (-11 : ℤ) := by
            convert Real.rpow_intCast t (-11 : ℤ) using 1; norm_num
          have hhPow : Real.rpow t (-3 : ℝ) = t ^ (-3 : ℤ) := by
            convert Real.rpow_intCast t (-3 : ℤ) using 1; norm_num
          have hTpaper : Ch02.ThetaRatio (originCube d 0) s t a =
              LambdaDefault (originCube d 0) s a / lambdaDefault (originCube d 0) t a := rfl
          simp only [H, T, X, BF, BH, Nf, Nh, L, Lt, Q,
            he, hfPow, hhPow, PaperPositiveSobolevField.norm]
          rw [hTpaper]
          change _ * (_ * (lambdaDefault (originCube d 0) t a * _ +
              _ * (lambdaDefault (originCube d 0) t a)⁻¹ * _ +
              _ * LambdaDefault (originCube d 0) t a * _)) = _
          ring

end
end SubdiffusiveProcess.Caccioppoli
