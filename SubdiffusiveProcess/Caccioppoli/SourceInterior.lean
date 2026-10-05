module

public import SubdiffusiveProcess.Caccioppoli.Interior
public import SubdiffusiveProcess.Caccioppoli.ExactDatum
@[expose] public section

namespace SubdiffusiveProcess.Caccioppoli
open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open Homogenization hiding Vec Mat TriadicCube
open Homogenization.Book.Ch03
open scoped ENNReal
noncomputable section
theorem source_interior_caccioppoli {d : ℕ} :
    2 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ (s t : ℝ), 0 < s → s < 1 → 0 < t → t < (1 / 2 : ℝ) → s + t < 1 →
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
          ∀ u : H1Function (openCubeSet (originCube d 0)),
            ∀ f : PaperPositiveSobolevField
                (originCube d 0) (2 * t) FiniteLpExponent.two,
              Ch03.ABK26.IsForcedEquation
                (originCube d 0) (a.coeffOn (originCube d 0)) u f.toField →
              coefficientEnergyNorm (originCube d (-1)) a u.grad ^ 2 ≤
                Real.rpow (C / (1 - s - t))
                    (2 + 4 * s / (1 - s - t)) *
                  Real.rpow
                    (LambdaDefault (originCube d 0) s a /
                      lambdaDefault (originCube d 0) t a)
                    (s / (1 - s - t)) *
                  LambdaDefault (originCube d 0) s a *
                  cubeLpNorm (originCube d 0) (2 : ℝ≥0∞) u.toFun ^ 2 +
                t ^ (-11 : ℤ) *
                  Real.rpow (C / (1 - s - t))
                    (2 + 4 * s / (1 - s - t)) *
                  Real.rpow
                    (LambdaDefault (originCube d 0) s a /
                      lambdaDefault (originCube d 0) t a)
                    ((1 - t) / (1 - s - t)) *
                  (lambdaDefault (originCube d 0) t a)⁻¹ *
                  f.norm.toReal ^ 2 := by
  intro hd
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C₀, hC₀, hraw⟩ := exists_originCube_caccioppoli_besov d
  let D : ℝ := caccioppoliExactDatumConstant d
  let K : ℝ := max 1 (D ^ 2)
  let C : ℝ := (Real.exp 2 * K) ^ 2 * C₀
  have hD : 0 < D := caccioppoliExactDatumConstant_pos d
  have hK_one : 1 ≤ K := le_max_left _ _
  have hDsqK : D ^ 2 ≤ K := le_max_right _ _
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK_one
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (sq_pos_of_pos (mul_pos (Real.exp_pos 2) hK_pos)) hC₀
  refine ⟨C, hC, ?_⟩
  intro s t hs hs_one ht ht_half hst a hsymm u f hEq
  have hhead := entropy_and_constant_absorption
    hC₀ hK_one hs hs_one ht ht_half hst
  cases f with
  | firstOrder hr hp F =>
      exfalso
      linarith only [hr, ht_half]
  | fractional sF hsF F =>
      let Q : Homogenization.TriadicCube d := originCube d 0
      let g : Homogenization.Vec d → Homogenization.Vec d := fun x => -F.toField x
      have hpublic : IsForcedEquation Q a u g := by
        intro phi
        have h := hEq phi
        change
          (∫ x in openCubeSet (originCube d 0),
              vecDot (matVecMul ((a.coeffOn (originCube d 0)).toCoeffField x)
                (u.grad x)) (phi.toH1Function.grad x)) =
            ∫ x in openCubeSet (originCube d 0),
              vecDot (g x) (phi.toH1Function.grad x)
        calc
          ∫ x in openCubeSet (originCube d 0),
              vecDot (matVecMul ((a.coeffOn (originCube d 0)).toCoeffField x)
                (u.grad x))
                (phi.toH1Function.grad x) =
              -(∫ x in openCubeSet (originCube d 0),
                vecDot (F.toField x) (phi.toH1Function.grad x)) := by
                simpa using! h
          _ = ∫ x in openCubeSet (originCube d 0),
              vecDot (g x) (phi.toH1Function.grad x) := by
                rw [← MeasureTheory.integral_neg]
                apply MeasureTheory.integral_congr_ae
                filter_upwards with x
                exact (vecDot_neg_left (F.toField x) (phi.toH1Function.grad x)).symm
      let G : CubeEuclideanWspField Q sF FiniteLpExponent.two :=
        negCubeEuclideanWspField F
      have hg : ForceBesovRegularity Q (2 * t) g := by
        simpa [Q, g, G, hsF] using
          Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity.toForceBesovRegularity
            (cubeEuclideanWspField_forceSobolevRegularity sF G)
            sF.2.1 sF.2.2.le
      have hrawBound := hraw s t hs hs_one ht ht_half hst a u g hsymm hpublic hg
      let L : ℝ := Ch02.lambdaS Q t a
      let T : ℝ := Ch02.ThetaRatio Q s t a
      let X : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) u.toFun ^ 2
      let N : ℝ := (paperFractionalFullNorm Q sF FiniteLpExponent.two
        F.toField).toReal ^ 2
      let R : ℝ := Real.rpow t (-10 : ℝ)
      let P₀ : ℝ := caccioppoliWithRHSPrefactor C₀ Q a s t
      let H₀ : ℝ := Real.rpow (C₀ / (1 - s - t))
          (2 + 4 * s / (1 - s - t)) *
        Real.rpow s (-(2 * s / (1 - s - t)))
      let H : ℝ := Real.rpow (C / (1 - s - t))
        (2 + 4 * s / (1 - s - t))
      have hL : 0 < L := by
        dsimp [L, Q, Ch02.lambdaS]
        exact Ch02.lambdaSq_finite_pos _ _ ht (by norm_num)
      have hT : 0 ≤ T := by
        dsimp [T]
        exact Ch02.ThetaRatio_nonneg Q a hs ht
      have hLambda : 0 ≤ Ch02.LambdaS Q s a := by
        unfold Ch02.LambdaS
        exact Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num)
      have hX : 0 ≤ X := sq_nonneg _
      have hN : 0 ≤ N := sq_nonneg _
      have hP₀ : 0 ≤ P₀ := by
        dsimp [P₀]
        exact caccioppoliWithRHSPrefactor_nonneg hC₀.le hs ht hst
      have hden : 0 < 1 - s - t := by linarith
      have hH₀ : 0 ≤ H₀ := by
        dsimp [H₀]
        exact mul_nonneg (Real.rpow_nonneg (div_nonneg hC₀.le hden.le) _)
          (Real.rpow_nonneg hs.le _)
      have hH : 0 ≤ H := by
        dsimp [H]
        exact Real.rpow_nonneg (div_nonneg hC.le hden.le) _
      have hH₀H : H₀ ≤ H := by
        have hle : H₀ ≤ K * H₀ := by
          nlinarith only [hK_one, hH₀]
        exact hle.trans (by simpa [H₀, H, C, D, K, Q] using hhead)
      have hDH₀H : D ^ 2 * H₀ ≤ H := by
        calc
          D ^ 2 * H₀ ≤ K * H₀ :=
            mul_le_mul_of_nonneg_right hDsqK hH₀
          _ ≤ H := by simpa [H₀, H, C, D, K, Q] using hhead
      have hbesov := besov_neg_sq_le_paperFractionalFullNorm d ht sF hsF F
      have hcoef : Real.rpow t (-10 : ℝ) * Real.rpow (2 * t) (-1 : ℝ) ≤
          Real.rpow t (-11 : ℝ) := by
        simpa only [show -(10 + 1 : ℝ) = -11 by norm_num] using
          (rpow_mul_two_t_inv_le (k := 10) ht)
      have hforceInside :
          R * Real.rpow L (-1 : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 ≤
            D ^ 2 * Real.rpow t (-11 : ℝ) * Real.rpow L (-1 : ℝ) * N := by
        have hR : 0 ≤ R := by
          dsimp [R]
          exact Real.rpow_nonneg ht.le _
        have hLinv : 0 ≤ Real.rpow L (-1 : ℝ) := Real.rpow_nonneg hL.le _
        calc
          R * Real.rpow L (-1 : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 ≤
            R * Real.rpow L (-1 : ℝ) *
              (D ^ 2 * Real.rpow (2 * t) (-1 : ℝ) * N) :=
                mul_le_mul_of_nonneg_left (by simpa [Q, g, D, N] using hbesov)
                  (mul_nonneg hR hLinv)
          _ = D ^ 2 * (R * Real.rpow (2 * t) (-1 : ℝ)) *
              Real.rpow L (-1 : ℝ) * N := by ring
          _ ≤ D ^ 2 * Real.rpow t (-11 : ℝ) * Real.rpow L (-1 : ℝ) * N := by
            have hmain : D ^ 2 * (R * Real.rpow (2 * t) (-1 : ℝ)) ≤
                D ^ 2 * Real.rpow t (-11 : ℝ) :=
              mul_le_mul_of_nonneg_left (by simpa [R] using hcoef) (sq_nonneg D)
            calc
              D ^ 2 * (R * Real.rpow (2 * t) (-1 : ℝ)) *
                  Real.rpow L (-1 : ℝ) * N ≤
                (D ^ 2 * Real.rpow t (-11 : ℝ)) *
                  Real.rpow L (-1 : ℝ) * N :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_right hmain hLinv) hN
              _ = _ := by ring
      have hhom :
          P₀ * (L * X) ≤
            H * Real.rpow T (s / (1 - s - t)) * Ch02.LambdaS Q s a * X := by
        have htail : 0 ≤ Real.rpow T (s / (1 - s - t)) *
            Ch02.LambdaS Q s a * X :=
          mul_nonneg (mul_nonneg (Real.rpow_nonneg hT _) hLambda) hX
        have hexp : (1 - t) / (1 - s - t) =
            s / (1 - s - t) + 1 := by
          field_simp [hden.ne']
          ring
        have hT_pos : 0 < T := by
          exact lt_of_lt_of_le zero_lt_one
            (by simpa [T] using Ch02.one_le_ThetaRatio_of_pos Q a hs ht)
        have hTL : T * L = Ch02.LambdaS Q s a := by
          change Ch02.LambdaS Q s a / L * L = Ch02.LambdaS Q s a
          exact div_mul_cancel₀ _ hL.ne'
        have hTadd : Real.rpow T (s / (1 - s - t) + 1) =
            Real.rpow T (s / (1 - s - t)) * T := by
          simpa using
            (Real.rpow_add hT_pos (s / (1 - s - t)) (1 : ℝ))
        calc
          P₀ * (L * X) =
              H₀ * (Real.rpow T (s / (1 - s - t)) *
                Ch02.LambdaS Q s a * X) := by
            dsimp [P₀]
            unfold caccioppoliWithRHSPrefactor
            change H₀ * Real.rpow T ((1 - t) / (1 - s - t)) * (L * X) = _
            rw [hexp, hTadd]
            let W : ℝ := Real.rpow T (s / (1 - s - t))
            change H₀ * (W * T) * (L * X) = H₀ * (W * Ch02.LambdaS Q s a * X)
            calc
              H₀ * (W * T) * (L * X) = H₀ * W * (T * L) * X := by ring
              _ = H₀ * W * Ch02.LambdaS Q s a * X := by rw [hTL]
              _ = H₀ * (W * Ch02.LambdaS Q s a * X) := by ring
          _ ≤ H * (Real.rpow T (s / (1 - s - t)) *
                Ch02.LambdaS Q s a * X) :=
            mul_le_mul_of_nonneg_right hH₀H htail
          _ = H * Real.rpow T (s / (1 - s - t)) *
                Ch02.LambdaS Q s a * X := by ring
      have hforce :
          P₀ * (R * Real.rpow L (-1 : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) ≤
            Real.rpow t (-11 : ℝ) * H *
              Real.rpow T ((1 - t) / (1 - s - t)) *
              L⁻¹ * N := by
        have htail : 0 ≤ Real.rpow t (-11 : ℝ) *
            Real.rpow T ((1 - t) / (1 - s - t)) * L⁻¹ * N :=
          mul_nonneg
            (mul_nonneg
              (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hT _))
              (inv_nonneg.mpr hL.le)) hN
        calc
          P₀ * (R * Real.rpow L (-1 : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) ≤
            P₀ * (D ^ 2 * Real.rpow t (-11 : ℝ) *
              Real.rpow L (-1 : ℝ) * N) :=
                mul_le_mul_of_nonneg_left hforceInside hP₀
          _ = (D ^ 2 * H₀) *
              (Real.rpow t (-11 : ℝ) *
                Real.rpow T ((1 - t) / (1 - s - t)) * L⁻¹ * N) := by
            dsimp [P₀]
            unfold caccioppoliWithRHSPrefactor
            change H₀ * Real.rpow T ((1 - t) / (1 - s - t)) *
              (D ^ 2 * Real.rpow t (-11 : ℝ) * Real.rpow L (-1 : ℝ) * N) = _
            have hLinvEq : Real.rpow L (-1 : ℝ) = L⁻¹ :=
              Real.rpow_neg_one L
            rw [hLinvEq]
            let Z : ℝ := Real.rpow t (-11 : ℝ)
            let W : ℝ := Real.rpow T ((1 - t) / (1 - s - t))
            change H₀ * W * (D ^ 2 * Z * L⁻¹ * N) =
              (D ^ 2 * H₀) * (Z * W * L⁻¹ * N)
            ring
          _ ≤ H * (Real.rpow t (-11 : ℝ) *
                Real.rpow T ((1 - t) / (1 - s - t)) * L⁻¹ * N) :=
            mul_le_mul_of_nonneg_right hDH₀H htail
          _ = Real.rpow t (-11 : ℝ) * H *
              Real.rpow T ((1 - t) / (1 - s - t)) * L⁻¹ * N := by ring
      calc
        coefficientEnergyNorm (originCube d (-1)) a u.grad ^ 2 ≤
            P₀ * (L * X + R * Real.rpow L (-1 : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := by
          simpa [Q, g, L, X, R, P₀] using hrawBound
        _ = P₀ * (L * X) + P₀ *
            (R * Real.rpow L (-1 : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) :=
          mul_add _ _ _
        _ ≤ H * Real.rpow T (s / (1 - s - t)) *
              Ch02.LambdaS Q s a * X +
            Real.rpow t (-11 : ℝ) * H *
              Real.rpow T ((1 - t) / (1 - s - t)) * L⁻¹ * N :=
          add_le_add hhom hforce
        _ = _ := by
          have ht11 : Real.rpow t (-11 : ℝ) = t ^ (-11 : ℤ) :=
            by
              convert Real.rpow_intCast t (-11 : ℤ) using 1
              norm_num
          have hTpaper : Ch02.ThetaRatio (originCube d 0) s t a =
              LambdaDefault (originCube d 0) s a /
                lambdaDefault (originCube d 0) t a := rfl
          rw [ht11]
          simp only [H, T, L, X, N, Q, C, PaperPositiveSobolevField.norm]
          rw [hTpaper]
          change
            _ * _ * LambdaDefault (originCube d 0) s a * _ +
                _ * _ * _ * (lambdaDefault (originCube d 0) t a)⁻¹ * _ = _
          ring

end
end SubdiffusiveProcess.Caccioppoli
