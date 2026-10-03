module

public import SubdiffusiveProcess.Section10.InitialSimplexEnergyAnnealed
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteReadoutComparison

@[expose] public section

/-!
# Source-derived cube energy bounds for the initial simplex packing

The Section 4 normalized-defect provider yields the affine Dirichlet energy
bound on cubes whose size matches their cutoff. Stationarity transports it to
every triadic cube. Both the disorder threshold and the bound are selected
before the model, scale, cube and slope.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Uniform cube supplier derived from the actual Section 4 provider. No
caller-supplied cube energy estimate occurs in this statement. -/
theorem exists_initialCubeEnergy_constants (d : ℕ) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 1 ≤ C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ (k : ℕ) (Q : TriadicCube d), Q.scale = (k : ℤ) → ∀ p : Vec d,
        expectedAffineDirichletEnergy M k (Ch02.cubeDomain Q) p ≤
          C * ahom M k * vecNormSq p := by
  obtain ⟨_c, C, _hc, hC, hcoarse⟩ := SubdiffusiveProcess.Frozen.Section4.coarse_grained_bound (d := d)
  let B := 1 + 2 * C * Real.log 3
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith
  refine ⟨C⁻¹, B, inv_pos.mpr hC, hB, ?_⟩
  intro M hM k Q hQ p
  letI : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  have hdeltaOne : M.delta ≤ 1 := M.shellPrefix.delta_le_half.trans (by norm_num)
  have hdeltaSq : M.delta ^ 2 ≤ 1 := by nlinarith [M.shellPrefix.delta_pos]
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hproductPos : 0 < C * M.delta ^ 2 * |Real.log M.delta| :=
    mul_pos (mul_pos hC (sq_pos_of_pos M.shellPrefix.delta_pos))
      (abs_pos.mpr hlogNeg.ne)
  have hCproduct : C * M.delta ^ 2 * |Real.log M.delta| ≤ 1 := by
    calc
      _ = C * (M.delta ^ 2 * |Real.log M.delta|) := by ring
      _ ≤ C * M.delta := mul_le_mul_of_nonneg_left
        (delta_sq_mul_abs_log_le_self M.shellPrefix.delta_pos hdeltaOne) hC.le
      _ ≤ C * C⁻¹ := mul_le_mul_of_nonneg_left hM hC.le
      _ = 1 := mul_inv_cancel₀ hC.ne'
  have hxi : 1 ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
    have hinv := (one_le_inv₀ hproductPos).2 hCproduct
    simpa only [mul_inv] using hinv
  let eps := C * Real.log 3 * M.delta ^ 2
  have heps : 0 ≤ eps := mul_nonneg (mul_nonneg hC.le hlog3.le) (sq_nonneg _)
  have hdefect := (hcoarse M 1 (by norm_num) hxi k).1
  have hdefect' : paperENNRealLpNorm M.P.toMeasure 1
      (normalizedDefect M k (Ch02.cubeDomain (originCube d (k : ℤ)))) ≤
      ENNReal.ofReal eps := by
    convert hdefect using 1
    norm_num [eps]
  let e : Vec d := Pi.single (0 : Fin d) 1
  have he : vecNormSq e = 1 := by
    change vecNormSq (Pi.single (0 : Fin d) 1) = 1
    rw [vecNormSq, vecDot, Finset.sum_eq_single (0 : Fin d)]
    · simp
    · intro b _hb hb
      simp [hb]
    · simp
  have hreadout := (sameScale_readouts_le_of_expectedJ M k k e he
    (expectedJ_le_of_normalizedDefect_lpnorm_one_le M k k e he heps hdefect')).1
  have hfactor : 1 + 2 * eps ≤ B := by
    have h := mul_le_mul_of_nonneg_left hdeltaSq
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC.le) hlog3.le)
    dsimp only [eps, B]
    nlinarith
  have hscalar : abarScalarReadout M k k ≤ B * ahom M k :=
    hreadout.trans (mul_le_mul_of_nonneg_right hfactor (ahom_pos M k).le)
  rw [expectedAffineDirichletEnergy_eq_abar, abar_cube_eq_originCube M k Q, hQ,
    abar_eq_abarScalarReadout_smul_one]
  simp only [smul_matVecMul, matVecMul_one, Homogenization.vecDot_smul_right]
  exact mul_le_mul_of_nonneg_right hscalar (vecNormSq_nonneg p)

/-- The source's annealed ordering, including equal cutoffs. -/
theorem ahom_le_exp_mul_of_le {d : ℕ} (M : GMCModel d) {k ell : ℕ} (hk : k ≤ ell) :
    ahom M k ≤ Real.exp (2 * tauSq M.P * ((ell - k : ℕ) : ℝ)) * ahom M ell := by
  rcases eq_or_lt_of_le hk with rfl | hk
  · simp only [Nat.sub_self, Nat.cast_zero, mul_zero, Real.exp_zero, one_mul]
    exact le_refl _
  · exact (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).2 M ell k hk |>.2

/-- The actual model already supplies a uniform geometric ratio below one. -/
theorem exp_two_tauSq_le_two {d : ℕ} (M : GMCModel d) : Real.exp (2 * tauSq M.P) ≤ 2 := by
  have hdeltaSq : M.delta ^ 2 ≤ 1 := by
    nlinarith [M.shellPrefix.delta_le_half, M.shellPrefix.delta_pos]
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have htau := tauSq_le_delta_sq M
  have hprod := mul_le_mul_of_nonneg_left hdeltaSq hlog2
  have harg : 2 * tauSq M.P ≤ Real.log 2 := by nlinarith
  calc
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr harg
    _ = 2 := Real.exp_log (by norm_num)

end
end SubdiffusiveProcess.Section10
