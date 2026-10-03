module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CoefficientEnergyBridge

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The lower-ellipticity factor is the square root of the inverse. -/
theorem poincareLowerEllipticityFactor_eq_sqrt_inv [NeZero d]
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    Ch03.poincareLowerEllipticityFactor Q A s (.finite 2) =
      Real.sqrt (Ch02.lambdaSq Q s (.finite 2) A)⁻¹ := by
  have hpos : 0 < Ch02.lambdaSq Q s (.finite 2) A :=
    Ch02.lambdaSq_finite_pos Q A hs (by norm_num)
  unfold Ch03.poincareLowerEllipticityFactor
  rw [Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg hpos.le]
  rfl

theorem poincareLowerEllipticityFactor_nonneg [NeZero d]
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    0 ≤ Ch03.poincareLowerEllipticityFactor Q A s (.finite 2) := by
  rw [poincareLowerEllipticityFactor_eq_sqrt_inv Q A hs]
  exact Real.sqrt_nonneg _

/-- **The pairing.**  A deterministic ellipticity cap turns `sigma^{1/2}` times
the lower-ellipticity factor into the deterministic constant `K^{1/2}`. -/
theorem sqrt_mul_poincareLowerEllipticityFactor_le [NeZero d]
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d) {s sigma K : ℝ}
    (hs : 0 < s) (hsigma : 0 ≤ sigma)
    (hcap : sigma * (Ch02.lambdaSq Q s (.finite 2) A)⁻¹ ≤ K) :
    Real.sqrt sigma * Ch03.poincareLowerEllipticityFactor Q A s (.finite 2) ≤
      Real.sqrt K := by
  rw [poincareLowerEllipticityFactor_eq_sqrt_inv Q A hs,
    ← Real.sqrt_mul hsigma]
  exact Real.sqrt_le_sqrt hcap

/-- A cap at a lower order slot is a cap at a higher one: `lambdaSq` is monotone
in the order parameter, so its inverse is antitone. -/
theorem lambdaSq_cap_mono [NeZero d]
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d) {t s sigma K : ℝ}
    (ht : 0 < t) (hts : t ≤ s) (hsigma : 0 ≤ sigma)
    (hcap : sigma * (Ch02.lambdaSq Q t (.finite 2) A)⁻¹ ≤ K) :
    sigma * (Ch02.lambdaSq Q s (.finite 2) A)⁻¹ ≤ K := by
  rcases hts.eq_or_lt with hEq | hlt
  · rwa [← hEq]
  · have hmono : Ch02.lambdaSq Q t (.finite 2) A ≤
        Ch02.lambdaSq Q s (.finite 2) A :=
      Ch02.lambdaSq_finite_mono Q A ht hlt (by norm_num)
    have hinv : (Ch02.lambdaSq Q s (.finite 2) A)⁻¹ ≤
        (Ch02.lambdaSq Q t (.finite 2) A)⁻¹ :=
      inv_anti₀ (Ch02.lambdaSq_finite_pos Q A ht (by norm_num)) hmono
    exact (mul_le_mul_of_nonneg_left hinv hsigma).trans hcap

/-! ### The composed oscillation-to-weighted-energy leg -/

/-- The dimension-only constant of the composed leg: the fractional-Poincaré
constant times the coarse-Poincaré geometric discount at `s = 1/2`, `q = 2`. -/
def interiorOscEnergyConst (d : ℕ) [NeZero d] : ℝ :=
  interiorFractionalPoincareConst d *
    Ch03.poincareDiscountFactor (1 / 2 : ℝ) (.finite 2)

theorem poincareDiscountFactor_half_two_nonneg :
    0 ≤ Ch03.poincareDiscountFactor (1 / 2 : ℝ) (Ch02.MultiscaleExponent.finite 2) := by
  unfold Ch03.poincareDiscountFactor
  exact Real.rpow_nonneg
    (Ch02.book_geometricDiscount_pos (by norm_num : (0 : ℝ) < (1 / 2) * 2)).le _

theorem interiorOscEnergyConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ interiorOscEnergyConst d :=
  mul_nonneg (interiorFractionalPoincareConst_nonneg d)
    poincareDiscountFactor_half_two_nonneg



theorem sqrt_mul_oscillation_le_weightedEnergy [NeZero d]
    (Q : TriadicCube d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {sigma K : ℝ}
    (hsigma : 0 ≤ sigma)
    (hcap : sigma *
      (Ch02.lambdaSq Q (1 / 2 : ℝ) (.finite 2) (aCutoffFamily M L omega))⁻¹ ≤ K)
    (u : H1Function (openCubeSet Q)) :
    Real.sqrt sigma *
        (cubeBesovScaleWeight (1 : ℝ) Q *
          normalizedL2On (openCubeSet Q)
            (fun y ↦ u.toFun y - volumeAverage (openCubeSet Q) u.toFun)) ≤
      interiorOscEnergyConst d * Real.sqrt K *
        vectorNormalizedL2On (openCubeSet Q)
          (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
            u.grad p) := by
  set E := vectorNormalizedL2On (openCubeSet Q)
    (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p)
    with hE
  have hE0 : 0 ≤ E := Section6Iteration.normalizedL2On_nonneg _ _
  have hdisc0 := poincareDiscountFactor_half_two_nonneg
  have hfrac0 := interiorFractionalPoincareConst_nonneg d
  have hlow0 : 0 ≤ Ch03.poincareLowerEllipticityFactor Q
      (aCutoffFamily M L omega) (1 / 2 : ℝ) (.finite 2) :=
    poincareLowerEllipticityFactor_nonneg Q _ (by norm_num)
  have h1 := normalizedL2On_fluctuation_le_scaleNormalized Q u
  have h2 := scaleNormalizedNegativeBesov_grad_le_weightedEnergy Q M L omega
    (1 / 2 : ℝ) (by norm_num) (.finite 2) (by norm_num) u
  have hpair := sqrt_mul_poincareLowerEllipticityFactor_le Q
    (aCutoffFamily M L omega) (s := 1 / 2) (sigma := sigma) (K := K)
    (by norm_num) hsigma hcap
  calc Real.sqrt sigma *
        (cubeBesovScaleWeight (1 : ℝ) Q *
          normalizedL2On (openCubeSet Q)
            (fun y ↦ u.toFun y - volumeAverage (openCubeSet Q) u.toFun))
      ≤ Real.sqrt sigma *
        (interiorFractionalPoincareConst d *
          Ch03.scaleNormalizedNegativeBesovVectorNorm Q (1 / 2 : ℝ)
            (.finite 2) u.grad) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt sigma *
        (interiorFractionalPoincareConst d *
          (Ch03.poincareDiscountFactor (1 / 2 : ℝ) (.finite 2) *
            Ch03.poincareLowerEllipticityFactor Q (aCutoffFamily M L omega)
              (1 / 2 : ℝ) (.finite 2) * E)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left h2 hfrac0
    _ = interiorOscEnergyConst d *
        (Real.sqrt sigma *
          Ch03.poincareLowerEllipticityFactor Q (aCutoffFamily M L omega)
            (1 / 2 : ℝ) (.finite 2)) * E := by
        unfold interiorOscEnergyConst
        ring
    _ ≤ interiorOscEnergyConst d * Real.sqrt K * E := by
        refine mul_le_mul_of_nonneg_right ?_ hE0
        exact mul_le_mul_of_nonneg_left hpair (interiorOscEnergyConst_nonneg d)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
