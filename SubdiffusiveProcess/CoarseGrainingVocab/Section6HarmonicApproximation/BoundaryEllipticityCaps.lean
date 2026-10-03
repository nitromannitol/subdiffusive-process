module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ExponentComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.GoodEventErrorCap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalEllipticityControl
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl

@[expose] public section

/-!
# Good-event ellipticity caps for boundary Caccioppoli

The local `q=2` error cap is converted into the two `q=1` quantities used by
boundary Caccioppoli.  The upper slot is `1/2`, the lower slot is `s/3`; their
finite-`2` companions are `1/4` and `s/6`.  Antitonicity bounds the former by
the already controlled `s/6` slot.

PROVENANCE: mirrors `Algsuperdiff/Section4/Provider/ExcessDecay/
BoundaryPrefactor.lean`, especially `ae_coveringCubeCapsPair_le`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The library's dimension-lossy upper ellipticity comparison, with the
finite-dimensional cardinal simplified. -/
theorem localMaxWeightedEllipticity_le_error
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d) {t sigma : ℝ}
    (ht : 0 < t) (hsigma : 0 < sigma) :
    max (sigma⁻¹ * Ch02.LambdaSq Q t (.finite 2) A)
        (sigma * (Ch02.lambdaSq Q t (.finite 2) A)⁻¹) ≤
      2 * (d : ℝ) *
        (Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma) ^ 2 + 1) := by
  have h :=
    Ch02.max_weightedEllipticity_finite_two_le_card_mul_homogenizationError_sq_add_one
      Q A ht hsigma
  rwa [Fintype.card_fin] at h

/-- A `q=2` ratio cap at `u/2` bounds the upper `q=1` quantity at `u`. -/
theorem LambdaS_le_of_localRatioCap
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    {u sigma B : ℝ} (hu : 0 < u) (hsigma : 0 < sigma)
    (hcap : sigma⁻¹ * Ch02.LambdaSq Q (u / 2) (.finite 2) A ≤ B) :
    Ch02.LambdaS Q u A ≤ B * sigma := by
  have hq := LambdaSq_finite_one_le_two_half Q A hu
  have hkey : sigma⁻¹ * Ch02.LambdaSq Q u (.finite 1) A ≤ B :=
    (mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hsigma.le)).trans hcap
  rw [Ch02.LambdaS]
  have hmul := mul_le_mul_of_nonneg_right hkey hsigma.le
  rw [inv_mul_eq_div, div_mul_cancel₀ _ hsigma.ne'] at hmul
  exact hmul

/-- A `q=2` ratio cap at `u/2` bounds the inverse lower `q=1` quantity. -/
theorem lambdaS_inv_le_of_localRatioCap
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    {u sigma B : ℝ} (hu : 0 < u) (hsigma : 0 < sigma)
    (hcap : sigma * (Ch02.lambdaSq Q (u / 2) (.finite 2) A)⁻¹ ≤ B) :
    (Ch02.lambdaS Q u A)⁻¹ ≤ B * sigma⁻¹ := by
  have hq := lambdaSq_finite_one_inv_le_two_half Q A hu
  have hkey : sigma * (Ch02.lambdaSq Q u (.finite 1) A)⁻¹ ≤ B :=
    (mul_le_mul_of_nonneg_left hq hsigma.le).trans hcap
  rw [Ch02.lambdaS]
  have hmul := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr hsigma.le)
  rw [mul_comm sigma, mul_assoc, mul_inv_cancel₀ hsigma.ne', mul_one] at hmul
  exact hmul

/-- The lower `q=1` constant is bounded by the upper one at positive slots. -/
theorem lambdaS_le_LambdaS_local
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    Ch02.lambdaS Q t A ≤ Ch02.LambdaS Q u A := by
  have h := Ch02.one_le_ThetaRatio_of_pos Q A hu ht
  have hpos : 0 < Ch02.lambdaS Q t A := by
    rw [Ch02.lambdaS]
    exact Ch02.lambdaSq_finite_pos Q A ht (by norm_num)
  rw [Ch02.ThetaRatio] at h
  exact (one_le_div hpos).mp h

/-- A pair of `q=1` caps bounds their contrast. -/
theorem thetaRatio_le_of_localCaps
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    {u t B₁ B₂ : ℝ} (hu : 0 < u) (ht : 0 < t)
    (h₁ : Ch02.LambdaS Q u A ≤ B₁)
    (h₂ : (Ch02.lambdaS Q t A)⁻¹ ≤ B₂) :
    Ch02.ThetaRatio Q u t A ≤ B₁ * B₂ := by
  have hL : 0 ≤ Ch02.LambdaS Q u A := by
    rw [Ch02.LambdaS]
    exact Ch02.LambdaSq_finite_nonneg Q A hu (by norm_num)
  have hl : 0 ≤ (Ch02.lambdaS Q t A)⁻¹ := by
    exact inv_nonneg.mpr (by
      rw [Ch02.lambdaS]
      exact Ch02.lambdaSq_finite_nonneg Q A ht (by norm_num))
  rw [Ch02.ThetaRatio, div_eq_mul_inv]
  exact mul_le_mul h₁ h₂ hl (hL.trans h₁)

/-- The finite-`2` cap at `s/6` also controls the two ellipticity slots used by
the Dirichlet RHS at regularity `s`: `lambda_(s/2)^{-1}` and `Lambda_s`.
This is the monotonicity step implicit in the manuscript's use of the single
local-control display. -/
theorem datumEllipticityCaps_of_sixth
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d) {s sigma K : ℝ}
    (hs : 0 < s) (hsigma : 0 < sigma)
    (hupper : sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ K)
    (hlower : sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ K) :
    sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹ ≤ K ∧
      sigma⁻¹ * Ch02.LambdaSq Q s (.finite 2) A ≤ K := by
  have hlmono : Ch02.lambdaSq Q (s / 6) (.finite 2) A ≤
      Ch02.lambdaSq Q (s / 2) (.finite 2) A :=
    Ch02.lambdaSq_finite_mono Q A (by linarith only [hs])
      (by linarith only [hs]) (by norm_num)
  have hlpos : 0 < Ch02.lambdaSq Q (s / 6) (.finite 2) A :=
    Ch02.lambdaSq_finite_pos Q A (by linarith only [hs]) (by norm_num)
  have hlinv : (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹ ≤
      (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ :=
    inv_anti₀ hlpos hlmono
  have hLmono : Ch02.LambdaSq Q s (.finite 2) A ≤
      Ch02.LambdaSq Q (s / 6) (.finite 2) A :=
    Ch02.LambdaSq_antitone Q A (by linarith only [hs])
      (by linarith only [hs]) (by norm_num)
  exact ⟨
    (mul_le_mul_of_nonneg_left hlinv hsigma.le).trans hlower,
    (mul_le_mul_of_nonneg_left hLmono (inv_nonneg.mpr hsigma.le)).trans hupper⟩

/-- The same finite-`2` cap supplies the `t=s/2` lower slot used by the
interior Caccioppoli theorem, together with its contrast against `1/2`. -/
theorem interiorHalfEllipticityCaps_of_sixth
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d) {s sigma B : ℝ}
    (hs : 0 < s) (hsigma : 0 < sigma)
    (hupper : Ch02.LambdaS Q (1 / 2) A ≤ B * sigma)
    (hlower6 : sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B) :
    (Ch02.lambdaS Q (s / 2) A)⁻¹ ≤ B * sigma⁻¹ ∧
      Ch02.lambdaS Q (s / 2) A ≤ B * sigma ∧
      Ch02.ThetaRatio Q (1 / 2) (s / 2) A ≤ B ^ (2 : ℕ) := by
  have hlmono : Ch02.lambdaSq Q (s / 6) (.finite 2) A ≤
      Ch02.lambdaSq Q (s / 4) (.finite 2) A :=
    Ch02.lambdaSq_finite_mono Q A (by linarith only [hs])
      (by linarith only [hs]) (by norm_num)
  have hlpos : 0 < Ch02.lambdaSq Q (s / 6) (.finite 2) A :=
    Ch02.lambdaSq_finite_pos Q A (by linarith only [hs]) (by norm_num)
  have hlinv : (Ch02.lambdaSq Q (s / 4) (.finite 2) A)⁻¹ ≤
      (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ :=
    inv_anti₀ hlpos hlmono
  have hlower4 : sigma * (Ch02.lambdaSq Q (s / 4) (.finite 2) A)⁻¹ ≤ B :=
    (mul_le_mul_of_nonneg_left hlinv hsigma.le).trans hlower6
  have hlamInv : (Ch02.lambdaS Q (s / 2) A)⁻¹ ≤ B * sigma⁻¹ :=
    lambdaS_inv_le_of_localRatioCap Q A (by linarith only [hs]) hsigma
      (by simpa [show s / 2 / 2 = s / 4 by ring] using! hlower4)
  have hlam : Ch02.lambdaS Q (s / 2) A ≤ B * sigma :=
    (lambdaS_le_LambdaS_local Q A (by norm_num) (by linarith only [hs])).trans hupper
  have htheta := thetaRatio_le_of_localCaps Q A (by norm_num)
    (by linarith only [hs]) hupper hlamInv
  have hcancel : (B * sigma) * (B * sigma⁻¹) = B ^ (2 : ℕ) := by
    field_simp [hsigma.ne']
  rw [hcancel] at htheta
  exact ⟨hlamInv, hlam, htheta⟩



theorem localBoundaryEllipticityCaps_of_errorCap
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    {s sigma E₀ : ℝ} (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hsigma : 0 < sigma)
    (hlocal : Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
      (scalarMatrix (d := d) sigma) ≤ E₀) :
    let B := 2 * (d : ℝ) * (E₀ ^ 2 + 1)
    sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B ∧
      sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B ∧
      Ch02.LambdaS Q (1 / 2) A ≤ B * sigma ∧
      (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * sigma⁻¹ ∧
      Ch02.lambdaS Q (s / 3) A ≤ B * sigma ∧
      Ch02.ThetaRatio Q (1 / 2) (s / 3) A ≤ B ^ (2 : ℕ) := by
  let B : ℝ := 2 * (d : ℝ) * (E₀ ^ 2 + 1)
  have hE0 : 0 ≤ Ch02.HomogenizationErrorOnCube Q (s / 6)
      .infinity (.finite 2) A (scalarMatrix (d := d) sigma) :=
    LambdaStabilitySupport.homogenizationErrorOnCube_infinity_two_nonneg
      Q A (scalarMatrix (d := d) sigma) (by linarith only [hs])
  have hsq : Ch02.HomogenizationErrorOnCube Q (s / 6)
          .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ^ 2 ≤ E₀ ^ 2 :=
    pow_le_pow_left₀ hE0 hlocal 2
  have hratio := localMaxWeightedEllipticity_le_error Q A
    (by linarith only [hs] : 0 < s / 6) hsigma
  have hratioB : max (sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A)
        (sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹) ≤ B :=
    hratio.trans (mul_le_mul_of_nonneg_left (by linarith only [hsq]) (by positivity))
  have hupper6 : sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B :=
    (le_max_left _ _).trans hratioB
  have hlower6 : sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B :=
    (le_max_right _ _).trans hratioB
  have hquarter : Ch02.LambdaSq Q (1 / 4) (.finite 2) A ≤
      Ch02.LambdaSq Q (s / 6) (.finite 2) A :=
    Ch02.LambdaSq_antitone Q A (by linarith only [hs])
      (by linarith only [hs4]) (by norm_num)
  have hupperQuarter : sigma⁻¹ * Ch02.LambdaSq Q (1 / 4) (.finite 2) A ≤ B :=
    (mul_le_mul_of_nonneg_left hquarter (inv_nonneg.mpr hsigma.le)).trans hupper6
  have hLam : Ch02.LambdaS Q (1 / 2) A ≤ B * sigma :=
    LambdaS_le_of_localRatioCap Q A (by norm_num) hsigma (by
      rw [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num]
      exact hupperQuarter)
  have hlamInv : (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * sigma⁻¹ :=
    lambdaS_inv_le_of_localRatioCap Q A (by linarith only [hs]) hsigma
      (by simpa [show s / 3 / 2 = s / 6 by ring] using! hlower6)
  have hlam : Ch02.lambdaS Q (s / 3) A ≤ B * sigma :=
    (lambdaS_le_LambdaS_local Q A (by norm_num) (by linarith only [hs])).trans hLam
  have htheta := thetaRatio_le_of_localCaps Q A (by norm_num)
    (by linarith only [hs]) hLam hlamInv
  have hcancel : (B * sigma) * (B * sigma⁻¹) = B ^ (2 : ℕ) := by
    field_simp [hsigma.ne']
  rw [hcancel] at htheta
  exact ⟨hupper6, hlower6, hLam, hlamInv, hlam, htheta⟩

/-- On the harmonic-approximation good event, all boundary-Caccioppoli
ellipticity data on `y+cube_(n-2)` are controlled by dimension-only constants.
The local error itself is retained because the coarse-graining leg consumes
it separately. -/
theorem exists_localBoundaryEllipticityCaps (d : ℕ) [NeZero d] :
    ∃ E₀ B : ℝ, 0 < E₀ ∧ 0 < B ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, n + 2 ≤ L → ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        let Q := originCube d ((n : ℤ) - 2)
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
              (scalarMatrix (d := d) sigma) ≤ E₀ ∧
          sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B ∧
          sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B ∧
          Ch02.LambdaS Q (1 / 2) A ≤ B * sigma ∧
          (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * sigma⁻¹ ∧
          Ch02.lambdaS Q (s / 3) A ≤ B * sigma ∧
          Ch02.ThetaRatio Q (1 / 2) (s / 3) A ≤ B ^ (2 : ℕ) := by
  obtain ⟨C, hC, hgoodCap⟩ := exists_section6HomogenizationError_le_of_goodEvent (d := d)
  let E₀ : ℝ := Real.sqrt (192 * (d : ℝ)) * (3 * C)
  let B : ℝ := 2 * (d : ℝ) * (E₀ ^ 2 + 1)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hE₀ : 0 < E₀ := by
    dsimp [E₀]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨E₀, B, hE₀, hB, ?_⟩
  intro M s hs L m n hnL z x y omega hx hD hgood
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using! h
  have hsection := hgoodCap M s hs L (n + 2) hnL omega z hgood
  have hlocal := localHomogenizationError_two_le_anchor M hs
    (L := L) (m := m) (n := n) hnL
    omega x y z hx hD hgood
  have hexp : s / 8 * (4 : ℝ) ≤ 1 := by linarith only [hs.2]
  have hpow : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ 3 := by
    calc
      (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 3 := by norm_num
  have hlocalCap : Ch02.HomogenizationErrorOnCube Q (s / 6)
        .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E₀ := by
    refine hlocal.trans ?_
    have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
      ENNReal.toReal_nonneg
    have hinner : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
        section6HomogenizationError M (s / 8) L (n + 2) omega z ≤ 3 * C :=
      (mul_le_mul_of_nonneg_right hpow hsec0).trans
        (mul_le_mul_of_nonneg_left hsection (by norm_num))
    exact mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg _)
  have hE0 : 0 ≤ Ch02.HomogenizationErrorOnCube Q (s / 6)
      .infinity (.finite 2) A (scalarMatrix (d := d) sigma) :=
    LambdaStabilitySupport.homogenizationErrorOnCube_infinity_two_nonneg
      Q A (scalarMatrix (d := d) sigma) (by linarith only [hs0])
  have hratio := localMaxWeightedEllipticity_le_error Q A
    (by linarith only [hs0] : 0 < s / 6) hsigma
  have hsq : Ch02.HomogenizationErrorOnCube Q (s / 6)
          .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ^ 2 ≤ E₀ ^ 2 :=
    pow_le_pow_left₀ hE0 hlocalCap 2
  have hratioB : max (sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A)
        (sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹) ≤ B :=
    hratio.trans (mul_le_mul_of_nonneg_left (by linarith only [hsq]) (by positivity))
  have hupper6 : sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B :=
    (le_max_left _ _).trans hratioB
  have hlower6 : sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B :=
    (le_max_right _ _).trans hratioB
  have hquarter : Ch02.LambdaSq Q (1 / 4) (.finite 2) A ≤
      Ch02.LambdaSq Q (s / 6) (.finite 2) A := by
    exact Ch02.LambdaSq_antitone Q A (by linarith only [hs0])
      (by linarith only [hs.2]) (by norm_num)
  have hupperQuarter : sigma⁻¹ * Ch02.LambdaSq Q (1 / 4) (.finite 2) A ≤ B :=
    (mul_le_mul_of_nonneg_left hquarter (inv_nonneg.mpr hsigma.le)).trans hupper6
  have hLam : Ch02.LambdaS Q (1 / 2) A ≤ B * sigma :=
    LambdaS_le_of_localRatioCap Q A (by norm_num) hsigma (by
      rw [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num]
      exact hupperQuarter)
  have hlamInv : (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * sigma⁻¹ :=
    lambdaS_inv_le_of_localRatioCap Q A (by linarith only [hs0]) hsigma
      (by simpa [show s / 3 / 2 = s / 6 by ring] using! hlower6)
  have hlam : Ch02.lambdaS Q (s / 3) A ≤ B * sigma :=
    (lambdaS_le_LambdaS_local Q A (by norm_num) (by linarith only [hs0])).trans hLam
  have htheta := thetaRatio_le_of_localCaps Q A (by norm_num)
    (by linarith only [hs0]) hLam hlamInv
  have hcancel : (B * sigma) * (B * sigma⁻¹) = B ^ (2 : ℕ) := by
    field_simp [hsigma.ne']
  rw [hcancel] at htheta
  simpa only [Q, A, sigma] using!
    ⟨hlocalCap, hupper6, hlower6, hLam, hlamInv, hlam, htheta⟩

/-- The same dimension-only package for a projected cell whose centre lies in
the next truncated window. -/
theorem exists_localBoundaryEllipticityCaps_nextWindow (d : ℕ) [NeZero d] :
    ∃ E₀ B : ℝ, 0 < E₀ ∧ 0 < B ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, n + 2 ≤ L → ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        y ∈ truncatedCube d m n x →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        let Q := originCube d ((n : ℤ) - 2)
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
              (scalarMatrix (d := d) sigma) ≤ E₀ ∧
          sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B ∧
          sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B ∧
          Ch02.LambdaS Q (1 / 2) A ≤ B * sigma ∧
          (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * sigma⁻¹ ∧
          Ch02.lambdaS Q (s / 3) A ≤ B * sigma ∧
          Ch02.ThetaRatio Q (1 / 2) (s / 3) A ≤ B ^ (2 : ℕ) := by
  obtain ⟨C, hC, hgoodCap⟩ := exists_section6HomogenizationError_le_of_goodEvent (d := d)
  let E₀ : ℝ := Real.sqrt (192 * (d : ℝ)) * (3 * C)
  let B : ℝ := 2 * (d : ℝ) * (E₀ ^ 2 + 1)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hE₀ : 0 < E₀ := by
    dsimp [E₀]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨E₀, B, hE₀, hB, ?_⟩
  intro M s hs L m n hnL z x y omega hx hy hgood
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using! h
  have hsection := hgoodCap M s hs L (n + 2) hnL omega z hgood
  have hlocal := localHomogenizationError_two_le_anchor_nextWindow M hs
    (L := L) (m := m) (n := n) hnL omega x y z hx hy hgood
  have hexp : s / 8 * (4 : ℝ) ≤ 1 := by linarith only [hs.2]
  have hpow : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ 3 := by
    calc
      (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 3 := by norm_num
  have hlocalCap : Ch02.HomogenizationErrorOnCube Q (s / 6)
        .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E₀ := by
    refine hlocal.trans ?_
    have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
      ENNReal.toReal_nonneg
    have hinner : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
        section6HomogenizationError M (s / 8) L (n + 2) omega z ≤ 3 * C :=
      (mul_le_mul_of_nonneg_right hpow hsec0).trans
        (mul_le_mul_of_nonneg_left hsection (by norm_num))
    exact mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg _)
  have hcaps := localBoundaryEllipticityCaps_of_errorCap Q A hs0 hs.2 hsigma hlocalCap
  simpa only [Q, A, sigma, B] using! ⟨hlocalCap, hcaps⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
