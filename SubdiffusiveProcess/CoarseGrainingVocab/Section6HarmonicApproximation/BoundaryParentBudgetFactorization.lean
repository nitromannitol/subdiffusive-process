import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCenteredForce

/-!
# Radius-independent factorization of the common boundary budget

This file separates the polynomial bookkeeping in the finite-cell Young
envelope from the geometric estimates used to bound its coefficients.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03

noncomputable section

/-- The solution-side finite-`2` normalizer is exactly linear in the common
descendant weight.  Keeping this identity intact avoids separating the
canceling `sigma` factors later in the boundary budget. -/
theorem boundaryCommon_solutionNormalizer_sq
    {C t W K sigma : ℝ} (hW : 0 ≤ W) (hK : 0 ≤ K) (hsigma : 0 < sigma) :
    (C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)) ^ 2 =
      (C ^ 2 * t⁻¹ ^ 2 * K * sigma) * W := by
  calc
    _ = C ^ 2 * t⁻¹ ^ 2 * (Real.sqrt (W * K)) ^ 2 *
        (Real.sqrt sigma) ^ 2 := by ring
    _ = _ := by
      rw [Real.sq_sqrt (mul_nonneg hW hK), Real.sq_sqrt hsigma.le]
      ring

/-- The forcing-side finite-`2` normalizers cancel exactly, leaving a
quadratic common descendant weight. -/
theorem boundaryCommon_forceNormalizer_sq
    {C t W K sigma : ℝ} (hW : 0 ≤ W) (hK : 0 ≤ K) (hsigma : 0 < sigma) :
    (C * Real.rpow t (-(5 / 2 : ℝ)) *
      (Real.sqrt (W * K) * Real.sqrt sigma) *
      (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)) ^ 2 =
      (C ^ 2 * Real.rpow t (-(5 / 2 : ℝ)) ^ 2 * K ^ 2) * W ^ 2 := by
  have hInv : 0 ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
  calc
    _ = C ^ 2 * Real.rpow t (-(5 / 2 : ℝ)) ^ 2 *
        (Real.sqrt (W * K)) ^ 4 * (Real.sqrt sigma) ^ 2 *
          (Real.sqrt sigma⁻¹) ^ 2 := by ring
    _ = C ^ 2 * Real.rpow t (-(5 / 2 : ℝ)) ^ 2 *
        (W * K) ^ 2 * sigma * sigma⁻¹ := by
      rw [show (Real.sqrt (W * K)) ^ 4 = (W * K) ^ 2 by
        calc
          (Real.sqrt (W * K)) ^ 4 = ((Real.sqrt (W * K)) ^ 2) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt (mul_nonneg hW hK)],
        Real.sq_sqrt hsigma.le, Real.sq_sqrt hInv]
    _ = _ := by field_simp [hsigma.ne']

/-- Scalar cancellation behind the finite-height tail coefficient.  If the
prefactor `c*A*sqrt 2*Y` is at most `D*W`, the tail is at most `2`, and
`A^2=a2*W`, then the square of `Y*tail` is again only linear in `W`.
This is the normalization-preserving form used by both boundary lanes. -/
theorem boundaryCommon_tailCoefficient_sq_le_weight
    {c A Y tail D W a2 : ℝ}
    (hc : 0 < c) (hA : 0 < A) (hY : 0 ≤ Y) (htail0 : 0 ≤ tail)
    (htail2 : tail ≤ 2) (hD : 0 ≤ D) (hW : 1 ≤ W) (ha2 : 0 < a2)
    (hAsq : A ^ 2 = a2 * W)
    (hpref : c * A * Real.sqrt 2 * Y ≤ D * W) :
    (Y * tail) ^ 2 ≤ (2 * D ^ 2 / (c ^ 2 * a2)) * W := by
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hfront0 : 0 ≤ c * A * Real.sqrt 2 * Y := by positivity
  have hright0 : 0 ≤ D * W := mul_nonneg hD hW0.le
  have hsq := pow_le_pow_left₀ hfront0 hpref 2
  have hsqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hcore : 2 * (c ^ 2 * a2) * W * Y ^ 2 ≤ D ^ 2 * W ^ 2 := by
    calc
      _ = (c * A * Real.sqrt 2 * Y) ^ 2 := by
        calc
          _ = 2 * c ^ 2 * (a2 * W) * Y ^ 2 := by ring
          _ = 2 * c ^ 2 * A ^ 2 * Y ^ 2 := by rw [hAsq]
          _ = c ^ 2 * A ^ 2 * (Real.sqrt 2) ^ 2 * Y ^ 2 := by
            rw [hsqrt2]
            ring
          _ = _ := by ring
      _ ≤ (D * W) ^ 2 := hsq
      _ = _ := by ring
  have hcancel : 2 * (c ^ 2 * a2) * Y ^ 2 ≤ D ^ 2 * W := by
    apply le_of_mul_le_mul_right (a := W) _ hW0
    convert hcore using 1 <;> ring
  have htailSq : (Y * tail) ^ 2 ≤ 4 * Y ^ 2 := by
    have hp := pow_le_pow_left₀ htail0 htail2 2
    calc
      _ = Y ^ 2 * tail ^ 2 := by ring
      _ ≤ Y ^ 2 * 2 ^ 2 := mul_le_mul_of_nonneg_left hp (sq_nonneg Y)
      _ = _ := by ring
  have hden : 0 < c ^ 2 * a2 := mul_pos (sq_pos_of_pos hc) ha2
  rw [show (2 * D ^ 2 / (c ^ 2 * a2)) * W =
      (2 * D ^ 2 * W) / (c ^ 2 * a2) by ring, le_div_iff₀ hden]
  calc
    (Y * tail) ^ 2 * (c ^ 2 * a2) ≤
        (4 * Y ^ 2) * (c ^ 2 * a2) :=
      mul_le_mul_of_nonneg_right htailSq hden.le
    _ ≤ 2 * D ^ 2 * W := by nlinarith only [hcancel]
    _ = 2 * D ^ 2 * W := rfl

/-- The prefactor-selected finite tail is at most two.  The sharper product
estimate is used for absorption; this coarse bound is the one needed after
the normalizer cancellation in the averaged parent budget. -/
theorem boundaryFiniteHeightTail_heightOfPrefactor_le_two
    {t P : ℝ} (ht : 0 < t) (ht4 : t ≤ 1 / 4) :
    boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t)
        (Nat.ceil (boundaryFiniteHeightOfPrefactor t P)) ≤ 2 := by
  have htail := boundaryFiniteHeightTailOneSub_natCeil_le_two_mul
    (t := t) (h := boundaryFiniteHeightOfPrefactor t P) ht4
  have hheight := boundaryFiniteHeightOfPrefactor_nonneg t P
  have hexp : -(1 - 2 * t) * boundaryFiniteHeightOfPrefactor t P ≤ 0 := by
    have : 0 ≤ 1 - 2 * t := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr this) hheight
  have hp : Real.rpow (3 : ℝ)
      (-(1 - 2 * t) * boundaryFiniteHeightOfPrefactor t P) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
  exact htail.trans (by nlinarith)

/-- The uncentered-solution coefficient carries at most the squared
canonical cutoff loss.  This scalar form keeps the parent inverse length
outside the radius-dependent carrier. -/
theorem boundaryCommon_uncenteredCoeff_sq_le
    {dim xi ellChild ell B Gs D : ℝ}
    (hellChild : 0 ≤ ellChild)
    (hell : 0 < ell) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hellChild_le : ellChild ≤ ell) (hDdef : D = ell ^ 2 * B)
    (hxiSq : xi ^ 2 ≤ 2 * ell⁻¹ ^ 2 * D) :
    (dim * xi + 2 * ellChild * B * Gs) ^ 2 ≤
      ((4 * dim ^ 2 + 8 * Gs ^ 2) * ell⁻¹ ^ 2) * (1 + D) ^ 2 := by
  have hell0 : 0 ≤ ell := hell.le
  have hfirst : 2 * (dim * xi) ^ 2 ≤
      4 * dim ^ 2 * ell⁻¹ ^ 2 * D := by
    calc
      _ = 2 * dim ^ 2 * xi ^ 2 := by ring
      _ ≤ 2 * dim ^ 2 * (2 * ell⁻¹ ^ 2 * D) := by gcongr
      _ = _ := by ring
  have hchildB : ellChild * B ≤ ell * B :=
    mul_le_mul_of_nonneg_right hellChild_le hB
  have hsecond : 2 * (2 * ellChild * B * Gs) ^ 2 ≤
      8 * Gs ^ 2 * ell⁻¹ ^ 2 * D ^ 2 := by
    have hp := pow_le_pow_left₀ (mul_nonneg hellChild hB) hchildB 2
    calc
      _ = 8 * (ellChild * B) ^ 2 * Gs ^ 2 := by ring
      _ ≤ 8 * (ell * B) ^ 2 * Gs ^ 2 := by gcongr
      _ = 8 * Gs ^ 2 * ell⁻¹ ^ 2 * D ^ 2 := by
        rw [hDdef]
        field_simp [hell.ne']
  have hadd : (dim * xi + 2 * ellChild * B * Gs) ^ 2 ≤
      2 * (dim * xi) ^ 2 + 2 * (2 * ellChild * B * Gs) ^ 2 := by
    nlinarith [sq_nonneg (dim * xi - 2 * ellChild * B * Gs)]
  have hDlin : D ≤ (1 + D) ^ 2 := by nlinarith [sq_nonneg D]
  have hDsq : D ^ 2 ≤ (1 + D) ^ 2 := by nlinarith
  calc
    _ ≤ 2 * (dim * xi) ^ 2 + 2 * (2 * ellChild * B * Gs) ^ 2 := hadd
    _ ≤ 4 * dim ^ 2 * ell⁻¹ ^ 2 * D +
        8 * Gs ^ 2 * ell⁻¹ ^ 2 * D ^ 2 := add_le_add hfirst hsecond
    _ ≤ 4 * dim ^ 2 * ell⁻¹ ^ 2 * (1 + D) ^ 2 +
        8 * Gs ^ 2 * ell⁻¹ ^ 2 * (1 + D) ^ 2 := by gcongr
    _ = _ := by ring

/-- The centered-solution coefficient is paid by one cutoff loss and the
finite-height head. -/
theorem boundaryCommon_centeredCoeff_sq_le
    {xi ell head D : ℝ} (hell : 0 < ell) (hD : 0 ≤ D)
    (hxiSq : xi ^ 2 ≤ 2 * ell⁻¹ ^ 2 * D) :
    (2 * xi * head) ^ 2 ≤
      (8 * ell⁻¹ ^ 2) * (1 + head ^ 2) * (1 + D) := by
  have hmain : (2 * xi * head) ^ 2 ≤
      8 * ell⁻¹ ^ 2 * D * head ^ 2 := by
    calc
      _ = 4 * xi ^ 2 * head ^ 2 := by ring
      _ ≤ 4 * (2 * ell⁻¹ ^ 2 * D) * head ^ 2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 8 * ell⁻¹ ^ 2 * D * head ^ 2 := hmain
    _ ≤ (8 * ell⁻¹ ^ 2) * (1 + head ^ 2) * (1 + D) := by
      have : D * head ^ 2 ≤ (1 + head ^ 2) * (1 + D) := by
        nlinarith [sq_nonneg head]
      calc
        _ = (8 * ell⁻¹ ^ 2) * (D * head ^ 2) := by ring
        _ ≤ (8 * ell⁻¹ ^ 2) * ((1 + head ^ 2) * (1 + D)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring

private theorem youngKz_le
    {C sigma A W a2 : ℝ} (hsigma : 0 < sigma) (hW : 1 ≤ W)
    (_ha2 : 0 ≤ a2) (hAsq : A ^ 2 ≤ a2 * W) :
    4 * (C * A) ^ 2 + sigma / 2 ≤
      (4 * C ^ 2 * a2 + sigma / 2) * W := by
  calc
    4 * (C * A) ^ 2 + sigma / 2 = 4 * C ^ 2 * A ^ 2 + sigma / 2 := by ring
    _ ≤ 4 * C ^ 2 * (a2 * W) + sigma / 2 := by gcongr
    _ ≤ (4 * C ^ 2 * a2 + sigma / 2) * W := by
      nlinarith [hsigma.le, hW]

private theorem youngKg_le
    {C sigma mu T W E mm2 : ℝ}
    (hsigma : 0 < sigma) (hT : 1 ≤ T) (hW : 1 ≤ W) (hE : 1 ≤ E)
    (_hmm2 : 0 ≤ mm2) (hmusq : mu ^ 2 ≤ mm2 * T * W * E) :
    4 * (C * Real.sqrt 2 * mu) ^ 2 + C ^ 2 / (2 * sigma) ≤
      (8 * C ^ 2 * mm2 + C ^ 2 / (2 * sigma)) * (T * W * E) := by
  have hTW : 1 ≤ T * W :=
    one_mul (1 : ℝ) ▸ mul_le_mul hT hW (by norm_num) (by linarith)
  have hcarrier : 1 ≤ T * W * E :=
    one_mul (1 : ℝ) ▸ mul_le_mul hTW hE (by norm_num) (by positivity)
  have hden : 0 ≤ C ^ 2 / (2 * sigma) := by positivity
  calc
    4 * (C * Real.sqrt 2 * mu) ^ 2 + C ^ 2 / (2 * sigma) =
        8 * C ^ 2 * mu ^ 2 + C ^ 2 / (2 * sigma) := by
      calc
        _ = 4 * C ^ 2 * (Real.sqrt 2) ^ 2 * mu ^ 2 +
            C ^ 2 / (2 * sigma) := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
    _ ≤ 8 * C ^ 2 * (mm2 * T * W * E) + C ^ 2 / (2 * sigma) := by gcongr
    _ ≤ 8 * C ^ 2 * (mm2 * T * W * E) +
        (C ^ 2 / (2 * sigma)) * (T * W * E) :=
      add_le_add_right (le_mul_of_one_le_right hden hcarrier) _
    _ = (8 * C ^ 2 * mm2 + C ^ 2 / (2 * sigma)) * (T * W * E) := by ring

private theorem youngMain_le
    {mu Au Bu BE X T W E mm2 au2 bu2 : ℝ}
    (hBE : 0 ≤ BE) (_hX : 0 ≤ X) (hT : 1 ≤ T) (hW : 1 ≤ W)
    (hE : 1 ≤ E) (hmm2 : 0 ≤ mm2) (hau2 : 0 ≤ au2)
    (hbu2 : 0 ≤ bu2)
    (hmusq : mu ^ 2 ≤ mm2 * T * W * E)
    (hAusq : Au ^ 2 ≤ au2 * E ^ 2)
    (hBusq : Bu ^ 2 ≤ bu2 * T * E) :
    4 * mu ^ 2 * BE + 2 * (2 * Au ^ 2 + 8 * Bu ^ 2) * X ^ 2 ≤
      (4 * mm2 * BE + (4 * au2 + 16 * bu2) * X ^ 2) * (T * W * E ^ 2) := by
  have hT0 : 0 ≤ T := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hmuTerm : 4 * mu ^ 2 * BE ≤ 4 * mm2 * BE * (T * W * E ^ 2) := by
    calc
      _ ≤ 4 * (mm2 * T * W * E) * BE := by gcongr
      _ ≤ 4 * (mm2 * T * W * E) * BE * E := by
        exact le_mul_of_one_le_right (by positivity) hE
      _ = _ := by ring
  have hTW : 1 ≤ T * W :=
    one_mul (1 : ℝ) ▸ mul_le_mul hT hW (by norm_num) hT0
  have hAuTerm : 4 * Au ^ 2 * X ^ 2 ≤ 4 * au2 * X ^ 2 * (T * W * E ^ 2) := by
    calc
      _ ≤ 4 * (au2 * E ^ 2) * X ^ 2 := by gcongr
      _ ≤ (4 * (au2 * E ^ 2) * X ^ 2) * (T * W) :=
        le_mul_of_one_le_right (by positivity) hTW
      _ = _ := by ring
  have hWE : 1 ≤ W * E :=
    one_mul (1 : ℝ) ▸ mul_le_mul hW hE (by norm_num) hW0
  have hBuTerm : 16 * Bu ^ 2 * X ^ 2 ≤ 16 * bu2 * X ^ 2 * (T * W * E ^ 2) := by
    calc
      _ ≤ 16 * (bu2 * T * E) * X ^ 2 := by gcongr
      _ ≤ (16 * (bu2 * T * E) * X ^ 2) * (W * E) :=
        le_mul_of_one_le_right (by positivity) hWE
      _ = _ := by ring
  calc
    _ = 4 * mu ^ 2 * BE + 4 * Au ^ 2 * X ^ 2 + 16 * Bu ^ 2 * X ^ 2 := by ring
    _ ≤ 4 * mm2 * BE * (T * W * E ^ 2) +
        4 * au2 * X ^ 2 * (T * W * E ^ 2) +
        16 * bu2 * X ^ 2 * (T * W * E ^ 2) :=
      add_le_add (add_le_add hmuTerm hAuTerm) hBuTerm
    _ = _ := by ring

private theorem youngForce_le
    {Af Bf G L W af2 bf2 : ℝ} (_hG : 0 ≤ G) (_hL : 0 ≤ L)
    (hW : 1 ≤ W) (_haf2 : 0 ≤ af2) (hbf2 : 0 ≤ bf2)
    (hAfsq : Af ^ 2 ≤ af2 * W ^ 2) (hBfsq : Bf ^ 2 ≤ bf2) :
    2 * Af ^ 2 * G ^ 2 + 2 * Bf ^ 2 * L ^ 2 ≤
      (2 * af2 * G ^ 2 + 2 * bf2 * L ^ 2) * W ^ 2 := by
  have hWsq : 1 ≤ W ^ 2 := by nlinarith
  have hfirst : 2 * Af ^ 2 * G ^ 2 ≤ 2 * af2 * G ^ 2 * W ^ 2 := by
    calc
      _ ≤ 2 * (af2 * W ^ 2) * G ^ 2 := by gcongr
      _ = _ := by ring
  have hsecond : 2 * Bf ^ 2 * L ^ 2 ≤ 2 * bf2 * L ^ 2 * W ^ 2 := by
    calc
      _ ≤ 2 * bf2 * L ^ 2 := by gcongr
      _ ≤ (2 * bf2 * L ^ 2) * W ^ 2 :=
        le_mul_of_one_le_right (by positivity) hWsq
      _ = _ := by ring
  calc
    _ ≤ 2 * af2 * G ^ 2 * W ^ 2 + 2 * bf2 * L ^ 2 * W ^ 2 :=
      add_le_add hfirst hsecond
    _ = _ := by ring

/-- Pure scalar factorization of the normalizer-preserving parent budget.
The hypotheses are the six coefficient estimates supplied by the canonical
cutoff and the finite-height construction. -/
theorem boundaryCommonYoungBudget_le_factored
    {C sigma A Af mu Au Bu Bf H W D BE X G L
      a2 af2 mm2 au2 bu2 bf2 : ℝ}
    (hsigma : 0 < sigma)
    (hBE : 0 ≤ BE) (hX : 0 ≤ X)
    (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hW : 1 ≤ W) (hD : 0 ≤ D)
    (ha2 : 0 ≤ a2) (haf2 : 0 ≤ af2) (hmm2 : 0 ≤ mm2)
    (hau2 : 0 ≤ au2) (hbu2 : 0 ≤ bu2) (hbf2 : 0 ≤ bf2)
    (hAsq : A ^ 2 ≤ a2 * W)
    (hAfsq : Af ^ 2 ≤ af2 * W ^ 2)
    (hmusq : mu ^ 2 ≤ mm2 * (1 + H ^ 2) * W * (1 + D))
    (hAusq : Au ^ 2 ≤ au2 * (1 + D) ^ 2)
    (hBusq : Bu ^ 2 ≤ bu2 * (1 + H ^ 2) * (1 + D))
    (hBfsq : Bf ^ 2 ≤ bf2) :
    (4 * (C * A) ^ 2 + sigma / 2) *
        (4 * mu ^ 2 * BE +
          2 * (2 * Au ^ 2 + 8 * Bu ^ 2) * X ^ 2) +
      (4 * (C * Real.sqrt 2 * mu) ^ 2 + C ^ 2 / (2 * sigma)) *
        (2 * Af ^ 2 * G ^ 2 + 2 * Bf ^ 2 * L ^ 2) ≤
      ((4 * C ^ 2 * a2 + sigma / 2) *
          (4 * mm2 * BE + (4 * au2 + 16 * bu2) * X ^ 2) +
        (8 * C ^ 2 * mm2 + C ^ 2 / (2 * sigma)) *
          (2 * af2 * G ^ 2 + 2 * bf2 * L ^ 2)) *
        ((1 + H ^ 2) * W ^ 3 * (1 + D) ^ 2) := by
  have hT : 1 ≤ 1 + H ^ 2 := by nlinarith [sq_nonneg H]
  have hE : 1 ≤ 1 + D := by linarith
  have hKz := youngKz_le (C := C) hsigma hW ha2 hAsq
  have hKg := youngKg_le (C := C) hsigma hT hW hE hmm2 hmusq
  have hmain := youngMain_le hBE hX hT hW hE hmm2 hau2 hbu2 hmusq hAusq hBusq
  have hforce := youngForce_le hG hL hW haf2 hbf2 hAfsq hBfsq
  have hz0 : 0 ≤ 4 * C ^ 2 * a2 + sigma / 2 := by positivity
  have hz1 : 0 ≤ 4 * mm2 * BE + (4 * au2 + 16 * bu2) * X ^ 2 := by positivity
  have hg0 : 0 ≤ 8 * C ^ 2 * mm2 + C ^ 2 / (2 * sigma) := by positivity
  have hg1 : 0 ≤ 2 * af2 * G ^ 2 + 2 * bf2 * L ^ 2 := by positivity
  let bz := 4 * C ^ 2 * a2 + sigma / 2
  let bm := 4 * mm2 * BE + (4 * au2 + 16 * bu2) * X ^ 2
  let bg := 8 * C ^ 2 * mm2 + C ^ 2 / (2 * sigma)
  let bf := 2 * af2 * G ^ 2 + 2 * bf2 * L ^ 2
  let T := 1 + H ^ 2
  let E := 1 + D
  have hfirstGrow : (bz * W) * (bm * (T * W * E ^ 2)) ≤
      (bz * bm) * (T * W ^ 3 * E ^ 2) := by
    have hbase : 0 ≤ bz * bm * T * W ^ 2 * E ^ 2 := by
      dsimp [bz, bm, T, E]
      positivity
    calc
      _ = bz * bm * T * W ^ 2 * E ^ 2 := by ring
      _ ≤ (bz * bm * T * W ^ 2 * E ^ 2) * W :=
        le_mul_of_one_le_right hbase hW
      _ = _ := by ring
  have hsecondGrow : (bg * (T * W * E)) * (bf * W ^ 2) ≤
      (bg * bf) * (T * W ^ 3 * E ^ 2) := by
    have hbase : 0 ≤ bg * bf * T * W ^ 3 * E := by
      dsimp [bg, bf, T, E]
      positivity
    calc
      _ = bg * bf * T * W ^ 3 * E := by ring
      _ ≤ (bg * bf * T * W ^ 3 * E) * E :=
        le_mul_of_one_le_right hbase hE
      _ = _ := by ring
  calc
    _ ≤ ((4 * C ^ 2 * a2 + sigma / 2) * W) *
          ((4 * mm2 * BE + (4 * au2 + 16 * bu2) * X ^ 2) *
            ((1 + H ^ 2) * W * (1 + D) ^ 2)) +
        ((8 * C ^ 2 * mm2 + C ^ 2 / (2 * sigma)) *
          ((1 + H ^ 2) * W * (1 + D))) *
          ((2 * af2 * G ^ 2 + 2 * bf2 * L ^ 2) * W ^ 2) := by
      exact add_le_add
        (mul_le_mul hKz hmain
          (by positivity) (by positivity))
        (mul_le_mul hKg hforce
          (by positivity) (by positivity))
    _ ≤ (bz * bm) * (T * W ^ 3 * E ^ 2) +
        (bg * bf) * (T * W ^ 3 * E ^ 2) :=
      add_le_add hfirstGrow hsecondGrow
    _ = ((4 * C ^ 2 * a2 + sigma / 2) *
          (4 * mm2 * BE + (4 * au2 + 16 * bu2) * X ^ 2) +
        (8 * C ^ 2 * mm2 + C ^ 2 / (2 * sigma)) *
          (2 * af2 * G ^ 2 + 2 * bf2 * L ^ 2)) *
        ((1 + H ^ 2) * W ^ 3 * (1 + D) ^ 2) := by
      dsimp [bz, bm, bg, bf, T, E]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
