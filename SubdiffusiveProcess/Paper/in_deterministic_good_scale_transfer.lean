/-
Reviewed transfer bridges.
Every supporting declaration is an `aux_in_deterministic_good_scale_transfer_*`
helper inside `namespace SubdiffusiveProcess.Paper`.
-/
module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Model.ACutoff
public import SubdiffusiveProcess.Vocab.Ahom
public import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.EllipticitySpecialization
public import Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import Homogenization.Book.Ch02.Theorems.Dilation
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import SubdiffusiveProcess.Assumptions.Cutoff
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.product_threshold_good_scale
public import SubdiffusiveProcess.Paper.product_threshold_regularities
public import SubdiffusiveProcess.Paper.in_deterministic_budget_transfer
public import SubdiffusiveProcess.Paper.in_deterministic_equal_scale_b12
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import Mathlib.Analysis.Complex.ExponentialBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.CoefficientResponse

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book
open SubdiffusiveProcess
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper


lemma aux_in_deterministic_good_scale_transfer_uv_ir_sum (F : ℤ → ℝ) (N K : ℕ) :
    ∑ k ∈ Finset.range (N + K + 1), F ((k : ℤ) - (N : ℤ)) =
      ∑ j ∈ Finset.range (N + 1), F (-(j : ℤ)) +
        ∑ n ∈ Finset.range K, F (((n + 1 : ℕ) : ℤ)) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show N + 1 ≤ N + K + 1 by omega)]
  congr 1
  · rw [← Finset.sum_range_reflect (fun j : ℕ => F (-(j : ℤ))) (N + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := by
      have := Finset.mem_range.mp hk
      omega
    have : ((N + 1 - 1 - k : ℕ) : ℤ) = (N : ℤ) - (k : ℤ) := by
      rw [show N + 1 - 1 - k = N - k by omega]
      exact Nat.cast_sub hkN
    simp only [this]
    congr 1
    ring
  · rw [Finset.sum_Ico_eq_sum_range]
    rw [show N + K + 1 - (N + 1) = K by omega]
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    push_cast
    ring

lemma aux_in_deterministic_good_scale_transfer_reflect (G : ℤ → ℝ) (N : ℕ) (a b : ℕ) :
      ∑ k ∈ Finset.Ico a b, G ((k : ℤ) - (N : ℤ)) =
        ∑ j ∈ Finset.Ico ((N : ℤ) + 1 - (b : ℤ)) ((N : ℤ) + 1 - (a : ℤ)), G (-j) := by
  apply Finset.sum_nbij' (fun k : ℕ => (N : ℤ) - (k : ℤ))
      (fun j : ℤ => ((N : ℤ) - j).toNat)
  · intro k hk
    simp only [Finset.mem_Ico] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj ⊢
    omega
  · intro k _
    show ((N : ℤ) - ((N : ℤ) - (k : ℤ))).toNat = k
    omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    show (N : ℤ) - (((N : ℤ) - j).toNat : ℤ) = j
    omega
  · intro k _
    congr 1
    ring

lemma aux_in_deterministic_good_scale_transfer_retained_sum (G : ℤ → ℝ) (N K : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ))
    (hK : ((N : ℤ) - l).toNat ≤ N + K) :
    (if 0 ≤ l then ∑ j ∈ Finset.Ico (0 : ℤ) l, G (-j)
      else -∑ j ∈ Finset.Ico l (0 : ℤ), G (-j)) +
      ∑ n ∈ Finset.range K, G (((n + 1 : ℕ) : ℤ)) =
      ∑ k ∈ Finset.Ico (((N : ℤ) - l).toNat + 1) (N + K + 1),
        G ((k : ℤ) - (N : ℤ)) := by
  set m : ℕ := ((N : ℤ) - l).toNat with hm
  have hmZ : (m : ℤ) = (N : ℤ) - l := by
    rw [hm]
    exact Int.toNat_of_nonneg (by omega)
  have hIR : ∑ k ∈ Finset.Ico (N + 1) (N + K + 1), G ((k : ℤ) - (N : ℤ)) =
      ∑ n ∈ Finset.range K, G (((n + 1 : ℕ) : ℤ)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show N + K + 1 - (N + 1) = K by omega]
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    push_cast
    ring
  by_cases hl0 : 0 ≤ l
  · rw [ite_eq_left hl0]
    have hcons := Finset.sum_Ico_consecutive (fun k : ℕ => G ((k : ℤ) - (N : ℤ)))
      (show m + 1 ≤ N + 1 by omega) (show N + 1 ≤ N + K + 1 by omega)
    rw [← hcons, hIR, aux_in_deterministic_good_scale_transfer_reflect]
    have h1 : (N : ℤ) + 1 - ((N + 1 : ℕ) : ℤ) = 0 := by push_cast; ring
    have h2 : (N : ℤ) + 1 - ((m + 1 : ℕ) : ℤ) = l := by push_cast; omega
    rw [h1, h2]
  · rw [ite_eq_right hl0]
    have hcons := Finset.sum_Ico_consecutive (fun k : ℕ => G ((k : ℤ) - (N : ℤ)))
      (show N + 1 ≤ m + 1 by omega) (show m + 1 ≤ N + K + 1 by omega)
    rw [← hIR, ← hcons, aux_in_deterministic_good_scale_transfer_reflect G N (N + 1) (m + 1)]
    have h1 : (N : ℤ) + 1 - ((N + 1 : ℕ) : ℤ) = 0 := by push_cast; ring
    have h2 : (N : ℤ) + 1 - ((m + 1 : ℕ) : ℤ) = l := by push_cast; omega
    rw [h1, h2]
    ring

/-- **Index-shift identity for the actual coefficient.**  On the physical
cutoff `N`, at signed level `l ≤ N` (either sign), with `m = (N - l).toNat`,
the actual coefficient `A_N` divided by the exact signed reference scalar of
`in_deterministic`'s `hsN` is the relabelled GMC coefficient `a_m / ahom_m` at
`y = 3^N x`, times the exponential of the centred long-wavelength shells
`k ∈ (m, N + K]` and of the infrared remainder after `K` infrared shells.
No limit is taken: the identity holds for every `K` with `m ≤ N + K`. -/
theorem aux_in_deterministic_good_scale_transfer_log_identity
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ))
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (x w : SpatialCoordinates d) (K : ℕ)
    (hK : ((N : ℤ) - l).toNat ≤ N + K) :
    let m : ℕ := ((N : ℤ) - l).toNat
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun ell v beta =>
        if 0 ≤ ell then
          ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
        else
          -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
    let sRef : ℝ := kappa m / kappa N * Real.exp (H omega w + retained l w omega)
    cutoffCoefficient M H omega N x / sRef =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)⁻¹ *
        _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • x) *
        Real.exp
          ((∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
              (eta k (((3 : ℝ) ^ N) • x) - eta k (((3 : ℝ) ^ N) • w))) +
            ((H omega x - H omega w) -
              ∑ n ∈ Finset.range K,
                (omega (((n + 1 : ℕ) : ℤ)) x - omega (((n + 1 : ℕ) : ℤ)) w))) := by
  intro m kappa retained sRef
  set tau := _root_.SubdiffusiveProcess.Model.tauSq M.P with htau
  have hunscale : ∀ v : SpatialCoordinates d,
      ((3 : ℝ) ^ (-(N : ℤ))) • (((3 : ℝ) ^ N) • v) = v := by
    intro v
    rw [smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul]
  have hEx : ∀ k : ℕ, eta k (((3 : ℝ) ^ N) • x) = omega ((k : ℤ) - (N : ℤ)) x := by
    intro k
    rw [hEta, hunscale]
  have hEw : ∀ k : ℕ, eta k (((3 : ℝ) ^ N) • w) = omega ((k : ℤ) - (N : ℤ)) w := by
    intro k
    rw [hEta, hunscale]
  have hahomN : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
    SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hahomm : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M m :=
    SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m
  -- the three reindexed sums
  have hF := aux_in_deterministic_good_scale_transfer_uv_ir_sum
    (fun i : ℤ => omega i x) N K
  have hG := aux_in_deterministic_good_scale_transfer_retained_sum
    (fun i : ℤ => omega i w) N K l hl hK
  have hSplit := Finset.sum_range_add_sum_Ico
    (fun k : ℕ => omega ((k : ℤ) - (N : ℤ)) x) (show m + 1 ≤ N + K + 1 by omega)
  have hret : retained l w omega =
      (if 0 ≤ l then ∑ j ∈ Finset.Ico (0 : ℤ) l, omega (-j) w
        else -∑ j ∈ Finset.Ico l (0 : ℤ), omega (-j) w) := rfl
  have hacut : _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • x) =
      Real.exp (∑ k ∈ Finset.range (m + 1), omega ((k : ℤ) - (N : ℤ)) x -
        ((m : ℝ) + 1) * tau) := by
    unfold _root_.SubdiffusiveProcess.Model.aCutoff
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [hEx]
    push_cast
    ring
  have hcut : cutoffCoefficient M H omega N x =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
        Real.exp (H omega x + ∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x -
          ((N : ℝ) + 1) * tau) := by
    unfold cutoffCoefficient cutoffPotential
    rfl
  have hsRef : sRef =
      Real.exp (((m : ℝ) + 1) * tau) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
        (Real.exp (((N : ℝ) + 1) * tau) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) *
        Real.exp (H omega w + retained l w omega) := rfl
  -- the exponent identity
  have hexp :
      H omega x + ∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x -
          ((N : ℝ) + 1) * tau + ((N : ℝ) + 1) * tau - ((m : ℝ) + 1) * tau -
          (H omega w + retained l w omega) =
        (∑ k ∈ Finset.range (m + 1), omega ((k : ℤ) - (N : ℤ)) x -
            ((m : ℝ) + 1) * tau) +
          ((∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
              (eta k (((3 : ℝ) ^ N) • x) - eta k (((3 : ℝ) ^ N) • w))) +
            ((H omega x - H omega w) -
              ∑ n ∈ Finset.range K,
                (omega (((n + 1 : ℕ) : ℤ)) x - omega (((n + 1 : ℕ) : ℤ)) w))) := by
    simp only [hEx, hEw]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hret]
    have hG' := hG
    have hF' := hF
    linarith [hSplit, hF', hG']
  rw [hsRef, hcut, hacut, mul_assoc, ← Real.exp_add, ← hexp]
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add]
  have hEN := (Real.exp_pos (((N : ℝ) + 1) * tau)).ne'
  have hEm := (Real.exp_pos (((m : ℝ) + 1) * tau)).ne'
  have hEH := (Real.exp_pos (H omega w + retained l w omega)).ne'
  field_simp [hahomN.ne', hahomm.ne', hEN, hEm, hEH]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring


/-- **Quadratic probe sensitivity with two reference scalars.**  This is
M `l.J.sensitivity` (`e.J.sensitivity`, δ = 1) in the paper-probe
normalization: the probe of `b` at reference `beta` is controlled by the probe
of `a` at reference `alpha`, with an additive price *quadratic* in the
multiplicative deviation `eta` of `(beta/alpha) a` from `b`. -/
theorem aux_in_deterministic_good_scale_transfer_probe_quadratic
    {d : ℕ} {U : Ch02.Domain d} {a b : Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    {alpha beta eta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (h1 : scalarRatioLInf U (fun x => (beta / alpha) * a x) b ≤ eta)
    (h2 : scalarRatioLInf U (fun x => (beta / alpha)⁻¹ * b x) a ≤ eta)
    (e : Vec d) (he : Homogenization.vecNormSq e = 1) :
    J U hb.toCoeffOn ((Real.sqrt beta)⁻¹ • e) (Real.sqrt beta • e) ≤
      (2 + 6 * eta ^ 2) *
          J U ha.toCoeffOn ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e) +
        6 * eta ^ 2 := by
  have hlam : 0 < beta / alpha := div_pos hbeta halpha
  have hsens := responseJ_sensitivity ha hb hlam (zero_lt_one' ℝ) le_rfl
    ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e)
  have hsa : 0 < Real.sqrt alpha := Real.sqrt_pos.mpr halpha
  have hsb : 0 < Real.sqrt beta := Real.sqrt_pos.mpr hbeta
  have hsqrt : Real.sqrt (beta / alpha) * Real.sqrt alpha = Real.sqrt beta := by
    rw [← Real.sqrt_mul hlam.le, div_mul_cancel₀ _ halpha.ne']
  have hp : (Real.sqrt (beta / alpha))⁻¹ • ((Real.sqrt alpha)⁻¹ • e) =
      (Real.sqrt beta)⁻¹ • e := by
    rw [smul_smul, ← mul_inv, hsqrt]
  have hq : Real.sqrt (beta / alpha) • (Real.sqrt alpha • e) =
      Real.sqrt beta • e := by
    rw [smul_smul, hsqrt]
  rw [hp, hq] at hsens
  have hdot : Homogenization.vecDot ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e) = 1 := by
    rw [Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_right]
    have : Homogenization.vecDot e e = 1 := he
    rw [this, mul_one, inv_mul_cancel₀ hsa.ne']
  rw [hdot] at hsens
  set Ja := J U ha.toCoeffOn ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e) with hJa
  have hJa0 : 0 ≤ Ja := Ch02.responseJ_nonneg _ _ _ _
  set r1 := scalarRatioLInf U (fun x => (beta / alpha) * a x) b
  set r2 := scalarRatioLInf U (fun x => (beta / alpha)⁻¹ * b x) a
  have hr1 : 0 ≤ r1 := ENNReal.toReal_nonneg
  have hr2 : 0 ≤ r2 := ENNReal.toReal_nonneg
  have hr1sq : r1 ^ 2 ≤ eta ^ 2 := pow_le_pow_left₀ hr1 h1 2
  have hr2sq : r2 ^ 2 ≤ eta ^ 2 := pow_le_pow_left₀ hr2 h2 2
  have hprice : 3 / 1 * (r1 ^ 2 + r2 ^ 2) * (Ja + 1) ≤ 6 * eta ^ 2 * (Ja + 1) := by
    have : 3 / 1 * (r1 ^ 2 + r2 ^ 2) ≤ 6 * eta ^ 2 := by linarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  calc
    _ ≤ (1 + 1) * Ja + 3 / 1 * (r1 ^ 2 + r2 ^ 2) * (Ja + 1) := hsens
    _ ≤ (1 + 1) * Ja + 6 * eta ^ 2 * (Ja + 1) := by linarith
    _ = (2 + 6 * eta ^ 2) * Ja + 6 * eta ^ 2 := by ring

/-- **Aggregation of an affine probe comparison through the paper
error** (`p = ∞`, `q = 2`).  The additive price is paid once because the
geometric weights have total mass one; the result is the Minkowski form. -/
theorem aux_in_deterministic_good_scale_transfer_error_affine
    {d : ℕ} (Q : TriadicCube d) (n : ℤ) {s : ℝ} (hs : 0 < s)
    (A B : Ch02.TriadicCoeffFamily d) (alpha beta c D : ℝ)
    (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hpoint : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ Homogenization.descendantsAtScale Q (n - (l : ℤ)) →
      ∀ e : Vec d, Homogenization.vecNormSq e = 1 →
        paperScalarProbe R B beta e ≤ c * paperScalarProbe R A alpha e + D) :
    paperHomogenizationError Q n s .infinity (.finite 2) B beta ≤
      ENNReal.ofReal (Real.sqrt c) *
          paperHomogenizationError Q n s .infinity (.finite 2) A alpha +
        ENNReal.ofReal (Real.sqrt D) := by
  rw [paperHomogenizationError_infinity_two_eq_weighted_series,
    paperHomogenizationError_infinity_two_eq_weighted_series]
  let w : ℕ → ℝ≥0∞ := fun l ↦ ENNReal.ofReal (Ch02.geometricWeight s 2 l)
  let X : ℕ → ℝ≥0∞ := fun l ↦ paperMaxDescendantProbeAtScale Q (n - (l : ℤ)) A alpha
  let Y : ℕ → ℝ≥0∞ := fun l ↦ paperMaxDescendantProbeAtScale Q (n - (l : ℤ)) B beta
  have hpt : ∀ l, Y l ≤ ENNReal.ofReal c * X l + ENNReal.ofReal D := by
    intro l
    refine iSup_le fun R ↦ ?_
    refine iSup_le fun e ↦ ?_
    have hprobe := hpoint l R.1 R.2 e.1 e.2
    have hA : ENNReal.ofReal (paperScalarProbe R.1 A alpha e.1) ≤ X l := by
      have h1 : ENNReal.ofReal (paperScalarProbe R.1 A alpha e.1) ≤
          paperScalarProbeMax R.1 A alpha :=
        le_iSup (fun e' : {e' : Vec d // Homogenization.vecNormSq e' = 1} ↦
          ENNReal.ofReal (paperScalarProbe R.1 A alpha e'.1)) e
      exact h1.trans (le_iSup (fun S : {S : TriadicCube d //
          S ∈ Homogenization.descendantsAtScale Q (n - (l : ℤ))} ↦
        paperScalarProbeMax S.1 A alpha) R)
    calc
      ENNReal.ofReal (paperScalarProbe R.1 B beta e.1)
          ≤ ENNReal.ofReal (c * paperScalarProbe R.1 A alpha e.1 + D) :=
        ENNReal.ofReal_le_ofReal hprobe
      _ ≤ ENNReal.ofReal (c * paperScalarProbe R.1 A alpha e.1) + ENNReal.ofReal D :=
        ENNReal.ofReal_add_le
      _ = ENNReal.ofReal c * ENNReal.ofReal (paperScalarProbe R.1 A alpha e.1) +
          ENNReal.ofReal D := by rw [ENNReal.ofReal_mul hc]
      _ ≤ ENNReal.ofReal c * X l + ENNReal.ofReal D := by
        gcongr
  have hwReal : Summable (fun l : ℕ ↦ Ch02.geometricWeight s 2 l) := by
    simpa only [Ch02.geometricWeight_eq_old] using
      (Homogenization.summable_geometricWeight (s := s) (q := 2) (by positivity))
  have hwSum : ∑' l : ℕ, w l = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · rw [show (∑' l : ℕ, Ch02.geometricWeight s 2 l) = 1 by
        simpa only [Ch02.geometricWeight_eq_old] using
          (Homogenization.tsum_geometricWeight_eq_one
            (s := s) (q := 2) (by positivity))]
      simp
    · intro l
      exact Homogenization.geometricWeight_nonneg l (by positivity)
    · exact hwReal
  have hseries : (∑' l : ℕ, w l * Y l) ≤
      ENNReal.ofReal c * (∑' l : ℕ, w l * X l) + ENNReal.ofReal D := by
    calc
      ∑' l : ℕ, w l * Y l ≤ ∑' l : ℕ, w l * (ENNReal.ofReal c * X l + ENNReal.ofReal D) :=
        ENNReal.tsum_le_tsum fun l ↦ mul_le_mul_right (hpt l) (w l)
      _ = ∑' l : ℕ, (ENNReal.ofReal c * (w l * X l) + ENNReal.ofReal D * w l) := by
        refine tsum_congr fun l ↦ ?_
        ring
      _ = ENNReal.ofReal c * (∑' l : ℕ, w l * X l) + ENNReal.ofReal D * (∑' l : ℕ, w l) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal c * (∑' l : ℕ, w l * X l) + ENNReal.ofReal D := by
        rw [hwSum, mul_one]
  have hroot := ENNReal.rpow_le_rpow hseries (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine hroot.trans ?_
  refine (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_rpow_of_nonneg hc (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hD (by norm_num),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]


/-- The paper probe is invariant under a public cube dilation of the family. -/
lemma aux_in_deterministic_good_scale_transfer_probe_dilate
    {d : ℕ} {k : ℤ} {a b : Ch02.TriadicCoeffFamily d}
    (h : Ch02.TriadicCoeffFamily.IsDilation k a b) (R : TriadicCube d)
    (alpha : ℝ) (e : Vec d) :
    paperScalarProbe (Ch02.dilateCube k R) b alpha e = paperScalarProbe R a alpha e := by
  unfold paperScalarProbe J
  exact Ch02.responseJ_dilate (h R) _ _

/-- The descendant-scale probe maximum commutes with dilation, with the scale
shifted by `k`. -/
lemma aux_in_deterministic_good_scale_transfer_maxprobe_dilate
    {d : ℕ} {k : ℤ} {a b : Ch02.TriadicCoeffFamily d}
    (h : Ch02.TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (j : ℤ) (alpha : ℝ) :
    paperMaxDescendantProbeAtScale (Ch02.dilateCube k Q) (j + k) b alpha =
      paperMaxDescendantProbeAtScale Q j a alpha := by
  classical
  have hmax : ∀ R : TriadicCube d,
      paperScalarProbeMax (Ch02.dilateCube k R) b alpha = paperScalarProbeMax R a alpha := by
    intro R
    unfold paperScalarProbeMax
    simp only [aux_in_deterministic_good_scale_transfer_probe_dilate h R alpha]
  unfold paperMaxDescendantProbeAtScale
  rw [Ch02.descendantsAtScale_dilateCube]
  apply le_antisymm
  · refine iSup_le fun R' ↦ ?_
    obtain ⟨R, hR, hRR'⟩ := Finset.mem_image.mp R'.2
    have : paperScalarProbeMax R'.1 b alpha = paperScalarProbeMax R a alpha := by
      rw [← hRR', hmax]
    rw [this]
    exact le_iSup (fun S : {S : TriadicCube d // S ∈ Homogenization.descendantsAtScale Q j} ↦
      paperScalarProbeMax S.1 a alpha) ⟨R, hR⟩
  · refine iSup_le fun R ↦ ?_
    rw [← hmax]
    exact le_iSup (fun S : {S : TriadicCube d //
        S ∈ (Homogenization.descendantsAtScale Q j).image (Ch02.dilateCube k)} ↦
      paperScalarProbeMax S.1 b alpha) ⟨Ch02.dilateCube k R.1, Finset.mem_image_of_mem _ R.2⟩

/-- **Dilation covariance of the paper error** (`p = ∞`, `q = 2`).  The
error of the dilated family on the dilated cube, at the shifted top scale, is
the error of the original family; the reference scalar is unchanged. -/
theorem aux_in_deterministic_good_scale_transfer_error_dilate
    {d : ℕ} {k : ℤ} {a b : Ch02.TriadicCoeffFamily d}
    (h : Ch02.TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (n : ℤ) (s alpha : ℝ) :
    paperHomogenizationError (Ch02.dilateCube k Q) (n + k) s .infinity (.finite 2) b alpha =
      paperHomogenizationError Q n s .infinity (.finite 2) a alpha := by
  rw [paperHomogenizationError_infinity_two_eq_weighted_series,
    paperHomogenizationError_infinity_two_eq_weighted_series]
  congr 1
  refine tsum_congr fun l ↦ ?_
  congr 1
  rw [show n + k - (l : ℤ) = (n - (l : ℤ)) + k by ring]
  exact aux_in_deterministic_good_scale_transfer_maxprobe_dilate h Q (n - (l : ℤ)) alpha

/-- The unit-chart form: the error on the GMC cube `□_m` at top scale `m` is the
error of the undilated family on the unit root at top scale `0`. -/
theorem aux_in_deterministic_good_scale_transfer_error_dilate_origin
    {d : ℕ} (m : ℕ) {a b : Ch02.TriadicCoeffFamily d}
    (h : Ch02.TriadicCoeffFamily.IsDilation (m : ℤ) a b) (s alpha : ℝ) :
    paperHomogenizationError (Homogenization.originCube d (m : ℤ)) (m : ℤ) s
        .infinity (.finite 2) b alpha =
      paperHomogenizationError (Homogenization.originCube d 0) 0 s
        .infinity (.finite 2) a alpha := by
  have hcube : Ch02.dilateCube (m : ℤ) (Homogenization.originCube d 0) =
      Homogenization.originCube d (m : ℤ) := by
    simp [Ch02.dilateCube, Homogenization.originCube]
  have := aux_in_deterministic_good_scale_transfer_error_dilate h
    (Homogenization.originCube d 0) 0 s alpha
  rw [hcube, zero_add] at this
  exact this


/-- **Chain: the actual-coefficient `in_J.err` on the physical chart is
controlled by the GMC equal-scale error `section6HomogenizationError M s m m`.**
The premises are exactly the per-cube local obligations: on each descendant of
the unit root, the physical chart and the undilated GMC comparison family are
(a.e.) scalar packages whose ratio, after the reference change
`a0 / ahom_m`, deviates from one by at most `eta`.  The price is linear in
`eta` (quadratic at the probe level). -/
theorem aux_in_deterministic_good_scale_transfer_chain
    {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (acoef : PositiveCoefficient (centeredCube w r hr)) (a0 : ℝ) (ha0 : 0 < a0)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (G' : Ch02.TriadicCoeffFamily d)
    (hdil : Ch02.TriadicCoeffFamily.IsDilation (m : ℤ) G'
      (aCutoffFamily M m (translatePotentialSample z g)))
    (phys comp : Vec d → ℝ) (eta : ℝ)
    (hcube : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (0 - (l : ℤ)) →
      ∃ (hP : ScalarCoeffOnData (Ch02.cubeDomain R) phys)
        (hC : ScalarCoeffOnData (Ch02.cubeDomain R) comp),
        Ch02.CoeffOn.AEEq ((I.chart w r hr acoef w r).coeffOn R) hP.toCoeffOn ∧
        Ch02.CoeffOn.AEEq (G'.coeffOn R) hC.toCoeffOn ∧
        scalarRatioLInf (Ch02.cubeDomain R) (fun x => (a0 / ahom M m) * comp x) phys ≤ eta ∧
        scalarRatioLInf (Ch02.cubeDomain R) (fun x => (a0 / ahom M m)⁻¹ * phys x) comp ≤ eta) :
    I.err w r hr acoef w r a0 s 2 ≤
      Real.sqrt (2 + 6 * eta ^ 2) * section6HomogenizationError M s m m g z +
        Real.sqrt (6 * eta ^ 2) := by
  have hahom : 0 < ahom M m := ahom_pos M m
  have hsub : (centeredCube w r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube w r hr : Set (SpatialCoordinates d)) := subset_rfl
  have hq : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  set chart := I.chart w r hr acoef w r with hchart
  set Q0 := Homogenization.originCube d 0
  -- the chart error and its finiteness, from `in_J`
  have herr := I.err_eq w r hr acoef w r hr hsub s hs 2 hq a0 ha0
  have hfin := I.err_finite w r hr acoef w r hr hsub s hs 2 hq a0 ha0
  simp only [ite_eq_right h2top] at herr hfin
  have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [htwo] at herr hfin
  change I.err w r hr acoef w r a0 s 2 =
    (paperHomogenizationError Q0 0 s .infinity (.finite 2) chart a0).toReal at herr
  change paperHomogenizationError Q0 0 s .infinity (.finite 2) chart a0 < ⊤ at hfin
  -- the GMC error, dilated back to the unit root
  have hgmc : section6HomogenizationError M s m m g z =
      (paperHomogenizationError Q0 0 s .infinity (.finite 2) G' (ahom M m)).toReal := by
    unfold section6HomogenizationError
    rw [tailCoefficientCubeAverage_self,
      aux_in_deterministic_good_scale_transfer_error_dilate_origin m hdil s (ahom M m)]
  -- per-cube quadratic sensitivity in both directions
  set c : ℝ := 2 + 6 * eta ^ 2
  set D : ℝ := 6 * eta ^ 2
  have hc : 0 ≤ c := by positivity
  have hD : 0 ≤ D := by positivity
  have hfwd : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ Homogenization.descendantsAtScale Q0 (0 - (l : ℤ)) →
      ∀ e : Vec d, Homogenization.vecNormSq e = 1 →
        paperScalarProbe R chart a0 e ≤ c * paperScalarProbe R G' (ahom M m) e + D := by
    intro l R hR e he
    obtain ⟨hP, hC, hPe, hCe, h1, h2⟩ := hcube l R hR
    unfold paperScalarProbe J
    rw [Ch02.responseJ_eq_ofAEEq hPe, Ch02.responseJ_eq_ofAEEq hCe]
    exact aux_in_deterministic_good_scale_transfer_probe_quadratic hC hP hahom ha0 h1 h2 e he
  have hbwd : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ Homogenization.descendantsAtScale Q0 (0 - (l : ℤ)) →
      ∀ e : Vec d, Homogenization.vecNormSq e = 1 →
        paperScalarProbe R G' (ahom M m) e ≤ c * paperScalarProbe R chart a0 e + D := by
    intro l R hR e he
    obtain ⟨hP, hC, hPe, hCe, h1, h2⟩ := hcube l R hR
    unfold paperScalarProbe J
    rw [Ch02.responseJ_eq_ofAEEq hPe, Ch02.responseJ_eq_ofAEEq hCe]
    have h1' : scalarRatioLInf (Ch02.cubeDomain R)
        (fun x => (ahom M m / a0) * phys x) comp ≤ eta := by
      have : (ahom M m / a0) = (a0 / ahom M m)⁻¹ := by rw [inv_div]
      simpa only [this] using h2
    have h2' : scalarRatioLInf (Ch02.cubeDomain R)
        (fun x => (ahom M m / a0)⁻¹ * comp x) phys ≤ eta := by
      have : (ahom M m / a0)⁻¹ = (a0 / ahom M m) := by rw [inv_div]
      simpa only [this] using h1
    exact aux_in_deterministic_good_scale_transfer_probe_quadratic hP hC ha0 hahom h1' h2' e he
  have hEfwd := aux_in_deterministic_good_scale_transfer_error_affine Q0 0 hs.1
    G' chart (ahom M m) a0 c D hc hD hfwd
  have hEbwd := aux_in_deterministic_good_scale_transfer_error_affine Q0 0 hs.1
    chart G' a0 (ahom M m) c D hc hD hbwd
  set Ech := paperHomogenizationError Q0 0 s .infinity (.finite 2) chart a0
  set Eg := paperHomogenizationError Q0 0 s .infinity (.finite 2) G' (ahom M m)
  have hEgfin : Eg ≠ ⊤ := by
    have : ENNReal.ofReal (Real.sqrt c) * Ech + ENNReal.ofReal (Real.sqrt D) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne,
        ENNReal.ofReal_ne_top⟩
    exact ne_top_of_le_ne_top this hEbwd
  have hrhs : ENNReal.ofReal (Real.sqrt c) * Eg + ENNReal.ofReal (Real.sqrt D) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEgfin,
      ENNReal.ofReal_ne_top⟩
  have hreal := ENNReal.toReal_mono hrhs hEfwd
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEgfin)
    ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hreal
  rw [herr, hgmc]
  exact hreal


/-! ## REVIEW ADDITIONS -/

open MeasureTheory

/-- **Undilation of the GMC family to the unit root** (removes the `hdil`
premise of the chain).  The comparison family is the concrete public
dilation `dilate (-m) A`; the dilation relation is `isDilation_dilate`. -/
theorem aux_in_deterministic_good_scale_transfer_error_undilate_origin
    {d : ℕ} (m : ℕ) (A : Ch02.TriadicCoeffFamily d) (s alpha : ℝ) :
    paperHomogenizationError (Homogenization.originCube d 0) 0 s .infinity (.finite 2)
        (Ch02.TriadicCoeffFamily.dilate (-(m : ℤ)) A) alpha =
      paperHomogenizationError (Homogenization.originCube d (m : ℤ)) (m : ℤ) s
        .infinity (.finite 2) A alpha := by
  have h := aux_in_deterministic_good_scale_transfer_error_dilate
    (Ch02.TriadicCoeffFamily.isDilation_dilate (-(m : ℤ)) A)
    (Homogenization.originCube d (m : ℤ)) (m : ℤ) s alpha
  have hcube : Ch02.dilateCube (-(m : ℤ)) (Homogenization.originCube d (m : ℤ)) =
      Homogenization.originCube d 0 := by
    simp [Ch02.dilateCube, Homogenization.originCube]
  rw [hcube, add_neg_cancel] at h
  exact h

lemma aux_in_deterministic_good_scale_transfer_undilateVec_neg {d : ℕ} (m : ℕ) (x : Vec d) :
    Ch02.undilateVec (-(m : ℤ)) x = ((3 : ℝ) ^ m) • x := by
  simp [Ch02.undilateVec, Ch02.triadicDilationFactor, zpow_neg, inv_inv, zpow_natCast]

/-- The undilated GMC family is, a.e. on every triadic cube, the scalar field
`x ↦ a_m(g^z)(3^m x)`. -/
theorem aux_in_deterministic_good_scale_transfer_comp_aeeq
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (gz : _root_.SubdiffusiveProcess.Model.PotentialSample d) (R : TriadicCube d)
    (hC : ScalarCoeffOnData (Ch02.cubeDomain R)
      (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M m gz (((3 : ℝ) ^ m) • x))) :
    Ch02.CoeffOn.AEEq
      ((Ch02.TriadicCoeffFamily.dilate (-(m : ℤ)) (aCutoffFamily M m gz)).coeffOn R)
      hC.toCoeffOn := by
  set Q' : TriadicCube d := Ch02.dilateCube (-(-(m : ℤ))) R with hQ'
  have hfg := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
    (Ch02.cubeDomain Q') ((aCutoffFamily M m gz).coeffOn Q')
  have hpull := Ch02.eventuallyEq_comp_undilate_of_ae_eq (-(m : ℤ)) (Q := Q') hfg
  rw [hQ', Ch02.dilateCube_dilateCube_neg] at hpull
  unfold Ch02.CoeffOn.AEEq
  refine hpull.trans (Filter.Eventually.of_forall fun x => ?_)
  change scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m gz)
      (Ch02.undilateVec (-(m : ℤ)) x) =
    scalarCoeffField (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M m gz (((3 : ℝ) ^ m) • x)) x
  simp only [scalarCoeffField, aux_in_deterministic_good_scale_transfer_undilateVec_neg]

lemma aux_in_deterministic_good_scale_transfer_mem_unit_root {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) (i : Fin d) :
    -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
  have h : ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
    simpa [Homogenization.openCubeSet, Homogenization.originCube,
      Homogenization.cubeScaleFactor] using hx
  exact h i

lemma aux_in_deterministic_good_scale_transfer_affine_mem {d : ℕ} (w : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) {x : SpatialCoordinates d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    (fun i => w i + r * x i) ∈ (centeredCube w r hr : Set (SpatialCoordinates d)) := by
  rw [centeredCube_eq_pi]
  intro i _
  obtain ⟨h1, h2⟩ := aux_in_deterministic_good_scale_transfer_mem_unit_root hx i
  have h1' : r * (-(1 / 2 : ℝ)) < r * x i := mul_lt_mul_of_pos_left h1 hr
  have h2' : r * x i < r * (1 / 2 : ℝ) := mul_lt_mul_of_pos_left h2 hr
  constructor <;> linarith

lemma aux_in_deterministic_good_scale_transfer_qmp_affine {d : ℕ} (w : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => fun i => w i + r * x i)
      volume volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => r • y)
      volume volume :=
    Measure.quasiMeasurePreserving_smul volume hr.ne'
  have h2 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => y + w)
      volume volume :=
    (measurePreserving_add_right volume w).quasiMeasurePreserving
  have heq : (fun x : SpatialCoordinates d => fun i => w i + r * x i) =
      (fun y : SpatialCoordinates d => y + w) ∘ (fun y : SpatialCoordinates d => r • y) := by
    funext x i
    simp [add_comm]
  rw [heq]
  exact h2.comp h1

lemma aux_in_deterministic_good_scale_transfer_ae_restrict_comp {d : ℕ}
    {f : SpatialCoordinates d → SpatialCoordinates d}
    (hf : Measure.QuasiMeasurePreserving f volume volume) {S S' : Set (SpatialCoordinates d)}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hmaps : ∀ y ∈ S', f y ∈ S)
    {P : SpatialCoordinates d → Prop} (h : ∀ᵐ x ∂volume.restrict S, P x) :
    ∀ᵐ y ∂volume.restrict S', P (f y) := by
  rw [ae_restrict_iff' hS] at h
  rw [ae_restrict_iff' hS']
  filter_upwards [hf.ae h] with y hy hyS'
  exact hy (hmaps y hyS')

/-- The actual chart of `in_deterministic` (root = inner cube = `centeredCube w r`),
is, a.e. on every sub-cube of the unit root, the scalar field
`x ↦ A_N(w + r x)`. -/
theorem aux_in_deterministic_good_scale_transfer_phys_aeeq
    {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (R : TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0))
    (hP : ScalarCoeffOnData (Ch02.cubeDomain R)
      (fun x => cutoffCoefficient M H omega N (fun i => w i + r * x i))) :
    Ch02.CoeffOn.AEEq
      ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn R)
      hP.toCoeffOn := by
  have : Fact ((centeredCube w r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube w r hr : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube w hr⟩
  have hc := I.chart_eq w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r hr
    subset_rfl R hR
  have h0 := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube w r hr) (closedCube w r hr)
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H omega N w hr)
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M H omega N w hr) 1 one_pos
  have hRmeas : MeasurableSet (Homogenization.openCubeSet R) :=
    Homogenization.measurableSet_openCubeSet R
  have hmaps : ∀ x ∈ Homogenization.openCubeSet R,
      (fun i => w i + r * x i) ∈ (centeredCube w r hr : Set (SpatialCoordinates d)) :=
    fun x hx => aux_in_deterministic_good_scale_transfer_affine_mem w r hr (hR hx)
  have hv := aux_in_deterministic_good_scale_transfer_ae_restrict_comp
    (aux_in_deterministic_good_scale_transfer_qmp_affine w r hr)
    (centeredCube w r hr).isOpen.measurableSet hRmeas hmaps h0
  unfold Ch02.CoeffOn.AEEq
  change ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn
      R).toCoeffField =ᵐ[volume.restrict (Homogenization.openCubeSet R)]
    scalarCoeffField (fun x => cutoffCoefficient M H omega N (fun i => w i + r * x i))
  filter_upwards [hc, hv, ae_restrict_mem hRmeas] with x hcx hvx hxR
  rw [hcx]
  have hval := hvx (hmaps x hxR)
  change Homogenization.scalarMatrix
      ((_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val (fun i => w i + r * x i)) =
    Homogenization.scalarMatrix (cutoffCoefficient M H omega N (fun i => w i + r * x i))
  congr 1
  rw [div_one] at hval
  exact hval

lemma aux_in_deterministic_good_scale_transfer_continuous_cutoffCoefficient {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    Continuous (cutoffCoefficient M H omega N) := by
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  exact Continuous.sub
    (Continuous.add (H omega).continuous
      (continuous_finsetSum _ fun j _ => (omega (-(Int.ofNat j))).continuous))
    continuous_const

lemma aux_in_deterministic_good_scale_transfer_cutoffCoefficient_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) : 0 < cutoffCoefficient M H omega N x :=
  mul_pos (inv_pos.2 (ahom_pos M N)) (Real.exp_pos _)

/-- **Chain against the actual objects, with only the pointwise ratio bound
left.**  No `IsDilation`, `AEEq` or scalar-package premise remains: the
comparison family is `dilate (-m) (aCutoffFamily M m g^z)`, and both packages
are the continuous-positive packages. -/
theorem aux_in_deterministic_good_scale_transfer_chain_actual
    {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (a0 : ℝ) (ha0 : 0 < a0)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (m : ℕ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d) (eta : ℝ) (heta : 0 ≤ eta)
    (hratio : ∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0),
      |(a0 / ahom M m) *
          _root_.SubdiffusiveProcess.Model.aCutoff M m (translatePotentialSample z g) (((3 : ℝ) ^ m) • x) /
          cutoffCoefficient M H omega N (fun i => w i + r * x i) - 1| ≤ eta ∧
      |(a0 / ahom M m)⁻¹ * cutoffCoefficient M H omega N (fun i => w i + r * x i) /
          _root_.SubdiffusiveProcess.Model.aCutoff M m (translatePotentialSample z g)
            (((3 : ℝ) ^ m) • x) - 1| ≤ eta) :
    I.err w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r a0 s 2 ≤
      Real.sqrt (2 + 6 * eta ^ 2) * section6HomogenizationError M s m m g z +
        Real.sqrt (6 * eta ^ 2) := by
  set gz := translatePotentialSample z g with hgz
  set phys : Vec d → ℝ := fun x => cutoffCoefficient M H omega N (fun i => w i + r * x i)
    with hphys
  set comp : Vec d → ℝ := fun x =>
    _root_.SubdiffusiveProcess.Model.aCutoff M m gz (((3 : ℝ) ^ m) • x) with hcomp
  have hphys_cont : Continuous phys := by
    refine (aux_in_deterministic_good_scale_transfer_continuous_cutoffCoefficient
      M H omega N).comp ?_
    exact continuous_pi fun i => continuous_const.add
      (continuous_const.mul (continuous_apply i))
  have hphys_pos : ∀ x, 0 < phys x := fun x =>
    aux_in_deterministic_good_scale_transfer_cutoffCoefficient_pos M H omega N _
  have hcomp_cont : Continuous comp :=
    (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M m gz).comp (continuous_const_smul _)
  have hcomp_pos : ∀ x, 0 < comp x := fun x =>
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M m gz _
  set G' := Ch02.TriadicCoeffFamily.dilate (-(m : ℤ)) (aCutoffFamily M m gz) with hG'
  have hahom : 0 < ahom M m := ahom_pos M m
  have hsub : (centeredCube w r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube w r hr : Set (SpatialCoordinates d)) := subset_rfl
  have hq : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  set acoef := _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr with hacoef
  set chart := I.chart w r hr acoef w r with hchart
  set Q0 := Homogenization.originCube d 0 with hQ0
  have herr := I.err_eq w r hr acoef w r hr hsub s hs 2 hq a0 ha0
  have hfin := I.err_finite w r hr acoef w r hr hsub s hs 2 hq a0 ha0
  simp only [ite_eq_right h2top] at herr hfin
  have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [htwo] at herr hfin
  change I.err w r hr acoef w r a0 s 2 =
    (paperHomogenizationError Q0 0 s .infinity (.finite 2) chart a0).toReal at herr
  change paperHomogenizationError Q0 0 s .infinity (.finite 2) chart a0 < ⊤ at hfin
  have hgmc : section6HomogenizationError M s m m g z =
      (paperHomogenizationError Q0 0 s .infinity (.finite 2) G' (ahom M m)).toReal := by
    unfold section6HomogenizationError
    rw [tailCoefficientCubeAverage_self, hG',
      aux_in_deterministic_good_scale_transfer_error_undilate_origin m _ s (ahom M m)]
  -- per-cube data
  have hcube : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ Homogenization.descendantsAtScale Q0 (0 - (l : ℤ)) →
      ∃ (hP : ScalarCoeffOnData (Ch02.cubeDomain R) phys)
        (hC : ScalarCoeffOnData (Ch02.cubeDomain R) comp),
        Ch02.CoeffOn.AEEq (chart.coeffOn R) hP.toCoeffOn ∧
        Ch02.CoeffOn.AEEq (G'.coeffOn R) hC.toCoeffOn ∧
        scalarRatioLInf (Ch02.cubeDomain R) (fun x => (a0 / ahom M m) * comp x) phys ≤ eta ∧
        scalarRatioLInf (Ch02.cubeDomain R) (fun x => (a0 / ahom M m)⁻¹ * phys x) comp ≤ eta := by
    intro l R hR
    have hk : (0 : ℤ) - (l : ℤ) ≤ Q0.scale := by
      simp [hQ0, Homogenization.originCube]
    have hRsub : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet Q0 :=
      Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk hR
    refine ⟨SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos
        hphys_cont hphys_pos (Ch02.cubeDomain R),
      SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos
        hcomp_cont hcomp_pos (Ch02.cubeDomain R), ?_, ?_, ?_, ?_⟩
    · exact aux_in_deterministic_good_scale_transfer_phys_aeeq I M H omega N w r hr R hRsub _
    · exact aux_in_deterministic_good_scale_transfer_comp_aeeq M m gz R _
    · exact Section6ThetaLadder.scalarRatioLInf_le_of_pointwise heta
        (fun x hx => (hratio x (hRsub hx)).1)
    · exact Section6ThetaLadder.scalarRatioLInf_le_of_pointwise heta
        (fun x hx => (hratio x (hRsub hx)).2)
  set c : ℝ := 2 + 6 * eta ^ 2
  set D : ℝ := 6 * eta ^ 2
  have hc : 0 ≤ c := by positivity
  have hD : 0 ≤ D := by positivity
  have hfwd : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ Homogenization.descendantsAtScale Q0 (0 - (l : ℤ)) →
      ∀ e : Vec d, Homogenization.vecNormSq e = 1 →
        paperScalarProbe R chart a0 e ≤ c * paperScalarProbe R G' (ahom M m) e + D := by
    intro l R hR e he
    obtain ⟨hP, hC, hPe, hCe, h1, h2⟩ := hcube l R hR
    unfold paperScalarProbe J
    rw [Ch02.responseJ_eq_ofAEEq hPe, Ch02.responseJ_eq_ofAEEq hCe]
    exact aux_in_deterministic_good_scale_transfer_probe_quadratic hC hP hahom ha0 h1 h2 e he
  have hbwd : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ Homogenization.descendantsAtScale Q0 (0 - (l : ℤ)) →
      ∀ e : Vec d, Homogenization.vecNormSq e = 1 →
        paperScalarProbe R G' (ahom M m) e ≤ c * paperScalarProbe R chart a0 e + D := by
    intro l R hR e he
    obtain ⟨hP, hC, hPe, hCe, h1, h2⟩ := hcube l R hR
    unfold paperScalarProbe J
    rw [Ch02.responseJ_eq_ofAEEq hPe, Ch02.responseJ_eq_ofAEEq hCe]
    have h1' : scalarRatioLInf (Ch02.cubeDomain R)
        (fun x => (ahom M m / a0) * phys x) comp ≤ eta := by
      have : (ahom M m / a0) = (a0 / ahom M m)⁻¹ := by rw [inv_div]
      simpa only [this] using h2
    have h2' : scalarRatioLInf (Ch02.cubeDomain R)
        (fun x => (ahom M m / a0)⁻¹ * comp x) phys ≤ eta := by
      have : (ahom M m / a0)⁻¹ = (a0 / ahom M m) := by rw [inv_div]
      simpa only [this] using h1
    exact aux_in_deterministic_good_scale_transfer_probe_quadratic hP hC ha0 hahom h1' h2' e he
  have hEfwd := aux_in_deterministic_good_scale_transfer_error_affine Q0 0 hs.1
    G' chart (ahom M m) a0 c D hc hD hfwd
  have hEbwd := aux_in_deterministic_good_scale_transfer_error_affine Q0 0 hs.1
    chart G' a0 (ahom M m) c D hc hD hbwd
  set Ech := paperHomogenizationError Q0 0 s .infinity (.finite 2) chart a0
  set Eg := paperHomogenizationError Q0 0 s .infinity (.finite 2) G' (ahom M m)
  have hEgfin : Eg ≠ ⊤ := by
    have : ENNReal.ofReal (Real.sqrt c) * Ech + ENNReal.ofReal (Real.sqrt D) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne,
        ENNReal.ofReal_ne_top⟩
    exact ne_top_of_le_ne_top this hEbwd
  have hrhs : ENNReal.ofReal (Real.sqrt c) * Eg + ENNReal.ofReal (Real.sqrt D) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEgfin,
      ENNReal.ofReal_ne_top⟩
  have hreal := ENNReal.toReal_mono hrhs hEfwd
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEgfin)
    ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hreal
  rw [herr, hgmc]
  exact hreal


lemma aux_in_deterministic_good_scale_transfer_scale_pow (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ)) :
    (3 : ℝ) ^ N * (3 : ℝ) ^ (-l) = (3 : ℝ) ^ ((N : ℤ) - l).toNat := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), ← zpow_natCast]
  congr 1
  rw [Int.toNat_of_nonneg (by omega)]
  ring

/-- **The normalized ratio at the `in_deterministic` instantiation is an exact
exponential**, for every signed level `l ≤ N` (both branches of `hsN`) and every
number `K` of infrared shells: with `r = 3^{-l}`, `z = 3^N w`, `m = (N-l)⁺` and
`a0` the literal `hsN` scalar, the two quantities of `chain_actual`'s `hratio`
are `exp (∓ E_K x)`, where `E_K` is the centred long-wavelength sum plus the
infrared remainder after `K` shells. -/
theorem aux_in_deterministic_good_scale_transfer_ratio_exp
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ))
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (w x : SpatialCoordinates d) (K : ℕ)
    (hK : ((N : ℤ) - l).toNat ≤ N + K) :
    let m : ℕ := ((N : ℤ) - l).toNat
    let r : ℝ := (3 : ℝ) ^ (-l)
    let z : Vec d := ((3 : ℝ) ^ N) • w
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun ell v beta =>
        if 0 ≤ ell then
          ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
        else
          -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
    let a0 : ℝ := kappa m / kappa N * Real.exp (H omega w + retained l w omega)
    let xp : SpatialCoordinates d := fun i => w i + r * x i
    let E : ℝ :=
      (∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
          (eta k (((3 : ℝ) ^ m) • x + z) - eta k z)) +
        ((H omega xp - H omega w) -
          ∑ n ∈ Finset.range K,
            (omega (((n + 1 : ℕ) : ℤ)) xp - omega (((n + 1 : ℕ) : ℤ)) w))
    (a0 / ahom M m)⁻¹ * cutoffCoefficient M H omega N xp /
        _root_.SubdiffusiveProcess.Model.aCutoff M m (translatePotentialSample z eta)
          (((3 : ℝ) ^ m) • x) = Real.exp E ∧
      (a0 / ahom M m) *
          _root_.SubdiffusiveProcess.Model.aCutoff M m (translatePotentialSample z eta)
            (((3 : ℝ) ^ m) • x) / cutoffCoefficient M H omega N xp = Real.exp (-E) := by
  intro m r z kappa retained a0 xp E
  have hid := aux_in_deterministic_good_scale_transfer_log_identity M H omega N l hl eta hEta
    xp w K hK
  simp only at hid
  have hvec : ((3 : ℝ) ^ N) • xp = ((3 : ℝ) ^ m) • x + z := by
    funext i
    simp only [xp, z, r, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [mul_add, ← mul_assoc, aux_in_deterministic_good_scale_transfer_scale_pow N l hl]
    ring
  have hcomp : _root_.SubdiffusiveProcess.Model.aCutoff M m (translatePotentialSample z eta)
      (((3 : ℝ) ^ m) • x) =
      _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) := by
    rw [hvec]
    unfold _root_.SubdiffusiveProcess.Model.aCutoff translatePotentialSample
    rfl
  have hE : (∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
        (eta k (((3 : ℝ) ^ N) • xp) - eta k (((3 : ℝ) ^ N) • w))) +
      ((H omega xp - H omega w) -
        ∑ n ∈ Finset.range K,
          (omega (((n + 1 : ℕ) : ℤ)) xp - omega (((n + 1 : ℕ) : ℤ)) w)) = E := by
    rw [hvec]
  rw [hE] at hid
  have ha0 : 0 < a0 := by
    have hk : ∀ J, 0 < kappa J := fun J => mul_pos (Real.exp_pos _) (ahom_pos M J)
    exact mul_pos (div_pos (hk m) (hk N)) (Real.exp_pos _)
  have hahom : 0 < ahom M m := ahom_pos M m
  have hac : 0 < _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) :=
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M m eta _
  have hcut : 0 < cutoffCoefficient M H omega N xp :=
    aux_in_deterministic_good_scale_transfer_cutoffCoefficient_pos M H omega N xp
  have hid' : cutoffCoefficient M H omega N xp / a0 =
      (ahom M m)⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) *
        Real.exp E := hid
  have h1 : cutoffCoefficient M H omega N xp =
      a0 * ((ahom M m)⁻¹ *
        _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) * Real.exp E) := by
    rw [← hid', mul_div_assoc']
    exact (mul_div_cancel_left₀ _ ha0.ne').symm
  clear_value a0 E
  have hmain : (a0 / ahom M m)⁻¹ * cutoffCoefficient M H omega N xp /
      _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) = Real.exp E := by
    rw [h1]
    field_simp
  refine ⟨by rw [hcomp]; exact hmain, ?_⟩
  rw [hcomp, Real.exp_neg, ← hmain]
  field_simp


lemma aux_in_deterministic_good_scale_transfer_abs_exp_sub_one (r : ℝ) :
    |Real.exp r - 1| ≤ |r| * Real.exp |r| := by
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hr))]
    have hneg := Real.add_one_le_exp (-r)
    have hmul := mul_le_mul_of_nonneg_left hneg (Real.exp_pos r).le
    rw [Real.exp_neg, mul_add, mul_one, mul_inv_cancel₀ (Real.exp_ne_zero r)] at hmul
    nlinarith
  · have hr' : r ≤ 0 := hr.le
    rw [abs_of_neg hr, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hr'))]
    have hlin := Real.add_one_le_exp r
    have hexp : 1 ≤ Real.exp (-r) := Real.one_le_exp (by linarith)
    nlinarith

/-- A quantity that equals `S K + b K` for all large `K`, with `b K → 0` and
`|S K| ≤ B`, is bounded by `B`. -/
lemma aux_in_deterministic_good_scale_transfer_limit_bound (X B : ℝ) (S b : ℕ → ℝ) (K0 : ℕ)
    (hX : ∀ K, K0 ≤ K → X = S K + b K)
    (hb : Filter.Tendsto b Filter.atTop (nhds 0))
    (hS : ∀ K, K0 ≤ K → |S K| ≤ B) : |X| ≤ B := by
  have hlim : Filter.Tendsto (fun K => B + |b K|) Filter.atTop (nhds (B + |0|)) :=
    tendsto_const_nhds.add hb.abs
  rw [abs_zero, add_zero] at hlim
  refine ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨K0, fun K hK => ?_⟩)
  rw [hX K hK]
  exact (abs_add_le _ _).trans (by linarith [hS K hK])

/-- The infrared remainder after `K` shells, centred between two points, tends
to zero when the infrared partial sums converge to `H omega` in `C(ℝ^d, ℝ)`. -/
lemma aux_in_deterministic_good_scale_transfer_ir_remainder {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (x w : SpatialCoordinates d) :
    Filter.Tendsto (fun K : ℕ => (H omega x - H omega w) -
        ∑ n ∈ Finset.range K,
          (omega (((n + 1 : ℕ) : ℤ)) x - omega (((n + 1 : ℕ) : ℤ)) w))
      Filter.atTop (nhds 0) := by
  have hx := ((continuous_eval_const x).tendsto (H omega)).comp hIR
  have hw := ((continuous_eval_const w).tendsto (H omega)).comp hIR
  have hsub := (tendsto_const_nhds (x := H omega x - H omega w)).sub (hx.sub hw)
  rw [sub_self] at hsub
  refine hsub.congr fun K => ?_
  simp only [Function.comp_apply, infraredPartialSum, ContinuousMap.coe_sum,
    Finset.sum_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    Int.ofNat_eq_natCast]
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Translating a potential field translates its stored gradient. -/
lemma aux_in_deterministic_good_scale_transfer_shellGradient_translate {d : ℕ}
    (z : Vec d) (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (x : Vec d) :
    shellGradient (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) x =
      shellGradient g (x + z) := rfl

lemma aux_in_deterministic_good_scale_transfer_vectorSupNormOn_translate {d : ℕ}
    (m : ℕ) (z : Vec d) (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    vectorSupNormOn (cube d m)
        (shellGradient (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)) =
      vectorSupNormOn (translatedCube d m z) (shellGradient g) := by
  unfold vectorSupNormOn
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨z + x, ⟨x, hx, rfl⟩, by
      rw [aux_in_deterministic_good_scale_transfer_shellGradient_translate, add_comm]⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by
      rw [aux_in_deterministic_good_scale_transfer_shellGradient_translate, add_comm]⟩

lemma aux_in_deterministic_good_scale_transfer_smul_mem_cube {d : ℕ} (m : ℕ) {x : Vec d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    ((3 : ℝ) ^ m) • x ∈ cube d m := by
  unfold cube
  rw [Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  obtain ⟨h1, h2⟩ := aux_in_deterministic_good_scale_transfer_mem_unit_root hx i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  simp only [Pi.smul_apply, smul_eq_mul, zpow_natCast]
  constructor <;> nlinarith

lemma aux_in_deterministic_good_scale_transfer_zero_mem_cube {d : ℕ} (m : ℕ) :
    (0 : Vec d) ∈ cube d m := by
  unfold cube
  rw [Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (m : ℤ) := by positivity
  simp only [Pi.zero_apply]
  constructor <;> linarith

/-- **Gradient (mean-value) control of the centred long-wavelength sum**, on the
physical chart: every finite block of shells `k ∈ [a, b)` with `m ≤ a` is
bounded by `d` times the literal fourth `accumulatedError` summands at `(m, z)`. -/
theorem aux_in_deterministic_good_scale_transfer_gradient_block {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m : ℕ) (z : Vec d)
    {x : Vec d} (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (a b : ℕ) :
    ∑ k ∈ Finset.Ico a b, |g k (((3 : ℝ) ^ m) • x + z) - g k z| ≤
      (d : ℝ) * ∑ k ∈ Finset.Ico a b,
        (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d m z) (shellGradient (g k)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have h := SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.abs_shell_sub_le_dimension_mul_scaled_gradientSup
    (_root_.SubdiffusiveProcess.Model.PotentialField.translate z (g k)) m
    (aux_in_deterministic_good_scale_transfer_smul_mem_cube m hx)
    (aux_in_deterministic_good_scale_transfer_zero_mem_cube m)
  rw [aux_in_deterministic_good_scale_transfer_vectorSupNormOn_translate] at h
  simpa only [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, zero_add] using h

/-- **Assembled pointwise transfer, modulo score facts.**  At the literal
`in_deterministic` instantiation (`r = 3^{-l}`, `z = 3^N w`, `m = (N-l)⁺`,
`a0` = the `hsN` scalar, `g` = the relabelled sample), for either sign of `l`:
if the infrared partial sums converge at `omega`, the centred long-wavelength
absolute sums are bounded by `B` (the `P < 12` input), and the fourth
accumulated-error term `T` bounds every finite gradient block (summability),
then the actual `I.err` is bounded by the GMC equal-scale error with a price
linear in `min B (d T)`. -/
theorem aux_in_deterministic_good_scale_transfer_pointwise
    {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ))
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (w : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ (-l))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hPbound : ∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0),
      ∀ K : ℕ, ∑ k ∈ Finset.Ico (((N : ℤ) - l).toNat + 1) (N + K + 1),
        |eta k (((3 : ℝ) ^ ((N : ℤ) - l).toNat) • x + ((3 : ℝ) ^ N) • w) -
          eta k (((3 : ℝ) ^ N) • w)| ≤ B)
    (hTbound : ∀ K : ℕ, ∑ k ∈ Finset.Ico (((N : ℤ) - l).toNat + 1) (N + K + 1),
        (3 : ℝ) ^ ((N : ℤ) - l).toNat *
          vectorSupNormOn (translatedCube d ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w))
            (shellGradient (eta k)) ≤ T) :
    let m : ℕ := ((N : ℤ) - l).toNat
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun ell v beta =>
        if 0 ≤ ell then
          ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
        else
          -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
    let a0 : ℝ := kappa m / kappa N * Real.exp (H omega w + retained l w omega)
    let eps : ℝ := min B ((d : ℝ) * T) * Real.exp B
    I.err w ((3 : ℝ) ^ (-l)) hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr)
        w ((3 : ℝ) ^ (-l)) a0 s 2 ≤
      Real.sqrt (2 + 6 * eps ^ 2) *
          section6HomogenizationError M s m m eta (((3 : ℝ) ^ N) • w) +
        Real.sqrt (6 * eps ^ 2) := by
  intro m kappa retained a0 eps
  set z : Vec d := ((3 : ℝ) ^ N) • w with hz
  have hk : ∀ J, 0 < kappa J := fun J => mul_pos (Real.exp_pos _) (ahom_pos M J)
  have ha0 : 0 < a0 := mul_pos (div_pos (hk m) (hk N)) (Real.exp_pos _)
  have heps : 0 ≤ eps := mul_nonneg (le_min hB (mul_nonneg (Nat.cast_nonneg d) hT))
    (Real.exp_pos _).le
  refine aux_in_deterministic_good_scale_transfer_chain_actual I M H omega N w
    ((3 : ℝ) ^ (-l)) hr a0 ha0 s hs m eta z eps heps ?_
  intro x hx
  set xp : SpatialCoordinates d := fun i => w i + (3 : ℝ) ^ (-l) * x i with hxp
  -- the exponent `E K` of `ratio_exp`
  let Sm : ℕ → ℝ := fun K => ∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
    (eta k (((3 : ℝ) ^ m) • x + z) - eta k z)
  let bK : ℕ → ℝ := fun K => (H omega xp - H omega w) -
    ∑ n ∈ Finset.range K, (omega (((n + 1 : ℕ) : ℤ)) xp - omega (((n + 1 : ℕ) : ℤ)) w)
  have hKm : ∀ K, m ≤ K → m ≤ N + K := fun K hK => by omega
  have hre := fun K (hK : m ≤ K) =>
    aux_in_deterministic_good_scale_transfer_ratio_exp M H omega N l hl eta hEta w x K (hKm K hK)
  -- all exponents agree with the one at `K = m`
  set X : ℝ := Sm m + bK m with hXdef
  have hXK : ∀ K, m ≤ K → X = Sm K + bK K := by
    intro K hK
    have h1 := (hre K hK).1
    have h0 := (hre m le_rfl).1
    simp only at h1 h0
    exact Real.exp_injective (h0.symm.trans h1)
  have hbT := aux_in_deterministic_good_scale_transfer_ir_remainder H omega hIR xp w
  have hSB : ∀ K, m ≤ K → |Sm K| ≤ min B ((d : ℝ) * T) := by
    intro K _
    have habs : |Sm K| ≤ ∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
        |eta k (((3 : ℝ) ^ m) • x + z) - eta k z| := Finset.abs_sum_le_sum_abs _ _
    refine le_min (habs.trans (hPbound x hx K)) (habs.trans ?_)
    refine (aux_in_deterministic_good_scale_transfer_gradient_block eta m z hx _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (hTbound K) (Nat.cast_nonneg d)
  have hXle := aux_in_deterministic_good_scale_transfer_limit_bound X _ Sm bK m hXK hbT hSB
  have hXB : |X| ≤ B := hXle.trans (min_le_left _ _)
  have hbound : ∀ t : ℝ, |t| ≤ min B ((d : ℝ) * T) → |t| ≤ B →
      |Real.exp t - 1| ≤ eps := by
    intro t ht htB
    refine (aux_in_deterministic_good_scale_transfer_abs_exp_sub_one t).trans ?_
    exact mul_le_mul ht (Real.exp_le_exp.mpr htB) (Real.exp_pos _).le
      (le_min hB (mul_nonneg (Nat.cast_nonneg d) hT))
  have hm0 := hre m le_rfl
  simp only at hm0
  obtain ⟨hfwd, hbwd⟩ := hm0
  have hXeq : Sm m + bK m = X := rfl
  constructor
  · have := hbwd
    rw [hXeq] at this
    change |(a0 / ahom M m) *
        _root_.SubdiffusiveProcess.Model.aCutoff M m (translatePotentialSample z eta) (((3 : ℝ) ^ m) • x) /
        cutoffCoefficient M H omega N xp - 1| ≤ eps
    rw [this]
    exact hbound (-X) (by rw [abs_neg]; exact hXle) (by rw [abs_neg]; exact hXB)
  · have := hfwd
    rw [hXeq] at this
    change |(a0 / ahom M m)⁻¹ * cutoffCoefficient M H omega N xp /
        _root_.SubdiffusiveProcess.Model.aCutoff M m (translatePotentialSample z eta)
          (((3 : ℝ) ^ m) • x) - 1| ≤ eps
    rw [this]
    exact hbound X hXle hXB


/-- `eramp a b X < 1` forces `X < b` (including `X = ⊤`). -/
lemma aux_in_deterministic_good_scale_transfer_eramp_lt {a b : ℝ} (hab : a < b) (ha : 0 ≤ a)
    (X : ENNReal)
    (h : (min (1 : ENNReal) ((X - ENNReal.ofReal a) / ENNReal.ofReal (b - a))).toReal < 1) :
    X < ENNReal.ofReal b := by
  by_contra hX
  push Not at hX
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hsub : ENNReal.ofReal (b - a) ≤ X - ENNReal.ofReal a := by
    rw [ENNReal.le_sub_iff_add_le_right ENNReal.ofReal_ne_top
      (le_trans (ENNReal.ofReal_le_ofReal hab.le) hX)]
    rw [← ENNReal.ofReal_add hba.le ha]
    simpa using hX
  have hone : 1 ≤ (X - ENNReal.ofReal a) / ENNReal.ofReal (b - a) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hba)) (Or.inl ENNReal.ofReal_ne_top),
      one_mul]
    exact hsub
  rw [min_eq_left hone] at h
  simp at h

/-- **`Z < 1` gives the `P < 12` oscillation bound** on the full relabelled
sample: every block of long-wavelength shells `k ≥ m` oscillates by less than
`log 12 / 4` between `z` and any point `z + 3^m x`, `x` in the unit root. -/
theorem aux_in_deterministic_good_scale_transfer_P_bound {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt)
    (m : ℕ) (z : Vec d) (hZ : Zsc m z < 1)
    {x : Vec d} (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (a b : ℕ) (hma : m ≤ a) :
    ∑ k ∈ Finset.Ico a b, |g k (((3 : ℝ) ^ m) • x + z) - g k z| ≤ Real.log 12 / 4 := by
  obtain ⟨hs0, hs1, he0, he1, _hF, hP, _hR, _hD, _hG, hZdef, _hbase⟩ := hPS
  obtain ⟨hZeq, _, _⟩ := hZdef m z
  set e1 := (min (1 : ENNReal) ((Fsc m z - ENNReal.ofReal (eps / 2)) /
      ENNReal.ofReal (eps - eps / 2))).toReal
  set e2 := (min (1 : ENNReal) ((Psc m z - ENNReal.ofReal 6) /
      ENNReal.ofReal (12 - 6))).toReal
  set e3 := (min (1 : ENNReal) ((Rsc m z - ENNReal.ofReal (eps ^ 2 / 4)) /
      ENNReal.ofReal (eps ^ 2 - eps ^ 2 / 4))).toReal
  have hZ' : e1 + e2 + e3 < 1 := by rw [← hZeq]; exact hZ
  have he2 : e2 < 1 := by
    have h1 : 0 ≤ e1 := ENNReal.toReal_nonneg
    have h3 : 0 ≤ e3 := ENNReal.toReal_nonneg
    linarith
  have hP12 : Psc m z < ENNReal.ofReal 12 :=
    aux_in_deterministic_good_scale_transfer_eramp_lt (by norm_num) (by norm_num) _ he2
  -- the point `y = z + 3^m x` lies in `translatedCube d (m + 1 + 0) z`
  set y : Vec d := ((3 : ℝ) ^ m) • x + z with hy
  have hymem : y ∈ translatedCube d ((m + 1 + 0 : ℕ) : ℤ) z := by
    refine ⟨((3 : ℝ) ^ m) • x, ?_, by rw [hy, add_comm]⟩
    have hc := aux_in_deterministic_good_scale_transfer_smul_mem_cube m hx
    unfold cube at hc ⊢
    rw [Homogenization.mem_openCubeSet_originCube_iff] at hc ⊢
    intro i
    obtain ⟨h1, h2⟩ := hc i
    have h3 : (3 : ℝ) ^ (m : ℤ) ≤ (3 : ℝ) ^ (((m + 1 + 0 : ℕ) : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    constructor <;> nlinarith
  -- every finite product from index `m` is below `12`
  have hprod : ∀ K : ℕ, ∏ i ∈ Finset.Icc m (m + K),
      ENNReal.ofReal (Real.exp (4 * |g i y - g i z|)) < ENNReal.ofReal 12 := by
    intro K
    refine lt_of_le_of_lt ?_ hP12
    rw [hP m z]
    refine le_trans ?_ (le_sSup ⟨0, rfl⟩)
    simp only [CharP.cast_eq_zero, mul_zero, zero_div, neg_zero, Real.rpow_zero,
      ENNReal.ofReal_one, one_mul]
    refine le_trans ?_ (le_sSup ⟨y, by simpa using hymem, rfl⟩)
    refine le_trans ?_ le_add_self
    exact le_sSup ⟨K, by simp⟩
  have hsumK : ∀ K : ℕ, ∑ i ∈ Finset.Icc m (m + K), |g i y - g i z| ≤ Real.log 12 / 4 := by
    intro K
    have h := hprod K
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
      ← Real.exp_sum] at h
    have h' := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp h
    have hlog := (Real.lt_log_iff_exp_lt (by norm_num)).mpr h'
    rw [← Finset.mul_sum] at hlog
    linarith
  by_cases hab : b ≤ a
  · rw [Finset.Ico_eq_empty_of_le hab, Finset.sum_empty]
    positivity
  · push Not at hab
    refine le_trans ?_ (hsumK (b - m))
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_Ico] at hk
      rw [Finset.mem_Icc]
      omega
    · intro _ _ _
      exact abs_nonneg _

/-- Real `sSup` of an absolute-value image is below the `toReal` of the
extended-valued `sSup`, whenever the latter is finite (junk-safe). -/
lemma aux_in_deterministic_good_scale_transfer_real_sSup_le {d : ℕ} (W : Set (Vec d))
    (f : Vec d → ℝ)
    (hfin : sSup {v : ENNReal | ∃ x : Vec d, x ∈ W ∧ v = ENNReal.ofReal |f x|} ≠ ⊤) :
    sSup {r : ℝ | ∃ x ∈ W, r = |f x|} ≤
      (sSup {v : ENNReal | ∃ x : Vec d, x ∈ W ∧ v = ENNReal.ofReal |f x|}).toReal := by
  by_cases hb : BddAbove {r : ℝ | ∃ x ∈ W, r = |f x|}
  · rcases Set.eq_empty_or_nonempty {r : ℝ | ∃ x ∈ W, r = |f x|} with he | hne
    · rw [he, Real.sSup_empty]; exact ENNReal.toReal_nonneg
    · refine csSup_le hne ?_
      rintro r ⟨x, hx, rfl⟩
      rw [← ENNReal.toReal_ofReal (abs_nonneg (f x))]
      exact ENNReal.toReal_mono hfin (le_sSup ⟨x, hx, rfl⟩)
  · rw [Real.sSup_of_not_bddAbove hb]; exact ENNReal.toReal_nonneg

/-- **The gradient tail is controlled by the finite `Draw` score**: every finite
block of the fourth `accumulatedError` summands at `(m, z)` is at most
`(Dsc m z).toReal`, provided `Dsc m z ≠ ⊤`. -/
theorem aux_in_deterministic_good_scale_transfer_T_bound {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt)
    (m : ℕ) (z : Vec d) (hD : Dsc m z ≠ ⊤) (a b : ℕ) (hma : m ≤ a) :
    ∑ k ∈ Finset.Ico a b,
        (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d m z) (shellGradient (g k)) ≤
      (Dsc m z).toReal := by
  obtain ⟨_, _, _, _, _, _, _, hDdef, _, _, _⟩ := hPS
  set t : ℕ → ENNReal := fun j => if m ≤ j then
      ENNReal.ofReal ((3 : ℝ) ^ m) *
        sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d m z ∧
          v = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (g j) x)|}
      else 0 with ht
  have hDeq := hDdef m z
  have htle : ∑' j, t j ≤ Dsc m z := by
    rw [hDeq]
    exact le_add_self
  have httop : ∑' j, t j ≠ ⊤ := ne_top_of_le_ne_top hD htle
  have hterm : ∀ k ∈ Finset.Ico a b,
      (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d m z) (shellGradient (g k)) ≤
        (t k).toReal := by
    intro k hk
    have hmk : m ≤ k := hma.trans (Finset.mem_Ico.mp hk).1
    have htk : t k ≠ ⊤ := ne_top_of_le_ne_top httop (ENNReal.le_tsum k)
    simp only [ht, ite_eq_left hmk] at htk ⊢
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hne : sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d m z ∧
        v = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (g k) x)|} ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top (by simp)] at htk
      exact htk rfl
    have h := aux_in_deterministic_good_scale_transfer_real_sSup_le (translatedCube d m z)
      (fun x => Homogenization.euclideanNorm (shellGradient (g k) x)) hne
    unfold vectorSupNormOn
    have hset : {r : ℝ | ∃ x ∈ translatedCube d m z,
        r = Homogenization.euclideanNorm (shellGradient (g k) x)} =
        {r : ℝ | ∃ x ∈ translatedCube d m z,
          r = |Homogenization.euclideanNorm (shellGradient (g k) x)|} := by
      ext r
      simp only [Set.mem_ofPred_eq, abs_of_nonneg (Homogenization.euclideanNorm_nonneg _)]
    rw [hset]
    exact h
  calc
    ∑ k ∈ Finset.Ico a b,
        (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d m z) (shellGradient (g k))
        ≤ ∑ k ∈ Finset.Ico a b, (t k).toReal := Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.Ico a b, t k).toReal := by
      rw [ENNReal.toReal_sum]
      intro k hk
      exact ne_top_of_le_ne_top httop (ENNReal.le_tsum k)
    _ ≤ (∑' j, t j).toReal := ENNReal.toReal_mono httop (ENNReal.sum_le_tsum _)
    _ ≤ (Dsc m z).toReal := ENNReal.toReal_mono hD htle


/-- **R2 closed from the inputs.**  At the literal `in_deterministic`
instantiation, on any `omega` where `hEta`, `primitive_scores` (at cutoff `N`)
and infrared convergence hold, for either sign of `l ≤ N`: if the primitive bad
score is `< 1` and the `Draw` score is finite at `(m, 3^N w)`, the actual
`I.err` is controlled by the GMC equal-scale error at `(m, m)` with an additive
price linear in `Draw`. -/
theorem aux_in_deterministic_good_scale_transfer_pointwise_of_scores
    {d : ℕ} [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ))
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (w : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ (-l))
    (hZ : Zsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) < 1)
    (hD : Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤) :
    let m : ℕ := ((N : ℤ) - l).toNat
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun ell v beta =>
        if 0 ≤ ell then
          ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
        else
          -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
    let a0 : ℝ := kappa m / kappa N * Real.exp (H omega w + retained l w omega)
    let e : ℝ := min (Real.log 12 / 4) ((d : ℝ) * (Dsc m (((3 : ℝ) ^ N) • w)).toReal) *
      Real.exp (Real.log 12 / 4)
    I.err w ((3 : ℝ) ^ (-l)) hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr)
        w ((3 : ℝ) ^ (-l)) a0 s 2 ≤
      Real.sqrt (2 + 6 * e ^ 2) *
          section6HomogenizationError M s m m eta (((3 : ℝ) ^ N) • w) +
        Real.sqrt (6 * e ^ 2) := by
  intro m kappa retained a0 e
  have hB : (0 : ℝ) ≤ Real.log 12 / 4 := by
    have : (0 : ℝ) ≤ Real.log 12 := Real.log_nonneg (by norm_num)
    positivity
  exact aux_in_deterministic_good_scale_transfer_pointwise I M H omega N l hl eta hEta hIR w hr
    s hs (Real.log 12 / 4) (Dsc m (((3 : ℝ) ^ N) • w)).toReal hB ENNReal.toReal_nonneg
    (fun x hx K => aux_in_deterministic_good_scale_transfer_P_bound M s eps eta
      Fsc Psc Rsc Dsc Zsc goodEvt hPS m _ hZ hx _ _ (Nat.le_succ m))
    (fun K => aux_in_deterministic_good_scale_transfer_T_bound M s eps eta
      Fsc Psc Rsc Dsc Zsc goodEvt hPS m _ hD _ _ (Nat.le_succ m))


/-- Junk-safe comparison of a real `sSup` with the `toReal` of a finite
extended-valued `sSup`, through elementwise partners. -/
lemma aux_in_deterministic_good_scale_transfer_sSup_le_toReal (S : Set ℝ) (T : Set ENNReal)
    (hT : sSup T ≠ ⊤) (h : ∀ r ∈ S, ∃ v ∈ T, r ≤ v.toReal) :
    sSup S ≤ (sSup T).toReal := by
  by_cases hb : BddAbove S
  · rcases Set.eq_empty_or_nonempty S with he | hne
    · rw [he, Real.sSup_empty]; exact ENNReal.toReal_nonneg
    · refine csSup_le hne fun r hr => ?_
      obtain ⟨v, hv, hrv⟩ := h r hr
      exact hrv.trans (ENNReal.toReal_mono hT (le_sSup hv))
  · rw [Real.sSup_of_not_bddAbove hb]; exact ENNReal.toReal_nonneg

lemma aux_in_deterministic_good_scale_transfer_scaled_sup_le {d : ℕ} (W : Set (Vec d))
    (f : Vec d → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hfin : ENNReal.ofReal c *
      sSup {v : ENNReal | ∃ x : Vec d, x ∈ W ∧ v = ENNReal.ofReal |f x|} ≠ ⊤) :
    c * supNormOn W f ≤
      (ENNReal.ofReal c *
        sSup {v : ENNReal | ∃ x : Vec d, x ∈ W ∧ v = ENNReal.ofReal |f x|}).toReal := by
  rcases hc.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact ENNReal.toReal_nonneg
  · have hne : sSup {v : ENNReal | ∃ x : Vec d, x ∈ W ∧ v = ENNReal.ofReal |f x|} ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top (by simpa using hpos)] at hfin
      exact hfin rfl
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
    exact mul_le_mul_of_nonneg_left
      (aux_in_deterministic_good_scale_transfer_real_sSup_le W f hne) hc

/-- **R4: the real `accumulatedError` at the equal cutoff is bounded by the
finite `Draw` score**, term by term, robust to real `sSup`/`tsum` junk. -/
theorem aux_in_deterministic_good_scale_transfer_accumulatedError_le {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt)
    (m : ℕ) (z : Vec d) (hD : Dsc m z ≠ ⊤) :
    accumulatedError M (some m) m z s g ≤ (Dsc m z).toReal := by
  obtain ⟨_, _, _, _, _, _, _, hDdef, _, _, _⟩ := hPS
  have hDeq := hDdef m z
  set A' := sSup {v : ENNReal | ∃ j l : ℕ, j ≤ m ∧ l ≤ m ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
          OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ)))) *
            (min (sSup {v : ENNReal | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
              v = ENNReal.ofReal (section6Response M l l g x e)}) 1) ^ (1 / 2 : ℝ)} with hA'
  set B' := sSup {v : ENNReal | ∃ j : ℕ, j ≤ m ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ)))) *
            sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d m z ∧
              v = ENNReal.ofReal |shellBlock m j g x|}} with hB'
  set C' := ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (m : ℝ))) *
          sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d m z ∧
            v = ENNReal.ofReal |g 0 x|} with hC'
  set t : ℕ → ENNReal := fun j => if m ≤ j then
      ENNReal.ofReal ((3 : ℝ) ^ m) *
        sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d m z ∧
          v = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (g j) x)|}
      else 0 with ht
  have hsum : Dsc m z = A' + B' + C' + ∑' j, t j := hDeq
  have hleA : A' ≤ Dsc m z := by
    rw [hsum]
    exact le_self_add.trans (le_self_add.trans le_self_add)
  have hleB : B' ≤ Dsc m z := by
    rw [hsum]
    exact le_add_self.trans (le_self_add.trans le_self_add)
  have hleC : C' ≤ Dsc m z := by
    rw [hsum]
    exact le_add_self.trans le_self_add
  have hleT : ∑' j, t j ≤ Dsc m z := by
    rw [hsum]
    exact le_add_self
  have hA'top : A' ≠ ⊤ := ne_top_of_le_ne_top hD hleA
  have hB'top : B' ≠ ⊤ := ne_top_of_le_ne_top hD hleB
  have hC'top : C' ≠ ⊤ := ne_top_of_le_ne_top hD hleC
  have htop : ∑' j, t j ≠ ⊤ := ne_top_of_le_ne_top hD hleT
  unfold accumulatedError
  rw [hsum, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hA'top, hB'top⟩,
      hC'top⟩) htop, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hA'top, hB'top⟩) hC'top,
    ENNReal.toReal_add hA'top hB'top]
  gcongr
  · -- first term: responses
    refine aux_in_deterministic_good_scale_transfer_sSup_le_toReal _ _ hA'top ?_
    rintro r ⟨j, l, hjm, hlj, z', hgrid, hann, rfl⟩
    refine ⟨_, ⟨j, l, hjm, by omega, hlj, z', hgrid, hann, rfl⟩, ?_⟩
    have hmin : min l ((some m).getD l) = l := by
      simp only [Option.getD_some]; omega
    rw [hmin]
    set RS := sSup {t : ℝ | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
      t = section6Response M l l g z' e}
    set J := sSup {v : ENNReal | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
      v = ENNReal.ofReal (section6Response M l l g z' e)}
    have hminle : min J 1 ≤ 1 := min_le_right _ _
    have hmintop : min J 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hminle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← ENNReal.toReal_rpow,
      ← Real.sqrt_eq_rpow]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
    by_cases hJ : J = ⊤
    · rw [hJ, min_eq_right le_top, ENNReal.toReal_one]; exact min_le_right _ _
    · rw [ENNReal.toReal_min hJ ENNReal.one_ne_top, ENNReal.toReal_one]
      refine min_le_min_right _ ?_
      refine aux_in_deterministic_good_scale_transfer_sSup_le_toReal _ _ hJ ?_
      rintro t ⟨e, he, rfl⟩
      exact ⟨_, ⟨e, he, rfl⟩, by rw [ENNReal.toReal_ofReal']; exact le_max_left _ _⟩
  · -- second term: short-wavelength shell blocks
    refine aux_in_deterministic_good_scale_transfer_sSup_le_toReal _ _ hB'top ?_
    rintro r ⟨j, hj, rfl⟩
    refine ⟨_, ⟨j, hj, rfl⟩, ?_⟩
    refine aux_in_deterministic_good_scale_transfer_scaled_sup_le _ _ _ (by positivity) ?_
    exact ne_top_of_le_ne_top hB'top (le_sSup ⟨j, hj, rfl⟩)
  · -- third term: the zeroth shell
    exact aux_in_deterministic_good_scale_transfer_scaled_sup_le _ _ _ (by positivity) hC'top
  · -- fourth term: the gradient tail
    refine tsum_le_of_sum_le' ENNReal.toReal_nonneg fun F => ?_
    have hterm : ∀ k : ℕ, (if m ≤ k then
        (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d m z) (shellGradient (g k)) else 0) ≤
        (t k).toReal := by
      intro k
      by_cases hmk : m ≤ k
      · have htk : t k ≠ ⊤ := ne_top_of_le_ne_top htop (ENNReal.le_tsum k)
        simp only [ht, ite_eq_left hmk] at htk ⊢
        have hset : vectorSupNormOn (translatedCube d m z) (shellGradient (g k)) =
            supNormOn (translatedCube d m z)
              (fun x => Homogenization.euclideanNorm (shellGradient (g k) x)) := by
          unfold vectorSupNormOn supNormOn
          congr 1
          ext r
          simp only [Set.mem_ofPred_eq, abs_of_nonneg (Homogenization.euclideanNorm_nonneg _)]
        rw [hset]
        exact aux_in_deterministic_good_scale_transfer_scaled_sup_le _ _ _ (by positivity) htk
      · simp only [ht, ite_eq_right hmk, ENNReal.toReal_zero, le_refl]
    calc
      ∑ k ∈ F, (if m ≤ k then
          (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d m z) (shellGradient (g k)) else 0)
          ≤ ∑ k ∈ F, (t k).toReal := Finset.sum_le_sum fun k _ => hterm k
      _ = (∑ k ∈ F, t k).toReal := by
        rw [ENNReal.toReal_sum]
        intro k _
        exact ne_top_of_le_ne_top htop (ENNReal.le_tsum k)
      _ ≤ (∑' j, t j).toReal := ENNReal.toReal_mono htop (ENNReal.sum_le_tsum _)


/-- A positive real multiple of an extended real below a finite real bound. -/
lemma aux_in_deterministic_good_scale_transfer_scaled_lt {c b : ℝ} (hc : 0 < c) (Y : ENNReal)
    (h : ENNReal.ofReal c * Y < ENNReal.ofReal b) :
    Y ≠ ⊤ ∧ Y.toReal < b / c := by
  have hY : Y ≠ ⊤ := by
    intro hY
    rw [hY, ENNReal.mul_top (by simpa using hc)] at h
    exact (not_top_lt h).elim
  refine ⟨hY, ?_⟩
  have hlhs : ENNReal.ofReal c * Y ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY
  have h' := (ENNReal.toReal_lt_toReal hlhs ENNReal.ofReal_ne_top).mpr h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at h'
  have hb : 0 ≤ b := by
    by_contra hb
    push Not at hb
    rw [ENNReal.ofReal_of_nonpos hb.le] at h
    exact (ENNReal.not_lt_zero h).elim
  rw [ENNReal.toReal_ofReal hb] at h'
  rw [lt_div_iff₀ hc]
  linarith

lemma aux_in_deterministic_good_scale_transfer_rpow_neg_inv (t : ℝ) :
    (1 : ℝ) / (3 : ℝ) ^ (-t) = (3 : ℝ) ^ t := by
  rw [Real.rpow_neg (by norm_num), one_div, inv_inv]

lemma aux_in_deterministic_good_scale_transfer_translatedCube_nonempty {d : ℕ} (k : ℕ)
    (z : Vec d) : z ∈ translatedCube d (k : ℤ) z :=
  ⟨0, aux_in_deterministic_good_scale_transfer_zero_mem_cube k, by simp⟩

/-- **R3: `Z < 1` puts the relabelled sample in the threshold-12 good event**
with the equal response cutoff `some m`, for every `eps' ∈ [eps, 1]`. -/
theorem aux_in_deterministic_good_scale_transfer_event {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt)
    (m : ℕ) (z : Vec d) (hZ : Zsc m z < 1) (eps' : ℝ) (hee : eps ≤ eps') (he1 : eps' ≤ 1) :
    g ∈ _root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some m) m z eps' s := by
  obtain ⟨hs0, hs1, he0, _he1, hF, hP, hR, _hD, _hG, hZdef, _hbase⟩ := hPS
  obtain ⟨hZeq, _, _⟩ := hZdef m z
  set e1 := (min (1 : ENNReal) ((Fsc m z - ENNReal.ofReal (eps / 2)) /
      ENNReal.ofReal (eps - eps / 2))).toReal
  set e2 := (min (1 : ENNReal) ((Psc m z - ENNReal.ofReal 6) /
      ENNReal.ofReal (12 - 6))).toReal
  set e3 := (min (1 : ENNReal) ((Rsc m z - ENNReal.ofReal (eps ^ 2 / 4)) /
      ENNReal.ofReal (eps ^ 2 - eps ^ 2 / 4))).toReal
  have hZ' : e1 + e2 + e3 < 1 := by rw [← hZeq]; exact hZ
  have h1 : 0 ≤ e1 := ENNReal.toReal_nonneg
  have h2 : 0 ≤ e2 := ENNReal.toReal_nonneg
  have h3 : 0 ≤ e3 := ENNReal.toReal_nonneg
  have hFlt : Fsc m z < ENNReal.ofReal eps :=
    aux_in_deterministic_good_scale_transfer_eramp_lt (by linarith) (by linarith) _
      (by linarith : e1 < 1)
  have hPlt : Psc m z < ENNReal.ofReal 12 :=
    aux_in_deterministic_good_scale_transfer_eramp_lt (by norm_num) (by norm_num) _
      (by linarith : e2 < 1)
  have hRlt : Rsc m z < ENNReal.ofReal (eps ^ 2) :=
    aux_in_deterministic_good_scale_transfer_eramp_lt (by nlinarith) (by positivity) _
      (by linarith : e3 < 1)
  refine ⟨by norm_num, hs0, hs1, by linarith, he1, ?_, ?_, ?_⟩
  · -- GoodFieldOne
    intro j
    set c : ℝ := (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) with hc
    have hcpos : 0 < c := by positivity
    set Nf : ℕ → ENNReal := fun i =>
      sSup {v : ENNReal | ∃ x ∈ translatedCube d ((m + 1 + j : ℕ) : ℤ) z,
        v = ENNReal.ofReal |(fun x : Vec d => |g i x| + (3 : ℝ) ^ (i : ℝ) *
          Homogenization.euclideanNorm (shellGradient (g i) x)) x|} with hNf
    have hle : ENNReal.ofReal c * ∑ i ∈ Finset.Icc (m - j) (m + j), Nf i ≤ Fsc m z := by
      rw [hF m z]
      exact le_sSup ⟨j, by simp [hNf, hc]⟩
    obtain ⟨hNtop, hNlt⟩ := aux_in_deterministic_good_scale_transfer_scaled_lt hcpos _
      (lt_of_le_of_lt hle hFlt)
    have hNi : ∀ i ∈ Finset.Icc (m - j) (m + j), Nf i ≠ ⊤ := fun i hi =>
      ne_top_of_le_ne_top hNtop (Finset.single_le_sum (fun _ _ => zero_le) hi)
    have hreal : ∀ i ∈ Finset.Icc (m - j) (m + j),
        supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) z) (fun x ↦
          |g i x| + (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (g i) x)) ≤
          (Nf i).toReal := by
      intro i hi
      have h := aux_in_deterministic_good_scale_transfer_real_sSup_le
        (translatedCube d ((m + 1 + j : ℕ) : ℤ) z)
        (fun x : Vec d => |g i x| + (3 : ℝ) ^ (i : ℝ) *
          Homogenization.euclideanNorm (shellGradient (g i) x))
        (by simpa [hNf] using hNi i hi)
      simp only [Real.rpow_natCast] at h
      unfold supNormOn
      simpa [hNf, Real.rpow_natCast] using h
    calc
      ∑ i ∈ Finset.Icc (m - j) (m + j),
          supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) z) (fun x ↦
            |g i x| + (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (g i) x))
          ≤ ∑ i ∈ Finset.Icc (m - j) (m + j), (Nf i).toReal := Finset.sum_le_sum hreal
      _ = (∑ i ∈ Finset.Icc (m - j) (m + j), Nf i).toReal := (ENNReal.toReal_sum hNi).symm
      _ ≤ eps / c := hNlt.le
      _ = eps * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) := by
        rw [div_eq_mul_one_div, hc, aux_in_deterministic_good_scale_transfer_rpow_neg_inv]
      _ ≤ eps' * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) :=
        mul_le_mul_of_nonneg_right hee (by positivity)
  · -- product clause
    intro j
    set c : ℝ := (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) with hc
    have hcpos : 0 < c := by positivity
    set Wc := translatedCube d ((m + 1 + j : ℕ) : ℤ) z with hWc
    set U : Vec d → ENNReal := fun x => sSup {u : ENNReal | ∃ K : ℕ,
      u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
        ENNReal.ofReal (Real.exp (4 * |g i x - g i z|))} with hU
    set A : Vec d → ℝ := fun x => ∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |g i x| with hA
    set Y := sSup {w : ENNReal | ∃ x ∈ Wc,
      w = ∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |g i x|) + U x} with hY
    have hle : ENNReal.ofReal c * Y ≤ Psc m z := by
      rw [hP m z]
      exact le_sSup ⟨j, by simp [hY, hU, hc, hWc]⟩
    obtain ⟨hYtop, hYlt⟩ := aux_in_deterministic_good_scale_transfer_scaled_lt hcpos _
      (lt_of_le_of_lt hle hPlt)
    have hbound : (12 : ℝ) / c = 12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) := by
      rw [div_eq_mul_one_div, hc, aux_in_deterministic_good_scale_transfer_rpow_neg_inv]
    -- pointwise analysis at `x ∈ Wc`
    have hpt : ∀ x ∈ Wc,
        Multipliable (fun i : ℕ =>
          if m + j ≤ i then Real.exp (4 * |g i x - g i z|) else 1) ∧
        0 ≤ A x + ∏' i : ℕ, (if m + j ≤ i then Real.exp (4 * |g i x - g i z|) else 1) ∧
        A x + ∏' i : ℕ, (if m + j ≤ i then Real.exp (4 * |g i x - g i z|) else 1) ≤
          12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) := by
      intro x hx
      have hWx : ENNReal.ofReal (A x) + U x ≤ Y := by
        rw [hA, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
        exact le_sSup ⟨x, hx, rfl⟩
      have hUtop : U x ≠ ⊤ := ne_top_of_le_ne_top hYtop (le_add_self.trans hWx)
      have hU1 : ENNReal.ofReal (Real.exp (4 * |g (m + j) x - g (m + j) z|)) ≤ U x := by
        refine le_trans ?_ (le_sSup ⟨0, rfl⟩)
        simp
      have hUpos : 0 < (U x).toReal := by
        refine lt_of_lt_of_le ?_ (ENNReal.toReal_mono hUtop hU1)
        rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
        exact Real.exp_pos _
      set a : ℕ → ℝ := fun i => if m + j ≤ i then 4 * |g i x - g i z| else 0 with ha
      have ha0 : ∀ i, 0 ≤ a i := fun i => by
        simp only [ha]; split
        · positivity
        · exact le_rfl
      have hpartial : ∀ n, ∑ i ∈ Finset.range n, a i ≤ Real.log (U x).toReal := by
        intro n
        rw [Real.le_log_iff_exp_le hUpos]
        have hsub : ∑ i ∈ Finset.range n, a i ≤
            ∑ i ∈ Finset.Icc (m + j) (m + j + n), 4 * |g i x - g i z| := by
          calc
            ∑ i ∈ Finset.range n, a i
                = ∑ i ∈ (Finset.range n).filter (fun i => m + j ≤ i),
                    4 * |g i x - g i z| := by
                  rw [Finset.sum_filter]
            _ ≤ ∑ i ∈ Finset.Icc (m + j) (m + j + n), 4 * |g i x - g i z| := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro i hi
                    rw [Finset.mem_filter, Finset.mem_range] at hi
                    rw [Finset.mem_Icc]
                    omega
                  · intro _ _ _; positivity
        calc
          Real.exp (∑ i ∈ Finset.range n, a i)
              ≤ Real.exp (∑ i ∈ Finset.Icc (m + j) (m + j + n), 4 * |g i x - g i z|) :=
                Real.exp_le_exp.mpr hsub
          _ = (∏ i ∈ Finset.Icc (m + j) (m + j + n),
                ENNReal.ofReal (Real.exp (4 * |g i x - g i z|))).toReal := by
                rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
                  ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le),
                  Real.exp_sum]
          _ ≤ (U x).toReal := ENNReal.toReal_mono hUtop (le_sSup ⟨n, rfl⟩)
      have hsumm : Summable a := summable_of_sum_range_le ha0 hpartial
      have hprod : HasProd (fun i : ℕ =>
          if m + j ≤ i then Real.exp (4 * |g i x - g i z|) else 1)
          (Real.exp (∑' i, a i)) := by
        have h := hsumm.hasSum.rexp
        convert h using 1
        funext i
        simp only [Function.comp_apply, ha]
        split
        · rfl
        · exact Real.exp_zero.symm
      have htprod := hprod.tprod_eq
      have htsum : ∑' i, a i ≤ Real.log (U x).toReal :=
        Real.tsum_le_of_sum_range_le ha0 hpartial
      have hAx : 0 ≤ A x := Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
      refine ⟨hprod.multipliable, ?_, ?_⟩
      · rw [htprod]; positivity
      · rw [htprod]
        have hexp : Real.exp (∑' i, a i) ≤ (U x).toReal := by
          calc Real.exp (∑' i, a i) ≤ Real.exp (Real.log (U x).toReal) :=
                Real.exp_le_exp.mpr htsum
            _ = (U x).toReal := Real.exp_log hUpos
        have hYx : (ENNReal.ofReal (A x) + U x).toReal ≤ Y.toReal :=
          ENNReal.toReal_mono hYtop hWx
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hUtop, ENNReal.toReal_ofReal hAx] at hYx
        rw [← hbound]
        linarith
    have hbdd : ∀ x ∈ Wc,
        |A x + ∏' i : ℕ, (if m + j ≤ i then Real.exp (4 * |g i x - g i z|) else 1)| ≤
          12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) := by
      intro x hx
      obtain ⟨_, h0, hle⟩ := hpt x hx
      rw [abs_of_nonneg h0]; exact hle
    refine ⟨fun x hx => (hpt x hx).1, ?_, ?_⟩
    · refine ⟨12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8), ?_⟩
      rintro r ⟨x, hx, rfl⟩
      exact hbdd x hx
    · unfold supNormOn
      refine csSup_le ⟨_, ⟨z, aux_in_deterministic_good_scale_transfer_translatedCube_nonempty
        (m + 1 + j) z, rfl⟩⟩ ?_
      rintro r ⟨x, hx, rfl⟩
      exact hbdd x hx
  · -- GoodResponse
    intro j n hjm hnj z' hgrid hann e he
    have hmin : min n ((some m).getD n) = n := by
      simp only [Option.getD_some]; omega
    rw [hmin]
    set c : ℝ := (3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8)) with hc
    have hcpos : 0 < c := by positivity
    set Jn := sSup {v : ENNReal | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
      v = ENNReal.ofReal (section6Response M n n g z' e)} with hJn
    have hJ : ENNReal.ofReal (section6Response M n n g z' e) ≤ Jn := le_sSup ⟨e, he, rfl⟩
    have hle : ENNReal.ofReal c * ENNReal.ofReal (section6Response M n n g z' e) ≤ Rsc m z := by
      rw [hR m z]
      calc
        ENNReal.ofReal c * ENNReal.ofReal (section6Response M n n g z' e)
            ≤ ENNReal.ofReal c * Jn := by gcongr
        _ ≤ _ := by
          apply le_sSup
          exact ⟨j, n, hjm, hnj, z', hgrid, hann, rfl⟩
    obtain ⟨_, hlt⟩ := aux_in_deterministic_good_scale_transfer_scaled_lt hcpos _
      (lt_of_le_of_lt hle hRlt)
    have hresp : section6Response M n n g z' e ≤
        (ENNReal.ofReal (section6Response M n n g z' e)).toReal := by
      rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
    have hbound : eps ^ 2 / c = eps ^ 2 * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := by
      rw [div_eq_mul_one_div, hc, aux_in_deterministic_good_scale_transfer_rpow_neg_inv]
    calc
      section6Response M n n g z' e ≤ eps ^ 2 / c := hresp.trans hlt.le
      _ = eps ^ 2 * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := hbound
      _ ≤ eps' ^ 2 * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := by
        gcongr


lemma aux_in_deterministic_good_scale_transfer_log12_div4_le_one : Real.log 12 / 4 ≤ 1 := by
  have h : Real.log 12 ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
    calc (12 : ℝ) ≤ 2.7 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h27 4
  linarith

/-- R5: the disorder smallness `delta ≤ √s / 8` gives every parameter window
of the threshold-12 bound. -/
lemma aux_in_deterministic_good_scale_transfer_params {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ) (hs0 : 0 < s) (hsSmall : s ≤ (1 / 32 : ℝ))
    (hdelta : M.delta ≤ Real.sqrt s / 8) :
    64 * M.delta ^ 2 ≤ s ∧ s ≤ 1 / 2 ∧ 0 ≤ s⁻¹ * M.delta ^ 2 ∧ s⁻¹ * M.delta ^ 2 ≤ 1 ∧
      _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 := by
  have hδ0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hδsq : M.delta ^ 2 ≤ s / 64 := by
    have h := pow_le_pow_left₀ hδ0.le hdelta 2
    rw [div_pow, Real.sq_sqrt hs0.le] at h
    norm_num at h
    linarith
  have hb1 : s⁻¹ * M.delta ^ 2 ≤ 1 := by
    have : s⁻¹ * M.delta ^ 2 ≤ s⁻¹ * (s / 64) :=
      mul_le_mul_of_nonneg_left hδsq (inv_nonneg.mpr hs0.le)
    have h2 : s⁻¹ * (s / 64) = 1 / 64 := by field_simp
    linarith
  refine ⟨by linarith, by linarith, by positivity, hb1, ?_⟩
  have ht := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
  have hl2 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ Real.log 2 / 2 * M.delta ^ 2 := ht
    _ ≤ Real.log 2 / 2 * (s / 64) := mul_le_mul_of_nonneg_left hδsq (by positivity)
    _ ≤ s * Real.log 3 / 16 := by nlinarith

/-- **GMC side**: from the threshold-12 carrier, on `Z < 1` with finite `Draw`,
the equal-scale GMC error is linear in `s⁻¹ δ² + eps⁸ + Draw`. -/
theorem aux_in_deterministic_good_scale_transfer_gmc_bound {d : ℕ} [NeZero d]
    (hreg : _root_.SubdiffusiveProcess.Paper.product_threshold_regularities d 12) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ),
      0 < s → s ≤ (1 / 32 : ℝ) → M.delta ≤ Real.sqrt s / 8 → eps < 1 →
      ∀ (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
        (goodEvt : ℕ → Vec d → Prop),
        _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt →
      ∀ (m : ℕ) (z : Vec d), Zsc m z < 1 → Dsc m z ≠ ⊤ →
        section6HomogenizationError M s m m g z ≤
          C * (2 * (s⁻¹ * M.delta ^ 2) + eps ^ 8 + (Dsc m z).toReal) := by
  obtain ⟨_, _, _, C, hC, hC4⟩ := hreg
  refine ⟨C, hC, ?_⟩
  intro M s eps hs0 hsSmall hdelta heps1 g Fsc Psc Rsc Dsc Zsc goodEvt hPS m z hZ hD
  obtain ⟨h64, hs12, hb0, hb1, htau⟩ :=
    aux_in_deterministic_good_scale_transfer_params M s hs0 hsSmall hdelta
  set eps' : ℝ := max eps (s⁻¹ * M.delta ^ 2) with heps'
  have hev := aux_in_deterministic_good_scale_transfer_event M s eps g _ _ _ _ _ _
    hPS m z hZ eps' (le_max_left _ _) (max_le heps1.le hb1)
  have hE := (hC4 M m s ⟨h64, hs12⟩ htau eps' ⟨le_max_right _ _, max_le heps1.le hb1⟩
    m z g).1
  simp only [indicatorValue, ite_eq_left hev] at hE
  have hacc := aux_in_deterministic_good_scale_transfer_accumulatedError_le M s eps g
    _ _ _ _ _ _ hPS m z hD
  have heps0 : 0 < eps := hPS.2.2.1
  have heps8 : eps' ^ 8 ≤ eps ^ 8 + s⁻¹ * M.delta ^ 2 := by
    have hpow : (s⁻¹ * M.delta ^ 2) ^ 8 ≤ s⁻¹ * M.delta ^ 2 :=
      pow_le_of_le_one hb0 hb1 (by norm_num)
    rcases le_total eps (s⁻¹ * M.delta ^ 2) with h | h
    · rw [heps', max_eq_right h]
      have : 0 ≤ eps ^ 8 := by positivity
      linarith
    · rw [heps', max_eq_left h]
      linarith
  refine hE.trans ((mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le).trans ?_)
  apply mul_le_mul_of_nonneg_left _ hC.le
  linarith

/-- The final numerical bookkeeping of the price. -/
lemma aux_in_deterministic_good_scale_transfer_numeric (d : ℕ) (C s delta eps Dt E : ℝ)
    (hC : 0 < C) (hs0 : 0 < s) (hDt : 0 ≤ Dt) (hE0 : 0 ≤ E)
    (hEb : E ≤ C * (2 * (s⁻¹ * delta ^ 2) + eps ^ 8 + Dt)) :
    let e : ℝ := min (Real.log 12 / 4) ((d : ℝ) * Dt) * Real.exp (Real.log 12 / 4)
    Real.sqrt (2 + 6 * e ^ 2) * E + Real.sqrt (6 * e ^ 2) ≤
      (16 * C * s⁻¹ + 8 * C + 9 * (d : ℝ) + 1) * (delta ^ 2 + eps ^ 8 + Dt) := by
  intro e
  have hmin0 : 0 ≤ min (Real.log 12 / 4) ((d : ℝ) * Dt) :=
    le_min (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 12); positivity)
      (mul_nonneg (Nat.cast_nonneg d) hDt)
  have hexp3 : Real.exp (Real.log 12 / 4) ≤ 3 := by
    have h1 := Real.exp_le_exp.mpr aux_in_deterministic_good_scale_transfer_log12_div4_le_one
    have h2 := Real.exp_one_lt_d9
    linarith
  have hexp0 : 0 ≤ Real.exp (Real.log 12 / 4) := (Real.exp_pos _).le
  have he0 : 0 ≤ e := mul_nonneg hmin0 hexp0
  have he3 : e ≤ 3 := by
    have h1 : min (Real.log 12 / 4) ((d : ℝ) * Dt) ≤ 1 :=
      (min_le_left _ _).trans aux_in_deterministic_good_scale_transfer_log12_div4_le_one
    calc e ≤ 1 * 3 := mul_le_mul h1 hexp3 hexp0 zero_le_one
      _ = 3 := one_mul 3
  have heD : e ≤ 3 * ((d : ℝ) * Dt) := by
    calc e ≤ ((d : ℝ) * Dt) * 3 := mul_le_mul (min_le_right _ _) hexp3 hexp0
          (mul_nonneg (Nat.cast_nonneg d) hDt)
      _ = 3 * ((d : ℝ) * Dt) := mul_comm _ _
  have hsq1 : Real.sqrt (2 + 6 * e ^ 2) ≤ 8 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hsq2 : Real.sqrt (6 * e ^ 2) ≤ 3 * e := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsinv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs0.le
  have he8 : 0 ≤ eps ^ 8 := by positivity
  have hdel : 0 ≤ delta ^ 2 := by positivity
  have hstep1 : Real.sqrt (2 + 6 * e ^ 2) * E + Real.sqrt (6 * e ^ 2) ≤
      8 * (C * (2 * (s⁻¹ * delta ^ 2) + eps ^ 8 + Dt)) + 3 * (3 * ((d : ℝ) * Dt)) := by
    have h1 : Real.sqrt (2 + 6 * e ^ 2) * E ≤ 8 * E := mul_le_mul_of_nonneg_right hsq1 hE0
    have h2 : 8 * E ≤ 8 * (C * (2 * (s⁻¹ * delta ^ 2) + eps ^ 8 + Dt)) := by linarith
    have h3 : 3 * e ≤ 3 * (3 * ((d : ℝ) * Dt)) := by linarith
    linarith
  have hdiff : 0 ≤ (8 * C + 9 * (d : ℝ) + 1) * delta ^ 2 +
      (16 * C * s⁻¹ + 9 * (d : ℝ) + 1) * eps ^ 8 + (16 * C * s⁻¹ + 1) * Dt := by
    have := hC.le
    positivity
  have hexpand : (16 * C * s⁻¹ + 8 * C + 9 * (d : ℝ) + 1) * (delta ^ 2 + eps ^ 8 + Dt) -
      (8 * (C * (2 * (s⁻¹ * delta ^ 2) + eps ^ 8 + Dt)) + 3 * (3 * ((d : ℝ) * Dt))) =
      (8 * C + 9 * (d : ℝ) + 1) * delta ^ 2 +
        (16 * C * s⁻¹ + 9 * (d : ℝ) + 1) * eps ^ 8 + (16 * C * s⁻¹ + 1) * Dt := by ring
  linarith

/-- The pointwise child estimate at one sample, before the a.e. wrapper. -/
theorem aux_in_deterministic_good_scale_transfer_child_pointwise
    {d : ℕ} [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (C : ℝ) (hC : 0 < C)
    (hgmc : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ),
      0 < s → s ≤ (1 / 32 : ℝ) → M.delta ≤ Real.sqrt s / 8 → eps < 1 →
      ∀ (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
        (goodEvt : ℕ → Vec d → Prop),
        _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt →
      ∀ (m : ℕ) (z : Vec d), Zsc m z < 1 → Dsc m z ≠ ⊤ →
        section6HomogenizationError M s m m g z ≤
          C * (2 * (s⁻¹ * M.delta ^ 2) + eps ^ 8 + (Dsc m z).toReal))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ))
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (hdelta : M.delta ≤ Real.sqrt s / 8) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (w : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ (-l))
    (hZ : Zsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) < 1)
    (hD : Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤) :
    let m : ℕ := ((N : ℤ) - l).toNat
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun ell v beta =>
        if 0 ≤ ell then
          ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
        else
          -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
    let a0 : ℝ := kappa m / kappa N * Real.exp (H omega w + retained l w omega)
    I.err w ((3 : ℝ) ^ (-l)) hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr)
        w ((3 : ℝ) ^ (-l)) a0 s 2 ≤
      (16 * C * s⁻¹ + 8 * C + 9 * (d : ℝ) + 1) *
        (M.delta ^ 2 + eps ^ 8 + (Dsc m (((3 : ℝ) ^ N) • w)).toReal) := by
  intro m kappa retained a0
  have hpt := aux_in_deterministic_good_scale_transfer_pointwise_of_scores I M H omega N l hl
    eta hEta hIR s eps hs Fsc Psc Rsc Dsc Zsc goodEvt hPS w hr hZ hD
  refine hpt.trans ?_
  exact aux_in_deterministic_good_scale_transfer_numeric d C s M.delta eps _ _ hC hs.1
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (hgmc M s eps hs.1 hsSmall hdelta heps.2 eta Fsc Psc Rsc Dsc Zsc goodEvt hPS m _ hZ hD)



theorem aux_in_deterministic_good_scale_transfer_child
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (hreg : _root_.SubdiffusiveProcess.Paper.product_threshold_regularities d 12)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ)) :
    ∃ Cg delta0 : ℝ, 0 < Cg ∧ 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (eps : ℝ), eps ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)) →
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)) →
      ∀ (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ),
        (∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d) (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
          Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega ≠ ⊤ →
          Z N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega < 1 →
          I.err w ((3 : ℝ) ^ (-j)) (by positivity)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
              w ((3 : ℝ) ^ (-j)) (sN N j w omega) s 2 ≤
            Cg * (M.delta ^ 2 + eps ^ 8 +
              (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega).toReal) := by
  obtain ⟨C, hC, hgmc⟩ := aux_in_deterministic_good_scale_transfer_gmc_bound hreg
  have hs0 : 0 < s := hs.1
  have hsqrt : 0 < Real.sqrt s / 8 := by
    have := Real.sqrt_pos.mpr hs0
    positivity
  have hCg : 0 < 16 * C * s⁻¹ + 8 * C + 9 * (d : ℝ) + 1 := by
    have := inv_pos.mpr hs0
    positivity
  refine ⟨16 * C * s⁻¹ + 8 * C + 9 * (d : ℝ) + 1, Real.sqrt s / 8, hCg, hsqrt, ?_⟩
  intro M H hMH hdelta eps heps eta F Praw Rraw Draw Z rawGood hEta hPrim sN hsN
  filter_upwards [hEta, hPrim, hMH.2] with omega hEω hPω hIRω
  intro N j w hjN hDraw hZ
  have hsN' := hsN N j w omega
  rw [ite_eq_left hjN] at hsN'
  rw [hsN']
  exact aux_in_deterministic_good_scale_transfer_child_pointwise I C hC hgmc M H omega N j hjN
    (eta N omega) (hEω N) hIRω s eps hs hsSmall hdelta heps _ _ _ _ _ _ (hPω N) w
    (by positivity) hZ hDraw


/-- **Guard/index glue**: on one sample, the child's pointwise bound and the
parent's `hFiniteScoreGuard` give exactly the `hPointwise` premise of the proved
budget child `in_deterministic_budget_transfer`, for any `Cbound ≥ Cg`. -/
theorem aux_in_deterministic_good_scale_transfer_hPointwise
    {d : ℕ} [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (Enl Shift : Type) (rootLevel : Enl × Shift → ℤ)
    (observationCentre : (Enl × Shift) → ∀ (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → SpatialCoordinates d)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
    (s eps Cg Cbound : ℝ) (hCg : Cg ≤ Cbound) (cbuf hk0 : ℕ)
    (hchild : ∀ (N : ℕ) (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
      Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega ≠ ⊤ →
      Z N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (sN N j w omega) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega).toReal))
    (hguard : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
      rootLevel U + (D : ℤ) ≤ (N : ℤ) →
      ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ)) (rootLevel U + (D : ℤ)),
        Draw N ((N : ℤ) - j).toNat
          (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
    (N : ℕ) (U : Enl × Shift) (D : ℕ) (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
    (hN : rootLevel U + (D : ℤ) ≤ (N : ℤ)) :
    ∀ (j : ℤ),
        rootLevel U + (hk0 : ℤ) ≤ j →
        j ≤ rootLevel U + (D : ℤ) →
        0 ≤ (N : ℤ) - j →
        Z N ((N : ℤ) - j).toNat
            (((3 : ℝ) ^ N) • observationCentre U D code) omega < 1 →
        I.err (observationCentre U D code) ((3 : ℝ) ^ (-j)) (by positivity)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (observationCentre U D code) (by positivity))
          (observationCentre U D code) ((3 : ℝ) ^ (-j))
          (sN N j (observationCentre U D code) omega) s 2 ≤
        Cbound * (M.delta ^ 2 + eps ^ 8 +
          (Draw N ((N : ℤ) - j).toNat
            (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal) := by
  intro j hlo hhi hNj hZ
  have hmem : j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ)) (rootLevel U + (D : ℤ)) :=
    Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  have hb := hchild N j (observationCentre U D code) (by omega)
    (hguard N U D code hN j hmem) hZ
  have hnn : 0 ≤ M.delta ^ 2 + eps ^ 8 +
      (Draw N ((N : ℤ) - j).toNat
        (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal := by
    have : 0 ≤ eps ^ 8 := by positivity
    have : 0 ≤ M.delta ^ 2 := by positivity
    have : 0 ≤ (Draw N ((N : ℤ) - j).toNat
        (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal := ENNReal.toReal_nonneg
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_right hCg hnn)


/-- The exact statement of the equal-scale threshold-12 bound
(`aux_in_deterministic_equal_scale_b12_error`, proved in the equal-scale development from the closed `obl_ramp_site_inputs`). -/
def aux_in_deterministic_good_scale_transfer_B12 (d : ℕ) [NeZero d] : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
    ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
    _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 →
    ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
    ∀ (m : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
      omega ∈ _root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some m) m z epsilon s →
      section6HomogenizationError M s m m omega z ≤
        C * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
          accumulatedError M (some m) m z s omega)

/-- The equal-scale statement is implied by conjunct 4 of the threshold-12
carrier at `L = m` (so it is strictly weaker than `hreg`). -/
theorem aux_in_deterministic_good_scale_transfer_B12_of_regularities {d : ℕ} [NeZero d]
    (hreg : _root_.SubdiffusiveProcess.Paper.product_threshold_regularities d 12) :
    aux_in_deterministic_good_scale_transfer_B12 d := by
  obtain ⟨_, _, _, C, hC, hC4⟩ := hreg
  refine ⟨C, hC, fun M s hs htau eps heps m z omega hev => ?_⟩
  have h := (hC4 M m s hs htau eps heps m z omega).1
  simp only [indicatorValue, ite_eq_left hev] at h
  exact h.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)

/-- GMC side from the equal-scale statement alone. -/
theorem aux_in_deterministic_good_scale_transfer_gmc_bound_of_B12 {d : ℕ} [NeZero d]
    (hB12 : aux_in_deterministic_good_scale_transfer_B12 d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ),
      0 < s → s ≤ (1 / 32 : ℝ) → M.delta ≤ Real.sqrt s / 8 → eps < 1 →
      ∀ (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
        (goodEvt : ℕ → Vec d → Prop),
        _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt →
      ∀ (m : ℕ) (z : Vec d), Zsc m z < 1 → Dsc m z ≠ ⊤ →
        section6HomogenizationError M s m m g z ≤
          C * (2 * (s⁻¹ * M.delta ^ 2) + eps ^ 8 + (Dsc m z).toReal) := by
  obtain ⟨C, hC, hB⟩ := hB12
  refine ⟨C, hC, ?_⟩
  intro M s eps hs0 hsSmall hdelta heps1 g Fsc Psc Rsc Dsc Zsc goodEvt hPS m z hZ hD
  obtain ⟨h64, hs12, hb0, hb1, htau⟩ :=
    aux_in_deterministic_good_scale_transfer_params M s hs0 hsSmall hdelta
  set eps' : ℝ := max eps (s⁻¹ * M.delta ^ 2) with heps'
  have hev := aux_in_deterministic_good_scale_transfer_event M s eps g _ _ _ _ _ _
    hPS m z hZ eps' (le_max_left _ _) (max_le heps1.le hb1)
  have hE := hB M s ⟨h64, hs12⟩ htau eps' ⟨le_max_right _ _, max_le heps1.le hb1⟩ m z g hev
  have hacc := aux_in_deterministic_good_scale_transfer_accumulatedError_le M s eps g
    _ _ _ _ _ _ hPS m z hD
  have heps0 : 0 < eps := hPS.2.2.1
  have heps8 : eps' ^ 8 ≤ eps ^ 8 + s⁻¹ * M.delta ^ 2 := by
    have hpow : (s⁻¹ * M.delta ^ 2) ^ 8 ≤ s⁻¹ * M.delta ^ 2 :=
      pow_le_of_le_one hb0 hb1 (by norm_num)
    rcases le_total eps (s⁻¹ * M.delta ^ 2) with h | h
    · rw [heps', max_eq_right h]
      have : 0 ≤ eps ^ 8 := by positivity
      linarith
    · rw [heps', max_eq_left h]
      linarith
  refine hE.trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  linarith

/-- **The proposed fine child with the equal-scale input only.**  Identical
conclusion to `…_child`; the external input is the equal-scale statement
`…_B12 d` instead of the full threshold-12 carrier. -/
theorem aux_in_deterministic_good_scale_transfer_child_of_B12
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (hB12 : aux_in_deterministic_good_scale_transfer_B12 d)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ)) :
    ∃ Cg delta0 : ℝ, 0 < Cg ∧ 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (eps : ℝ), eps ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)) →
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)) →
      ∀ (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ),
        (∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d) (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
          Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega ≠ ⊤ →
          Z N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega < 1 →
          I.err w ((3 : ℝ) ^ (-j)) (by positivity)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
              w ((3 : ℝ) ^ (-j)) (sN N j w omega) s 2 ≤
            Cg * (M.delta ^ 2 + eps ^ 8 +
              (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega).toReal) := by
  obtain ⟨C, hC, hgmc⟩ := aux_in_deterministic_good_scale_transfer_gmc_bound_of_B12 hB12
  have hs0 : 0 < s := hs.1
  have hsqrt : 0 < Real.sqrt s / 8 := by
    have := Real.sqrt_pos.mpr hs0
    positivity
  have hCg : 0 < 16 * C * s⁻¹ + 8 * C + 9 * (d : ℝ) + 1 := by
    have := inv_pos.mpr hs0
    positivity
  refine ⟨16 * C * s⁻¹ + 8 * C + 9 * (d : ℝ) + 1, Real.sqrt s / 8, hCg, hsqrt, ?_⟩
  intro M H hMH hdelta eps heps eta F Praw Rraw Draw Z rawGood hEta hPrim sN hsN
  filter_upwards [hEta, hPrim, hMH.2] with omega hEω hPω hIRω
  intro N j w hjN hDraw hZ
  have hsN' := hsN N j w omega
  rw [ite_eq_left hjN] at hsN'
  rw [hsN']
  exact aux_in_deterministic_good_scale_transfer_child_pointwise I C hC hgmc M H omega N j hjN
    (eta N omega) (hEω N) hIRω s eps hs hsSmall hdelta heps _ _ _ _ _ _ (hPω N) w
    (by positivity) hZ hDraw


/-- Actual physical-coefficient good-scale sensitivity bound for either sign of j. -/
theorem in_deterministic_good_scale_transfer
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ)) :
    ∃ Cg delta0 : ℝ, 0 < Cg ∧ 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (eps : ℝ), eps ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)) →
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)) →
      ∀ (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ),
        (∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d) (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
          Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega ≠ ⊤ →
          Z N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega < 1 →
          I.err w ((3 : ℝ) ^ (-j)) (by positivity)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
              w ((3 : ℝ) ^ (-j)) (sN N j w omega) s 2 ≤
            Cg * (M.delta ^ 2 + eps ^ 8 +
              (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega).toReal) := by
  exact aux_in_deterministic_good_scale_transfer_child_of_B12 d I
    (_root_.SubdiffusiveProcess.Paper.in_deterministic_equal_scale_b12 d) s hs hsSmall

end SubdiffusiveProcess.Paper
