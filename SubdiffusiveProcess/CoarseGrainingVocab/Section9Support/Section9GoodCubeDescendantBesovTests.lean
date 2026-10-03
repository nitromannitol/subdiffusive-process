module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHeadlineCellError
public import SubdiffusiveProcess.Section9.BesovRestriction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeBesovNormalization
@[expose] public section

/-!
# Deterministic descendant tests for good cubes

A single parent negative Besov test of `aCutoff M n - 1` controls the
cube average and the normalized `(1/8, 4d)` test on a descendant at
bounded depth. The cutoff remains `n`, including after translating the
sample. The explicit parent threshold is `1 / (32 * 3^(J/8))`.
-/

set_option autoImplicit false
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
private theorem goodCube_smoothness_factor_le_two (p P : ℝ) (hp : 8 ≤ p) (hP : 8*p ≤ P) :
    (ENNReal.ofReal (1/8:ℝ))^p⁻¹ * (ENNReal.ofReal (1/16:ℝ))^(-P⁻¹) ≤ 2 := by
  have hp0 : 0 < p := by linarith
  have hP4 : (4 : ℝ) ≤ P := by linarith
  have hfirst : (ENNReal.ofReal (1 / 8 : ℝ)) ^ p⁻¹ ≤ 1 :=
    ENNReal.rpow_le_one
      (by simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (show (1 / 8 : ℝ) ≤ 1 by norm_num))
      (inv_nonneg.mpr hp0.le)
  have hinv : (ENNReal.ofReal (1 / 16 : ℝ))⁻¹ = 16 := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 16)]
    norm_num
  have hpinv : P⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hP4
  have hsixteen : (16 : ℝ≥0∞) ^ (1 / 4 : ℝ) = 2 := by
    convert ENNReal.pow_rpow_inv_natCast (n := 4) (by decide) (2 : ℝ≥0∞) using 1; norm_num
  have hsecond : (ENNReal.ofReal (1 / 16 : ℝ)) ^ (-P⁻¹) ≤ 2 := by
    rw [ENNReal.rpow_neg, ← ENNReal.inv_rpow, hinv]
    exact (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hpinv).trans_eq hsixteen
  calc _ ≤ (1 : ℝ≥0∞) * 2 := mul_le_mul' hfirst hsecond
    _ = 2 := one_mul _

private theorem goodCube_geometric_factor_le_two (p P : ℝ) (hp : 8 ≤ p) (hP : 8*p ≤ P) :
    ((1 - ((3 : ℝ≥0∞)^(-(1/16:ℝ)))^(p*P/(P-p)))⁻¹)^((P-p)/(p*P)) ≤ 2 := by
  have hp0 : 0 < p := by linarith
  have hP0 : 0 < P := by linarith
  have hsub0 : 0 < P - p := by linarith
  have hprod0 : 0 < p * P := mul_pos hp0 hP0
  have ht : (8 : ℝ) ≤ p * P / (P - p) := by
    apply (le_div_iff₀ hsub0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hP0.le]
  have hr0 : 0 ≤ (P - p) / (p * P) := div_nonneg hsub0.le hprod0.le
  have hrhalf : (P - p) / (p * P) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hprod0).mpr
    nlinarith [mul_nonneg (show 0 ≤ p - 2 by linarith) hP0.le]
  have hhalf : (3 : ℝ≥0∞) ^ (-(1 / 2 : ℝ)) ≤ (3 / 4 : ℝ≥0∞) := by
    apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
    rw [← ENNReal.rpow_mul]
    norm_num only [neg_div, neg_mul_neg, div_mul_cancel₀, ENNReal.rpow_neg_one,
      ENNReal.rpow_two]
    apply (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mp
    norm_num
  have hratio : ((3 : ℝ≥0∞) ^ (-(1 / 16 : ℝ))) ^ (p * P / (P - p)) ≤
      (3 / 4 : ℝ≥0∞) := by
    rw [← ENNReal.rpow_mul]
    exact (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
      (show -(1 / 16 : ℝ) * (p * P / (P - p)) ≤ -(1 / 2 : ℝ) by linarith)).trans hhalf
  have hbase : (1 - ((3 : ℝ≥0∞) ^ (-(1 / 16 : ℝ))) ^ (p * P / (P - p)))⁻¹ ≤ 4 := by
    calc _ ≤ (1 - (3 / 4 : ℝ≥0∞))⁻¹ := ENNReal.inv_le_inv' (tsub_le_tsub_left hratio 1)
      _ = 4 := by
        have hq : (1 - (3 / 4 : ℝ≥0∞)) = ENNReal.ofReal (1 / 4 : ℝ) := by
          rw [show (1 / 4 : ℝ) = 1 - 3 / 4 by norm_num,
            ENNReal.ofReal_sub _ (by norm_num), ENNReal.ofReal_one,
            ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
          norm_num
        rw [hq, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        norm_num
  have hfour : (4 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 2 := by
    convert ENNReal.pow_rpow_inv_natCast (n := 2) (by decide) (2 : ℝ≥0∞) using 1; norm_num
  exact ((ENNReal.rpow_le_rpow hbase hr0).trans
    (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hrhalf)).trans_eq hfour

/-- Uniform prefactor in the restriction from smoothness `1/16` and exponent `P`
to smoothness `1/8` and exponent `p`. -/
theorem goodCube_descendant_besov_prefactor_le (p P : ℝ)
    (hp : 8 ≤ p) (hP : 8 * p ≤ P) :
    (ENNReal.ofReal (1 / 8 : ℝ)) ^ p⁻¹ *
      (ENNReal.ofReal (1 / 16 : ℝ)) ^ (-P⁻¹) *
      ((1 - ((3 : ℝ≥0∞) ^ (-(1 / 16 : ℝ))) ^
        (p * P / (P - p)))⁻¹) ^ ((P - p) / (p * P)) ≤ 4 := by
  exact (mul_le_mul' (goodCube_smoothness_factor_le_two p P hp hP)
    (goodCube_geometric_factor_le_two p P hp hP)).trans_eq (by norm_num)


/-- A fixed depth bound pays the scale loss in the descendant restriction. -/
theorem goodCube_descendant_besov_budget {d J a : ℕ} {P : ℝ}
    (hd : 2 ≤ d) (hP : 32*(d:ℝ) ≤ P) (ha : a ≤ J) :
    (3 : ℝ≥0∞)^(((1/16:ℝ)+(d:ℝ)/P)*(a:ℝ)) *
      ENNReal.ofReal ((32*(3:ℝ)^((J:ℝ)/8))⁻¹) ≤ ENNReal.ofReal (1/32:ℝ) := by
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hPpos : 0 < P := by linarith
  have hexp : ((1/16:ℝ)+(d:ℝ)/P)*(a:ℝ) ≤ (J:ℝ)/8 := by
    have h1 : (1/16:ℝ)+(d:ℝ)/P ≤ 3/32 := by
      have h2 : (d:ℝ)/P ≤ 1/32 := by
        rw [div_le_iff₀ hPpos]
        linarith
      linarith
    calc ((1/16:ℝ)+(d:ℝ)/P)*(a:ℝ) ≤ (3/32:ℝ)*(a:ℝ) :=
          mul_le_mul_of_nonneg_right h1 (by exact_mod_cast Nat.zero_le a)
      _ ≤ (3/32:ℝ)*(J:ℝ) := by
          exact mul_le_mul_of_nonneg_left (show (a:Real) ≤ (J:Real) by exact_mod_cast ha) (by norm_num)
      _ ≤ (J:ℝ)/8 := by linarith [Nat.cast_nonneg (α := ℝ) J]
  have hxpos : 0 < (3:ℝ)^((J:ℝ)/8) := Real.rpow_pos_of_pos (by norm_num) _
  have heq : ENNReal.ofReal ((3:ℝ)^((J:ℝ)/8)) = (3:ENNReal)^((J:ℝ)/8) := by
    simpa only [ENNReal.ofReal_ofNat] using (ENNReal.ofReal_rpow_of_pos (p := (J:ℝ)/8) (by norm_num : (0:ℝ) < 3)).symm
  calc
    (3:ENNReal)^(((1/16:ℝ)+(d:ℝ)/P)*(a:ℝ)) * ENNReal.ofReal ((32*(3:ℝ)^((J:ℝ)/8))⁻¹)
        ≤ (3:ENNReal)^((J:ℝ)/8) * ENNReal.ofReal ((32*(3:ℝ)^((J:ℝ)/8))⁻¹) :=
          mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp) le_rfl
    _ = ENNReal.ofReal ((3:ℝ)^((J:ℝ)/8) * (32*(3:ℝ)^((J:ℝ)/8))⁻¹) := by
          rw [←heq, ←ENNReal.ofReal_mul hxpos.le]
    _ = ENNReal.ofReal (1/32:ℝ) := by
          congr 1
          field_simp [hxpos.ne']


private lemma cubeAverage_sub_const {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) (c : ℝ)
    (hf : ExactCircIntegrable Q (fun x => f x - c)) :
    cubeAverage Q (fun x => f x - c) = cubeAverage Q f - c := by
  have hint : Integrable (fun x => f x - c) (normalizedCubeMeasure Q) :=
    hf.block 0 Q (by simp)
  have hintf : Integrable f (normalizedCubeMeasure Q) := by
    refine (hint.add (integrable_const c)).congr ?_
    filter_upwards with x
    simp only [Pi.add_apply]
    ring
  have hreal : (normalizedCubeMeasure Q).real Set.univ = 1 := by
    rw [Measure.real_def, normalizedCubeMeasure_apply_univ]
    norm_num
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure,
    integral_sub hintf (integrable_const c), integral_const, hreal]
  simp

/-- A small raw `(1/8,4d)` norm supplies both the mass bound and the test after
dividing by the actual cube average. -/
theorem goodCube_local_mass_and_besov_tests_of_raw
    {d : ℕ} (hd : 2 ≤ d) (m : ℤ) (a : Vec d → ℝ) (ha : Continuous a)
    (hf : ExactCircIntegrable (originCube d m) (fun x => a x - 1))
    (hb : ExactCircIntegrable (originCube d m)
      (fun x => a x / cubeAverage (originCube d m) a - 1))
    (hraw : ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d m) (1 / 8) (4 * (d : ℝ))
        (fun x => a x - 1) hf ≤ ENNReal.ofReal (1 / 8 : ℝ)) :
    ((1 / 2 : ℝ) ≤ cubeAverage (originCube d m) a ∧
      cubeAverage (originCube d m) a ≤ 3 / 2) ∧
    ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d m) (1 / 8) (4 * (d : ℝ))
        (fun x => a x / cubeAverage (originCube d m) a - 1) hb ≤ 1 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := Nat.cast_le.2 hd
  have hp : 0 < (4 * (d : ℝ)) := by linarith
  have hmem : originCube d m ∈ descendantsAtDepth (originCube d m) 0 := by simp
  have hmom := weightedSobolev_cell_moment hd m (fun x => a x - 1) hf (1 / 8) (by norm_num) hraw
    0 (originCube d m) hmem
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.rpow_zero, mul_one] at hmom
  have h256 : (2 : ℝ) ^ (8 : ℝ) = 256 := by norm_num
  have h8le : (8 : ℝ) ≤ (2 : ℝ) ^ (4 * (d : ℝ)) := by
    have h1 : (2 : ℝ) ^ (8 : ℝ) ≤ (2 : ℝ) ^ (4 * (d : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
    linarith
  have hpownonneg : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ (4 * (d : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsplit : (1 / 4 : ℝ) ^ (4 * (d : ℝ)) = (1 / 8 : ℝ) ^ (4 * (d : ℝ)) * (2 : ℝ) ^ (4 * (d : ℝ)) := by
    rw [show (1 / 4 : ℝ) = (1 / 8 : ℝ) * 2 from by norm_num,
      Real.mul_rpow (by norm_num) (by norm_num)]
  have hkey : |cubeAverage (originCube d m) (fun x => a x - 1)| ^ (4 * (d : ℝ))
      ≤ (1 / 4 : ℝ) ^ (4 * (d : ℝ)) := by
    have s1 : (8 : ℝ) * ((1 / 8 : ℝ) *
        |cubeAverage (originCube d m) (fun x => a x - 1)| ^ (4 * (d : ℝ)))
        ≤ (8 : ℝ) * (1 / 8 : ℝ) ^ (4 * (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hmom (by norm_num)
    have s2 : |cubeAverage (originCube d m) (fun x => a x - 1)| ^ (4 * (d : ℝ))
        ≤ (8 : ℝ) * (1 / 8 : ℝ) ^ (4 * (d : ℝ)) := by
      have eq8 : ∀ x : ℝ, (8 : ℝ) * ((1 / 8 : ℝ) * x) = x := fun x => by ring
      rwa [eq8] at s1
    calc |cubeAverage (originCube d m) (fun x => a x - 1)| ^ (4 * (d : ℝ))
        ≤ (8 : ℝ) * (1 / 8 : ℝ) ^ (4 * (d : ℝ)) := s2
      _ ≤ (2 : ℝ) ^ (4 * (d : ℝ)) * (1 / 8 : ℝ) ^ (4 * (d : ℝ)) :=
        mul_le_mul_of_nonneg_right h8le hpownonneg
      _ = (1 / 8 : ℝ) ^ (4 * (d : ℝ)) * (2 : ℝ) ^ (4 * (d : ℝ)) :=
        mul_comm ((2 : ℝ) ^ (4 * (d : ℝ))) ((1 / 8 : ℝ) ^ (4 * (d : ℝ)))
      _ = (1 / 4 : ℝ) ^ (4 * (d : ℝ)) := hsplit.symm
  have habs4 : |cubeAverage (originCube d m) (fun x => a x - 1)| ≤ (1 / 4 : ℝ) :=
    (Real.rpow_le_rpow_iff (abs_nonneg _) (by norm_num) hp).mp hkey
  have havgsub : cubeAverage (originCube d m) (fun x => a x - 1)
      = cubeAverage (originCube d m) a - 1 :=
    cubeAverage_sub_const (originCube d m) a 1 hf
  rw [havgsub] at habs4
  have hpair := abs_le.mp habs4
  refine ⟨⟨by linarith [hpair.1], by linarith [hpair.2]⟩, ?_⟩
  have h8 := goodCube_normalized_negativeBesov_le hd (originCube d m) a ha
    (by linarith [hpair.1]) hf hb
  calc ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d m) (1 / 8) (4 * (d : ℝ))
        (fun x => a x / cubeAverage (originCube d m) a - 1) hb
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
          ((8 : ℝ≥0∞) * paperNegativeBesovCircDiagonal (originCube d m) (1 / 8) (4 * (d : ℝ))
            (fun x => a x - 1) hf) := mul_le_mul' le_rfl h8
    _ = (8 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
          paperNegativeBesovCircDiagonal (originCube d m) (1 / 8) (4 * (d : ℝ))
            (fun x => a x - 1) hf) := by ring
    _ ≤ (8 : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) := mul_le_mul' le_rfl hraw
    _ = 1 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 8), ENNReal.ofReal_one,
          ENNReal.ofReal_ofNat, one_div]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)


private theorem goodCube_descendant_raw_besov_le
    {d : ℕ} (hd : 2 ≤ d) (n m J : ℕ) (hJ : n - m ≤ J)
    (P : ℝ) (hP : 32 * (d : ℝ) ≤ P)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable (originCube d (n : ℤ)) f)
    (hQ : originCube d (m : ℤ) ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - m))
    (hfac : (ENNReal.ofReal (1 / 8 : ℝ)) ^ (4 * (d : ℝ))⁻¹ *
      (ENNReal.ofReal (1 / 16 : ℝ)) ^ (-P⁻¹) *
      ((1 - ((3 : ℝ≥0∞) ^ (-(1 / 16 : ℝ))) ^
        ((4 * (d : ℝ)) * P / (P - 4 * (d : ℝ))))⁻¹) ^
        ((P - 4 * (d : ℝ)) / ((4 * (d : ℝ)) * P)) ≤ 4)
    (hZ : ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 16 : ℝ) * (n : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d (n : ℤ)) (1 / 16) P f hf ≤
        ENNReal.ofReal ((32 * (3 : ℝ) ^ ((J : ℝ) / 8))⁻¹)) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d (m : ℤ)) (1 / 8) (4 * (d : ℝ)) f
        (SubdiffusiveProcess.Section9.ExactCircIntegrable.descendant hf hQ) ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpc : 1 ≤ 4 * (d : ℝ) := by linarith
  have hpcP : 4 * (d : ℝ) < P := by linarith
  have hres := SubdiffusiveProcess.Section9.negativeBesovCircFinite_descendant_le_source hf hQ
    (s := (1 / 8 : ℝ)) (σ := (1 / 16 : ℝ)) (p := 4 * (d : ℝ)) (P := P)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hpc hpcP
  have hthree (t : ℝ) : ENNReal.ofReal ((3 : ℝ)^t) = (3 : ℝ≥0∞)^t := by
    simpa only [ENNReal.ofReal_ofNat] using
      (ENNReal.ofReal_rpow_of_pos (p := t) (by norm_num : (0 : ℝ) < 3)).symm
  have hnorm (Q : TriadicCube d) (s p : ℝ) (hs : 0 < s) (hs1 : s < 1)
      (hp : 1 ≤ p) (g : Vec d → ℝ) (hg : ExactCircIntegrable Q g) :
      negativeBesovCircFinite (SubdiffusiveProcess.Section9.exactCircDiagonalParameters s p hs hs1 hp)
        Q g hg = paperNegativeBesovCircDiagonal Q s p g hg := rfl
  rw [hnorm, hnorm] at hres
  norm_num only [show (1 / 8 : ℝ) - 1 / 16 = 1 / 16 by norm_num] at hres
  have hc : -(((originCube d (m : ℤ)).scale : ℝ) * (1 / 8)) =
      -(1 / 8 : ℝ) * (m : ℝ) := by
    change -(((m : ℤ) : ℝ) * (1 / 8)) = _
    rw [Int.cast_natCast]
    ring
  have hn : -(((originCube d (n : ℤ)).scale : ℝ) * (1 / 16)) =
      -(1 / 16 : ℝ) * (n : ℝ) := by
    change -(((n : ℤ) : ℝ) * (1 / 16)) = _
    rw [Int.cast_natCast]
    ring
  rw [hc, hn, ← hthree (-(1 / 8 : ℝ) * (m : ℝ)),
    ← hthree (-(1 / 16 : ℝ) * (n : ℝ))] at hres
  calc
    _ ≤ _ := hres
    _ ≤ (4 : ℝ≥0∞) * (3 : ℝ≥0∞)^(((1 / 16 : ℝ) + (d : ℝ) / P) * ((n - m : ℕ) : ℝ)) *
      (ENNReal.ofReal ((3 : ℝ)^(-(1 / 16 : ℝ) * (n : ℝ))) *
        paperNegativeBesovCircDiagonal (originCube d (n : ℤ)) (1 / 16) P f hf) :=
      mul_le_mul' (mul_le_mul' hfac le_rfl) le_rfl
    _ ≤ 4 * ((3 : ℝ≥0∞)^(((1 / 16 : ℝ) + (d : ℝ) / P) * ((n - m : ℕ) : ℝ)) *
      ENNReal.ofReal ((32 * (3 : ℝ)^((J : ℝ) / 8))⁻¹)) := by
      simpa only [mul_assoc] using mul_le_mul' (le_refl ((4 : ℝ≥0∞) *
        (3 : ℝ≥0∞)^(((1 / 16 : ℝ) + (d : ℝ) / P) * ((n - m : ℕ) : ℝ)))) hZ
    _ ≤ 4 * ENNReal.ofReal (1 / 32 : ℝ) :=
      mul_le_mul' le_rfl (goodCube_descendant_besov_budget hd hP hJ)
    _ = ENNReal.ofReal (1 / 8 : ℝ) := by
      rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num


/-- The single parent test for the actual translated cutoff coefficient gives
the good-cube mass and normalized Besov tests at every smaller nonnegative
scale whose depth is at most `J`. No inverse-average moment is assumed. -/
theorem goodCube_cutoff_descendant_mass_and_besov_tests
    {d : ℕ} (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n m J : ℕ) (hmn : m ≤ n) (hJ : n - m ≤ J)
    (P : ℝ) (hP : 32 * (d : ℝ) ≤ P)
    (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hf : ExactCircIntegrable (originCube d (n : ℤ))
      (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega) x - 1))
    (hZ : ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 16 : ℝ) * (n : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d (n : ℤ)) (1 / 16) P
        (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega) x - 1) hf ≤
          ENNReal.ofReal ((32 * (3 : ℝ) ^ ((J : ℝ) / 8))⁻¹)) :
    let Q := originCube d (m : ℤ)
    let a := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega)
    ((1 / 2 : ℝ) ≤ cubeAverage Q a ∧ cubeAverage Q a ≤ 3 / 2) ∧
      ∀ hb : ExactCircIntegrable Q (fun x => a x / cubeAverage Q a - 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
          paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ))
            (fun x => a x / cubeAverage Q a - 1) hb ≤ 1 := by
  have hscale : (originCube d (n : ℤ)).scale = (n : ℤ) := rfl
  have hQ : originCube d (m : ℤ) ∈
      descendantsAtDepth (originCube d (n : ℤ)) (n - m) := by
    have hmem := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.originCube_mem_descendantsAtScale_of_nat_le (d := d) (j := m) (K := n) hmn
    rw [mem_descendantsAtScale_iff (show (m : ℤ) ≤ (originCube d (n : ℤ)).scale by
      change (m : ℤ) ≤ (n : ℤ)
      exact_mod_cast hmn)] at hmem
    rw [hscale] at hmem
    have hdiff : (Int.toNat ((n : ℤ) - (m : ℤ)) : ℕ) = n - m := by omega
    rw [hdiff] at hmem
    exact hmem
  set a : Vec d → ℝ := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega) with ha_def
  have hac : Continuous a :=
    SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M n (translatePotentialSample z omega)
  have hf' : ExactCircIntegrable (originCube d (m : ℤ)) (fun x => a x - 1) :=
    SubdiffusiveProcess.Section9.ExactCircIntegrable.descendant hf hQ
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd4 : (8 : ℝ) ≤ 4 * (d : ℝ) := by linarith
  have hfac : (ENNReal.ofReal (1 / 8 : ℝ)) ^ (4 * (d : ℝ))⁻¹ *
      (ENNReal.ofReal (1 / 16 : ℝ)) ^ (-P⁻¹) *
      ((1 - ((3 : ℝ≥0∞) ^ (-(1 / 16 : ℝ))) ^
        ((4 * (d : ℝ)) * P / (P - 4 * (d : ℝ))))⁻¹) ^
        ((P - 4 * (d : ℝ)) / ((4 * (d : ℝ)) * P)) ≤ 4 :=
    goodCube_descendant_besov_prefactor_le (4 * (d : ℝ)) P hd4 (by linarith)
  have hraw : ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d (m : ℤ)) (1 / 8) (4 * (d : ℝ))
        (fun x => a x - 1) hf' ≤ ENNReal.ofReal (1 / 8 : ℝ) :=
    goodCube_descendant_raw_besov_le hd n m J hJ P hP (fun x => a x - 1) hf hQ hfac hZ
  have hnorm' : ExactCircIntegrable (originCube d (m : ℤ))
      (fun x => a x / cubeAverage (originCube d (m : ℤ)) a - 1) :=
    exactCircIntegrable_of_continuous _
      ((hac.div_const (cubeAverage (originCube d (m : ℤ)) a)).sub continuous_const)
  have hpair :=
    goodCube_local_mass_and_besov_tests_of_raw hd (m : ℤ) a
      hac hf' hnorm' hraw
  refine ⟨?_, ?_⟩
  · exact hpair.1
  · intro hb
    exact hpair.2

/-- A parent raw test with arbitrary nonnegative threshold gives a quantitative
raw child test. The cutoff can stay fixed when `f` is a translated cutoff field. -/
theorem goodCube_descendant_raw_besov_le_of_parent
    {d : ℕ} (hd : 2 ≤ d) (n m J : ℕ) (hmn : m ≤ n) (hJ : n - m ≤ J)
    (P : ℝ) (hP : 32 * (d : ℝ) ≤ P) (B : ℝ) (hB : 0 ≤ B)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable (originCube d (n : ℤ)) f)
    (hZ : ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 16 : ℝ) * (n : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d (n : ℤ)) (1 / 16) P f hf ≤
        ENNReal.ofReal B) :
    ∀ hfm : ExactCircIntegrable (originCube d (m : ℤ)) f,
      ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
        paperNegativeBesovCircDiagonal (originCube d (m : ℤ)) (1 / 8) (4 * (d : ℝ)) f hfm ≤
          ENNReal.ofReal (4 * (3 : ℝ) ^ ((J : ℝ) / 8) * B) := by
  intro hfm
  have hQ : originCube d (m : ℤ) ∈
      descendantsAtDepth (originCube d (n : ℤ)) (n - m) := by
    have hmem := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.originCube_mem_descendantsAtScale_of_nat_le
      (d := d) (j := m) (K := n) hmn
    rw [mem_descendantsAtScale_iff (show (m : ℤ) ≤ (originCube d (n : ℤ)).scale by
      change (m : ℤ) ≤ (n : ℤ)
      exact_mod_cast hmn)] at hmem
    change originCube d (m : ℤ) ∈
      descendantsAtDepth (originCube d (n : ℤ)) (Int.toNat ((n : ℤ) - (m : ℤ))) at hmem
    have hdiff : Int.toNat ((n : ℤ) - (m : ℤ)) = n - m := by omega
    rwa [hdiff] at hmem
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpc : 1 ≤ 4 * (d : ℝ) := by linarith
  have hpcP : 4 * (d : ℝ) < P := by linarith
  have hfac := goodCube_descendant_besov_prefactor_le (4 * (d : ℝ)) P
    (by linarith : 8 ≤ 4 * (d : ℝ)) (by linarith : 8 * (4 * (d : ℝ)) ≤ P)
  have hPpos : 0 < P := by linarith
  have hexp : ((1 / 16 : ℝ) + (d : ℝ) / P) * ((n - m : ℕ) : ℝ) ≤ (J : ℝ) / 8 := by
    have hsmall : (1 / 16 : ℝ) + (d : ℝ) / P ≤ 3 / 32 := by
      have hratio : (d : ℝ) / P ≤ 1 / 32 := by
        rw [div_le_iff₀ hPpos]
        linarith
      linarith
    calc
      _ ≤ (3 / 32 : ℝ) * ((n - m : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)
      _ ≤ (3 / 32 : ℝ) * (J : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hJ) (by norm_num)
      _ ≤ (J : ℝ) / 8 := by linarith [Nat.cast_nonneg (α := ℝ) J]
  have hres := SubdiffusiveProcess.Section9.negativeBesovCircFinite_descendant_le_source hf hQ
    (s := (1 / 8 : ℝ)) (σ := (1 / 16 : ℝ)) (p := 4 * (d : ℝ)) (P := P)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hpc hpcP
  have hthree (t : ℝ) : ENNReal.ofReal ((3 : ℝ)^t) = (3 : ℝ≥0∞)^t := by
    simpa only [ENNReal.ofReal_ofNat] using
      (ENNReal.ofReal_rpow_of_pos (p := t) (by norm_num : (0 : ℝ) < 3)).symm
  have hnorm (Q : TriadicCube d) (s p : ℝ) (hs : 0 < s) (hs1 : s < 1)
      (hp : 1 ≤ p) (g : Vec d → ℝ) (hg : ExactCircIntegrable Q g) :
      negativeBesovCircFinite (SubdiffusiveProcess.Section9.exactCircDiagonalParameters s p hs hs1 hp)
        Q g hg = paperNegativeBesovCircDiagonal Q s p g hg := rfl
  rw [hnorm, hnorm] at hres
  norm_num only [show (1 / 8 : ℝ) - 1 / 16 = 1 / 16 by norm_num] at hres
  have hc : -(((originCube d (m : ℤ)).scale : ℝ) * (1 / 8)) =
      -(1 / 8 : ℝ) * (m : ℝ) := by
    change -(((m : ℤ) : ℝ) * (1 / 8)) = _
    rw [Int.cast_natCast]
    ring
  have hn : -(((originCube d (n : ℤ)).scale : ℝ) * (1 / 16)) =
      -(1 / 16 : ℝ) * (n : ℝ) := by
    change -(((n : ℤ) : ℝ) * (1 / 16)) = _
    rw [Int.cast_natCast]
    ring
  rw [hc, hn, ← hthree (-(1 / 8 : ℝ) * (m : ℝ)),
    ← hthree (-(1 / 16 : ℝ) * (n : ℝ))] at hres
  have hdepth : (3 : ℝ≥0∞)^(((1 / 16 : ℝ) + (d : ℝ) / P) * ((n - m : ℕ) : ℝ)) ≤
      ENNReal.ofReal ((3 : ℝ)^((J : ℝ) / 8)) := by
    rw [hthree]
    exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  calc
    _ ≤ _ := hres
    _ ≤ (4 : ℝ≥0∞) * (3 : ℝ≥0∞)^(((1 / 16 : ℝ) + (d : ℝ) / P) * ((n - m : ℕ) : ℝ)) *
      (ENNReal.ofReal ((3 : ℝ)^(-(1 / 16 : ℝ) * (n : ℝ))) *
        paperNegativeBesovCircDiagonal (originCube d (n : ℤ)) (1 / 16) P f hf) :=
      mul_le_mul' (mul_le_mul' hfac le_rfl) le_rfl
    _ ≤ 4 * ENNReal.ofReal ((3 : ℝ)^((J : ℝ) / 8)) * ENNReal.ofReal B :=
      mul_le_mul' (mul_le_mul' le_rfl hdepth) hZ
    _ = ENNReal.ofReal (4 * (3 : ℝ)^((J : ℝ) / 8) * B) := by
      rw [← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ← ENNReal.ofReal_mul' hB]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
