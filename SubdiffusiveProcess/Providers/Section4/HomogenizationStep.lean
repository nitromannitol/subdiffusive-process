module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SquareResponseRosenthal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.BlockUpdate
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.CombineAlgebra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ExpectedResponseReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.FiniteRecurrence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseRosenthal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SecondMomentBudgets
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SphereQuarterNet
public import SubdiffusiveProcess.Section3.CrudeJBound
public import SubdiffusiveProcess.Section4.CombineUnderS
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section

/-!
# Homogenization-step provider spine

This file assembles the finite weighted-defect corridor used in the proof of
`p.homogenization.step`.  The consumer-side shift follows: recurrence
lags which cross the first admissible scale are paid by the sharp tail of the
geometric `1/3` kernel, and the already-proved unshifted recurrence engine is
then applied at shift zero.

The two proposition carriers below copy the only proof-layer statements which
the final provider is allowed to assume.  In particular this module does not
import either draft Section 4 anchor.
-/

namespace SubdiffusiveProcess.Providers.Section4

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
open scoped BigOperators ENNReal

noncomputable section


/-- Exact conclusion type of the conditional `p.combine.under.S`. -/
def CombineUnderSConclusion (d : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (xi delta1 : ℝ),
      16 * (d : ℝ) ≤ xi →
      C * xi * M.delta ^ 2 ≤ delta1 → delta1 ≤ c →
      inductionHypothesis M L xi delta1 →
      ∀ m : ℕ, 0 < m → L ≤ m →
        C * Real.rpow 3 (-((m - L : ℕ) : ℝ)) ≤ (1 / 4 : ℝ) →
        ∀ p q : Homogenization.Vec d,
          q = ahom M L • p → vecNormSq q ≤ ahom M L →
          expectedJ M L m p q ≤
            C * delta1 *
                (delta1 + Real.rpow 3 (-((m - L : ℕ) : ℝ))) +
              C * ∑ n ∈ Finset.Icc L m,
                Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
                  expectedJDifference M L n m p q

/-- The exact fixed-direction estimate printed.  This is
kept as a named boundary while the committed induction-hypothesis
subadditivity route is checked independently of the recurrence algebra. -/
def InitialFixedCutoffResponseConclusion (d : ℕ) : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m0 : ℕ) (xi delta1 : ℝ),
    16 * (d : ℝ) ≤ xi → inductionHypothesis M m0 xi delta1 →
    ∀ (L n : ℕ), L ≤ m0 → L ≤ n →
      ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
        (let p := (Real.sqrt (ahom M L))⁻¹ • e
         let q := Real.sqrt (ahom M L) • e
         Integrable
              (fun omega =>
                |cutoffResponseOnCube M L p q
                    (originCube d (n : ℤ)) omega| ^ xi)
              M.P.toMeasure ∧
           (∫ omega,
                |cutoffResponseOnCube M L p q
                    (originCube d (n : ℤ)) omega| ^ xi
                ∂M.P.toMeasure) ^ xi⁻¹ ≤ delta1)

/-- The fixed-cutoff Step-1 moment follows from response subadditivity onto
the scale-`L` partition and the induction hypothesis.  The fixed normalized
direction is bounded pointwise by the scalar probe supremum; the large-cube
partition theorem then supplies its full `L^xi` moment without a cardinality
loss. -/
theorem initial_fixed_cutoff_response_conclusion {d : ℕ} :
    InitialFixedCutoffResponseConclusion d := by
  intro M m0 xi delta1 _hxi hS L n hLm0 hLn e he
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  let p : Homogenization.Vec d := (Real.sqrt (ahom M L))⁻¹ • e
  let q : Homogenization.Vec d := Real.sqrt (ahom M L) • e
  let Q : Homogenization.TriadicCube d := originCube d (n : ℤ)
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    cutoffResponseOnCube M L p q Q
  let D : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ :=
    normalizedDefect M L (Ch02.cubeDomain Q)
  have hxi0 : 0 < xi := zero_lt_one.trans_le hS.1
  have hYmeas : Measurable Y :=
    measurable_cutoffResponseOnCube M L p q Q
  have hY0 : ∀ omega, 0 ≤ Y omega := by
    intro omega
    exact Ch02.responseJ_nonneg _ _ _ _
  have hpoint : ∀ omega, ENNReal.ofReal |Y omega| ≤ D omega := by
    intro omega
    rw [abs_of_nonneg (hY0 omega)]
    exact le_iSup (fun u :
        {u : Homogenization.Vec d // vecNormSq u = 1} =>
      ENNReal.ofReal
        (J (Ch02.cubeDomain Q)
          (aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)).toCoeffOn
          ((Real.sqrt (ahom M L))⁻¹ • (u : Homogenization.Vec d))
          (Real.sqrt (ahom M L) • (u : Homogenization.Vec d)))) ⟨e, he⟩
  have hDnorm : paperENNRealLpNorm M.P.toMeasure xi D ≤
      ENNReal.ofReal delta1 := by
    simpa [D, Q] using normalizedDefect_largeCube_lpnorm_le_induction
      M hS.1 hS hLn hLm0 Q rfl
  have hYnorm : paperENNRealLpNorm M.P.toMeasure xi
      (fun omega => ENNReal.ofReal |Y omega|) ≤ ENNReal.ofReal delta1 :=
    (paperENNRealLpNorm_mono_ae M.P.toMeasure hxi0.le
      (Filter.Eventually.of_forall hpoint)).trans hDnorm
  have hYelp : eLpNorm Y (ENNReal.ofReal xi) M.P.toMeasure ≤
      ENNReal.ofReal delta1 := by
    have heq :=
      paperENNRealLpNorm_eq_eLpNorm_toReal M.P.toMeasure hxi0
        (X := fun omega => ENNReal.ofReal |Y omega|)
        (fun _ => ENNReal.ofReal_ne_top)
    rw [show (fun omega => (ENNReal.ofReal |Y omega|).toReal) = Y by
      funext omega
      rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (hY0 omega)]] at heq
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hYmeas.aestronglyMeasurable] at heq
    rw [← heq]
    exact hYnorm
  have hYmem : MemLp Y (ENNReal.ofReal xi) M.P.toMeasure :=
    hYelp.trans_lt ENNReal.ofReal_lt_top
  have hYint : Integrable (fun omega => |Y omega| ^ xi) M.P.toMeasure := by
    have h := (integrable_norm_rpow_iff hYmeas.aestronglyMeasurable
      (ENNReal.ofReal_pos.mpr hxi0).ne' ENNReal.ofReal_ne_top).2 hYmem
    simpa [ENNReal.toReal_ofReal hxi0.le, Real.norm_eq_abs] using h
  refine ⟨by simpa [Y, p, q, Q] using hYint, ?_⟩
  have heq := paperENNRealLpNorm_ofReal_abs_eq_integral_abs_rpow_root
    M.P.toMeasure hxi0 hYmeas hYint
  have hrootENN : ENNReal.ofReal
      ((∫ omega, |Y omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹) ≤
        ENNReal.ofReal delta1 := by
    rw [← heq]
    exact hYnorm
  have hroot := ENNReal.toReal_mono ENNReal.ofReal_ne_top hrootENN
  have hI0 : 0 ≤ ∫ omega, |Y omega| ^ xi ∂M.P.toMeasure :=
    integral_nonneg (fun omega => Real.rpow_nonneg (abs_nonneg _) _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI0 _),
    ENNReal.toReal_ofReal hS.2.1.le] at hroot
  simpa [Y, p, q, Q] using hroot

/-- The proved crude-J export supplies the literal `j = 0` initialization on
the cutoff-scale cube.  It does not, and is not used as if it did, control a
fixed cutoff on every larger observation cube. -/
theorem exists_crude_sameScale_initialization {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (xi : ℝ),
        1 ≤ xi →
        paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M L L) ≤
          ENNReal.ofReal
            (C * xi * (L + 1 : ℝ) * M.delta ^ 2 *
              Real.exp (C * xi * (L + 1 : ℝ) * M.delta ^ 2)) := by
  rcases _root_.SubdiffusiveProcess.Section3.crude_j_bound (d := d) with ⟨C, hC, hcrude⟩
  refine ⟨C, hC, ?_⟩
  intro M L xi hxi
  simpa [normalizedDefectAt, normalizedDefect, paperScalarProbeMax,
    aCutoffFamily, aCutoffTriadicData] using!
      hcrude M L xi (Ch02.cubeDomain (originCube d (L : ℤ))) hxi
        (by intro x hx; exact hx)

private theorem halfWeightedSum_eq (j : ℕ) :
    ∑ k ∈ Finset.Icc 1 j, (k : ℝ) * (1 / 2 : ℝ) ^ k =
      2 - ((j : ℝ) + 2) * (1 / 2 : ℝ) ^ j := by
  induction j with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega)]
      norm_num
  | succ j ih =>
      have hins : Finset.Icc 1 (j + 1) =
          insert (j + 1) (Finset.Icc 1 j) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : j + 1 ∉ Finset.Icc 1 j := by simp
      rw [hins, Finset.sum_insert hnot, ih]
      push_cast
      simp only [pow_succ]
      ring

private theorem halfWeightedSum_le_two (j : ℕ) :
    ∑ k ∈ Finset.Icc 1 j, (k : ℝ) * (1 / 2 : ℝ) ^ k ≤ 2 := by
  rw [halfWeightedSum_eq j]
  have hnonneg : 0 ≤ ((j : ℝ) + 2) * (1 / 2 : ℝ) ^ j := by positivity
  linarith

private theorem one_sub_pow_le_mul_one_sub {rho : ℝ}
    (hrho0 : 0 ≤ rho) (k : ℕ) :
    1 - rho ^ k ≤ (1 - rho) * (k : ℝ) := by
  have h := one_add_mul_le_pow (by linarith : -2 ≤ rho - 1) k
  rw [show (1 : ℝ) + (rho - 1) = rho by ring] at h
  linarith

/-- A directly checkable sufficient condition for the proved weighted-defect
kernel. -/
theorem weightedDefectKernel_of_two_mul_le {C r rho : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hrrho : 2 * r ≤ rho) (hsmall : 2 * C * (1 - rho) ≤ (1 / 2 : ℝ)) :
    WeightedDefectKernel C r rho := by
  intro j
  have hhalf : r ≤ rho * (1 / 2 : ℝ) := by linarith
  have hterm : ∀ k ∈ Finset.Icc 1 j,
      r ^ k * (rho ^ (j - k) - rho ^ j) ≤
        rho ^ j * (1 - rho) * ((k : ℝ) * (1 / 2 : ℝ) ^ k) := by
    intro k hk
    have hkj : k ≤ j := (Finset.mem_Icc.mp hk).2
    have hmix : r ^ k * rho ^ (j - k) ≤
        rho ^ j * (1 / 2 : ℝ) ^ k := by
      calc
        r ^ k * rho ^ (j - k) ≤
            (rho * (1 / 2 : ℝ)) ^ k * rho ^ (j - k) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hhalf k)
            (pow_nonneg hrho0 (j - k))
        _ = rho ^ (j - k) * rho ^ k * (1 / 2 : ℝ) ^ k := by
          rw [mul_pow]
          ring
        _ = rho ^ j * (1 / 2 : ℝ) ^ k := by
          rw [pow_sub_mul_pow rho hkj]
    have hdiff : rho ^ (j - k) - rho ^ j =
        rho ^ (j - k) * (1 - rho ^ k) := by
      rw [mul_sub, mul_one, pow_sub_mul_pow rho hkj]
    have hle : rho ^ k ≤ 1 := pow_le_one₀ hrho0 hrho1
    rw [hdiff, ← mul_assoc]
    calc
      r ^ k * rho ^ (j - k) * (1 - rho ^ k) ≤
          rho ^ j * (1 / 2 : ℝ) ^ k * ((1 - rho) * (k : ℝ)) :=
        mul_le_mul hmix (one_sub_pow_le_mul_one_sub hrho0 k)
          (by linarith) (by positivity)
      _ = _ := by ring
  have hfactor : 0 ≤ rho ^ j * (1 - rho) :=
    mul_nonneg (pow_nonneg hrho0 j) (by linarith)
  have hsum : (∑ k ∈ Finset.Icc 1 j,
      r ^ k * (rho ^ (j - k) - rho ^ j)) ≤
      2 * (1 - rho) * rho ^ j := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 j,
          rho ^ j * (1 - rho) * ((k : ℝ) * (1 / 2 : ℝ) ^ k) :=
        Finset.sum_le_sum hterm
      _ = rho ^ j * (1 - rho) *
          ∑ k ∈ Finset.Icc 1 j, (k : ℝ) * (1 / 2 : ℝ) ^ k := by
        rw [Finset.mul_sum]
      _ ≤ rho ^ j * (1 - rho) * 2 :=
        mul_le_mul_of_nonneg_left (halfWeightedSum_le_two j) hfactor
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_left hsum hC
  have hrate := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hrho0 j)
  linarith

/-- The explicit contraction rate used by this provider. -/
noncomputable def homogenizationDecayRate (C : ℝ) : ℝ :=
  1 - (4 * (C + 1))⁻¹

theorem homogenizationDecayRate_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < homogenizationDecayRate C := by
  have hden : (0 : ℝ) < 4 * (C + 1) := by linarith
  have hle : (4 * (C + 1))⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  simp only [homogenizationDecayRate]
  linarith

theorem homogenizationDecayRate_lt_one {C : ℝ} (hC : 0 ≤ C) :
    homogenizationDecayRate C < 1 := by
  have hden : (0 : ℝ) < 4 * (C + 1) := by linarith
  have hgap : 0 < (4 * (C + 1))⁻¹ := inv_pos.mpr hden
  simp only [homogenizationDecayRate]
  linarith

theorem homogenizationDecayRate_kernel {C : ℝ} (hC : 0 ≤ C) :
    WeightedDefectKernel C (1 / 3) (homogenizationDecayRate C) := by
  have hden : (0 : ℝ) < 4 * (C + 1) := by linarith
  have hgapLe : (4 * (C + 1))⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hsmall : 2 * C * (4 * (C + 1))⁻¹ ≤ (1 / 2 : ℝ) := by
    calc
      2 * C * (4 * (C + 1))⁻¹ ≤
          2 * (C + 1) * (4 * (C + 1))⁻¹ := by
        gcongr
        linarith
      _ = 1 / 2 := by
        field_simp [show C + 1 ≠ 0 by linarith]
        ring
  apply weightedDefectKernel_of_two_mul_le hC (by norm_num)
  · simp only [homogenizationDecayRate]
    linarith
  · simp only [homogenizationDecayRate]
    have hgap0 : 0 < (4 * (C + 1))⁻¹ := inv_pos.mpr hden
    linarith
  · simp only [homogenizationDecayRate]
    linarith
  · simpa only [homogenizationDecayRate, sub_sub_cancel] using hsmall

/-- Sharp tail of the geometric `1/3` lag kernel beyond a consumer shift. -/
theorem geom_third_Icc_shift_le (j N : ℕ) :
    ∑ k ∈ Finset.Icc (j + 1) N, (1 / 3 : ℝ) ^ k ≤
      (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ j := by
  have hIcc : Finset.Icc (j + 1) N = Finset.Ico (j + 1) (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc]
  calc
    ∑ k ∈ Finset.Ico (j + 1) (N + 1), (1 / 3 : ℝ) ^ k ≤
        (1 / 3 : ℝ) ^ (j + 1) / (1 - 1 / 3) :=
      geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ = _ := by rw [pow_succ]; ring

/-- Reindex the physical corridor `[L,L+j]` by the backwards lag
`k = L+j-n`.  The current-scale endpoint has lag zero and vanishes, leaving
exactly the `Icc 1 j` convolution used by `WeightedDefectKernel`. -/
theorem sum_Icc_scale_eq_sum_Icc_lag (F : ℕ → ℝ) (r : ℝ)
    (L j : ℕ) :
    ∑ n ∈ Finset.Icc L (L + j),
        r ^ (L + j - n) * (F (n - L) - F j) =
      ∑ k ∈ Finset.Icc 1 j,
        r ^ k * (F (j - k) - F j) := by
  have hLI : L ≤ L + j := Nat.le_add_right L j
  rw [← Finset.Ico_insert_right hLI, Finset.sum_insert]
  · simp only [Nat.add_sub_cancel_left, sub_self, mul_zero, zero_add]
    refine Finset.sum_bij (fun n _ => L + j - n) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      simp only [Finset.mem_Icc]
      omega
    · intro n₁ hn₁ n₂ hn₂ heq
      simp only [Finset.mem_Ico] at hn₁ hn₂
      change L + j - n₁ = L + j - n₂ at heq
      have h₁ : L + j - n₁ + n₁ = L + j := Nat.sub_add_cancel hn₁.2.le
      have h₂ : L + j - n₂ + n₂ = L + j := Nat.sub_add_cancel hn₂.2.le
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      refine ⟨L + (j - k), ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        omega
      · omega
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      have hidx : j - (L + j - n) = n - L := by omega
      rw [hidx]
  · simp only [Finset.mem_Ico]
    omega

theorem three_rpow_neg_natCast_eq_third_pow (j : ℕ) :
    Real.rpow 3 (-((j : ℕ) : ℝ)) = (1 / 3 : ℝ) ^ j := by
  change (3 : ℝ) ^ (-((j : ℕ) : ℝ)) = _
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [one_div]
  exact (inv_pow (3 : ℝ) j).symm

/-- Restrict a finite induction hypothesis to an earlier terminal scale. -/
theorem inductionHypothesis_mono_terminal {d : ℕ}
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {m0 L : ℕ} {xi delta1 : ℝ}
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0) :
    inductionHypothesis M L xi delta1 := by
  apply inductionHypothesis_of_scale_bounds M L hS.1 hS.2.1 hS.2.2.1
  intro n hn
  exact inductionHypothesis_scale_bound hS (hn.trans hLm0)

/-- The physical expected-response difference sum is exactly the backwards
lag convolution.  This is the `Nat` corridor reindex in manuscript. -/
theorem expectedJDifference_scaleSum_eq_lagSum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L j : ℕ)
    (p q : Homogenization.Vec d) :
    ∑ n ∈ Finset.Icc L (L + j),
        Real.rpow 3 (-(((L + j) - n : ℕ) : ℝ)) *
          expectedJDifference M L n (L + j) p q =
      ∑ k ∈ Finset.Icc 1 j, (1 / 3 : ℝ) ^ k *
        (expectedJ M L (L + (j - k)) p q -
          expectedJ M L (L + j) p q) := by
  rw [show (∑ n ∈ Finset.Icc L (L + j),
      Real.rpow 3 (-(((L + j) - n : ℕ) : ℝ)) *
        expectedJDifference M L n (L + j) p q) =
      ∑ n ∈ Finset.Icc L (L + j),
        (1 / 3 : ℝ) ^ (L + j - n) *
          (expectedJ M L n p q - expectedJ M L (L + j) p q) by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [three_rpow_neg_natCast_eq_third_pow,
      expectedJDifference_eq_sub_unconditional]]
  let F : ℕ → ℝ := fun t => expectedJ M L (L + t) p q
  have hsum := sum_Icc_scale_eq_sum_Icc_lag F (1 / 3) L j
  calc
    ∑ n ∈ Finset.Icc L (L + j),
        (1 / 3 : ℝ) ^ (L + j - n) *
          (expectedJ M L n p q - expectedJ M L (L + j) p q) =
        ∑ n ∈ Finset.Icc L (L + j),
          (1 / 3 : ℝ) ^ (L + j - n) * (F (n - L) - F j) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      simp only [Finset.mem_Icc] at hn
      simp only [F, Nat.add_sub_of_le hn.1]
    _ = ∑ k ∈ Finset.Icc 1 j,
          (1 / 3 : ℝ) ^ k * (F (j - k) - F j) := hsum
    _ = _ := rfl

/-- A dimensional combine constant has a first scale after which its
`C 3⁻ʲ ≤ 1/4` separation gate holds. -/
theorem exists_combine_gate_shift (C : ℝ) :
    ∃ t0 : ℕ, ∀ t : ℕ, t0 < t →
      C * (1 / 3 : ℝ) ^ t ≤ (1 / 4 : ℝ) := by
  have htend : Filter.Tendsto (fun t : ℕ => C * (1 / 3 : ℝ) ^ t)
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1)).const_mul C
  have hevent : ∀ᶠ t : ℕ in Filter.atTop,
      C * (1 / 3 : ℝ) ^ t < 1 / 4 :=
    (tendsto_order.mp htend).2 (1 / 4) (by norm_num)
  rcases Filter.eventually_atTop.mp hevent with ⟨t0, ht0⟩
  exact ⟨t0, fun t ht => (ht0 t (by omega)).le⟩

private theorem normalized_loads_relation {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (e : Homogenization.Vec d) :
    Real.sqrt (ahom M L) • e =
      ahom M L • ((Real.sqrt (ahom M L))⁻¹ • e) := by
  have ha : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hs : Real.sqrt (ahom M L) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  rw [smul_smul]
  congr 1
  field_simp
  nlinarith [Real.sq_sqrt ha.le]

private theorem normalized_sqrt_load_normSq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    vecNormSq (Real.sqrt (ahom M L) • e) = ahom M L := by
  have ha : 0 ≤ ahom M L :=
    ((Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)).le
  rw [vecNormSq_smul, he, mul_one, Real.sq_sqrt ha]

private theorem expectedJ_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) :
    0 ≤ expectedJ M L n p q := by
  unfold expectedJ
  apply integral_nonneg
  intro omega
  exact Ch02.responseJ_nonneg _ _ _ _

private theorem expectedJ_le_of_initialMoment {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    {xi delta1 : ℝ} (hxi : 1 ≤ xi)
    (p q : Homogenization.Vec d)
    (hmoment : Integrable
      (fun omega =>
        |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi)
      M.P.toMeasure)
    (hroot :
      (∫ omega,
          |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi
          ∂M.P.toMeasure) ^ xi⁻¹ ≤ delta1) :
    expectedJ M L n p q ≤ delta1 := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  let f := cutoffResponseOnCube M L p q (originCube d (n : ℤ))
  have hlow :=
    IndependentSums.integral_abs_rpow_rpow_inv_le_of_le
      (f := f) (q := (1 : ℝ)) (p := xi) (by norm_num) hxi
      (measurable_cutoffResponseOnCube M L p q _) hmoment
  have hnonneg : ∀ omega, 0 ≤ f omega := by
    intro omega
    exact Ch02.responseJ_nonneg _ _ _ _
  have heq : ∫ omega, f omega ∂M.P.toMeasure =
      ∫ omega, |f omega| ∂M.P.toMeasure := by
    apply integral_congr_ae
    filter_upwards with omega
    exact (abs_of_nonneg (hnonneg omega)).symm
  have hlow' : ∫ omega, |f omega| ∂M.P.toMeasure ≤
      (∫ omega, |f omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ := by
    simpa using hlow
  change ∫ omega, f omega ∂M.P.toMeasure ≤ delta1
  rw [heq]
  exact hlow'.trans hroot

/-- The fixed-cell moment budget also controls its centered version, with the
standard factor two. -/
private theorem centeredCutoffResponse_root_le_two_mul {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    {xi delta1 : ℝ} (hxi : 1 ≤ xi)
    (p q : Homogenization.Vec d)
    (hmoment : Integrable
      (fun omega =>
        |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi)
      M.P.toMeasure)
    (hroot :
      (∫ omega,
          |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi
          ∂M.P.toMeasure) ^ xi⁻¹ ≤ delta1) :
    Integrable
        (fun omega =>
          |centeredCutoffResponseOnCube M L n p q
            (originCube d (n : ℤ)) omega| ^ xi) M.P.toMeasure ∧
      (∫ omega,
          |centeredCutoffResponseOnCube M L n p q
            (originCube d (n : ℤ)) omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ ≤
        2 * delta1 := by
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    cutoffResponseOnCube M L p q (originCube d (n : ℤ))
  let c : ℝ := ∫ omega, f omega ∂M.P.toMeasure
  have hxi0 : 0 < xi := zero_lt_one.trans_le hxi
  have hfmeas : Measurable f := measurable_cutoffResponseOnCube M L p q _
  have hc0 : 0 ≤ c := by
    dsimp [c, f]
    exact expectedJ_nonneg M L n p q
  have hc : c ≤ delta1 := by
    dsimp [c, f]
    exact expectedJ_le_of_initialMoment M L n hxi p q hmoment hroot
  have hcenterInt :=
    IndependentSums.integrable_abs_sub_integral_rpow_of_integrable_abs_rpow
      hxi hfmeas hmoment
  refine ⟨by simpa [centeredCutoffResponseOnCube, f, c] using hcenterInt, ?_⟩
  let X : Bool → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun b =>
    if b then fun _ => -c else f
  have hXmeas : ∀ b ∈ (Finset.univ : Finset Bool), Measurable (X b) := by
    intro b _
    cases b <;> simp [X, hfmeas]
  have hXint : ∀ b ∈ (Finset.univ : Finset Bool),
      Integrable (fun omega => |X b omega| ^ xi) M.P.toMeasure := by
    intro b _
    cases b
    · simpa [X] using hmoment
    · simp [X]
  have hsum := IndependentSums.integral_abs_finsetSum_rpow_rpow_inv_le_sum
    (μ := M.P.toMeasure) hxi hXmeas hXint
  have hconst :
      (∫ _omega, |-c| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ = c := by
    rw [integral_const, probReal_univ, one_smul, abs_neg, abs_of_nonneg hc0,
      ← Real.rpow_mul hc0, mul_inv_cancel₀ hxi0.ne', Real.rpow_one]
  have hconst' : (|c| ^ xi) ^ xi⁻¹ = c := by
    rw [abs_of_nonneg hc0, ← Real.rpow_mul hc0,
      mul_inv_cancel₀ hxi0.ne', Real.rpow_one]
  have hsumfun :
      (fun omega => ∑ b ∈ (Finset.univ : Finset Bool), X b omega) =
        fun omega => f omega - c := by
    funext omega
    simp [X]
    ring
  simp_rw [congrFun hsumfun] at hsum
  have hsum' :
      (∫ omega, |f omega - c| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ ≤
        (∫ omega, |f omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ + c := by
    simpa [X, hconst', add_comm] using hsum
  simpa [centeredCutoffResponseOnCube, f, c] using hsum'.trans (by linarith)

private theorem shifted_third_recurrence {F : ℕ → ℝ} {A C delta : ℝ}
    (t0 : ℕ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hFnn : ∀ t, 0 ≤ F t) (hFcr : ∀ t, F t ≤ delta)
    (hFrec : ∀ t, t0 < t →
      F t ≤ A * delta * (delta + (1 / 3 : ℝ) ^ t) +
        C * ∑ k ∈ Finset.Icc 1 t,
          (1 / 3 : ℝ) ^ k * (F (t - k) - F t)) :
    ∀ j, 0 < j →
      F (t0 + j) ≤ (A + C * (1 / 2)) * delta *
          (delta + (1 / 3 : ℝ) ^ j) +
        C * ∑ k ∈ Finset.Icc 1 j,
          (1 / 3 : ℝ) ^ k * (F (t0 + (j - k)) - F (t0 + j)) := by
  intro j hj
  have hraw := hFrec (t0 + j) (by omega)
  have hsplit : Finset.Icc 1 (t0 + j) =
      Finset.Icc 1 j ∪ Finset.Icc (j + 1) (t0 + j) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 j) (Finset.Icc (j + 1) (t0 + j)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  rw [hsplit, Finset.sum_union hdisj] at hraw
  have hinternal :
      ∑ k ∈ Finset.Icc 1 j,
          (1 / 3 : ℝ) ^ k * (F (t0 + j - k) - F (t0 + j)) =
        ∑ k ∈ Finset.Icc 1 j,
          (1 / 3 : ℝ) ^ k * (F (t0 + (j - k)) - F (t0 + j)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : k ≤ j := (Finset.mem_Icc.mp hk).2
    rw [show t0 + j - k = t0 + (j - k) by omega]
  rw [hinternal] at hraw
  have hprefix :
      ∑ k ∈ Finset.Icc (j + 1) (t0 + j),
          (1 / 3 : ℝ) ^ k * (F (t0 + j - k) - F (t0 + j)) ≤
        delta * ((1 / 2 : ℝ) * (1 / 3 : ℝ) ^ j) := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc (j + 1) (t0 + j),
          delta * (1 / 3 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro k _
        have hdiff : F (t0 + j - k) - F (t0 + j) ≤ delta := by
          linarith [hFcr (t0 + j - k), hFnn (t0 + j)]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) k]
      _ = delta * ∑ k ∈ Finset.Icc (j + 1) (t0 + j),
          (1 / 3 : ℝ) ^ k := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (geom_third_Icc_shift_le j (t0 + j)) hdelta
  have hCprefix := mul_le_mul_of_nonneg_left hprefix hC
  have hpow : (1 / 3 : ℝ) ^ (t0 + j) ≤ (1 / 3 : ℝ) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hforce : A * delta * (delta + (1 / 3 : ℝ) ^ (t0 + j)) ≤
      A * delta * (delta + (1 / 3 : ℝ) ^ j) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hdelta)
  have hsquare : 0 ≤ C * (1 / 2) * delta * delta := by positivity
  linarith

/-- Late recurrence plus the uniform crude bound gives geometric decay after
the first admissible scale.  This is the finite-corridor engine actually used
by the homogenization-step provider. -/
theorem weightedDefect_decay_of_late_recurrence {F : ℕ → ℝ}
    {A C delta : ℝ} (t0 : ℕ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hFnn : ∀ t, 0 ≤ F t) (hFcr : ∀ t, F t ≤ delta)
    (hFrec : ∀ t, t0 < t →
      F t ≤ A * delta * (delta + (1 / 3 : ℝ) ^ t) +
        C * ∑ k ∈ Finset.Icc 1 t,
          (1 / 3 : ℝ) ^ k * (F (t - k) - F t)) :
    ∀ j,
      F (t0 + j) ≤
        (2 * (A + C * (1 / 2) + 1)) * delta *
          (delta + homogenizationDecayRate C ^ j) := by
  let A' := A + C * (1 / 2) + 1
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  have hrho : (1 / 3 : ℝ) ≤ homogenizationDecayRate C := by
    have hpos := homogenizationDecayRate_pos hC
    have hgap : (4 * (C + 1))⁻¹ ≤ 1 / 4 := by
      have hden : (0 : ℝ) < 4 * (C + 1) := by linarith
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    simp only [homogenizationDecayRate]
    linarith
  apply weightedDefect_decay_of_kernel hC hdelta (by norm_num) hrho
    (K := 2 * A') (K₀ := 1) (A := A')
  · exact mul_nonneg (by norm_num) hA'
  · rfl
  · dsimp [A']
    nlinarith
  · exact homogenizationDecayRate_kernel hC
  · simpa using hFcr t0
  · intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · norm_num [Finset.Icc_eq_empty]
      have h := hFcr t0
      have hdelta' : delta ≤ A' * delta * (delta + 1) := by
        have hA'one : 1 ≤ A' := by dsimp [A']; nlinarith
        have hdeltaOne : 1 ≤ delta + 1 := by linarith
        calc
          delta = 1 * delta := by ring
          _ ≤ A' * delta :=
            mul_le_mul_of_nonneg_right hA'one hdelta
          _ = (A' * delta) * 1 := by ring
          _ ≤ (A' * delta) * (delta + 1) :=
            mul_le_mul_of_nonneg_left hdeltaOne (mul_nonneg hA' hdelta)
          _ = _ := by ring
      exact h.trans hdelta'
    · exact (shifted_third_recurrence t0 hA hC hdelta hFnn hFcr hFrec j hj).trans
        (by
          have hnonneg : 0 ≤ delta * (delta + (1 / 3 : ℝ) ^ j) := by
            positivity
          dsimp [A']
          nlinarith)

/-- The source choice `n = L + ceil((m-L)/2)`. -/
def homogenizationMidpoint (L m : ℕ) : ℕ :=
  L + (m - L + 1) / 2

theorem homogenizationMidpoint_corridor (L m : ℕ) (hLm : L ≤ m) :
    L ≤ homogenizationMidpoint L m ∧
      homogenizationMidpoint L m ≤ m ∧
      m - L ≤ 2 * (homogenizationMidpoint L m - L) ∧
      m - L ≤ 2 * (m - homogenizationMidpoint L m) + 1 := by
  unfold homogenizationMidpoint
  omega

/-- First of the two concrete midpoint exponential estimates.  The harmless factor `3^(d/4)` pays for integer rounding. -/
theorem three_rpow_midpoint_fluctuation {d L m : ℕ} (hLm : L ≤ m) :
    Real.rpow 3
        (-((d : ℝ) / 2) * ((m - homogenizationMidpoint L m : ℕ) : ℝ)) ≤
      Real.rpow 3 ((d : ℝ) / 4) *
        Real.rpow 3 (-((d : ℝ) / 4) * ((m - L : ℕ) : ℝ)) := by
  have hg := (homogenizationMidpoint_corridor L m hLm).2.2.2
  have hgR : ((m - L : ℕ) : ℝ) ≤
      2 * ((m - homogenizationMidpoint L m : ℕ) : ℝ) + 1 := by
    exact_mod_cast hg
  have hexp :
      -((d : ℝ) / 2) * ((m - homogenizationMidpoint L m : ℕ) : ℝ) ≤
        (d : ℝ) / 4 +
          (-((d : ℝ) / 4) * ((m - L : ℕ) : ℝ)) := by
    nlinarith [show (0 : ℝ) ≤ (d : ℝ) by positivity]
  have heq : Real.rpow 3
      ((d : ℝ) / 4 + (-((d : ℝ) / 4) * ((m - L : ℕ) : ℝ))) =
      Real.rpow 3 ((d : ℝ) / 4) *
        Real.rpow 3 (-((d : ℝ) / 4) * ((m - L : ℕ) : ℝ)) := by
    change (3 : ℝ) ^
        ((d : ℝ) / 4 + (-((d : ℝ) / 4) * ((m - L : ℕ) : ℝ))) =
      (3 : ℝ) ^ ((d : ℝ) / 4) *
        (3 : ℝ) ^ (-((d : ℝ) / 4) * ((m - L : ℕ) : ℝ))
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  rw [← heq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- Second concrete midpoint estimate: the iterated mean has at least half
the total scale gap in its contraction exponent. -/
theorem midpoint_contraction_le_half_gap {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) {L m : ℕ} (hLm : L ≤ m) :
    rho ^ (homogenizationMidpoint L m - L) ≤
      Real.rpow rho (((m - L : ℕ) : ℝ) / 2) := by
  have hg := (homogenizationMidpoint_corridor L m hLm).2.2.1
  have hgCast : ((m - L : ℕ) : ℝ) ≤
      2 * ((homogenizationMidpoint L m - L : ℕ) : ℝ) := by
    exact_mod_cast hg
  have hhalf : ((m - L : ℕ) : ℝ) / 2 ≤
      ((homogenizationMidpoint L m - L : ℕ) : ℝ) := by linarith
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hrho0 hrho1.le hhalf

/-- Dimension-only logarithmic scale separation absorbs an arbitrary fixed
prefactor against any strict geometric decay.  This is the analytic constant
fold used twice at the midpoint, once for the spatial fluctuation and once for
the iterated mean. -/
private theorem logarithmic_rpow_decay_absorption
    {r gamma A eta C xi H : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hgamma : 0 < gamma)
    (hA : 0 ≤ A) (heta : 0 < eta) (hxi : 1 ≤ xi)
    (hC : (2 * A * eta⁻¹ + 1) *
      (-gamma * Real.log r)⁻¹ ≤ C)
    (hgap : C * Real.log (2 + xi) ≤ H) :
    A * xi * Real.rpow r (gamma * H) ≤ eta := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d113_square_logarithmic_rpow_decay_absorption (r := r) (gamma := gamma) (A := A) (eta := eta) (C := C) (xi := xi) (H := H) (hr0 := hr0) (hr1 := hr1) (hgamma := hgamma) (hA := hA) (heta := heta) (hxi := hxi) (hC := hC) (hgap := hgap)

/-- The printed iteration of the combine estimate.  Its constants are fixed
before the model; the conclusion is the geometric expected-response bound
after the first admissible separation. -/
theorem exists_expectedJ_decay_of_combine {d : ℕ}
    (hcombine : CombineUnderSConclusion d)
    (hinitial : InitialFixedCutoffResponseConclusion d) :
    ∃ c C K rho : ℝ, ∃ t0 : ℕ,
      0 < c ∧ 0 < C ∧ 0 < K ∧ 0 < rho ∧ rho < 1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m0 : ℕ)
        (xi delta1 : ℝ),
        16 * (d : ℝ) ≤ xi →
        C * xi * M.delta ^ 2 ≤ delta1 → delta1 ≤ c →
        inductionHypothesis M m0 xi delta1 →
        ∀ (L : ℕ), L ≤ m0 →
          ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
            ∀ j : ℕ,
              expectedJ M L (L + t0 + j)
                  ((Real.sqrt (ahom M L))⁻¹ • e)
                  (Real.sqrt (ahom M L) • e) ≤
                K * delta1 * (delta1 + rho ^ j) := by
  rcases hcombine with ⟨c, C, hc, hC, hcombine⟩
  rcases exists_combine_gate_shift C with ⟨t0, ht0⟩
  let K : ℝ := 2 * (C + C * (1 / 2) + 1)
  let rho := homogenizationDecayRate C
  have hK : 0 < K := by dsimp [K]; nlinarith
  have hrho : 0 < rho := homogenizationDecayRate_pos hC.le
  have hrho1 : rho < 1 := homogenizationDecayRate_lt_one hC.le
  refine ⟨c, C, K, rho, t0, hc, hC, hK, hrho, hrho1, ?_⟩
  intro M m0 xi delta1 hxi hsmall hdelta hS L hLm0 e he j
  let p := (Real.sqrt (ahom M L))⁻¹ • e
  let q := Real.sqrt (ahom M L) • e
  let F : ℕ → ℝ := fun t => expectedJ M L (L + t) p q
  have hSL : inductionHypothesis M L xi delta1 :=
    inductionHypothesis_mono_terminal hS hLm0
  have hcrude : ∀ t, F t ≤ delta1 := by
    intro t
    obtain ⟨hmoment, hroot⟩ := hinitial M m0 xi delta1 hxi hS L (L + t)
      hLm0 (by omega) e he
    exact expectedJ_le_of_initialMoment M L (L + t) hS.1 p q hmoment hroot
  have hnonneg : ∀ t, 0 ≤ F t := fun t => expectedJ_nonneg M L (L + t) p q
  have hrec : ∀ t, t0 < t →
      F t ≤ C * delta1 * (delta1 + (1 / 3 : ℝ) ^ t) +
        C * ∑ k ∈ Finset.Icc 1 t,
          (1 / 3 : ℝ) ^ k * (F (t - k) - F t) := by
    intro t htt0
    have hraw := hcombine M L xi delta1 hxi hsmall hdelta hSL (L + t)
      (by omega) (by omega)
      (by simpa [three_rpow_neg_natCast_eq_third_pow] using ht0 t htt0)
      p q (by
        dsimp only [p, q]
        exact normalized_loads_relation M L e)
      (by
        dsimp only [q]
        rw [normalized_sqrt_load_normSq M L e he])
    rw [show (L + t - L : ℕ) = t by omega,
      three_rpow_neg_natCast_eq_third_pow] at hraw
    rw [expectedJDifference_scaleSum_eq_lagSum M L t p q] at hraw
    simpa only [F, Nat.add_assoc] using hraw
  have hdecay := weightedDefect_decay_of_late_recurrence t0
    (F := F) (A := C) (C := C) (delta := delta1)
    hC.le hC.le hS.2.1.le hnonneg hcrude hrec j
  simpa only [F, K, rho, Nat.add_assoc] using hdecay

/-- The complete fixed-direction estimate before the midpoint constants are
folded.  This is the source display obtained by combining subadditivity,
colored Rosenthal, and the stationary mean. -/
theorem exists_fixedDirection_midpoint_bound {d : ℕ}
    (hinitial : InitialFixedCutoffResponseConclusion d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m0 : ℕ)
        (xi delta1 : ℝ),
        16 * (d : ℝ) ≤ xi →
        inductionHypothesis M m0 xi delta1 →
        ∀ (L m : ℕ), L ≤ m0 → L ≤ m →
          ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
            paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
                ENNReal.ofReal
                  (cutoffResponseOnCube M L
                    ((Real.sqrt (ahom M L))⁻¹ • e)
                    (Real.sqrt (ahom M L) • e)
                    (originCube d (m : ℤ)) omega)) ≤
              ENNReal.ofReal
                (C * xi * delta1 *
                    Real.rpow 3
                      (-((d : ℝ) / 2) *
                        ((m - homogenizationMidpoint L m : ℕ) : ℝ)) +
                  expectedJ M L (homogenizationMidpoint L m)
                    ((Real.sqrt (ahom M L))⁻¹ • e)
                    (Real.sqrt (ahom M L) • e)) := by
  rcases exists_centeredCutoffResponseAverage_dimensional_bound d with
    ⟨C0, hC0, hC0bound⟩
  refine ⟨2 * C0, by positivity, ?_⟩
  intro M m0 xi delta1 hxi hS L m hLm0 hLm e he
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  let n := homogenizationMidpoint L m
  let p := (Real.sqrt (ahom M L))⁻¹ • e
  let q := Real.sqrt (ahom M L) • e
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast M.shellPrefix.dimension
  have hxi2 : 2 ≤ xi := by nlinarith
  have hLn : L ≤ n := (homogenizationMidpoint_corridor L m hLm).1
  have hnm : n ≤ m := (homogenizationMidpoint_corridor L m hLm).2.1
  obtain ⟨hmoment, hroot⟩ :=
    hinitial M m0 xi delta1 hxi hS L n hLm0 hLn e he
  obtain ⟨hcenterInt, hcenterRoot⟩ :=
    centeredCutoffResponse_root_le_two_mul M L n hS.1 p q hmoment hroot
  have hcenter := hC0bound M L n m hLn hnm p q xi (2 * delta1)
    hxi2 (mul_nonneg (by norm_num) hS.2.1.le) hcenterInt hcenterRoot
  have hparent :=
    paperENNRealLpNorm_cutoffResponseOnCube_le_centered_root_add_mean
      M L n m hLn hnm p q (xi := xi)
        (A := (2 * C0) * xi * delta1 *
          Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)))
      hxi2 hcenterInt (hcenter.trans_eq (by ring))
  simpa only [n, p, q, expectedJ, cutoffResponseOnCube] using hparent

/-- The midpoint estimate after the two exponential terms and the quadratic
mean term have been absorbed by the printed logarithmic separation. -/
private theorem exists_fixedDirection_logarithmic_bound {d : ℕ}
    (hcombine : CombineUnderSConclusion d)
    (hinitial : InitialFixedCutoffResponseConclusion d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m0 : ℕ)
        (xi delta1 : ℝ),
        16 * (d : ℝ) ≤ xi →
        C * xi * M.delta ^ 2 ≤ delta1 → delta1 ≤ c →
        inductionHypothesis M m0 xi delta1 →
        ∀ (m L : ℕ), L ≤ m0 →
          (L : ℝ) + C * Real.log (2 + xi) ≤ m →
          ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
            paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
                ENNReal.ofReal
                  (cutoffResponseOnCube M L
                    ((Real.sqrt (ahom M L))⁻¹ • e)
                    (Real.sqrt (ahom M L) • e)
                    (originCube d (m : ℤ)) omega)) ≤
              ENNReal.ofReal
                (((16 *
                    ((sphereQuarterNet d).points.card : ℝ))⁻¹) * delta1) := by
  by_cases hd : d = 0
  · subst d
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro M
    have hdim : 2 ≤ (0 : ℕ) := M.shellPrefix.dimension
    omega
  let : NeZero d := ⟨hd⟩
  rcases exists_expectedJ_decay_of_combine hcombine hinitial with
    ⟨c0, C0, K, rho, t0, hc0, hC0, hK, hrho0, hrho1, hmean⟩
  rcases exists_fixedDirection_midpoint_bound hinitial with
    ⟨Cf, hCf, hfixed⟩
  let Q : ℝ := ((sphereQuarterNet d).points.card : ℝ)
  let eta : ℝ := (64 * Q)⁻¹
  let gammaF : ℝ := (d : ℝ) / 4
  let Af : ℝ := Cf * Real.rpow 3 ((d : ℝ) / 4)
  let Am : ℝ := K * (rho ^ t0)⁻¹
  let Cfsep : ℝ :=
    (2 * Af * eta⁻¹ + 1) *
      (-gammaF * Real.log (1 / 3 : ℝ))⁻¹
  let Cmsep : ℝ :=
    (2 * Am * eta⁻¹ + 1) *
      (-(1 / 2 : ℝ) * Real.log rho)⁻¹
  let C : ℝ :=
    max 1 (max C0 (max Cfsep (max Cmsep (4 * (t0 : ℝ) + 1))))
  let c : ℝ := min c0 (eta * K⁻¹)
  have hQDef : Q = ((sphereQuarterNet d).points.card : ℝ) := rfl
  have hEtaDef : eta = (64 * Q)⁻¹ := rfl
  have hGammaFDef : gammaF = (d : ℝ) / 4 := rfl
  have hAfDef : Af = Cf * Real.rpow 3 ((d : ℝ) / 4) := rfl
  have hAmDef : Am = K * (rho ^ t0)⁻¹ := rfl
  have hCfsepDef : Cfsep = (2 * Af * eta⁻¹ + 1) *
      (-gammaF * Real.log (1 / 3 : ℝ))⁻¹ := rfl
  have hCmsepDef : Cmsep = (2 * Am * eta⁻¹ + 1) *
      (-(1 / 2 : ℝ) * Real.log rho)⁻¹ := rfl
  have hCDef : C = max 1 (max C0 (max Cfsep (max Cmsep (4 * (t0 : ℝ) + 1)))) := rfl
  have hQnat : 0 < (sphereQuarterNet d).points.card :=
    (sphereQuarterNet_points_nonempty (d := d)).card_pos
  have hQ : 0 < Q := by
    rw [hQDef]
    exact_mod_cast hQnat
  have heta : 0 < eta := by rw [hEtaDef]; positivity
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hc0 (mul_pos heta (inv_pos.mpr hK))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc0Bound : c ≤ c0 := min_le_left _ _
  have hcEtaBound : c ≤ eta * K⁻¹ := min_le_right _ _
  have hC0Bound : C0 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCtimeBound : (4 * (t0 : ℝ) + 1) ≤ C :=
    le_trans (le_max_right _ _) <|
      le_trans (le_max_right _ _) <|
        le_trans (le_max_right _ _) (le_max_right _ _)
  clear_value Q eta gammaF Af Am Cfsep Cmsep C c
  refine ⟨c, C, hc, hC, ?_⟩
  intro M m0 xi delta1 hxi hsmall hdelta hS m L hLm0 hgap e he
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast M.shellPrefix.dimension
  have hxi1 : 1 ≤ xi := hS.1
  have hxi0 : 0 < xi := zero_lt_one.trans_le hxi1
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 + xi) := by
    have htwo : (2 : ℝ) ≤ 2 + xi := by linarith
    exact (by nlinarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) htwo)
  have hCL : (L : ℝ) ≤ (m : ℝ) := by
    have hClog : 0 ≤ C * Real.log (2 + xi) :=
      mul_nonneg hC.le (le_trans (by norm_num) hlog)
    linarith
  have hLm : L ≤ m := by exact_mod_cast hCL
  let H : ℝ := ((m - L : ℕ) : ℝ)
  have hH : H = (m : ℝ) - (L : ℝ) := by
    dsimp [H]
    rw [Nat.cast_sub hLm]
  have hgapH : C * Real.log (2 + xi) ≤ H := by
    rw [hH]
    linarith
  have hC0le : C0 ≤ C := hC0Bound
  have hsmall0 : C0 * xi * M.delta ^ 2 ≤ delta1 :=
    calc
      C0 * xi * M.delta ^ 2 = C0 * (xi * M.delta ^ 2) := by ring
      _ ≤ C * (xi * M.delta ^ 2) :=
        mul_le_mul_of_nonneg_right hC0le
          (mul_nonneg hxi0.le (sq_nonneg M.delta))
      _ = C * xi * M.delta ^ 2 := by ring
      _ ≤ delta1 := hsmall
  have hdelta0 : delta1 ≤ c0 := hdelta.trans hc0Bound
  have hdeltaEtaK : delta1 ≤ eta * K⁻¹ := hdelta.trans hcEtaBound
  let n := homogenizationMidpoint L m
  have hLn : L ≤ n := (homogenizationMidpoint_corridor L m hLm).1
  have hnm : n ≤ m := (homogenizationMidpoint_corridor L m hLm).2.1
  have hhalfNat : m - L ≤ 2 * (n - L) :=
    (homogenizationMidpoint_corridor L m hLm).2.2.1
  have hCtime : (4 * (t0 : ℝ) + 1) ≤ C := hCtimeBound
  have hHtime : (2 * (t0 : ℝ)) ≤ H := by
    have htimeLog : (2 * (t0 : ℝ)) ≤
        C * Real.log (2 + xi) := by
      have hm := mul_le_mul_of_nonneg_right hCtime
        (le_trans (by norm_num) hlog)
      nlinarith only [hm, hlog, (Nat.cast_nonneg t0 : (0 : ℝ) ≤ (t0 : ℝ))]
    exact htimeLog.trans hgapH
  have ht0 : t0 ≤ n - L := by
    have hhalfR : H ≤ 2 * ((n - L : ℕ) : ℝ) := by
      dsimp [H]
      exact_mod_cast hhalfNat
    exact_mod_cast (show (t0 : ℝ) ≤ ((n - L : ℕ) : ℝ) by linarith only [hhalfR, hHtime])
  let j := n - L - t0
  have hnEq : L + t0 + j = n := by dsimp [j]; omega
  have hmeanRaw := hmean M m0 xi delta1 hxi hsmall0 hdelta0 hS L hLm0 e he j
  rw [hnEq] at hmeanRaw
  have hfixedRaw := hfixed M m0 xi delta1 hxi hS L m hLm0 hLm e he
  have hAf : 0 ≤ Af := by
    rw [hAfDef]
    exact mul_nonneg hCf.le (Real.rpow_nonneg (by norm_num) _)
  have hAm : 0 ≤ Am := by
    rw [hAmDef]
    exact mul_nonneg hK.le (inv_nonneg.mpr (pow_pos hrho0 _).le)
  have hgammaF : 0 < gammaF := by rw [hGammaFDef]; linarith only [hdR]
  have hCfsep : Cfsep ≤ C := by
    rw [hCDef]
    exact (le_max_left Cfsep _).trans <|
      (le_max_right C0 _).trans (le_max_right 1 _)
  have hCmsep : Cmsep ≤ C := by
    rw [hCDef]
    exact (le_max_left Cmsep _).trans <|
      (le_max_right Cfsep _).trans <|
        (le_max_right C0 _).trans (le_max_right 1 _)
  have hfluctAbsorb :
      Af * xi * Real.rpow (1 / 3 : ℝ) (gammaF * H) ≤ eta := by
    exact logarithmic_rpow_decay_absorption (by norm_num) (by norm_num)
      hgammaF hAf heta hxi1 (by simpa only [hCfsepDef] using hCfsep) hgapH
  have hmeanAbsorb :
      Am * xi * Real.rpow rho ((1 / 2 : ℝ) * H) ≤ eta := by
    exact logarithmic_rpow_decay_absorption hrho0 hrho1 (by norm_num)
      hAm heta hxi1 (by simpa only [hCmsepDef] using hCmsep) hgapH
  have hfluctBase :
      Real.rpow (1 / 3 : ℝ) (gammaF * H) =
        Real.rpow 3 (-((d : ℝ) / 4) * H) := by
    rw [show Real.rpow (1 / 3 : ℝ) (gammaF * H) =
        Real.exp (Real.log (1 / 3 : ℝ) * (gammaF * H)) from
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 3) (gammaF * H)]
    rw [show Real.rpow 3 (-((d : ℝ) / 4) * H) =
        Real.exp (Real.log 3 * (-((d : ℝ) / 4) * H)) from
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)
        (-((d : ℝ) / 4) * H)]
    rw [show Real.log (1 / 3 : ℝ) = -Real.log 3 by
      rw [one_div, Real.log_inv]]
    rw [hGammaFDef]
    congr 1
    ring
  have hfluct :
      Cf * xi * delta1 *
          Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) ≤
        eta * delta1 := by
    have hmid := three_rpow_midpoint_fluctuation (d := d) hLm
    change Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) ≤ _ at hmid
    calc
      _ ≤ Cf * xi * delta1 *
          (Real.rpow 3 ((d : ℝ) / 4) *
            Real.rpow 3 (-((d : ℝ) / 4) * H)) :=
        mul_le_mul_of_nonneg_left hmid
          (mul_nonneg (mul_nonneg hCf.le hxi0.le) hS.2.1.le)
      _ = (Af * xi * Real.rpow (1 / 3 : ℝ) (gammaF * H)) * delta1 := by
        rw [hfluctBase]
        rw [hAfDef]
        ring
      _ ≤ eta * delta1 :=
        mul_le_mul_of_nonneg_right hfluctAbsorb hS.2.1.le
  have hrhoShift : rho ^ j ≤
      (rho ^ t0)⁻¹ * rho ^ (n - L) := by
    have hpow : rho ^ j * rho ^ t0 = rho ^ (n - L) := by
      rw [← pow_add]
      congr 1
      dsimp [j]
      omega
    have hpos : 0 < rho ^ t0 := pow_pos hrho0 _
    rw [← hpow]
    rw [mul_comm (rho ^ j), ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  have hrhoMid : rho ^ (n - L) ≤
      Real.rpow rho ((1 / 2 : ℝ) * H) := by
    have hmid := midpoint_contraction_le_half_gap hrho0 hrho1 hLm
    change rho ^ (n - L) ≤ Real.rpow rho (((m - L : ℕ) : ℝ) / 2) at hmid
    simpa [H, mul_comm, div_eq_mul_inv] using hmid
  have hrhoj : K * rho ^ j ≤ eta := by
    have hchain : K * rho ^ j ≤
        Am * Real.rpow rho ((1 / 2 : ℝ) * H) := by
      calc
        K * rho ^ j ≤ K * ((rho ^ t0)⁻¹ * rho ^ (n - L)) :=
          mul_le_mul_of_nonneg_left hrhoShift hK.le
        _ ≤ K * ((rho ^ t0)⁻¹ *
            Real.rpow rho ((1 / 2 : ℝ) * H)) := by
          gcongr
        _ = Am * Real.rpow rho ((1 / 2 : ℝ) * H) := by
          rw [hAmDef]
          ring
    have hxiFactor : Am * Real.rpow rho ((1 / 2 : ℝ) * H) ≤
        Am * xi * Real.rpow rho ((1 / 2 : ℝ) * H) := by
      have hrpow0 := Real.rpow_nonneg hrho0.le ((1 / 2 : ℝ) * H)
      calc
        Am * Real.rpow rho ((1 / 2 : ℝ) * H) =
            Am * 1 * Real.rpow rho ((1 / 2 : ℝ) * H) := by ring
        _ ≤ Am * xi * Real.rpow rho ((1 / 2 : ℝ) * H) := by
          gcongr
    exact hchain.trans (hxiFactor.trans hmeanAbsorb)
  have hsquare : K * delta1 ^ 2 ≤ eta * delta1 := by
    have hKdelta : K * delta1 ≤ eta := by
      have hm := mul_le_mul_of_nonneg_left hdeltaEtaK hK.le
      field_simp [hK.ne'] at hm
      simpa [mul_comm] using hm
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hKdelta hS.2.1.le
  have hmeanFinal :
      expectedJ M L n ((Real.sqrt (ahom M L))⁻¹ • e)
          (Real.sqrt (ahom M L) • e) ≤ 2 * eta * delta1 := by
    calc
      _ ≤ K * delta1 * (delta1 + rho ^ j) := hmeanRaw
      _ = K * delta1 ^ 2 + (K * rho ^ j) * delta1 := by ring
      _ ≤ eta * delta1 + eta * delta1 :=
        add_le_add hsquare
          (mul_le_mul_of_nonneg_right hrhoj hS.2.1.le)
      _ = 2 * eta * delta1 := by ring
  have htotal :
      Cf * xi * delta1 *
          Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) +
        expectedJ M L n ((Real.sqrt (ahom M L))⁻¹ • e)
          (Real.sqrt (ahom M L) • e) ≤
        ((16 * Q)⁻¹) * delta1 := by
    have hetaCompare : 3 * eta ≤ (16 * Q)⁻¹ := by
      rw [hEtaDef]
      field_simp [hQ.ne']
      nlinarith only [hQ]
    calc
      _ ≤ eta * delta1 + 2 * eta * delta1 := add_le_add hfluct hmeanFinal
      _ = (3 * eta) * delta1 := by ring
      _ ≤ (16 * Q)⁻¹ * delta1 :=
        mul_le_mul_of_nonneg_right hetaCompare hS.2.1.le
  exact hfixedRaw.trans (ENNReal.ofReal_le_ofReal (by simpa only [n, hQDef] using htotal))



theorem homogenization_step_of_combine_and_initial {d : ℕ}
    (hcombine : CombineUnderSConclusion d)
    (hinitial : InitialFixedCutoffResponseConclusion d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m0 : ℕ) (xi delta1 : ℝ),
        0 < m0 → 16 * (d : ℝ) ≤ xi →
        C * xi * M.delta ^ 2 ≤ delta1 → delta1 ≤ c →
        inductionHypothesis M m0 xi delta1 →
        ∀ (m L : ℕ), 0 < m → L ≤ m0 →
          (L : ℝ) + C * Real.log (2 + xi) ≤ m →
          paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M L m) ≤
            ENNReal.ofReal ((1 / 4 : ℝ) * delta1) := by
  rcases exists_fixedDirection_logarithmic_bound hcombine hinitial with
    ⟨c, C, hc, hC, hdir⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro M m0 xi delta1 _hm0 hxi hsmall hdelta hS m L _hm hLm0 hgap
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  let s := (sphereQuarterNet d).points
  let a : ℝ := (16 * (s.card : ℝ))⁻¹ * delta1
  have hs : s.Nonempty := sphereQuarterNet_points_nonempty
  have hscard : 0 < (s.card : ℝ) := by
    exact_mod_cast hs.card_pos
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (inv_nonneg.mpr (by positivity)) hS.2.1.le
  have hquarter :=
    paperENNRealLpNorm_normalizedDefect_le_quarterNetSum M L
      (Ch02.cubeDomain (originCube d (m : ℤ))) hS.1
  have hterm : ∀ e ∈ s,
      paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
          ENNReal.ofReal
            (J (Ch02.cubeDomain (originCube d (m : ℤ)))
              (aCutoffCoeffOnData M L omega
                (Ch02.cubeDomain (originCube d (m : ℤ)))).toCoeffOn
              ((Real.sqrt (ahom M L))⁻¹ • e)
              (Real.sqrt (ahom M L) • e))) ≤ ENNReal.ofReal a := by
    intro e he
    have heunit := (sphereQuarterNet d).unit e he
    have h := hdir M m0 xi delta1 hxi hsmall hdelta hS m L hLm0 hgap e heunit
    simpa only [s, a, cutoffResponseOnCube, aCutoffFamily, aCutoffTriadicData]
      using! h
  have hsum :
      ∑ e ∈ s,
          paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
            ENNReal.ofReal
              (J (Ch02.cubeDomain (originCube d (m : ℤ)))
                (aCutoffCoeffOnData M L omega
                  (Ch02.cubeDomain (originCube d (m : ℤ)))).toCoeffOn
                ((Real.sqrt (ahom M L))⁻¹ • e)
                (Real.sqrt (ahom M L) • e))) ≤
        ∑ _e ∈ s, ENNReal.ofReal a :=
    Finset.sum_le_sum fun e he => hterm e he
  have hreal : 2 * (s.card : ℝ) * a ≤ (1 / 4 : ℝ) * delta1 := by
    dsimp [a]
    field_simp [ne_of_gt hscard]
    nlinarith [hS.2.1.le]
  calc
    paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M L m) =
        paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M L (Ch02.cubeDomain (originCube d (m : ℤ)))) := by
      rfl
    _ ≤ 2 * ∑ e ∈ s,
          paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
            ENNReal.ofReal
              (J (Ch02.cubeDomain (originCube d (m : ℤ)))
                (aCutoffCoeffOnData M L omega
                  (Ch02.cubeDomain (originCube d (m : ℤ)))).toCoeffOn
                ((Real.sqrt (ahom M L))⁻¹ • e)
                (Real.sqrt (ahom M L) • e))) := by
      simpa only [s] using hquarter
    _ ≤ 2 * ∑ _e ∈ s, ENNReal.ofReal a :=
      mul_le_mul_right hsum 2
    _ = ENNReal.ofReal (2 * (s.card : ℝ) * a) := by
      calc
        2 * ∑ _e ∈ s, ENNReal.ofReal a =
            ENNReal.ofReal 2 * ENNReal.ofReal (∑ _e ∈ s, a) := by
          rw [ENNReal.ofReal_ofNat,
            ENNReal.ofReal_sum_of_nonneg (fun _e _he => ha0)]
        _ = ENNReal.ofReal (2 * (∑ _e ∈ s, a)) :=
          (ENNReal.ofReal_mul (by norm_num)).symm
        _ = ENNReal.ofReal (2 * (s.card : ℝ) * a) := by
          congr 1
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ENNReal.ofReal ((1 / 4 : ℝ) * delta1) :=
      ENNReal.ofReal_le_ofReal hreal



theorem homogenization_step_of_combine {d : ℕ}
    (hcombine : CombineUnderSConclusion d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m0 : ℕ) (xi delta1 : ℝ),
        0 < m0 → 16 * (d : ℝ) ≤ xi →
        C * xi * M.delta ^ 2 ≤ delta1 → delta1 ≤ c →
        inductionHypothesis M m0 xi delta1 →
        ∀ (m L : ℕ), 0 < m → L ≤ m0 →
          (L : ℝ) + C * Real.log (2 + xi) ≤ m →
          paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M L m) ≤
            ENNReal.ofReal ((1 / 4 : ℝ) * delta1) :=
  homogenization_step_of_combine_and_initial hcombine
    initial_fixed_cutoff_response_conclusion

/-- The unconditional provider: the combine premise is discharged by the
proved frozen anchor. -/
theorem homogenization_step {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m0 : ℕ) (ξ δ1 : ℝ),
        0 < m0 → 16 * (d : ℝ) ≤ ξ →
        C * ξ * M.delta ^ 2 ≤ δ1 → δ1 ≤ c →
        inductionHypothesis M m0 ξ δ1 →
        ∀ (m L : ℕ), 0 < m → L ≤ m0 →
          (L : ℝ) + C * Real.log (2 + ξ) ≤ m →
          paperENNRealLpNorm M.P.toMeasure ξ (normalizedDefectAt M L m) ≤
            ENNReal.ofReal ((1 / 4 : ℝ) * δ1) :=
  homogenization_step_of_combine _root_.SubdiffusiveProcess.Section4.combine_under_s

end

end SubdiffusiveProcess.Providers.Section4
