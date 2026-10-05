module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpperMean

@[expose] public section

/-!
# The exit-time tail at a fixed time, and the two assumptions from the homogeneous inequality

Two independent steps:

* choosing the resolvent scale comparable to `AF` and the number of resolvent steps comparable to
  `t/(AF)` turns the geometric decay of the survival mass into the exponential tail
  `P_x[τ_U>t] ≤ C A^C exp(-c t/(AF))`;
* Hölder's inequality between the exponents `2` and `p₀` derives both the Sobolev and the Poincaré
  assumption from the homogeneous Sobolev inequality.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}

/-! ### The decay rate and the geometric split -/

/-- The exponential rate produced by the resolvent iteration. -/
def rate : ℝ := Real.log (3 / 2) / 5

theorem rate_pos : 0 < rate := by
  have h : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  unfold rate
  positivity

/-- A geometric factor at most `2/3`, raised to a power comparable to `t/(5T)`, decays
exponentially. -/
theorem geometric_le_exp {T t x : ℝ} {m : ℕ} (hT : 0 < T)
    (hx0 : 0 ≤ x) (hx : x ≤ 2 / 3) (hm : t / (5 * T) ≤ (m : ℝ)) :
    x ^ m ≤ Real.exp (-rate * t / T) := by
  have hbase : (0 : ℝ) < 2 / 3 := by norm_num
  have hstep1 : x ^ m ≤ (2 / 3 : ℝ) ^ m := by gcongr
  have hstep2 : (2 / 3 : ℝ) ^ m = (2 / 3 : ℝ) ^ ((m : ℕ) : ℝ) := (Real.rpow_natCast _ m).symm
  have hstep3 : (2 / 3 : ℝ) ^ ((m : ℕ) : ℝ) ≤ (2 / 3 : ℝ) ^ (t / (5 * T)) :=
    Real.rpow_le_rpow_of_exponent_ge hbase (by norm_num) hm
  have hlog : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2) := by
    rw [show (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv]
  have hstep4 : (2 / 3 : ℝ) ^ (t / (5 * T)) = Real.exp (-rate * t / T) := by
    rw [Real.rpow_def_of_pos hbase, hlog]
    congr 1
    unfold rate
    field_simp
  calc x ^ m ≤ (2 / 3 : ℝ) ^ m := hstep1
    _ = (2 / 3 : ℝ) ^ ((m : ℕ) : ℝ) := hstep2
    _ ≤ (2 / 3 : ℝ) ^ (t / (5 * T)) := hstep3
    _ = Real.exp (-rate * t / T) := hstep4

/-- Splitting a large time into a fixed initial step and a whole number of resolvent scales, each
at least twice the torsion scale. -/
theorem exists_geometric_split {T F t : ℝ} (hT : 0 < T) (hFT : F ≤ T)
    (h5 : 5 * T ≤ t) :
    ∃ n : ℕ, ∃ s : ℝ, 0 < s ∧ t = F + ((n + 1 : ℕ) : ℝ) * s ∧ 2 * T ≤ s ∧
      t / (5 * T) ≤ ((n + 1 : ℕ) : ℝ) := by
  set t2 : ℝ := t - F with ht2def
  have ht2 : 4 * T ≤ t2 := by rw [ht2def]; linarith
  have ht2pos : 0 < t2 := by linarith
  have hq : (2 : ℝ) ≤ t2 / (2 * T) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  set m : ℕ := ⌊t2 / (2 * T)⌋₊ with hmdef
  have hm1 : 1 ≤ m := by
    rw [hmdef]
    exact Nat.le_floor (by exact_mod_cast le_trans (by norm_num) hq)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hmle : (m : ℝ) ≤ t2 / (2 * T) := Nat.floor_le (by positivity)
  have hmgt : t2 / (2 * T) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm1).symm⟩
  refine ⟨n, t2 / (m : ℝ), by positivity, ?_, ?_, ?_⟩
  · rw [← hn]
    field_simp
    linarith
  · rw [le_div_iff₀ hmpos]
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * T)).mp hmle
    linarith
  · rw [← hn]
    have hexp : t2 < 2 * T * ((m : ℝ) + 1) := by
      have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * T)).mp hmgt
      linarith
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 5 * T)]
    nlinarith

/-! ### The exponential tail at a fixed time -/

/-- **The exponential exit-time tail.**  For times beyond five torsion scales the survival
probability decays exponentially, with the pointwise density bound as prefactor. -/
theorem survival_tail_le
    (hDiff : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hmtop : (weightedMeasure rho) U ≠ ∞)
    {A F : ℝ} (hA : 1 ≤ A) (hF : 0 < F)
    (hPoin : PoincareAssumption c rho U A F)
    {p : ℝ → Vec d → Vec d → ℝ} (hp : IsKilledDensity law rho U p)
    {D : ℝ} (hD0 : 0 ≤ D)
    {x : Vec d} (hx : x ∈ U) (hDx : ∀ y ∈ U, p F x y ≤ D)
    {t : ℝ} (ht : 5 * (A * F) ≤ t) :
    law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} ≤
      ENNReal.ofReal (D * ((weightedMeasure rho) U).toReal *
        Real.exp (-rate * t / (A * F))) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  set T : ℝ := A * F with hTdef
  have hT : 0 < T := by positivity
  have hFT : F ≤ T := by
    rw [hTdef]
    nlinarith
  obtain ⟨n, s, hs, hteq, hsT, hmT⟩ := exists_geometric_split hT hFT ht
  set m : ℕ := n + 1 with hmdef
  set kappa : ℝ := (1 + s / T)⁻¹ with hkappadef
  have hkappa0 : 0 ≤ kappa := by
    rw [hkappadef]
    positivity
  have hkappa23 : 2 * kappa ≤ 2 / 3 := by
    have h3 : (3 : ℝ) ≤ 1 + s / T := by
      have : (2 : ℝ) ≤ s / T := (le_div_iff₀ hT).mpr (by linarith)
      linarith
    have hden : (0 : ℝ) < 1 + s / T := by linarith
    have hk1 : kappa * (1 + s / T) = 1 := by
      rw [hkappadef]
      exact inv_mul_cancel₀ hden.ne'
    have hk3 : 3 * kappa ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left h3 hkappa0]
    linarith
  have ht2pos : (0 : ℝ) < ((m : ℕ) : ℝ) * s := by
    have : (0 : ℝ) < (m : ℝ) := by positivity
    positivity
  -- the split survival estimate
  have hsurv := survival_le_density_mul_mass hDiff.1 hU hp hF ht2pos hx hDx
  have hmass := lintegral_survival_le hDiff hU hUb hmtop hApos hF hs hPoin n
  have hcomb : law x {w | ENNReal.ofReal (F + ((m : ℕ) : ℝ) * s) < LifetimePath.exitTime U w} ≤
      ENNReal.ofReal D * (((2 : ℝ≥0∞) * ENNReal.ofReal kappa) ^ m *
        ENNReal.ofReal (((weightedMeasure rho) U).toReal)) :=
    le_trans hsurv (mul_le_mul' le_rfl hmass)
  -- convert to a single real bound
  have htwo : ((2 : ℝ≥0∞) * ENNReal.ofReal kappa) ^ m = ENNReal.ofReal ((2 * kappa) ^ m) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hpow : (2 * kappa) ^ m ≤ Real.exp (-rate * t / T) :=
    geometric_le_exp hT (by positivity) hkappa23 hmT
  have hmassnn : (0 : ℝ) ≤ ((weightedMeasure rho) U).toReal := ENNReal.toReal_nonneg
  calc law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w}
      = law x {w | ENNReal.ofReal (F + ((m : ℕ) : ℝ) * s) < LifetimePath.exitTime U w} := by
        rw [← hteq]
    _ ≤ ENNReal.ofReal D * (((2 : ℝ≥0∞) * ENNReal.ofReal kappa) ^ m *
          ENNReal.ofReal (((weightedMeasure rho) U).toReal)) := hcomb
    _ = ENNReal.ofReal (D * ((2 * kappa) ^ m * ((weightedMeasure rho) U).toReal)) := by
        rw [htwo, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hD0]
    _ ≤ ENNReal.ofReal (D * ((weightedMeasure rho) U).toReal * Real.exp (-rate * t / T)) := by
        apply ENNReal.ofReal_le_ofReal
        have hmul : (2 * kappa) ^ m * ((weightedMeasure rho) U).toReal ≤
            Real.exp (-rate * t / T) * ((weightedMeasure rho) U).toReal :=
          mul_le_mul_of_nonneg_right hpow hmassnn
        nlinarith [mul_le_mul_of_nonneg_left hmul hD0]

/-! ### Both assumptions from the homogeneous Sobolev inequality -/

/-- **Hölder's inequality gives both assumptions.**  The homogeneous Sobolev inequality implies
the Sobolev and Poincaré assumptions with the same constants. -/
theorem assumptions_of_homogeneous
    {U : Set (Vec d)} (hU : IsOpen U) (hr : CoefficientOn U rho)
    (hm0 : (weightedMeasure rho) U ≠ 0) (hmtop : (weightedMeasure rho) U ≠ ∞)
    {p0 A F : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A)
    (hhom : ∀ f : H10Function U,
      lpSq rho U p0 f.toH1Function.toFun ≤
        ENNReal.ofReal (A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p0)) *
          F * energy c U f.toH1Function)) :
    SobolevAssumption c rho U p0 A F ∧ PoincareAssumption c rho U A F := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  set mass : ℝ := ((weightedMeasure rho) U).toReal with hmassdef
  have hmass : 0 < mass := ENNReal.toReal_pos hm0 hmtop
  set theta : ℝ := 1 - 2 / p0 with hthetadef
  have hp0pos : 0 < p0 := by linarith
  have htheta : 0 < theta := by
    rw [hthetadef]
    have : 2 / p0 < 1 := (div_lt_one hp0pos).mpr hp0
    linarith
  have hcoef : (0 : ℝ) ≤ A * mass ^ (-theta) := by positivity
  refine ⟨fun f => ?_, fun f => ?_⟩
  · refine le_trans (hhom f) ?_
    have hassoc : A * mass ^ (-theta) * F * energy c U f.toH1Function
        = (A * mass ^ (-theta)) * (F * energy c U f.toH1Function) := by ring
    rw [hassoc, ENNReal.ofReal_mul hcoef]
    exact mul_le_mul' le_rfl le_add_self
  · -- Hölder between the exponents `2` and `p₀`
    have hfmem : MemLp f.toH1Function.toFun 2 ((weightedMeasure rho).restrict U) :=
      memLp_weighted_of_volume_restrict hU.measurableSet hr f.toH1Function.memL2
    have hmuniv : ((weightedMeasure rho).restrict U) Set.univ = ENNReal.ofReal mass := by
      rw [Measure.restrict_apply_univ, hmassdef, ENNReal.ofReal_toReal hmtop]
    have hfmeas : AEStronglyMeasurable f.toH1Function.toFun ((volume.withDensity (fun x => ENNReal.ofReal (rho x))).restrict U) := by
      simpa only [weightedMeasure] using! hfmem.aestronglyMeasurable
    have hlp2 : lpSq rho U 2 f.toH1Function.toFun
        = (eLpNorm f.toH1Function.toFun 2 ((weightedMeasure rho).restrict U)) ^ 2 := by
      simp only [lpSq, weightedMeasure, ENNReal.ofReal_ofNat, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hfmeas]
    have hlpp : lpSq rho U p0 f.toH1Function.toFun
        = (eLpNorm f.toH1Function.toFun (ENNReal.ofReal p0)
            ((weightedMeasure rho).restrict U)) ^ 2 := by
      simp only [lpSq, weightedMeasure, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hfmeas]
    have hple : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p0 := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
      exact ENNReal.ofReal_le_ofReal (le_of_lt hp0)
    have hholder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := (weightedMeasure rho).restrict U) (f := f.toH1Function.toFun) hple hfmem.aestronglyMeasurable
    rw [ENNReal.toReal_ofReal (le_of_lt hp0pos),
      show ENNReal.toReal 2 = (2 : ℝ) from by norm_num] at hholder
    have hexp : (ENNReal.ofReal mass ^ (1 / (2 : ℝ) - 1 / p0)) ^ 2
        = ENNReal.ofReal (mass ^ theta) := by
      rw [← ENNReal.rpow_natCast (ENNReal.ofReal mass ^ (1 / (2 : ℝ) - 1 / p0)) 2,
        ← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_pos hmass]
      congr 1
      rw [hthetadef]
      push_cast
      field_simp
    have hsq : lpSq rho U 2 f.toH1Function.toFun ≤
        lpSq rho U p0 f.toH1Function.toFun * ENNReal.ofReal (mass ^ theta) := by
      rw [hlp2, hlpp, ← hexp, ← mul_pow, ← hmuniv]
      gcongr
    refine le_trans hsq (le_trans (mul_le_mul' (hhom f) le_rfl) ?_)
    rw [← ENNReal.ofReal_mul' (by positivity : (0:ℝ) ≤ mass ^ theta)]
    apply ENNReal.ofReal_le_ofReal
    have hcancel : mass ^ (-theta) * mass ^ theta = 1 := by
      rw [Real.rpow_neg hmass.le, inv_mul_cancel₀ (by positivity)]
    have hfinal : A * mass ^ (-theta) * F * energy c U f.toH1Function * mass ^ theta
        = A * F * energy c U f.toH1Function := by
      calc A * mass ^ (-theta) * F * energy c U f.toH1Function * mass ^ theta
          = (A * F * energy c U f.toH1Function) * (mass ^ (-theta) * mass ^ theta) := by ring
        _ = A * F * energy c U f.toH1Function := by rw [hcancel, mul_one]
    exact le_of_eq hfinal

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
