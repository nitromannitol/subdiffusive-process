module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section10.BetaMinusClockGap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientStrictDecay
public import SubdiffusiveProcess.Section5.SharpAsymptotic

@[expose] public section




set_option autoImplicit false
open SubdiffusiveProcess _root_.SubdiffusiveProcess.Model Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Process
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Exponents
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section13

variable {d : ℕ}

/-! ## The triadic block containing a radius -/

theorem three_pow_triadicIndex_le {r : ℝ} (hr : 1 ≤ r) :
    (3 : ℝ) ^ triadicIndex r ≤ r := by
  have hlog : 0 ≤ Real.logb 3 r := Real.logb_nonneg (by norm_num) hr
  have hfloor : ((triadicIndex r : ℕ) : ℝ) ≤ Real.logb 3 r := Nat.floor_le hlog
  have hpow : (3 : ℝ) ^ ((triadicIndex r : ℕ) : ℝ) ≤ (3 : ℝ) ^ (Real.logb 3 r) :=
    Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 3) |>.mpr hfloor
  rwa [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)] at hpow

theorem lt_three_pow_triadicIndex_succ (r : ℝ) :
    r < (3 : ℝ) ^ (triadicIndex r + 1) ∨ r ≤ 0 := by
  rcases le_or_gt r 0 with h | h
  · exact Or.inr h
  refine Or.inl ?_
  have hlt : Real.logb 3 r < (triadicIndex r : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpow : (3 : ℝ) ^ (Real.logb 3 r) < (3 : ℝ) ^ ((triadicIndex r : ℝ) + 1) :=
    Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 3) |>.mpr hlt
  rw [Real.rpow_logb (by norm_num) (by norm_num) h] at hpow
  have hcast : (3 : ℝ) ^ ((triadicIndex r : ℝ) + 1) = (3 : ℝ) ^ (triadicIndex r + 1) := by
    rw [show ((triadicIndex r : ℝ) + 1) = ((triadicIndex r + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rwa [hcast] at hpow

/-! ## The clock's lower power bound from strict decay -/

/-- **The clock's exact lower power bound at the triadic radii.**  The exact mirror of
`Section10.timeScale_triadic_le`: from `ahom m ≤ 3^{-eta(m+1)}` -- the fourth conjunct of the
PROVED `p.homogenized.coefficient.strict.decay`, and of the law-indexed `etaSub` clause the
frozen anchors carry -- the clock satisfies `Tr (3^m) ≥ 3^eta · (3^m)^{2+eta}`. -/
theorem timeScale_triadic_ge_of_decay {eta : ℝ} (M : GMCModel d)
    (hdec : ∀ m : ℕ, ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ))) (m : ℕ) :
    Real.rpow 3 eta * ((3 : ℝ) ^ m) ^ (2 + eta) ≤ timeScale (ahom M) ((3 : ℝ) ^ m) := by
  have hL : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hpos := ahom_pos M m
  have hb : (0 : ℝ) < Real.rpow 3 (-eta * (m + 1 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hnum : (0 : ℝ) < (3 : ℝ) ^ (2 * m) := by positivity
  rw [timeScale_triadic, timeScaleTriadic]
  have hstep : (3 : ℝ) ^ (2 * m) / Real.rpow 3 (-eta * (m + 1 : ℝ))
      ≤ (3 : ℝ) ^ (2 * m) / ahom M m :=
    div_le_div_of_nonneg_left hnum.le hpos (hdec m)
  refine le_trans (le_of_eq ?_) hstep
  have hrp : ∀ y : ℝ, Real.rpow 3 y = Real.exp (y * Real.log 3) := by
    intro y
    have hid : Real.rpow 3 y = (3 : ℝ) ^ y := rfl
    rw [hid, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
    congr 1
    ring
  have hlhs : Real.rpow 3 eta * ((3 : ℝ) ^ m) ^ (2 + eta)
      = Real.exp (eta * Real.log 3 + (2 + eta) * ((m : ℝ) * Real.log 3)) := by
    rw [Section10.three_pow_rpow, hrp, ← Real.exp_add]
  have h2m : ((3 : ℝ) ^ (2 * m)) = Real.exp ((2 * (m : ℝ)) * Real.log 3) := by
    rw [Section10.three_pow_eq_exp (2 * m)]
    congr 1
    push_cast
    ring
  have hrhs : (3 : ℝ) ^ (2 * m) / Real.rpow 3 (-eta * (m + 1 : ℝ))
      = Real.exp ((2 * (m : ℝ)) * Real.log 3 + eta * ((m : ℝ) + 1) * Real.log 3) := by
    rw [h2m, hrp, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  rw [hlhs, hrhs]
  congr 1
  ring

/-- **The clock's log-affine exponent is at least two.**  `ahom` is nonincreasing, so the ratio
of consecutive triadic clock values is at least `9`. -/
theorem two_le_timeScaleExponent (M : GMCModel d) (m : ℕ) :
    2 ≤ timeScaleExponent (ahom M) m := by
  have h1 := ahom_pos M m
  have h2 := ahom_pos M (m + 1)
  have hmono : ahom M (m + 1) ≤ ahom M m :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ahom_le_ahom_of_le M (Nat.le_succ m)
  have hBDpos : (0 : ℝ) < ahom M (m + 1) / ahom M m := by positivity
  have hBD1 : ahom M (m + 1) / ahom M m ≤ 1 := (div_le_one h1).mpr hmono
  have hratio : (9 : ℝ) ≤ timeScaleTriadic (ahom M) (m + 1) / timeScaleTriadic (ahom M) m := by
    rw [timeScaleTriadic, timeScaleTriadic, div_div_div_comm]
    have hAC : (3 : ℝ) ^ (2 * (m + 1)) / (3 : ℝ) ^ (2 * m) = 9 := by
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
      field_simp
      norm_num
    rw [hAC, le_div_iff₀ hBDpos]
    nlinarith [hBD1]
  have hlogb : Real.logb 3 9 ≤ Real.logb 3
      (timeScaleTriadic (ahom M) (m + 1) / timeScaleTriadic (ahom M) m) :=
    Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 3) (by norm_num) hratio
  have h9 : Real.logb 3 (9 : ℝ) = 2 := by
    have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have h3 : (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [Real.logb, h3, Real.log_pow]
    field_simp
    norm_num
  rwa [h9] at hlogb

/-- **The clock's lower power bound at every radius `r ≥ 1`.**  The triadic bound of
`timeScale_triadic_ge_of_decay` is transported off the triadic grid by the clock's own log-affine
interpolation: on a block the interpolation exponent is at least `2`, and the block ratio `r/3^m`
lies in `[1, 3)`, so the `3^eta` of the triadic bound is exactly what the interpolation can
lose.  The resulting constant is `1`. -/
theorem timeScale_ge_rpow_of_decay {eta : ℝ} (heta : 0 ≤ eta) (M : GMCModel d)
    (hdec : ∀ m : ℕ, ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ)))
    {r : ℝ} (hr : 1 ≤ r) :
    r ^ (2 + eta) ≤ timeScale (ahom M) r := by
  rcases le_or_gt r 1 with hle | hgt
  · have hr1 : r = 1 := le_antisymm hle hr
    subst hr1
    rw [timeScale_one, Real.one_rpow]
    have h0 := hdec 0
    norm_num at h0
    have hle1 : (3 : ℝ) ^ (-eta) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hpos := ahom_pos M 0
    rw [le_div_iff₀ hpos]
    linarith
  · set m : ℕ := triadicIndex r with hm
    have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
    have hlow : (3 : ℝ) ^ m ≤ r := three_pow_triadicIndex_le hr
    have hhigh : r < (3 : ℝ) ^ (m + 1) :=
      (lt_three_pow_triadicIndex_succ r).resolve_right (by linarith)
    set u : ℝ := r / (3 : ℝ) ^ m with hu
    have hu1 : 1 ≤ u := (one_le_div h3m).mpr hlow
    have hu0 : (0 : ℝ) < u := by linarith
    have hu3 : u ≤ 3 := by
      rw [hu, div_le_iff₀ h3m]
      have : ((3 : ℝ) ^ (m + 1)) = 3 * (3 : ℝ) ^ m := by rw [pow_succ]; ring
      linarith [hhigh, this]
    have hsplit : r ^ (2 + eta) = ((3 : ℝ) ^ m) ^ (2 + eta) * u ^ (2 + eta) := by
      rw [← Real.mul_rpow h3m.le hu0.le, hu, mul_div_cancel₀ _ (ne_of_gt h3m)]
    have hexp : u ^ (2 + eta) ≤ Real.rpow 3 eta * u ^ timeScaleExponent (ahom M) m := by
      have hadd : u ^ (2 + eta) = u ^ (2 : ℝ) * u ^ eta := Real.rpow_add hu0 2 eta
      have hue : u ^ eta ≤ Real.rpow 3 eta := Real.rpow_le_rpow hu0.le hu3 heta
      have hu2 : u ^ (2 : ℝ) ≤ u ^ timeScaleExponent (ahom M) m :=
        Real.rpow_le_rpow_of_exponent_le hu1 (two_le_timeScaleExponent M m)
      have hnn : (0:ℝ) ≤ u ^ (2 : ℝ) := Real.rpow_nonneg hu0.le _
      have hnn2 : (0:ℝ) ≤ Real.rpow 3 eta := Real.rpow_nonneg (by norm_num) _
      calc u ^ (2 + eta) = u ^ (2 : ℝ) * u ^ eta := hadd
        _ ≤ u ^ timeScaleExponent (ahom M) m * Real.rpow 3 eta := by
            exact mul_le_mul hu2 hue (Real.rpow_nonneg hu0.le _) (le_trans hnn hu2)
        _ = Real.rpow 3 eta * u ^ timeScaleExponent (ahom M) m := by ring
    have htri : Real.rpow 3 eta * ((3 : ℝ) ^ m) ^ (2 + eta) ≤ timeScaleTriadic (ahom M) m := by
      have := timeScale_triadic_ge_of_decay M hdec m
      rwa [timeScale_triadic] at this
    rw [timeScale, ite_eq_right (not_le.mpr hgt), ← hm, ← hu]
    have hupos : (0:ℝ) ≤ u ^ timeScaleExponent (ahom M) m := Real.rpow_nonneg hu0.le _
    have h3mpos : (0:ℝ) ≤ ((3 : ℝ) ^ m) ^ (2 + eta) := Real.rpow_nonneg h3m.le _
    calc r ^ (2 + eta) = ((3 : ℝ) ^ m) ^ (2 + eta) * u ^ (2 + eta) := hsplit
      _ ≤ ((3 : ℝ) ^ m) ^ (2 + eta) * (Real.rpow 3 eta * u ^ timeScaleExponent (ahom M) m) :=
          mul_le_mul_of_nonneg_left hexp h3mpos
      _ = (Real.rpow 3 eta * ((3 : ℝ) ^ m) ^ (2 + eta)) * u ^ timeScaleExponent (ahom M) m := by
          ring
      _ ≤ timeScaleTriadic (ahom M) m * u ^ timeScaleExponent (ahom M) m :=
          mul_le_mul_of_nonneg_right htri hupos

/-! ## The law-indexed `etaSub` convention -/

/-- The law-indexed subdiffusivity clause, copied from the shape the six frozen anchors carry
(`SubdiffusiveProcess.Section11.divergence_power_laws` and its siblings): the exponent is a function of
the *law* `zeroPotentialLaw M.P`, not of the model.  Carrying it as a hypothesis is deliberate --
turning the per-model exponent of `p.homogenized.coefficient.strict.decay` into a law-indexed one
is the uniformity question the §13 plans flag, and it is not settled here. -/
def EtaSubClause (d : ℕ) (etaSub : ProbabilityMeasure (PotentialField d) → ℝ) : Prop :=
  ∀ M : GMCModel d,
    0 < etaSub (zeroPotentialLaw M.P) ∧
    (d = 2 → etaSub (zeroPotentialLaw M.P) = tauSq M.P / Real.log 3) ∧
    (3 ≤ d → etaSub (zeroPotentialLaw M.P) ≤ tauSq M.P / ((d : ℝ) * Real.log 3)) ∧
    ∀ m : ℕ, ahom M m ≤ Real.rpow 3 (-etaSub (zeroPotentialLaw M.P) * (m + 1 : ℝ))



theorem timeScale_ge_rpow_of_etaSubClause
    {etaSub : ProbabilityMeasure (PotentialField d) → ℝ} (h : EtaSubClause d etaSub)
    (M : GMCModel d) {r : ℝ} (hr : 1 ≤ r) :
    r ^ (2 + etaSub (zeroPotentialLaw M.P)) ≤ timeScale (ahom M) r :=
  timeScale_ge_rpow_of_decay (h M).1.le M (h M).2.2.2 hr



theorem exists_eta_timeScale_ge (M : GMCModel d) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ r : ℝ, 1 ≤ r → r ^ (2 + eta) ≤ timeScale (ahom M) r := by
  obtain ⟨eta, heta, -, -, hdec⟩ := _root_.SubdiffusiveProcess.Section5.homogenized_coefficient_strict_decay M
  exact ⟨eta, heta, fun r hr => timeScale_ge_rpow_of_decay heta.le M hdec hr⟩

/-! ## The triadic `beta_0 ± C_0 delta^3 |log delta|` window from the sharp asymptotic -/

/-- **Both triadic bounds from `p.sharp.asymptotic`.**  With `C_0 := C / log 3`,

```text
exp(2tau^2/d - C delta^2 |log delta|) (3^m)^{beta_0 - C_0 delta^3 |log delta|}
  ≤ Tr(3^m) ≤
exp(2tau^2/d + C delta^2 |log delta|) (3^m)^{beta_0 + C_0 delta^3 |log delta|}.
```

The exponent deviation is `delta^3`, not `delta^2`: only the `m delta` half of the sharp
asymptotic's `(1 + m delta)` survives division by `m`, and `C delta^2 |log delta| * (m delta)
= (C / log 3) delta^3 |log delta| * (m log 3)`.  The `delta^2` half stays in the prefactor.

This is the triadic half of the uniform power-law bound for the diffusion time scale; the interpolation off
the triadic grid and the `max` defining `beta_-` are deliberately **not** assembled here. -/
theorem timeScale_triadic_betaZero_bounds {C : ℝ} (M : GMCModel d) (hd : 2 ≤ d)
    (hsharp : ∀ m : ℕ, |Real.log (ahom M m) + 2 * tauSq M.P * (m + 1 : ℝ) / d|
      ≤ C * M.delta ^ 2 * |Real.log M.delta| * (1 + (m : ℝ) * M.delta))
    (m : ℕ) :
    Real.exp (2 * tauSq M.P / d - C * M.delta ^ 2 * |Real.log M.delta|) *
        ((3 : ℝ) ^ m) ^ (betaZero M - (C / Real.log 3) * M.delta ^ 3 * |Real.log M.delta|)
      ≤ timeScale (ahom M) ((3 : ℝ) ^ m) ∧
    timeScale (ahom M) ((3 : ℝ) ^ m)
      ≤ Real.exp (2 * tauSq M.P / d + C * M.delta ^ 2 * |Real.log M.delta|) *
        ((3 : ℝ) ^ m) ^ (betaZero M + (C / Real.log 3) * M.delta ^ 3 * |Real.log M.delta|) := by
  have hL : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hpos := ahom_pos M m
  have hTr : timeScale (ahom M) ((3 : ℝ) ^ m)
      = Real.exp (2 * (m : ℝ) * Real.log 3 - Real.log (ahom M m)) := by
    rw [timeScale_triadic, timeScaleTriadic, Real.exp_sub, Real.exp_log hpos]
    congr 1
    rw [Section10.three_pow_eq_exp (2 * m)]
    congr 1
    push_cast
    ring
  have hbz : betaZero M * ((m : ℝ) * Real.log 3)
      = 2 * (m : ℝ) * Real.log 3 + 2 * tauSq M.P * (m : ℝ) / (d : ℝ) := by
    rw [betaZero]
    field_simp
  have hC0 : (C / Real.log 3) * M.delta ^ 3 * |Real.log M.delta| * ((m : ℝ) * Real.log 3)
      = C * M.delta ^ 2 * |Real.log M.delta| * ((m : ℝ) * M.delta) := by
    field_simp
  have hsplit : 2 * tauSq M.P * ((m : ℝ) + 1) / (d : ℝ)
      = 2 * tauSq M.P * (m : ℝ) / (d : ℝ) + 2 * tauSq M.P / (d : ℝ) := by
    field_simp
  have hprod : C * M.delta ^ 2 * |Real.log M.delta| * (1 + (m : ℝ) * M.delta)
      = C * M.delta ^ 2 * |Real.log M.delta|
        + C * M.delta ^ 2 * |Real.log M.delta| * ((m : ℝ) * M.delta) := by ring
  have habs := hsharp m
  rw [abs_le, hsplit, hprod] at habs
  obtain ⟨hlo, hhi⟩ := habs
  constructor
  · rw [hTr, Section10.three_pow_rpow, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [sub_mul, hbz, hC0]
    linarith
  · rw [hTr, Section10.three_pow_rpow, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [add_mul, hbz, hC0]
    linarith

/-- **The triadic window, instantiated from the PROVED `p.sharp.asymptotic`.**  The exponent
constant is `C / log 3` where `C` is the sharp asymptotic's own constant. -/
theorem exists_triadic_betaZero_window (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 → ∀ m : ℕ,
        Real.exp (2 * tauSq M.P / d - C * M.delta ^ 2 * |Real.log M.delta|) *
            ((3 : ℝ) ^ m) ^ (betaZero M - (C / Real.log 3) * M.delta ^ 3 * |Real.log M.delta|)
          ≤ timeScale (ahom M) ((3 : ℝ) ^ m) ∧
        timeScale (ahom M) ((3 : ℝ) ^ m)
          ≤ Real.exp (2 * tauSq M.P / d + C * M.delta ^ 2 * |Real.log M.delta|) *
            ((3 : ℝ) ^ m) ^
              (betaZero M + (C / Real.log 3) * M.delta ^ 3 * |Real.log M.delta|) := by
  obtain ⟨delta0, C, hdelta0, hC, hmain⟩ := _root_.SubdiffusiveProcess.Section5.sharp_asymptotic (d := d)
  exact ⟨delta0, C, hdelta0, hC, fun M hM m =>
    timeScale_triadic_betaZero_bounds M hd (hmain M hM) m⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section13
