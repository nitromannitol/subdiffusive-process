module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalASDDiameterMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalHeightTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTruncationTail

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The triadic scale realising a diameter threshold -/

/-- The triadic scale attached to a diameter threshold. -/
def asdScaleOf (R : ℝ) : ℕ := Nat.log 3 ⌊R⌋₊ - 1

private theorem one_le_log_floor {R : ℝ} (hR : 3 ≤ R) : 1 ≤ Nat.log 3 ⌊R⌋₊ := by
  have h3 : (3 : ℕ) ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR)
  exact (Nat.le_log_iff_pow_le (b := 3) (by norm_num) (x := 1) (y := ⌊R⌋₊)
    (by omega)).mpr (by simpa using h3)

theorem asdScaleOf_succ {R : ℝ} (hR : 3 ≤ R) :
    asdScaleOf R + 1 = Nat.log 3 ⌊R⌋₊ :=
  Nat.sub_add_cancel (one_le_log_floor hR)

theorem three_pow_succ_asdScaleOf_le {R : ℝ} (hR : 3 ≤ R) :
    ((3 ^ (asdScaleOf R + 1) : ℕ) : ℝ) ≤ R := by
  have h3 : (3 : ℕ) ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR)
  have hp : (3 : ℕ) ^ Nat.log 3 ⌊R⌋₊ ≤ ⌊R⌋₊ := Nat.pow_log_le_self 3 (by omega)
  have hc : ((3 ^ (asdScaleOf R + 1) : ℕ) : ℝ) ≤ ((⌊R⌋₊ : ℕ) : ℝ) := by
    rw [asdScaleOf_succ hR]
    exact_mod_cast hp
  exact hc.trans (Nat.floor_le (by linarith))

theorem le_nine_mul_three_pow_asdScaleOf {R : ℝ} (hR : 3 ≤ R) :
    R ≤ 9 * ((3 ^ asdScaleOf R : ℕ) : ℝ) := by
  have h3 : (3 : ℕ) ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR)
  have hlt : ⌊R⌋₊ < 3 ^ (Nat.log 3 ⌊R⌋₊ + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) ⌊R⌋₊
  have hsplit : (3 : ℕ) ^ (Nat.log 3 ⌊R⌋₊ + 1) = 9 * 3 ^ asdScaleOf R := by
    have h1 : Nat.log 3 ⌊R⌋₊ + 1 = asdScaleOf R + 2 := by rw [← asdScaleOf_succ hR]
    rw [h1, pow_add]
    ring
  have hfl : R < (⌊R⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one R
  have hnat : ⌊R⌋₊ + 1 ≤ 9 * 3 ^ asdScaleOf R := by
    have hb : ⌊R⌋₊ < 9 * 3 ^ asdScaleOf R := by rw [← hsplit]; exact hlt
    omega
  have hcast : ((⌊R⌋₊ : ℕ) : ℝ) + 1 ≤ 9 * ((3 ^ asdScaleOf R : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- The crossing gain at the scale attached to `R` is at least `√R / 3`. -/
theorem sqrt_div_three_le_rpow_asdScaleOf {R : ℝ} (hR : 3 ≤ R) :
    Real.sqrt R / 3 ≤ (3 : ℝ) ^ ((1 : ℝ) / 2 * (asdScaleOf R : ℝ)) := by
  have hk : ((3 ^ asdScaleOf R : ℕ) : ℝ) = (3 : ℝ) ^ (asdScaleOf R) := by
    push_cast
    ring
  have hrpow : (3 : ℝ) ^ ((1 : ℝ) / 2 * (asdScaleOf R : ℝ)) =
      Real.sqrt ((3 : ℝ) ^ (asdScaleOf R)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (3 : ℝ) (asdScaleOf R),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  rw [hrpow]
  have h9 : R ≤ 9 * (3 : ℝ) ^ (asdScaleOf R) := by
    rw [← hk]
    exact le_nine_mul_three_pow_asdScaleOf hR
  have hs : Real.sqrt R ≤ Real.sqrt (9 * (3 : ℝ) ^ (asdScaleOf R)) := Real.sqrt_le_sqrt h9
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 9)] at hs
  have h3 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
  rw [h3] at hs
  linarith

/-! ## The entropy/decay balance -/

/-- **The entropy/decay balance.**  The `(2 m + 1) ^ dim` centres of the union
bound over `B_m(z)` are beaten by the `(2 + m) ^ (-alpha)` gain of the crossing
estimate as soon as `alpha` exceeds `2 dim + 2`, with a summable remainder. -/
theorem entropy_decay (dim m : ℕ) {alpha : ℝ}
    (halpha : ((2 * dim + 2 : ℕ) : ℝ) ≤ alpha) :
    (((2 * m + 1) ^ dim : ℕ) : ℝ) * Real.exp (-(alpha * Real.log (2 + (m : ℝ)))) ≤
      1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  set P : ℝ := 2 + (m : ℝ) with hPdef
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hP2 : (2 : ℝ) ≤ P := by rw [hPdef]; linarith [hm]
  have hPpos : 0 < P := by rw [hPdef]; positivity
  have hPnn : 0 ≤ P := by linarith [hP2]
  have hlog : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hstep1 : Real.exp (-(alpha * Real.log P)) ≤
      Real.exp (-(((2 * dim + 2 : ℕ) : ℝ) * Real.log P)) :=
    Real.exp_le_exp.mpr (by nlinarith [halpha, hlog])
  have hexp : Real.exp (((2 * dim + 2 : ℕ) : ℝ) * Real.log P) = P ^ (2 * dim + 2) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hPpos, Real.rpow_natCast]
  have hstep2 : Real.exp (-(((2 * dim + 2 : ℕ) : ℝ) * Real.log P)) = 1 / P ^ (2 * dim + 2) := by
    rw [Real.exp_neg, hexp, inv_eq_one_div]
  have hE1 : Real.exp (-(alpha * Real.log P)) ≤ 1 / P ^ (2 * dim + 2) := by
    rw [← hstep2]; exact hstep1
  have hA : (((2 * m + 1) ^ dim : ℕ) : ℝ) ≤ (2 : ℝ) ^ dim * P ^ dim := by
    have h1 : ((2 * m + 1) ^ dim : ℕ) ≤ (2 * (m + 1)) ^ dim := Nat.pow_le_pow_left (by omega) dim
    have h2 : (((2 * (m + 1)) ^ dim : ℕ) : ℝ) = (2 : ℝ) ^ dim * (((m : ℝ) + 1) ^ dim) := by
      push_cast; rw [mul_pow]
    calc (((2 * m + 1) ^ dim : ℕ) : ℝ) ≤ (((2 * (m + 1)) ^ dim : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (2 : ℝ) ^ dim * (((m : ℝ) + 1) ^ dim) := h2
      _ ≤ (2 : ℝ) ^ dim * P ^ dim :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by rw [hPdef]; linarith) dim) (by positivity)
  have hPd : (2 : ℝ) ^ dim ≤ P ^ dim := pow_le_pow_left₀ (by norm_num) hP2 dim
  have hPdnn : (0 : ℝ) ≤ P ^ dim := pow_nonneg hPnn dim
  have hfac : P ^ (2 * dim + 2) = P ^ dim * (P ^ dim * P ^ 2) := by
    rw [show (2 * dim + 2 : ℕ) = dim + (dim + 2) by omega, pow_add, pow_add]
  have hsq : ((m : ℝ) + 1) * ((m : ℝ) + 2) ≤ P ^ 2 := by
    rw [hPdef]; nlinarith [hm]
  have key : (2 : ℝ) ^ dim * (((m : ℝ) + 1) * ((m : ℝ) + 2)) ≤ P ^ dim * P ^ 2 := by
    nlinarith [hPd, hsq, show (0 : ℝ) ≤ (2 : ℝ) ^ dim by positivity,
      show (0 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) by positivity]
  have hbp : 0 < P ^ dim * (P ^ dim * P ^ 2) :=
    mul_pos (pow_pos hPpos dim) (mul_pos (pow_pos hPpos dim) (pow_pos hPpos 2))
  have hdp : 0 < ((m : ℝ) + 1) * ((m : ℝ) + 2) := by positivity
  calc (((2 * m + 1) ^ dim : ℕ) : ℝ) * Real.exp (-(alpha * Real.log P))
      ≤ (2 : ℝ) ^ dim * P ^ dim * (1 / P ^ (2 * dim + 2)) :=
        mul_le_mul hA hE1 (by positivity) (by positivity)
    _ ≤ 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
        rw [hfac, mul_one_div, div_le_div_iff₀ hbp hdp]
        nlinarith [key, hPdnn]
/-! ## The constants of the minimal scale -/

/-- The `q`-free half of the site-family rate. -/
def asdKappa (Cbox Cdep : ℕ) (cprob : ℝ) : ℝ :=
  cprob / 2 * (3 : ℝ) ^ (-((3 : ℝ) * (asdShift Cbox Cdep : ℝ) / 2))

theorem asdKappa_pos (Cbox Cdep : ℕ) {cprob : ℝ} (h : 0 < cprob) :
    0 < asdKappa Cbox Cdep cprob :=
  mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _)

theorem asdRate_eq_mul (Cbox Cdep : ℕ) (cprob q : ℝ) :
    asdRate Cbox Cdep cprob q = q * asdKappa Cbox Cdep cprob := by
  rw [asdRate, asdKappa]
  ring

/-- The exponential rate, per unit of `q`, of the minimal-scale tail. -/
def asdAlpha (Cbox Cdep : ℕ) (cprob C : ℝ) : ℝ :=
  Real.exp (-(80 : ℝ)) * asdKappa Cbox Cdep cprob * Real.sqrt C / 6

/-! ## The dyadic radius family -/

/-- The diameter threshold of clause (ii) at level `h` and integer radius `m`. -/
def asdBadRadius (C q : ℝ) (h m : ℕ) : ℝ :=
  C * (1 + (h : ℝ) + q⁻¹ * Real.log (2 + (m : ℝ))) ^ 2

theorem one_le_asdLambda {q : ℝ} (hq : 0 < q) (h m : ℕ) :
    1 ≤ 1 + (h : ℝ) + q⁻¹ * Real.log (2 + (m : ℝ)) := by
  have h1 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h2 : 0 ≤ Real.log (2 + (m : ℝ)) := Real.log_nonneg (by linarith)
  have h3 : 0 ≤ q⁻¹ * Real.log (2 + (m : ℝ)) :=
    mul_nonneg (inv_nonneg.mpr hq.le) h2
  linarith

theorem three_le_asdBadRadius {C q : ℝ} (hC : 3 ≤ C) (hq : 0 < q) (h m : ℕ) :
    3 ≤ asdBadRadius C q h m := by
  have hL := one_le_asdLambda hq h m
  have hsq : (1 : ℝ) ≤ (1 + (h : ℝ) + q⁻¹ * Real.log (2 + (m : ℝ))) ^ 2 := by
    nlinarith
  rw [asdBadRadius]
  nlinarith

theorem sqrt_asdBadRadius {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (h m : ℕ) :
    Real.sqrt (asdBadRadius C q h m) =
      Real.sqrt C * (1 + (h : ℝ) + q⁻¹ * Real.log (2 + (m : ℝ))) := by
  rw [asdBadRadius, Real.sqrt_mul hC,
    Real.sqrt_sq (by linarith [one_le_asdLambda hq h m])]

theorem asdBadRadius_mono {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q) {h h' : ℕ}
    (hh : h ≤ h') (m : ℕ) : asdBadRadius C q h m ≤ asdBadRadius C q h' m := by
  have hcast : (h : ℝ) ≤ (h' : ℝ) := by exact_mod_cast hh
  have hL := one_le_asdLambda hq h m
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2) hC

/-! ## The measure of one failure event -/

/-- **The `[ASD]` failure estimate at one integer radius.**  The crossing bound of
`Section9ChemicalASDSiteFamily`, summed over the `(2m+1)^d` centres of `B_m(z)`
and balanced against the `(2+m)^{-alpha}` gain. -/
theorem measure_badComponentFailureEvent_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} {Cbox Cdep : ℕ}
    (hdim : 1 ≤ d) (hCbox : 1 ≤ Cbox)
    {Cprob cprob q C : ℝ} (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hq : 0 < q)
    (hC3 : 3 ≤ C)
    (hth1 : Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob) ≤ cprob * q / 2)
    (hth2 : (d : ℝ) * Real.log 3 ≤ cprob * q / 2)
    (hgate : 16 * (d : ℝ) * Real.exp 80 ≤ asdRate Cbox Cdep cprob q / 2)
    (halpha : ((2 * d + 2 : ℕ) : ℝ) ≤ asdAlpha Cbox Cdep cprob C)
    (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (z : Lattice d) (hh m : ℕ) :
    mu (badComponentFailureEvent E Cbox 1 z (m : ℝ) (asdBadRadius C q hh m)) ≤
      ENNReal.ofReal (Real.exp (-(asdAlpha Cbox Cdep cprob C * q * (1 + (hh : ℝ)))) *
        (1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))) := by
  have hApos : 0 < cprob * q := mul_pos hcprob hq
  have hRpos : 0 < asdRate Cbox Cdep cprob q := asdRate_pos Cbox Cdep hApos
  have hR3 : 3 ≤ asdBadRadius C q hh m := three_le_asdBadRadius hC3 hq hh m
  set k : ℕ := asdScaleOf (asdBadRadius C q hh m) with hk
  set Λ : ℝ := 1 + (hh : ℝ) + q⁻¹ * Real.log (2 + (m : ℝ)) with hΛ
  have hΛ1 : 1 ≤ Λ := one_le_asdLambda hq hh m
  -- step 1: the union bound over the centres of `B_m(z)`
  have hstep1 : mu (badComponentFailureEvent E Cbox 1 z (m : ℝ) (asdBadRadius C q hh m)) ≤
      ((((2 * m + 1) ^ d : ℕ)) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(Real.exp (-(80 : ℝ)) * asdRate Cbox Cdep cprob q *
          (3 : ℝ) ^ ((1 : ℝ) / 2 * (k : ℝ)) / 2))) := by
    refine (measure_mono (badComponentFailureEvent_subset_iUnion_crossing
      (E := E) (Cbox := Cbox) (Cdep := Cdep) (k := k) (m := m)
      (three_pow_succ_asdScaleOf_le hR3) z)).trans ?_
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun v _ => measure_crossingEvent₂At_asdSiteEvent_le mu
      hdim hCbox hCprob hApos hth1 hth2 hgate hE hsc hr hprob k v).trans ?_
    rw [Finset.sum_const, card_latticeBallFinset, nsmul_eq_mul]
  refine hstep1.trans ?_
  -- step 2: the scalar comparison
  have hgain : Real.sqrt (asdBadRadius C q hh m) / 3 ≤ (3 : ℝ) ^ ((1 : ℝ) / 2 * (k : ℝ)) :=
    sqrt_div_three_le_rpow_asdScaleOf hR3
  have hsqrtR : Real.sqrt (asdBadRadius C q hh m) = Real.sqrt C * Λ :=
    sqrt_asdBadRadius (by linarith) hq hh m
  have hexpo : asdAlpha Cbox Cdep cprob C * q * Λ ≤
      Real.exp (-(80 : ℝ)) * asdRate Cbox Cdep cprob q *
        (3 : ℝ) ^ ((1 : ℝ) / 2 * (k : ℝ)) / 2 := by
    have hgamma : (0 : ℝ) < Real.exp (-(80 : ℝ)) := Real.exp_pos _
    have hprod : (0 : ℝ) < Real.exp (-(80 : ℝ)) * asdRate Cbox Cdep cprob q :=
      mul_pos hgamma hRpos
    have hstep : Real.exp (-(80 : ℝ)) * asdRate Cbox Cdep cprob q *
        (Real.sqrt C * Λ / 3) / 2 ≤
        Real.exp (-(80 : ℝ)) * asdRate Cbox Cdep cprob q *
          (3 : ℝ) ^ ((1 : ℝ) / 2 * (k : ℝ)) / 2 := by
      rw [hsqrtR] at hgain
      have := mul_le_mul_of_nonneg_left hgain hprod.le
      linarith
    refine le_trans (le_of_eq ?_) hstep
    rw [asdAlpha, asdRate_eq_mul]
    ring
  have hsplit : asdAlpha Cbox Cdep cprob C * q * Λ =
      asdAlpha Cbox Cdep cprob C * q * (1 + (hh : ℝ)) +
        asdAlpha Cbox Cdep cprob C * Real.log (2 + (m : ℝ)) := by
    rw [hΛ]
    field_simp
  have hreal : (((2 * m + 1) ^ d : ℕ) : ℝ) *
      Real.exp (-(Real.exp (-(80 : ℝ)) * asdRate Cbox Cdep cprob q *
        (3 : ℝ) ^ ((1 : ℝ) / 2 * (k : ℝ)) / 2)) ≤
      Real.exp (-(asdAlpha Cbox Cdep cprob C * q * (1 + (hh : ℝ)))) *
        (1 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) := by
    have h1 : Real.exp (-(Real.exp (-(80 : ℝ)) * asdRate Cbox Cdep cprob q *
        (3 : ℝ) ^ ((1 : ℝ) / 2 * (k : ℝ)) / 2)) ≤
        Real.exp (-(asdAlpha Cbox Cdep cprob C * q * Λ)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(asdAlpha Cbox Cdep cprob C * q * Λ)) =
        Real.exp (-(asdAlpha Cbox Cdep cprob C * q * (1 + (hh : ℝ)))) *
          Real.exp (-(asdAlpha Cbox Cdep cprob C * Real.log (2 + (m : ℝ)))) := by
      rw [← Real.exp_add, hsplit]
      congr 1
      ring
    have h3 := entropy_decay d m halpha
    calc (((2 * m + 1) ^ d : ℕ) : ℝ) *
          Real.exp (-(Real.exp (-(80 : ℝ)) * asdRate Cbox Cdep cprob q *
            (3 : ℝ) ^ ((1 : ℝ) / 2 * (k : ℝ)) / 2))
        ≤ (((2 * m + 1) ^ d : ℕ) : ℝ) * Real.exp (-(asdAlpha Cbox Cdep cprob C * q * Λ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.exp (-(asdAlpha Cbox Cdep cprob C * q * (1 + (hh : ℝ)))) *
            ((((2 * m + 1) ^ d : ℕ) : ℝ) *
              Real.exp (-(asdAlpha Cbox Cdep cprob C * Real.log (2 + (m : ℝ))))) := by
          rw [h2]; ring
      _ ≤ Real.exp (-(asdAlpha Cbox Cdep cprob C * q * (1 + (hh : ℝ)))) *
            (1 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ## The failure event at one level -/

theorem badComponentFailureEvent_antitone (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ)
    (z : Lattice d) (s : ℝ) {R R' : ℝ} (hR : R ≤ R') :
    badComponentFailureEvent E Cbox J z s R' ⊆ badComponentFailureEvent E Cbox J z s R := by
  rintro ω ⟨v, hv, hbad, hdiam⟩
  refine ⟨v, hv, hbad, fun hcon => hdiam ?_⟩
  exact fun a ha b hb i => (hcon a ha b hb i).trans hR

/-- The union over all integer radii of the `[ASD]` failure events at level `h`. -/
def asdDiameterFailure (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (C q : ℝ)
    (z : Lattice d) (h : ℕ) : Set Ω :=
  ⋃ m : ℕ, badComponentFailureEvent E Cbox 1 z (m : ℝ) (asdBadRadius C q h m)

theorem asdDiameterFailure_antitone {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {C q : ℝ}
    (hC : 0 ≤ C) (hq : 0 < q) (z : Lattice d) {h h' : ℕ} (hh : h ≤ h') :
    asdDiameterFailure E Cbox C q z h' ⊆ asdDiameterFailure E Cbox C q z h :=
  Set.iUnion_mono fun m =>
    badComponentFailureEvent_antitone E Cbox 1 z (m : ℝ) (asdBadRadius_mono hC hq hh m)

theorem measurableSet_asdDiameterFailure [MeasurableSpace Ω]
    {E : ℕ → Lattice d → Set Ω} (hE : ∀ j z, MeasurableSet (E j z)) (Cbox : ℕ)
    (C q : ℝ) (z : Lattice d) (h : ℕ) :
    MeasurableSet (asdDiameterFailure E Cbox C q z h) :=
  MeasurableSet.iUnion fun m =>
    measurableSet_badComponentFailureEvent hE Cbox 1 z (m : ℝ) (asdBadRadius C q h m)

/-! ## The summable remainder -/

private theorem tele_sum (N : ℕ) :
    ∑ m ∈ Finset.range N, (1 : ℝ) / ((m + 1) * (m + 2)) = 1 - 1 / (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

private theorem tele_nonneg (m : ℕ) : (0 : ℝ) ≤ 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  positivity

private theorem tele_partial (N : ℕ) :
    ∑ m ∈ Finset.range N, (1 : ℝ) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) ≤ 1 := by
  rw [tele_sum N]
  have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  linarith

private theorem tele_summable :
    Summable fun m : ℕ => (1 : ℝ) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
  summable_of_sum_range_le tele_nonneg tele_partial

private theorem tele_tsum :
    ∑' m : ℕ, (1 : ℝ) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) ≤ 1 :=
  Real.tsum_le_of_sum_range_le tele_nonneg tele_partial

/-! ## The measure of the level failure event -/

/-- **The level-`h` failure event has probability at most `exp (-(alpha q (1+h)))`.** -/
theorem measure_asdDiameterFailure_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} {Cbox Cdep : ℕ}
    (hdim : 1 ≤ d) (hCbox : 1 ≤ Cbox)
    {Cprob cprob q C : ℝ} (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hq : 0 < q)
    (hC3 : 3 ≤ C)
    (hth1 : Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob) ≤ cprob * q / 2)
    (hth2 : (d : ℝ) * Real.log 3 ≤ cprob * q / 2)
    (hgate : 16 * (d : ℝ) * Real.exp 80 ≤ asdRate Cbox Cdep cprob q / 2)
    (halpha : ((2 * d + 2 : ℕ) : ℝ) ≤ asdAlpha Cbox Cdep cprob C)
    (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (z : Lattice d) (hh : ℕ) :
    mu (asdDiameterFailure E Cbox C q z hh) ≤
      ENNReal.ofReal (Real.exp (-(asdAlpha Cbox Cdep cprob C * q * (1 + (hh : ℝ))))) := by
  set c : ℝ := Real.exp (-(asdAlpha Cbox Cdep cprob C * q * (1 + (hh : ℝ)))) with hc
  have hcpos : 0 < c := Real.exp_pos _
  have hnn : ∀ m : ℕ, (0 : ℝ) ≤ c * (1 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) := fun m => by
    have := tele_nonneg m
    positivity
  calc mu (asdDiameterFailure E Cbox C q z hh)
      ≤ ∑' m : ℕ, mu (badComponentFailureEvent E Cbox 1 z (m : ℝ) (asdBadRadius C q hh m)) :=
        measure_iUnion_le _
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (c * (1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))) :=
        ENNReal.tsum_le_tsum fun m => measure_badComponentFailureEvent_le mu hdim hCbox
          hCprob hcprob hq hC3 hth1 hth2 hgate halpha hE hsc hr hprob z hh m
    _ = ENNReal.ofReal (∑' m : ℕ, c * (1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))) :=
        (ENNReal.ofReal_tsum_of_nonneg hnn (tele_summable.mul_left c)).symm
    _ ≤ ENNReal.ofReal c := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left]
        nlinarith [tele_tsum, hcpos]

/-! ## The minimal scale and its measurability -/

/-- The set of levels above which no `[ASD]` failure occurs at `z`. -/
def asdHeightSet (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (C q : ℝ) (z : Lattice d)
    (ω : Ω) : Set ℕ := {h | ω ∉ asdDiameterFailure E Cbox C q z h}

/-- The manuscript's minimal scale `H₁(z)`, as a least upward-closed threshold. -/
def asdMinScale (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (C q : ℝ) (z : Lattice d)
    (ω : Ω) : ℕ := sInf (asdHeightSet E Cbox C q z ω)

/-- The clause-(ii) witness: the minimal scale, kept at least `1`. -/
def asdComponent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (C q : ℝ) (z : Lattice d)
    (ω : Ω) : ℕ := max 1 (asdMinScale E Cbox C q z ω)

theorem one_le_asdComponent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (C q : ℝ)
    (z : Lattice d) (ω : Ω) : 1 ≤ asdComponent E Cbox C q z ω := le_max_left _ _

theorem asdHeightSet_upward {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {C q : ℝ}
    (hC : 0 ≤ C) (hq : 0 < q) {z : Lattice d} {ω : Ω} {h h' : ℕ}
    (hmem : h ∈ asdHeightSet E Cbox C q z ω) (hle : h ≤ h') :
    h' ∈ asdHeightSet E Cbox C q z ω :=
  fun hcon => hmem (asdDiameterFailure_antitone hC hq z hle hcon)

theorem not_mem_asdDiameterFailure_asdComponent {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q) {z : Lattice d} {ω : Ω}
    (hne : (asdHeightSet E Cbox C q z ω).Nonempty) :
    ω ∉ asdDiameterFailure E Cbox C q z (asdComponent E Cbox C q z ω) :=
  asdHeightSet_upward hC hq (Nat.sInf_mem hne) (le_max_right _ _)

/-- **Clause (ii) at every sample where the minimal scale is defined.** -/
theorem badComponentDiameterBound_asdComponent {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q) {z : Lattice d} {ω : Ω}
    (hne : (asdHeightSet E Cbox C q z ω).Nonempty) :
    BadComponentDiameterBound E Cbox 1 ω z (4 * C) q (asdComponent E Cbox C q z ω) := by
  refine badComponentDiameterBound_of_natRadius hC hq fun m => ?_
  intro hmem
  exact not_mem_asdDiameterFailure_asdComponent hC hq hne (Set.mem_iUnion.mpr ⟨m, hmem⟩)

theorem measurable_asdMinScale [MeasurableSpace Ω] {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox : ℕ) {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q)
    (z : Lattice d) : Measurable (asdMinScale E Cbox C q z) := by
  classical
  refine measurable_to_countable' fun j => ?_
  show MeasurableSet {ω | asdMinScale E Cbox C q z ω = j}
  rcases j with _ | j
  · have heq : {ω : Ω | asdMinScale E Cbox C q z ω = 0} =
        (asdDiameterFailure E Cbox C q z 0)ᶜ ∪
          ⋂ h : ℕ, asdDiameterFailure E Cbox C q z h := by
      ext ω
      simp only [asdMinScale, Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff,
        Set.mem_iInter]
      rw [Nat.sInf_eq_zero]
      constructor
      · rintro (h0 | hempty)
        · exact Or.inl h0
        · refine Or.inr fun h => ?_
          by_contra hcon
          exact (Set.eq_empty_iff_forall_notMem.mp hempty) h hcon
      · rintro (h0 | hall)
        · exact Or.inl h0
        · refine Or.inr (Set.eq_empty_iff_forall_notMem.mpr fun h hh => ?_)
          exact hh (hall h)
    rw [heq]
    exact (measurableSet_asdDiameterFailure hE Cbox C q z 0).compl.union
      (MeasurableSet.iInter fun h => measurableSet_asdDiameterFailure hE Cbox C q z h)
  · have heq : {ω : Ω | asdMinScale E Cbox C q z ω = j + 1} =
        (asdDiameterFailure E Cbox C q z (j + 1))ᶜ ∩
          asdDiameterFailure E Cbox C q z j := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · intro hval
        have hne : (asdHeightSet E Cbox C q z ω).Nonempty := by
          by_contra hcon
          rw [Set.not_nonempty_iff_eq_empty] at hcon
          simp only [asdMinScale, hcon, Nat.sInf_empty] at hval
          omega
        have hmem : asdMinScale E Cbox C q z ω ∈ asdHeightSet E Cbox C q z ω :=
          Nat.sInf_mem hne
        rw [hval] at hmem
        refine ⟨hmem, ?_⟩
        by_contra hcon
        have hjmem : j ∈ asdHeightSet E Cbox C q z ω := hcon
        have hsle := Nat.sInf_le hjmem
        have hval' : sInf (asdHeightSet E Cbox C q z ω) = j + 1 := hval
        omega
      · rintro ⟨h1, h2⟩
        have hmem : j + 1 ∈ asdHeightSet E Cbox C q z ω := h1
        have hle : asdMinScale E Cbox C q z ω ≤ j + 1 := Nat.sInf_le hmem
        have hne : (asdHeightSet E Cbox C q z ω).Nonempty := ⟨j + 1, hmem⟩
        by_contra hcon
        have hlt : asdMinScale E Cbox C q z ω ≤ j := by omega
        exact (asdHeightSet_upward hC hq (Nat.sInf_mem hne) hlt) h2
    rw [heq]
    exact (measurableSet_asdDiameterFailure hE Cbox C q z (j + 1)).compl.inter
      (measurableSet_asdDiameterFailure hE Cbox C q z j)

/-! ## The geometric tail of the minimal scale -/

theorem measure_asdMinScale_ge_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} {Cbox Cdep : ℕ}
    (hdim : 1 ≤ d) (hCbox : 1 ≤ Cbox)
    {Cprob cprob q C : ℝ} (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hq : 0 < q)
    (hC3 : 3 ≤ C)
    (hth1 : Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob) ≤ cprob * q / 2)
    (hth2 : (d : ℝ) * Real.log 3 ≤ cprob * q / 2)
    (hgate : 16 * (d : ℝ) * Real.exp 80 ≤ asdRate Cbox Cdep cprob q / 2)
    (halpha : ((2 * d + 2 : ℕ) : ℝ) ≤ asdAlpha Cbox Cdep cprob C)
    (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (z : Lattice d) (k : ℕ) :
    mu {ω | k ≤ asdMinScale E Cbox C q z ω} ≤
      ENNReal.ofReal (Real.exp (-(asdAlpha Cbox Cdep cprob C * q))) ^ k := by
  rcases k with _ | j
  · simp
  · have hsub : {ω | j + 1 ≤ asdMinScale E Cbox C q z ω} ⊆
        asdDiameterFailure E Cbox C q z j := by
      intro ω hω
      by_contra hcon
      have hjmem : j ∈ asdHeightSet E Cbox C q z ω := hcon
      have hsle := Nat.sInf_le hjmem
      have hω' : j + 1 ≤ sInf (asdHeightSet E Cbox C q z ω) := hω
      omega
    refine (measure_mono hsub).trans ?_
    refine (measure_asdDiameterFailure_le mu hdim hCbox hCprob hcprob hq hC3 hth1 hth2
      hgate halpha hE hsc hr hprob z j).trans ?_
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring

/-- Two observables with the same positive part carry the same `O_{Γ_σ}` bound. -/
theorem ogammaLE_of_max_eq [MeasurableSpace Ω] {mu : Measure Ω} {sigma A : ℝ}
    {X Y : Ω → ℝ} (h : ∀ ω, max (X ω) 0 = max (Y ω) 0)
    (hY : SubdiffusiveProcess.OGammaLE mu sigma A Y) : SubdiffusiveProcess.OGammaLE mu sigma A X := by
  unfold SubdiffusiveProcess.OGammaLE at hY ⊢
  simpa only [h] using hY

theorem max_asdComponent_eq (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (C q : ℝ)
    (z : Lattice d) (ω : Ω) :
    max ((asdComponent E Cbox C q z ω : ℝ) - 1) 0 =
      max ((asdMinScale E Cbox C q z ω : ℝ) - 1) 0 := by
  rcases Nat.eq_zero_or_pos (asdMinScale E Cbox C q z ω) with h0 | hpos
  · rw [asdComponent, h0]
    norm_num
  · have hmax : max 1 (asdMinScale E Cbox C q z ω) = asdMinScale E Cbox C q z ω :=
      max_eq_right hpos
    rw [asdComponent, hmax]

/-- **The `O_{Γ₁}(C / q)` tail of the clause-(ii) witness.** -/
theorem ogammaLE_asdComponent [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} {Cbox Cdep : ℕ}
    (hdim : 1 ≤ d) (hCbox : 1 ≤ Cbox)
    {Cprob cprob q C : ℝ} (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hq : 0 < q)
    (hC3 : 3 ≤ C)
    (hth1 : Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob) ≤ cprob * q / 2)
    (hth2 : (d : ℝ) * Real.log 3 ≤ cprob * q / 2)
    (hgate : 16 * (d : ℝ) * Real.exp 80 ≤ asdRate Cbox Cdep cprob q / 2)
    (halpha : ((2 * d + 2 : ℕ) : ℝ) ≤ asdAlpha Cbox Cdep cprob C)
    (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (z : Lattice d) :
    SubdiffusiveProcess.OGammaLE mu 1 (4 / asdAlpha Cbox Cdep cprob C / q)
      (fun ω => (asdComponent E Cbox C q z ω : ℝ) - 1) := by
  have hCpos : (0 : ℝ) < C := by linarith
  have halphapos : 0 < asdAlpha Cbox Cdep cprob C := by
    have : (0 : ℝ) < ((2 * d + 2 : ℕ) : ℝ) := by positivity
    linarith
  set r : ℝ := asdAlpha Cbox Cdep cprob C * q with hrdef
  have hrpos : 0 < r := mul_pos halphapos hq
  set theta : ENNReal := ENNReal.ofReal (Real.exp (-r)) with hthetadef
  have hthetapos : 0 < theta := by
    rw [hthetadef, ENNReal.ofReal_pos]
    exact Real.exp_pos _
  have hthetalt : theta < 1 := by
    rw [hthetadef, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
      (Real.exp_lt_one_iff.mpr (by linarith))
  have htail : ∀ k : ℕ, 0 ≤ k →
      mu {ω | k ≤ asdMinScale E Cbox C q z ω} ≤ 1 * theta ^ k := by
    intro k _
    rw [one_mul, hthetadef]
    exact measure_asdMinScale_ge_le mu hdim hCbox hCprob hcprob hq hC3 hth1 hth2
      hgate halpha hE hsc hr hprob z k
  have hbridge := Section8Resolvent.ogammaLE_of_geometric_tail (mu := mu)
    (measurable_asdMinScale hE Cbox (by linarith) hq z) (C := 1) (theta := theta)
    (by simp) hthetapos hthetalt 0 htail
  rw [stoppingTailRate_ofReal_exp_neg] at hbridge
  have hcentre : Section8Resolvent.stoppingTailCenter 1 theta 0 = Real.log 3 := by
    simp [Section8Resolvent.stoppingTailCenter, Section8Resolvent.stoppingTailCenterBracket]
  rw [hcentre] at hbridge
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hres := ogammaLE_one_rescale (mu := mu) hlog3 hbridge
  rw [div_self (ne_of_gt hlog3)] at hres
  have hamp : Section8Resolvent.stoppingTailGammaOneConstant * Real.log 3 / r /
      Real.log 3 = 4 / asdAlpha Cbox Cdep cprob C / q := by
    rw [Section8Resolvent.stoppingTailGammaOneConstant, hrdef]
    field_simp
  rw [hamp] at hres
  exact ogammaLE_of_max_eq (max_asdComponent_eq E Cbox C q z) hres

/-! ## Clause (ii) for the concrete field -/

/-- **The minimal scale is almost surely defined.** -/
theorem measure_asdHeightSet_not_nonempty_eq_zero [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} {Cbox Cdep : ℕ}
    (hdim : 1 ≤ d) (hCbox : 1 ≤ Cbox)
    {Cprob cprob q C : ℝ} (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hq : 0 < q)
    (hC3 : 3 ≤ C)
    (hth1 : Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob) ≤ cprob * q / 2)
    (hth2 : (d : ℝ) * Real.log 3 ≤ cprob * q / 2)
    (hgate : 16 * (d : ℝ) * Real.exp 80 ≤ asdRate Cbox Cdep cprob q / 2)
    (halpha : ((2 * d + 2 : ℕ) : ℝ) ≤ asdAlpha Cbox Cdep cprob C)
    (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (z : Lattice d) :
    mu {ω | ¬ (asdHeightSet E Cbox C q z ω).Nonempty} = 0 := by
  have halphapos : 0 < asdAlpha Cbox Cdep cprob C := by
    have : (0 : ℝ) < ((2 * d + 2 : ℕ) : ℝ) := by positivity
    linarith
  set r : ℝ := asdAlpha Cbox Cdep cprob C * q with hrdef
  have hrpos : 0 < r := mul_pos halphapos hq
  have hset : {ω : Ω | ¬ (asdHeightSet E Cbox C q z ω).Nonempty} =
      ⋂ h : ℕ, asdDiameterFailure E Cbox C q z h := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.not_nonempty_iff_eq_empty, Set.mem_iInter]
    constructor
    · intro hempty h
      by_contra hcon
      exact (Set.eq_empty_iff_forall_notMem.mp hempty) h hcon
    · intro hall
      exact Set.eq_empty_iff_forall_notMem.mpr fun h hh => hh (hall h)
  rw [hset]
  refine measure_eq_zero_of_le_geometric mu _ (Cf := Real.exp (-r)) hrpos fun h => ?_
  refine (measure_mono (Set.iInter_subset _ h)).trans ?_
  refine (measure_asdDiameterFailure_le mu hdim hCbox hCprob hcprob hq hC3 hth1 hth2
    hgate halpha hE hsc hr hprob z h).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hexp : Real.exp (-(r * (1 + (h : ℝ)))) = Real.exp (-r) * Real.exp (-(r * h)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hd1 : 0 < 1 - Real.exp (-r) := by
    have hlt : Real.exp (-r) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hd2 : 1 - Real.exp (-r) ≤ 1 := by
    have := Real.exp_pos (-r)
    linarith
  rw [hexp, le_div_iff₀ hd1]
  have hX : 0 < Real.exp (-r) * Real.exp (-(r * (h : ℝ))) :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hXe : 0 < (Real.exp (-r) * Real.exp (-(r * (h : ℝ)))) * Real.exp (-r) :=
    mul_pos hX (Real.exp_pos _)
  nlinarith [hXe]

/-- **`[ASD, Lemma B.1(3)]` for the concrete field.**  Clause (ii) of the
multiscale percolation geometry holds almost surely with the witness
`asdComponent`, which is at least `1` and has the printed `O_{Γ₁}(C / q)` tail.

Everything is derived from the field's own hypotheses; no external input is
assumed.  The three explicit thresholds `hth1`, `hth2`, `hgate` and the
constant condition `halpha` do not depend on the field. -/
theorem ae_badComponentDiameterBound_asdComponent [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} {Cbox Cdep : ℕ}
    (hdim : 1 ≤ d) (hCbox : 1 ≤ Cbox)
    {Cprob cprob q C : ℝ} (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hq : 0 < q)
    (hC3 : 3 ≤ C)
    (hth1 : Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob) ≤ cprob * q / 2)
    (hth2 : (d : ℝ) * Real.log 3 ≤ cprob * q / 2)
    (hgate : 16 * (d : ℝ) * Real.exp 80 ≤ asdRate Cbox Cdep cprob q / 2)
    (halpha : ((2 * d + 2 : ℕ) : ℝ) ≤ asdAlpha Cbox Cdep cprob C)
    (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) :
    ∀ᵐ ω ∂mu, ∀ z : Lattice d,
      BadComponentDiameterBound E Cbox 1 ω z (4 * C) q (asdComponent E Cbox C q z ω) := by
  have hCpos : (0 : ℝ) < C := by linarith
  refine ae_all_iff.2 fun z => ?_
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_asdHeightSet_not_nonempty_eq_zero mu hdim hCbox
    hCprob hcprob hq hC3 hth1 hth2 hgate halpha hE hsc hr hprob z)
  intro ω hω hne
  exact hω (badComponentDiameterBound_asdComponent hCpos.le hq hne)

/-- Scale monotonicity of `SubdiffusiveProcess.OGammaLE` at `σ = 1`, for a measurable observable.
(The Section 6 lemma `ogammaLE_mono_scale'` removes the measurability side
condition; here the observable is measurable, so the elementary form suffices
and no Section 6 import is needed.) -/
theorem ogammaLE_mono_scale_one [MeasurableSpace Ω] {mu : Measure Ω} {A B : ℝ}
    {X : Ω → ℝ} (hX : Measurable X) (hA : 0 < A) (hAB : A ≤ B)
    (h : SubdiffusiveProcess.OGammaLE mu 1 A X) : SubdiffusiveProcess.OGammaLE mu 1 B X := by
  obtain ⟨hint, hbound⟩ := h
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hinv : B⁻¹ ≤ A⁻¹ := by
    rw [inv_le_inv₀ hB hA]
    exact hAB
  have hle : ∀ ω, Real.exp ((B⁻¹ * max (X ω) 0) ^ (1 : ℝ)) ≤
      Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ)) := by
    intro ω
    rw [Real.rpow_one, Real.rpow_one]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hinv (le_max_right _ _))
  have hmeas : Measurable (fun ω => Real.exp ((B⁻¹ * max (X ω) 0) ^ (1 : ℝ))) := by
    simp only [Real.rpow_one]
    fun_prop
  have hintB : Integrable (fun ω => Real.exp ((B⁻¹ * max (X ω) 0) ^ (1 : ℝ))) mu := by
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hle ω
  exact ⟨hintB, (integral_mono hintB hint hle).trans hbound⟩

theorem measurable_asdComponentSub [MeasurableSpace Ω] {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox : ℕ) {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q)
    (z : Lattice d) :
    Measurable (fun ω => (asdComponent E Cbox C q z ω : ℝ) - 1) :=
  (measurable_of_countable fun n : ℕ => ((max 1 n : ℕ) : ℝ) - 1).comp
    (measurable_asdMinScale hE Cbox hC hq z)

/-- **The clause-(ii) witness is measurable.**  `asdComponent = max 1 ∘ asdMinScale`, and
every map out of `ℕ` is measurable. -/
theorem measurable_asdComponent [MeasurableSpace Ω] {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox : ℕ) {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q)
    (z : Lattice d) : Measurable (asdComponent E Cbox C q z) :=
  (measurable_of_countable fun n : ℕ => max 1 n).comp
    (measurable_asdMinScale hE Cbox hC hq z)

/-! ## The packaged clause-(ii) datum -/

theorem badComponentDiameterBound_mono {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} {ω : Ω}
    {z : Lattice d} {C C' q : ℝ} {h : ℕ} (hCC : C ≤ C') (_hq : 0 < q)
    (hb : BadComponentDiameterBound E Cbox J ω z C q h) :
    BadComponentDiameterBound E Cbox J ω z C' q h := by
  intro s hs v hv hbad a ha b hb2 i
  refine (hb s hs v hv hbad a ha b hb2 i).trans ?_
  nlinarith [sq_nonneg (1 + (h : ℝ) + q⁻¹ * Real.log (2 + s))]

/-- The geometric constant of clause (ii): large enough that the crossing gain
beats the influence-box entropy of the union bound. -/
def asdGeomBase (dim Cbox Cdep : ℕ) (cprob : ℝ) : ℝ :=
  max 3 ((6 * ((2 * dim + 2 : ℕ) : ℝ) /
    (Real.exp (-(80 : ℝ)) * asdKappa Cbox Cdep cprob)) ^ 2)

theorem three_le_asdGeomBase (dim Cbox Cdep : ℕ) (cprob : ℝ) :
    3 ≤ asdGeomBase dim Cbox Cdep cprob := le_max_left _ _

theorem asdGeomBase_alpha (dim Cbox Cdep : ℕ) {cprob : ℝ} (hcprob : 0 < cprob) :
    ((2 * dim + 2 : ℕ) : ℝ) ≤
      asdAlpha Cbox Cdep cprob (asdGeomBase dim Cbox Cdep cprob) := by
  have hkappa : 0 < asdKappa Cbox Cdep cprob := asdKappa_pos Cbox Cdep hcprob
  have hgamma : (0 : ℝ) < Real.exp (-(80 : ℝ)) := Real.exp_pos _
  have hprod : 0 < Real.exp (-(80 : ℝ)) * asdKappa Cbox Cdep cprob := mul_pos hgamma hkappa
  set y : ℝ := 6 * ((2 * dim + 2 : ℕ) : ℝ) /
    (Real.exp (-(80 : ℝ)) * asdKappa Cbox Cdep cprob) with hy
  have hy0 : 0 ≤ y := by
    rw [hy]
    positivity
  have hsq : Real.sqrt (y ^ 2) = y := Real.sqrt_sq hy0
  have hmono : Real.sqrt (y ^ 2) ≤ Real.sqrt (asdGeomBase dim Cbox Cdep cprob) :=
    Real.sqrt_le_sqrt (le_max_right _ _)
  rw [hsq] at hmono
  have hstep : Real.exp (-(80 : ℝ)) * asdKappa Cbox Cdep cprob * y / 6 =
      ((2 * dim + 2 : ℕ) : ℝ) := by
    rw [hy]
    field_simp
  rw [asdAlpha, ← hstep]
  have := mul_le_mul_of_nonneg_left hmono hprod.le
  linarith

/-- **`[ASD, Lemma B.1(3)]`, packaged for the provider.**

For every dimension `d ≥ 1`, every `Cbox ≥ 1` and every pair `(Cprob, cprob)` of
positive constants there are a natural threshold `q0` and a positive constant
`Cgeom`, both independent of the field, such that every field satisfying the
multiscale-percolation hypotheses at a parameter `q ≥ q0` carries a `ℕ`-valued
minimal scale with

* `1 ≤ component`,
* the printed tail `component - 1 ≤ O_{Γ₁}(Cgeom / q)`,
* clause (ii) at almost every sample.

Nothing external is assumed. -/
theorem exists_asd_clause_two (d Cbox Cdep : ℕ) (Cprob cprob : ℝ)
    (hdim : 1 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 : ℕ, ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ component : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (Cgeom / q)
            (fun omega => (component z omega : ℝ) - 1)) ∧
          (∀ᵐ omega ∂mu, ∀ z : Lattice d,
            BadComponentDiameterBound E Cbox 1 omega z Cgeom q (component z omega)) ∧
          (∀ z, Measurable (component z)) := by
  classical
  set C : ℝ := asdGeomBase d Cbox Cdep cprob with hCdef
  have hC3 : 3 ≤ C := three_le_asdGeomBase d Cbox Cdep cprob
  have halpha : ((2 * d + 2 : ℕ) : ℝ) ≤ asdAlpha Cbox Cdep cprob C :=
    asdGeomBase_alpha d Cbox Cdep hcprob
  have halphapos : 0 < asdAlpha Cbox Cdep cprob C := by
    have : (0 : ℝ) < ((2 * d + 2 : ℕ) : ℝ) := by positivity
    linarith
  have hkappa : 0 < asdKappa Cbox Cdep cprob := asdKappa_pos Cbox Cdep hcprob
  obtain ⟨q1, hq1⟩ := exists_uniform_threshold (c := cprob)
    (X := 2 * Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob)) hcprob
  obtain ⟨q2, hq2⟩ := exists_uniform_threshold (c := cprob)
    (X := 2 * (d : ℝ) * Real.log 3) hcprob
  obtain ⟨q3, hq3⟩ := exists_uniform_threshold (c := asdKappa Cbox Cdep cprob)
    (X := 32 * (d : ℝ) * Real.exp 80) hkappa
  refine ⟨max 1 (max q1 (max q2 q3)),
    max (4 / asdAlpha Cbox Cdep cprob C) (4 * C), ?_, ?_⟩
  · have : (0 : ℝ) < 4 * C := by linarith
    exact lt_of_lt_of_le this (le_max_right _ _)
  intro Omega _ mu _ E q hq hprob hsc hr hlaw
  have hq1' : (q1 : ℝ) ≤ q :=
    le_trans (by exact_mod_cast (Nat.le_max_left q1 _).trans (Nat.le_max_right 1 _)) hq
  have hq2' : (q2 : ℝ) ≤ q :=
    le_trans (by
      exact_mod_cast ((Nat.le_max_left q2 q3).trans (Nat.le_max_right q1 _)).trans
        (Nat.le_max_right 1 _)) hq
  have hq3' : (q3 : ℝ) ≤ q :=
    le_trans (by
      exact_mod_cast ((Nat.le_max_right q2 q3).trans (Nat.le_max_right q1 _)).trans
        (Nat.le_max_right 1 _)) hq
  have hqpos : 0 < q :=
    lt_of_lt_of_le zero_lt_one
      (le_trans (by exact_mod_cast Nat.le_max_left 1 _) hq)
  have hth1 : Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob) ≤ cprob * q / 2 := by
    have := hq1 q hq1'
    linarith
  have hth2 : (d : ℝ) * Real.log 3 ≤ cprob * q / 2 := by
    have := hq2 q hq2'
    linarith
  have hgate : 16 * (d : ℝ) * Real.exp 80 ≤ asdRate Cbox Cdep cprob q / 2 := by
    have h := hq3 q hq3'
    rw [asdRate_eq_mul]
    nlinarith
  refine ⟨asdComponent E Cbox C q, fun z omega => one_le_asdComponent E Cbox C q z omega,
    fun z => ?_, ?_, ?_⟩
  · refine ogammaLE_mono_scale_one
      (measurable_asdComponentSub hlaw.1 Cbox (by linarith) hqpos z)
      (by positivity) ?_
      (ogammaLE_asdComponent mu hdim hCbox hCprob hcprob hqpos hC3 hth1 hth2 hgate
        halpha hlaw.1 hsc hr hprob z)
    exact div_le_div_of_nonneg_right (le_max_left _ _) hqpos.le
  · filter_upwards [ae_badComponentDiameterBound_asdComponent mu hdim hCbox hCprob hcprob
      hqpos hC3 hth1 hth2 hgate halpha hlaw.1 hsc hr hprob] with omega homega
    intro z
    exact badComponentDiameterBound_mono (le_max_right _ _) hqpos (homega z)
  · exact fun z => measurable_asdComponent hlaw.1 Cbox (by linarith) hqpos z

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
