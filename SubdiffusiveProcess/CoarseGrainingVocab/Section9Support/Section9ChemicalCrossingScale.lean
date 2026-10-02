import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingRate




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The constants -/

/-- The number of good vertices the crossing clause asks for at scale `l`. -/
def crossCount (J l : ℕ) : ℕ := l / (12 * J + 12)

/-- The coverage constant of a certificate. -/
def crossAc (Cbox Cdep J : ℕ) : ℝ := 6 * ((Cbox + Cdep : ℕ) : ℝ) + 3 * (J : ℝ)

theorem crossAc_pos {Cbox Cdep J : ℕ} (hCbox : 1 ≤ Cbox) : 0 < crossAc Cbox Cdep J := by
  have h1 : (1 : ℝ) ≤ ((Cbox + Cdep : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have h2 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
  rw [crossAc]; linarith

/-- Half of the per-scale exponential rate. -/
def crossBeta (d : ℕ) (cprob : ℝ) : ℝ := cprob / 2 / 2 ^ d

theorem crossBeta_pos {d : ℕ} {cprob : ℝ} (h : 0 < cprob) : 0 < crossBeta d cprob := by
  rw [crossBeta]; positivity

/-- The rate of the crossing estimate. -/
def crossRate (d Cbox Cdep J : ℕ) (cprob : ℝ) : ℝ :=
  crossBeta d cprob / (4 * crossAc Cbox Cdep J)

theorem crossRate_pos {d Cbox Cdep J : ℕ} {cprob : ℝ} (hc : 0 < cprob)
    (hCbox : 1 ≤ Cbox) : 0 < crossRate d Cbox Cdep J cprob := by
  rw [crossRate]
  have hac : 0 < crossAc Cbox Cdep J := crossAc_pos hCbox
  exact div_pos (crossBeta_pos hc) (by linarith)

/-- The `l`-independent part of the certificate entropy. -/
def crossPolyBase (d Cbox Cdep : ℕ) (Cprob : ℝ) : ℝ :=
  2 ^ d * 2 * (1 + 2 * crossScaleConst d Cbox Cdep Cprob)

/-- The entropy exponent per unit of `l`. -/
def crossEntropy (d Cbox Cdep J : ℕ) (Cprob : ℝ) : ℝ :=
  (d : ℝ) + 3 * Real.log (max 1 (4 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ))) +
    Real.log (max 1 (crossPolyBase d Cbox Cdep Cprob))

theorem crossEntropy_nonneg (d Cbox Cdep J : ℕ) (Cprob : ℝ) :
    0 ≤ crossEntropy d Cbox Cdep J Cprob := by
  rw [crossEntropy]
  have h1 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ Real.log (max 1 (4 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ))) :=
    Real.log_nonneg (le_max_left _ _)
  have h3 : (0 : ℝ) ≤ Real.log (max 1 (crossPolyBase d Cbox Cdep Cprob)) :=
    Real.log_nonneg (le_max_left _ _)
  linarith

/-! ## The entropy is at most `exp (crossEntropy · l)` -/

theorem crossEntropy_bound (d Cbox Cdep J : ℕ) (Cprob : ℝ) {N l : ℕ}
    (hl : 1 ≤ l) (hN : N ≤ l) :
    ((2 ^ d * (l + 1) ^ d : ℕ) : ℝ) * 2 *
        (4 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ)) ^ (N + 2) *
        (1 + 2 * crossScaleConst d Cbox Cdep Cprob) ≤
      Real.exp (crossEntropy d Cbox Cdep J Cprob * (l : ℝ)) := by
  set kr : ℝ := 4 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) with hkr
  set M : ℝ := crossPolyBase d Cbox Cdep Cprob with hM
  have hlR : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  -- the polynomial factor
  have hpoly : ((l + 1 : ℕ) : ℝ) ^ d ≤ Real.exp ((d : ℝ) * (l : ℝ)) := by
    have hlog : Real.log (((l + 1 : ℕ) : ℝ)) ≤ (l : ℝ) := by
      have hpos : (0 : ℝ) < ((l + 1 : ℕ) : ℝ) := by positivity
      have := Real.log_le_sub_one_of_pos hpos
      push_cast at this ⊢
      linarith
    have hbase : (0 : ℝ) < ((l + 1 : ℕ) : ℝ) := by positivity
    calc ((l + 1 : ℕ) : ℝ) ^ d = Real.exp ((d : ℝ) * Real.log (((l + 1 : ℕ) : ℝ))) := by
          rw [← Real.rpow_natCast (((l + 1 : ℕ) : ℝ)) d, Real.rpow_def_of_pos hbase]
          congr 1
          ring
      _ ≤ Real.exp ((d : ℝ) * (l : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
          nlinarith
  -- the good-budget factor
  have hkrpos : (0 : ℝ) < kr := by
    rw [hkr]
    have : (0 : ℝ) < ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) := by
      have : 0 < 2 ^ d * (J + 1) ^ d := by positivity
      exact_mod_cast this
    linarith
  have hbud : kr ^ (N + 2) ≤
      Real.exp (3 * Real.log (max 1 kr) * (l : ℝ)) := by
    have hkrle : kr ≤ max 1 kr := le_max_right _ _
    have hmax1 : (1 : ℝ) ≤ max 1 kr := le_max_left _ _
    have hlog0 : (0 : ℝ) ≤ Real.log (max 1 kr) := Real.log_nonneg hmax1
    calc kr ^ (N + 2) ≤ (max 1 kr) ^ (N + 2) :=
          pow_le_pow_left₀ hkrpos.le hkrle _
      _ = Real.exp (((N : ℝ) + 2) * Real.log (max 1 kr)) := by
          rw [← Real.rpow_natCast (max 1 kr) (N + 2),
            Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hmax1)]
          congr 1
          push_cast
          ring
      _ ≤ Real.exp (3 * Real.log (max 1 kr) * (l : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          have hNl : (N : ℝ) ≤ (l : ℝ) := by exact_mod_cast hN
          nlinarith
  -- the constant factor
  have hMpos : (0 : ℝ) < M := by
    rw [hM, crossPolyBase]
    have := crossScaleConst_pos d Cbox Cdep Cprob
    positivity
  have hconst : M ≤ Real.exp (Real.log (max 1 M) * (l : ℝ)) := by
    have hmax1 : (1 : ℝ) ≤ max 1 M := le_max_left _ _
    have hlog0 : (0 : ℝ) ≤ Real.log (max 1 M) := Real.log_nonneg hmax1
    calc M ≤ max 1 M := le_max_right _ _
      _ = Real.exp (Real.log (max 1 M)) := (Real.exp_log (lt_of_lt_of_le zero_lt_one hmax1)).symm
      _ ≤ Real.exp (Real.log (max 1 M) * (l : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith
  -- assemble
  have hsplit : ((2 ^ d * (l + 1) ^ d : ℕ) : ℝ) * 2 *
      kr ^ (N + 2) * (1 + 2 * crossScaleConst d Cbox Cdep Cprob) =
      M * (((l + 1 : ℕ) : ℝ) ^ d) * kr ^ (N + 2) := by
    rw [hM, crossPolyBase]
    push_cast
    ring
  rw [hsplit]
  have h1 : (0 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) ^ d := by positivity
  have h2 : (0 : ℝ) ≤ kr ^ (N + 2) := by positivity
  calc M * (((l + 1 : ℕ) : ℝ) ^ d) * kr ^ (N + 2)
      ≤ Real.exp (Real.log (max 1 M) * (l : ℝ)) *
          Real.exp ((d : ℝ) * (l : ℝ)) *
          Real.exp (3 * Real.log (max 1 kr) * (l : ℝ)) := by
        have hp1 : (0 : ℝ) ≤ Real.exp (Real.log (max 1 M) * (l : ℝ)) := (Real.exp_pos _).le
        have hp2 : (0 : ℝ) ≤ Real.exp ((d : ℝ) * (l : ℝ)) := (Real.exp_pos _).le
        have hstep1 : M * (((l + 1 : ℕ) : ℝ) ^ d) ≤
            Real.exp (Real.log (max 1 M) * (l : ℝ)) * Real.exp ((d : ℝ) * (l : ℝ)) :=
          mul_le_mul hconst hpoly h1 hp1
        exact mul_le_mul hstep1 hbud h2 (mul_nonneg hp1 hp2)
    _ = Real.exp (crossEntropy d Cbox Cdep J Cprob * (l : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add, crossEntropy, hkr, hM]
        congr 1
        ring

/-! ## The two thresholds, as separate lemmas -/

/-- Under the second threshold on `q`, the scale sum is small enough for the
chain-sum bound. -/
theorem crossScaleSum_small (d Cbox Cdep J : ℕ) {Cprob cprob q : ℝ}
    (hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ crossBeta d cprob * q)
    (hth2 : Real.log (8 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ crossBeta d cprob * q) :
    8 * crossBranch d J * crossBranch d J *
      crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤ 2 * crossBranch d J := by
  set kn : ℝ := ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) with hkn
  set B : ℝ := crossScaleConst d Cbox Cdep Cprob with hB
  set beta : ℝ := crossBeta d cprob with hbeta
  have hkn1 : (1 : ℝ) ≤ kn := by
    rw [hkn]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hBpos : 0 < B := crossScaleConst_pos d Cbox Cdep Cprob
  have hbranch : crossBranch d J = ENNReal.ofReal kn := by
    rw [crossBranch, hkn, ENNReal.ofReal_natCast]
  have hss : crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤
      ENNReal.ofReal (2 * (B * Real.exp (-(beta * q)))) := by
    have h := crossScaleSum_le d Cbox Cdep (Cprob := Cprob) (cprob := cprob / 2)
      (q := q) (by rw [hbeta, crossBeta] at hth1; exact hth1)
    rw [hB, hbeta, crossBeta]
    exact h
  have hposP : (0 : ℝ) < 8 * kn * B := by nlinarith
  have hexpq : Real.exp (-(beta * q)) ≤ (8 * kn * B)⁻¹ := by
    rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hposP]
    calc 8 * kn * B = Real.exp (Real.log (8 * kn * B)) := (Real.exp_log hposP).symm
      _ ≤ Real.exp (beta * q) := Real.exp_le_exp.mpr hth2
  have hkey : 8 * kn * kn * (2 * (B * Real.exp (-(beta * q)))) ≤ 2 * kn := by
    have hpos2 : (0 : ℝ) ≤ 16 * kn * kn * B := by nlinarith
    have h2 : 16 * kn * kn * B * Real.exp (-(beta * q)) ≤
        16 * kn * kn * B * (8 * kn * B)⁻¹ := mul_le_mul_of_nonneg_left hexpq hpos2
    have h3 : 16 * kn * kn * B * (8 * kn * B)⁻¹ = 2 * kn := by
      field_simp
      ring
    calc 8 * kn * kn * (2 * (B * Real.exp (-(beta * q))))
        = 16 * kn * kn * B * Real.exp (-(beta * q)) := by ring
      _ ≤ 16 * kn * kn * B * (8 * kn * B)⁻¹ := h2
      _ = 2 * kn := h3
  refine le_trans (mul_le_mul' le_rfl hss) ?_
  have hcast : 8 * ENNReal.ofReal kn * ENNReal.ofReal kn *
      ENNReal.ofReal (2 * (B * Real.exp (-(beta * q)))) =
      ENNReal.ofReal (8 * kn * kn * (2 * (B * Real.exp (-(beta * q))))) := by
    rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have hcast2 : (2 : ℝ≥0∞) * ENNReal.ofReal kn = ENNReal.ofReal (2 * kn) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  rw [hbranch, hcast, hcast2]
  exact ENNReal.ofReal_le_ofReal hkey

/-- The certificate's gain, after the good-vertex budget is paid for. -/
theorem crossGain_le {Cbox Cdep J N l : ℕ} {beta q : ℝ}
    (hbeta : 0 ≤ beta) (hq0 : 0 ≤ q) (hCbox : 1 ≤ Cbox)
    (hl2 : 24 * J ≤ l) (hNR : (N : ℝ) * (12 * (J : ℝ) + 12) ≤ (l : ℝ)) :
    -beta * q * (((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) / crossAc Cbox Cdep J) ≤
      -(beta * q) * (l : ℝ) / (2 * crossAc Cbox Cdep J) := by
  set Ac : ℝ := crossAc Cbox Cdep J with hAc
  have hAcpos : 0 < Ac := crossAc_pos hCbox
  have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
  have hlR : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
  have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have h24 : 24 * (J : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
  have hNJ : 6 * (J : ℝ) * (N : ℝ) ≤ (l : ℝ) / 2 := by nlinarith [hNR]
  have hbudget : 6 * (J : ℝ) * ((N : ℝ) + 2) ≤ (l : ℝ) := by nlinarith [hNJ, h24]
  have hdiv : (l : ℝ) / (2 * Ac) ≤
      ((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) / Ac := by
    rw [div_le_div_iff₀ (by linarith) hAcpos]
    have hprod : (0 : ℝ) ≤ ((l : ℝ) - 6 * (J : ℝ) * ((N : ℝ) + 2)) * Ac :=
      mul_nonneg (by linarith) hAcpos.le
    nlinarith [hprod]
  have hmul : beta * q * ((l : ℝ) / (2 * Ac)) ≤
      beta * q * (((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) / Ac) :=
    mul_le_mul_of_nonneg_left hdiv (mul_nonneg hbeta hq0)
  have heq1 : -beta * q * (((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) / Ac) =
      -(beta * q * (((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) / Ac)) := by ring
  have heq2 : -(beta * q) * (l : ℝ) / (2 * Ac) = -(beta * q * ((l : ℝ) / (2 * Ac))) := by
    field_simp
  rw [heq1, heq2]
  linarith [hmul]

/-! ## The crossing estimate at one scale -/


/-- **`[ASD, Lemma B.1(2)]` for the concrete field: the clean exponential form.**

For `q` above an explicit threshold and `l` above an explicit scale, the
probability that some `J`-step crossing of the annulus at scale `l` carries fewer
than `crossCount J l` annulus-good vertices is at most `exp(-c q l)`. -/
theorem measure_crossFailEvent_le_exp [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep J : ℕ)
    {Cprob cprob q : ℝ} (hcprob : 0 < cprob) (hq0 : 0 ≤ q) (hCbox : 1 ≤ Cbox)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ crossBeta d cprob * q)
    (hth2 : Real.log (8 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ crossBeta d cprob * q)
    (hth3 : crossEntropy d Cbox Cdep J Cprob ≤
      crossBeta d cprob * q / (4 * crossAc Cbox Cdep J))
    (z : Lattice d) (l : ℕ) (hl1 : 12 * Cbox ≤ l) (hl2 : 24 * J ≤ l) (hl3 : 1 ≤ l) :
    mu (crossFailEvent E Cbox J z l (crossCount J l)) ≤
      ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep J cprob) * q * (l : ℝ))) := by
  classical
  set kn : ℝ := ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) with hkn
  set B : ℝ := crossScaleConst d Cbox Cdep Cprob with hB
  set beta : ℝ := crossBeta d cprob with hbeta
  set Ac : ℝ := crossAc Cbox Cdep J with hAc
  set N : ℕ := crossCount J l with hN
  have hknpos : (1 : ℝ) ≤ kn := by
    rw [hkn]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hBpos : 0 < B := crossScaleConst_pos d Cbox Cdep Cprob
  have hbetapos : 0 < beta := crossBeta_pos hcprob
  have hAcpos : 0 < Ac := crossAc_pos hCbox
  have hbranch : crossBranch d J = ENNReal.ofReal kn := by
    rw [crossBranch, hkn, ENNReal.ofReal_natCast]
  have hbq : 0 ≤ beta * q := mul_nonneg hbetapos.le hq0
  have hpi := crossScaleSum_small d Cbox Cdep J
    (by rw [hbeta] at *; exact hth1) (by rw [hbeta, hkn, hB] at *; exact hth2)
  have hss : crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤
      ENNReal.ofReal (2 * (B * Real.exp (-(beta * q)))) := by
    have h := crossScaleSum_le d Cbox Cdep (Cprob := Cprob) (cprob := cprob / 2)
      (q := q) (by rw [hbeta, crossBeta] at hth1; exact hth1)
    rw [hB, hbeta, crossBeta]
    exact h
  -- the certificate bound
  have hmain := measure_crossFailEvent_le mu E Cbox Cdep J
    (Cprob := Cprob) (cprob := cprob) (q := q) (mul_nonneg hcprob.le hq0) hsc hr hprob
    hpi z l N hl1 hCbox
  refine hmain.trans ?_
  have hNl : N ≤ l := by
    rw [hN, crossCount]
    exact Nat.div_le_self _ _
  have hNR : (N : ℝ) * (12 * (J : ℝ) + 12) ≤ (l : ℝ) := by
    have hnat : N * (12 * J + 12) ≤ l := by
      rw [hN, crossCount]
      exact Nat.div_mul_le_self _ _
    have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at hcast
    linarith
  have hgain : -beta * q * (((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) / Ac) ≤
      -(beta * q) * (l : ℝ) / (2 * Ac) := by
    rw [hAc]
    exact crossGain_le hbetapos.le hq0 hCbox hl2 hNR
  have hentropy := crossEntropy_bound d Cbox Cdep J Cprob (N := N) (l := l) hl3 hNl
  -- put the two together
  have hPr : (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) *
      (2 * (4 * crossBranch d J) ^ (N + 2)) *
      (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q) ≤
      ENNReal.ofReal (((2 ^ d * (l + 1) ^ d : ℕ) : ℝ) * 2 *
        (4 * kn) ^ (N + 2) * (1 + 2 * B)) := by
    have h1 : (1 : ℝ≥0∞) + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤
        ENNReal.ofReal (1 + 2 * B) := by
      refine le_trans (add_le_add le_rfl hss) ?_
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp1 : Real.exp (-(beta * q)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      nlinarith [hBpos, hexp1]
    have h2 : (4 : ℝ≥0∞) * crossBranch d J = ENNReal.ofReal (4 * kn) := by
      rw [hbranch, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
    calc (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) *
          (2 * (4 * crossBranch d J) ^ (N + 2)) *
          (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q)
        ≤ (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) *
            (2 * (4 * crossBranch d J) ^ (N + 2)) * ENNReal.ofReal (1 + 2 * B) :=
          mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (((2 ^ d * (l + 1) ^ d : ℕ) : ℝ) * 2 *
            (4 * kn) ^ (N + 2) * (1 + 2 * B)) := by
          rw [h2, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  refine le_trans (mul_le_mul' le_rfl hPr) ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.exp (-(beta) * q * (((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) / Ac)) *
        (((2 ^ d * (l + 1) ^ d : ℕ) : ℝ) * 2 * (4 * kn) ^ (N + 2) * (1 + 2 * B))
      ≤ Real.exp (-(beta * q) * (l : ℝ) / (2 * Ac)) *
          Real.exp (crossEntropy d Cbox Cdep J Cprob * (l : ℝ)) := by
        refine mul_le_mul (Real.exp_le_exp.mpr hgain) hentropy (by positivity)
          (Real.exp_pos _).le
    _ = Real.exp (-(beta * q) * (l : ℝ) / (2 * Ac) +
          crossEntropy d Cbox Cdep J Cprob * (l : ℝ)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(crossRate d Cbox Cdep J cprob) * q * (l : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have hlR : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
        have hrate : crossRate d Cbox Cdep J cprob = beta / (4 * Ac) := by
          rw [crossRate, hbeta, hAc]
        rw [hrate]
        have hmul := mul_le_mul_of_nonneg_right hth3 hlR
        have hAc4 : (0 : ℝ) < 4 * Ac := by linarith
        have hkey : -(beta * q) * (l : ℝ) / (2 * Ac) +
            beta * q / (4 * Ac) * (l : ℝ) = -(beta * q / (4 * Ac)) * (l : ℝ) := by
          field_simp
          ring
        have hgoal : -(beta / (4 * Ac)) * q * (l : ℝ) = -(beta * q / (4 * Ac)) * (l : ℝ) := by
          field_simp
        rw [hgoal, ← hkey]
        linarith [hmul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
