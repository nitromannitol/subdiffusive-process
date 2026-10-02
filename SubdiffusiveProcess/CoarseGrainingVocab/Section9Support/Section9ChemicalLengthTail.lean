import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTube




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

/-! ## The tube radius and the budget it costs -/

/-- The tube radius used at scale `L`: the largest clause-(ii) diameter threshold whose level
`h = ⌈(log L) ^ 2⌉` still carries the rate `exp (-(alpha q (log L) ^ 2))`, with the harmless
`q⁻¹ ≤ 1` already substituted so that the radius does not depend on `q`. -/
def chemicalTubeRadius (C : ℝ) (L : ℕ) : ℕ :=
  ⌈C * (1 + (⌈Real.log (L : ℝ) ^ 2⌉₊ : ℝ) + Real.log (2 + 2 * (L : ℝ))) ^ 2⌉₊

/-- The number of sites of the tube of radius `chemicalTubeRadius C L + 1` around a geodesic of
at most `2 L + 1` sites: the length budget of `Section9ChemicalTube`. -/
def chemicalTubeBudget (C : ℝ) (dim L : ℕ) : ℝ :=
  (((2 * L + 1) * (2 * (chemicalTubeRadius C L + 1) + 1) ^ dim : ℕ) : ℝ)

/-- **The budget is `L` times a polylogarithm.**  For `L ≥ 3` the tube radius is at most
`1 + 36 C (log L) ^ 4`, so the budget is at most `(2L+1) (5 + 72 C (log L) ^ 4) ^ d`. -/
theorem chemicalTubeRadius_le {C : ℝ} (hC : 0 ≤ C) {L : ℕ} (hL : 3 ≤ L) :
    ((chemicalTubeRadius C L : ℕ) : ℝ) ≤ 1 + 36 * C * Real.log (L : ℝ) ^ 4 := by
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hlog1 : (1 : ℝ) ≤ Real.log (L : ℝ) := by
    have hle : Real.log 3 ≤ Real.log (L : ℝ) := Real.log_le_log (by norm_num) hL3
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      have h : Real.log (Real.exp 1) ≤ Real.log 3 :=
        Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
      rwa [Real.log_exp] at h
    linarith
  have hsq : (1 : ℝ) ≤ Real.log (L : ℝ) ^ 2 := by nlinarith
  -- `log (2 + 2 L) ≤ 3 log L`
  have hstep1 : (9 : ℝ) * (L : ℝ) ≤ 3 * (L : ℝ) ^ 2 := by nlinarith
  have hstep2 : (3 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 3 := by nlinarith
  have hcube : 2 + 2 * (L : ℝ) ≤ (L : ℝ) ^ 3 := by nlinarith
  have hlog2 : Real.log (2 + 2 * (L : ℝ)) ≤ 3 * Real.log (L : ℝ) := by
    have h1 : Real.log (2 + 2 * (L : ℝ)) ≤ Real.log ((L : ℝ) ^ 3) :=
      Real.log_le_log (by linarith) hcube
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hceil : ((⌈Real.log (L : ℝ) ^ 2⌉₊ : ℕ) : ℝ) ≤ Real.log (L : ℝ) ^ 2 + 1 := by
    have h := Nat.ceil_lt_add_one (a := Real.log (L : ℝ) ^ 2) (by positivity)
    linarith
  have hinnernn : (0 : ℝ) ≤
      1 + ((⌈Real.log (L : ℝ) ^ 2⌉₊ : ℕ) : ℝ) + Real.log (2 + 2 * (L : ℝ)) := by
    have h1 : (0 : ℝ) ≤ ((⌈Real.log (L : ℝ) ^ 2⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ Real.log (2 + 2 * (L : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  have hinner : 1 + ((⌈Real.log (L : ℝ) ^ 2⌉₊ : ℕ) : ℝ) + Real.log (2 + 2 * (L : ℝ))
      ≤ 6 * Real.log (L : ℝ) ^ 2 := by nlinarith
  have hsq2 : (1 + ((⌈Real.log (L : ℝ) ^ 2⌉₊ : ℕ) : ℝ) + Real.log (2 + 2 * (L : ℝ))) ^ 2
      ≤ 36 * Real.log (L : ℝ) ^ 4 := by nlinarith
  have hmain : C * (1 + ((⌈Real.log (L : ℝ) ^ 2⌉₊ : ℕ) : ℝ) + Real.log (2 + 2 * (L : ℝ))) ^ 2
      ≤ 36 * C * Real.log (L : ℝ) ^ 4 := by nlinarith
  have hlast := Nat.ceil_lt_add_one
    (a := C * (1 + ((⌈Real.log (L : ℝ) ^ 2⌉₊ : ℕ) : ℝ) + Real.log (2 + 2 * (L : ℝ))) ^ 2)
    (by positivity)
  rw [chemicalTubeRadius]
  linarith

/-! ## The diameter tail at the tube radius -/

/-- **`P[some bad component meeting `B_{2L}(z)` has diameter above the tube radius]`
`≤ exp (-(alpha q (log L) ^ 2))`.**

The clause-(ii) estimate at the level `h = ⌈(log L) ^ 2⌉`, whose diameter threshold
`asdBadRadius C q h (2 L)` is below `chemicalTubeRadius C L` for every `q ≥ 1`. -/
theorem exists_badComponentDiameter_polylog_tail (d Cbox Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 : ℕ, ∃ crate C : ℝ, 0 < crate ∧ 3 ≤ C ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∀ (z : Lattice d) (L : ℕ), 1 ≤ L →
          mu (badComponentFailureEvent E Cbox 1 z (2 * L : ℝ)
              ((chemicalTubeRadius C L : ℕ) : ℝ)) ≤
            ENNReal.ofReal (Real.exp (-(crate * q * Real.log (L : ℝ) ^ 2))) := by
  classical
  set C : ℝ := asdGeomBase d Cbox Cdep cprob with hCdef
  have hC3 : 3 ≤ C := three_le_asdGeomBase d Cbox Cdep cprob
  have halpha : ((2 * d + 2 : ℕ) : ℝ) ≤ asdAlpha Cbox Cdep cprob C :=
    asdGeomBase_alpha d Cbox Cdep hcprob
  have halphapos : 0 < asdAlpha Cbox Cdep cprob C := by
    have : (0 : ℝ) < ((2 * d + 2 : ℕ) : ℝ) := by positivity
    linarith
  have hkappa : 0 < asdKappa Cbox Cdep cprob := asdKappa_pos Cbox Cdep hcprob
  have hCpos : (0 : ℝ) < C := by linarith
  obtain ⟨q1, hq1⟩ := exists_uniform_threshold (c := cprob)
    (X := 2 * Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob)) hcprob
  obtain ⟨q2, hq2⟩ := exists_uniform_threshold (c := cprob)
    (X := 2 * (d : ℝ) * Real.log 3) hcprob
  obtain ⟨q3, hq3⟩ := exists_uniform_threshold (c := asdKappa Cbox Cdep cprob)
    (X := 32 * (d : ℝ) * Real.exp 80) hkappa
  refine ⟨max 1 (max q1 (max q2 q3)), asdAlpha Cbox Cdep cprob C, C, halphapos, hC3, ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw z L hL
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
  have hqone : (1 : ℝ) ≤ q := le_trans (by exact_mod_cast Nat.le_max_left 1 _) hq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hqone
  have hth1 : Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob) ≤ cprob * q / 2 := by
    have := hq1 q hq1'; linarith
  have hth2 : (d : ℝ) * Real.log 3 ≤ cprob * q / 2 := by
    have := hq2 q hq2'; linarith
  have hgate : 16 * (d : ℝ) * Real.exp 80 ≤ asdRate Cbox Cdep cprob q / 2 := by
    have h := hq3 q hq3'
    rw [asdRate_eq_mul]
    nlinarith
  set h : ℕ := ⌈Real.log (L : ℝ) ^ 2⌉₊ with hhdef
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hcast : (((2 * L : ℕ)) : ℝ) = 2 * (L : ℝ) := by push_cast; ring
  have hlognn : (0 : ℝ) ≤ Real.log (2 + 2 * (L : ℝ)) := Real.log_nonneg (by linarith)
  have hqinv : q⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hqone
  have hqinvnn : (0 : ℝ) ≤ q⁻¹ := by positivity
  have hhnn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hrad : asdBadRadius C q h (2 * L) ≤ ((chemicalTubeRadius C L : ℕ) : ℝ) := by
    have hmix : q⁻¹ * Real.log (2 + ((2 * L : ℕ) : ℝ)) ≤ Real.log (2 + 2 * (L : ℝ)) := by
      rw [hcast]
      nlinarith
    have hSnn : (0 : ℝ) ≤ 1 + (h : ℝ) + q⁻¹ * Real.log (2 + ((2 * L : ℕ) : ℝ)) := by
      have : (0 : ℝ) ≤ q⁻¹ * Real.log (2 + ((2 * L : ℕ) : ℝ)) := by
        refine mul_nonneg hqinvnn (Real.log_nonneg ?_)
        have : (0 : ℝ) ≤ ((2 * L : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    have hle : (1 + (h : ℝ) + q⁻¹ * Real.log (2 + ((2 * L : ℕ) : ℝ))) ^ 2
        ≤ (1 + (h : ℝ) + Real.log (2 + 2 * (L : ℝ))) ^ 2 :=
      pow_le_pow_left₀ hSnn (by linarith) 2
    calc asdBadRadius C q h (2 * L)
        = C * (1 + (h : ℝ) + q⁻¹ * Real.log (2 + ((2 * L : ℕ) : ℝ))) ^ 2 := rfl
      _ ≤ C * (1 + (h : ℝ) + Real.log (2 + 2 * (L : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_left hle hCpos.le
      _ ≤ ((chemicalTubeRadius C L : ℕ) : ℝ) := by
          rw [chemicalTubeRadius, ← hhdef]
          exact Nat.le_ceil _
  have hsub : badComponentFailureEvent E Cbox 1 z (2 * L : ℝ)
      ((chemicalTubeRadius C L : ℕ) : ℝ) ⊆ asdDiameterFailure E Cbox C q z h := by
    intro omega homega
    refine Set.mem_iUnion.mpr ⟨2 * L, ?_⟩
    rw [hcast]
    exact badComponentFailureEvent_antitone E Cbox 1 z (2 * (L : ℝ)) hrad homega
  have hlogsq : Real.log (L : ℝ) ^ 2 ≤ 1 + (h : ℝ) := by
    have := Nat.le_ceil (Real.log (L : ℝ) ^ 2)
    rw [← hhdef] at this
    linarith
  calc mu (badComponentFailureEvent E Cbox 1 z (2 * L : ℝ)
        ((chemicalTubeRadius C L : ℕ) : ℝ))
      ≤ mu (asdDiameterFailure E Cbox C q z h) := measure_mono hsub
    _ ≤ ENNReal.ofReal
          (Real.exp (-(asdAlpha Cbox Cdep cprob C * q * (1 + (h : ℝ))))) :=
        measure_asdDiameterFailure_le mu (by omega) hCbox hCprob hcprob hqpos hC3
          hth1 hth2 hgate halpha hlaw.1 hsc hr hprob z h
    _ ≤ ENNReal.ofReal
          (Real.exp (-(asdAlpha Cbox Cdep cprob C * q * Real.log (L : ℝ) ^ 2))) := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have := mul_le_mul_of_nonneg_left hlogsq
          (mul_nonneg halphapos.le hqpos.le)
        linarith

/-! ## `(log L) ^ 2` is dominated by `√L` -/

/-- `(log L) ^ 2 ≤ 64 √L` for every `L ≥ 1`: the square of
`Section9ChemicalConnectivityTail.log_two_add_two_mul_le`. -/
theorem log_sq_le_sqrt {L : ℕ} (hL : 1 ≤ L) :
    Real.log (L : ℝ) ^ 2 ≤ 64 * Real.sqrt (L : ℝ) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h1 : Real.log (L : ℝ) ≤ Real.log (2 + 2 * (L : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (2 + 2 * (L : ℝ)) ≤ 8 * Real.sqrt (Real.sqrt (L : ℝ)) :=
    log_two_add_two_mul_le hL
  have hnn : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  have hs : Real.sqrt (Real.sqrt (L : ℝ)) ^ 2 = Real.sqrt (L : ℝ) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  nlinarith [Real.sqrt_nonneg (Real.sqrt (L : ℝ))]

/-! ## The chemical-distance bound at the tube budget -/

/-- **The frozen display, proved at a polylogarithmically inflated length budget.**

For every dimension `d ≥ 2`, box constant `Cbox ≥ 1`, dependence constant `Cdep` and pair of
positive probability constants there are `q0`, `L0 ≥ 1`, a rate `c > 0` and a geometric
constant `C ≥ 3` such that every field satisfying the multiscale-percolation hypotheses at
`q ≥ q0` obeys, at every centre `z` and every scale `L ≥ L0`,

```text
    mu (chemicalDistanceFailureEventAt E Cbox (chemicalTubeBudget C d L) z L)
      ≤ 2 exp (-(c q (log L) ^ 2)) ,
```

with `chemicalTubeBudget C d L ≤ (2 L + 1) (5 + 72 C (log L) ^ 4) ^ d`
(`chemicalTubeRadius_le`).

This is `UniformChemicalDistanceBoundBox` — the sole residual of the percolation anchor —
**except** that the length budget is `L · polylog L` instead of the frozen `Clen * L`.  Both
halves are proved with no external input: the connectivity half by
`exists_connectivity_tail`, the length half by confining the good detour to a tube
(`Section9ChemicalTube`) whose radius is paid for by the clause-(ii) diameter estimate. -/
theorem exists_chemicalDistance_polylog_tail (d Cbox Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 L0 : ℕ, ∃ c C : ℝ, 1 ≤ L0 ∧ 0 < c ∧ 3 ≤ C ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∀ (z : Lattice d) (L : ℕ), L0 ≤ L →
          mu (chemicalDistanceFailureEventAt E Cbox (chemicalTubeBudget C d L) z L) ≤
            ENNReal.ofReal (2 * Real.exp (-(c * q * Real.log (L : ℝ) ^ 2))) := by
  classical
  obtain ⟨q0c, L0, crate, hL0, hcrate, hconn⟩ :=
    exists_connectivity_tail d Cbox Cdep Cprob cprob hd hCbox hCprob hcprob
  obtain ⟨q0d, alpha, C, halpha, hC3, hdiam⟩ :=
    exists_badComponentDiameter_polylog_tail d Cbox Cdep Cprob cprob hd hCbox hCprob hcprob
  refine ⟨max 1 (max q0c q0d), L0, min (crate / 64) alpha, C, hL0, ?_, hC3, ?_⟩
  · exact lt_min (by positivity) halpha
  intro Omega _ mu _ E q hq hprob hsc hr hlaw z L hLL0
  have hq0c : (q0c : ℝ) ≤ q :=
    le_trans (by exact_mod_cast (Nat.le_max_left q0c q0d).trans (Nat.le_max_right 1 _)) hq
  have hq0d : (q0d : ℝ) ≤ q :=
    le_trans (by exact_mod_cast (Nat.le_max_right q0c q0d).trans (Nat.le_max_right 1 _)) hq
  have hqone : (1 : ℝ) ≤ q := le_trans (by exact_mod_cast Nat.le_max_left 1 _) hq
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hqone
  have hL1 : 1 ≤ L := le_trans hL0 hLL0
  set clen : ℝ := min (crate / 64) alpha with hclen
  have hclen1 : clen ≤ crate / 64 := min_le_left _ _
  have hclen2 : clen ≤ alpha := min_le_right _ _
  have hlognn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ 2 := by positivity
  set X : ℝ := Real.exp (-(clen * q * Real.log (L : ℝ) ^ 2)) with hX
  have hXnn : (0 : ℝ) ≤ X := (Real.exp_pos _).le
  -- the connectivity half
  have hA : mu {omega | ¬ GoodConnectedInDoubleBallAt E Cbox omega z L ((L : ℝ) / 20)} ≤
      ENNReal.ofReal X := by
    refine le_trans (hconn mu E q hq0c hprob hsc hr hlaw z L hLL0 ((L : ℝ) / 20) le_rfl) ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hsq := log_sq_le_sqrt hL1
    have h1 : clen * Real.log (L : ℝ) ^ 2 ≤ crate * Real.sqrt (L : ℝ) := by
      have hc0 : (0 : ℝ) ≤ clen := le_trans (le_min (by positivity) halpha.le) le_rfl
      nlinarith [Real.sqrt_nonneg (L : ℝ)]
    nlinarith [hqpos.le]
  -- the length half
  have hB : mu (badComponentFailureEvent E Cbox 1 z (2 * L : ℝ)
      ((chemicalTubeRadius C L : ℕ) : ℝ)) ≤ ENNReal.ofReal X := by
    refine le_trans (hdiam mu E q hq0d hprob hsc hr hlaw z L hL1) ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hkey : clen * (q * Real.log (L : ℝ) ^ 2) ≤ alpha * (q * Real.log (L : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hclen2 (by positivity)
    linarith
  have hsub := chemicalDistanceFailureEventAt_subset_union E Cbox z L (chemicalTubeRadius C L)
    (bound := chemicalTubeBudget C d L) le_rfl
  calc mu (chemicalDistanceFailureEventAt E Cbox (chemicalTubeBudget C d L) z L)
      ≤ mu ({omega | ¬ GoodConnectedInDoubleBallAt E Cbox omega z L ((L : ℝ) / 20)} ∪
          badComponentFailureEvent E Cbox 1 z (2 * L : ℝ)
            ((chemicalTubeRadius C L : ℕ) : ℝ)) := measure_mono hsub
    _ ≤ mu {omega | ¬ GoodConnectedInDoubleBallAt E Cbox omega z L ((L : ℝ) / 20)} +
          mu (badComponentFailureEvent E Cbox 1 z (2 * L : ℝ)
            ((chemicalTubeRadius C L : ℕ) : ℝ)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal X + ENNReal.ofReal X := add_le_add hA hB
    _ = ENNReal.ofReal (2 * X) := by
        rw [← ENNReal.ofReal_add hXnn hXnn]
        ring_nf

/-! ## The small scales -/

/-- **The failure event below the connectivity threshold.**  At any scale the chemical-distance
failure event at a budget of at least `2 L + 1` is covered by the bad-site events of `B_L(z)`,
so its probability is at most `(2L+1)^d` times the bad-site bound `C e^{-c q}`. -/
theorem measure_chemicalDistanceFailureEventAt_le_badSites {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) {E : ℕ → Lattice d → Set Omega} {Cbox : ℕ}
    (hCbox : 1 ≤ Cbox) {Cprob cprob q : ℝ} (hCprob : 0 ≤ Cprob) (hA : 0 ≤ cprob * q)
    (hqlog : Real.log ((3 : ℝ) ^ d) + Real.log 2 ≤ cprob * q)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (z : Lattice d) (L : ℕ) {bound : ℝ} (hbound : ((2 * L + 1 : ℕ) : ℝ) ≤ bound) :
    mu (chemicalDistanceFailureEventAt E Cbox bound z L) ≤
      ENNReal.ofReal ((((2 * L + 1) ^ d : ℕ) : ℝ) *
        (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) * Real.exp (-(cprob * q)))) := by
  classical
  have hsub := chemicalDistanceFailureEventAt_subset_badSite_union E Cbox z L hbound
  have hK : (0 : ℝ) ≤ 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) * Real.exp (-(cprob * q)) := by
    have h1 : (0 : ℝ) ≤ (((3 * Cbox) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) < Real.exp (-(cprob * q)) := Real.exp_pos _
    positivity
  calc mu (chemicalDistanceFailureEventAt E Cbox bound z L)
      ≤ mu (⋃ u ∈ latticeBallFinset z L, percolationBadSite E Cbox u) := measure_mono hsub
    _ ≤ ∑ u ∈ latticeBallFinset z L, mu (percolationBadSite E Cbox u) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _u ∈ latticeBallFinset z L,
          ENNReal.ofReal (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) *
            Real.exp (-(cprob * q))) :=
        Finset.sum_le_sum fun u _ =>
          measure_percolationBadSite_le mu hCbox hCprob hA hqlog hprob u
    _ = (((2 * L + 1) ^ d : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) *
            Real.exp (-(cprob * q))) := by
        rw [Finset.sum_const, card_latticeBallFinset, nsmul_eq_mul]
    _ = ENNReal.ofReal ((((2 * L + 1) ^ d : ℕ) : ℝ) *
          (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) * Real.exp (-(cprob * q)))) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

/-! ## The chemical-distance bound at every scale -/

/-- **`UniformChemicalDistanceBoundBox` at the tube budget, at every scale `L ≥ 1`.**

Same conclusion as `exists_chemicalDistance_polylog_tail`, extended to the finitely many
scales below the connectivity threshold by the bad-site union bound.  This is *exactly* the
frozen residual `UniformChemicalDistanceBoundBox d Cdep Cprob cprob`
(`Section9ChemicalUniformProvider`), with the single change that the length budget is
`chemicalTubeBudget C d L ≍ C' L (log L) ^ (4 d)` in place of `Clen * L`. -/
theorem exists_chemicalDistance_polylog_bound (d Cbox Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 : ℕ, ∃ c Cfail C : ℝ, 0 < c ∧ 0 < Cfail ∧ 3 ≤ C ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∀ (z : Lattice d) (L : ℕ), 1 ≤ L →
          mu (chemicalDistanceFailureEventAt E Cbox (chemicalTubeBudget C d L) z L) ≤
            ENNReal.ofReal (Cfail * Real.exp (-(c * q * Real.log (L : ℝ) ^ 2))) := by
  classical
  obtain ⟨q0t, L0, ctail, C, hL0, hctail, hC3, htail⟩ :=
    exists_chemicalDistance_polylog_tail d Cbox Cdep Cprob cprob hd hCbox hCprob hcprob
  obtain ⟨q0s, hq0s⟩ := exists_uniform_threshold (c := cprob)
    (X := Real.log ((3 : ℝ) ^ d) + Real.log 2) hcprob
  set B : ℝ := Real.log (L0 : ℝ) ^ 2 + 1 with hB
  have hB1 : (1 : ℝ) ≤ B := by
    have : (0 : ℝ) ≤ Real.log (L0 : ℝ) ^ 2 := by positivity
    rw [hB]; linarith
  set Cfail : ℝ := 2 + (((2 * L0 + 1) ^ d : ℕ) : ℝ) *
    (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ))) with hCfail
  have hCfailpos : 0 < Cfail := by
    have h1 : (0 : ℝ) ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (((3 * Cbox) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hCfail]; positivity
  refine ⟨max 1 (max q0t q0s), min ctail (cprob / B), Cfail, C,
    lt_min hctail (by positivity), hCfailpos, hC3, ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw z L hL1
  have hq0t : (q0t : ℝ) ≤ q :=
    le_trans (by exact_mod_cast (Nat.le_max_left q0t q0s).trans (Nat.le_max_right 1 _)) hq
  have hq0s' : (q0s : ℝ) ≤ q :=
    le_trans (by exact_mod_cast (Nat.le_max_right q0t q0s).trans (Nat.le_max_right 1 _)) hq
  have hqone : (1 : ℝ) ≤ q := le_trans (by exact_mod_cast Nat.le_max_left 1 _) hq
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hqone
  set c : ℝ := min ctail (cprob / B) with hc
  have hc1 : c ≤ ctail := min_le_left _ _
  have hc2 : c ≤ cprob / B := min_le_right _ _
  have hcpos : 0 < c := lt_min hctail (by positivity)
  have hlognn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ 2 := by positivity
  by_cases hLL0 : L0 ≤ L
  · -- the main regime
    refine le_trans (htail mu E q hq0t hprob hsc hr hlaw z L hLL0) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp : Real.exp (-(ctail * q * Real.log (L : ℝ) ^ 2)) ≤
        Real.exp (-(c * q * Real.log (L : ℝ) ^ 2)) := by
      refine Real.exp_le_exp.mpr ?_
      have hkey : c * (q * Real.log (L : ℝ) ^ 2) ≤ ctail * (q * Real.log (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hc1 (by positivity)
      linarith
    have hpos : (0 : ℝ) < Real.exp (-(c * q * Real.log (L : ℝ) ^ 2)) := Real.exp_pos _
    have hCf : (2 : ℝ) ≤ Cfail := by
      have h1 : (0 : ℝ) ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (((3 * Cbox) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
      have h3 : (0 : ℝ) ≤ Cprob := hCprob.le
      have hnn : (0 : ℝ) ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) *
          (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ))) := by positivity
      rw [hCfail]
      linarith
    nlinarith [Real.exp_pos (-(ctail * q * Real.log (L : ℝ) ^ 2))]
  · -- the finitely many small scales
    push_neg at hLL0
    have hbudget : ((2 * L + 1 : ℕ) : ℝ) ≤ chemicalTubeBudget C d L := by
      rw [chemicalTubeBudget]
      have hone : 1 ≤ (2 * (chemicalTubeRadius C L + 1) + 1) ^ d :=
        Nat.one_le_pow _ _ (by omega)
      have : (2 * L + 1) * 1 ≤ (2 * L + 1) * (2 * (chemicalTubeRadius C L + 1) + 1) ^ d :=
        Nat.mul_le_mul_left _ hone
      exact_mod_cast (by omega : 2 * L + 1 ≤
        (2 * L + 1) * (2 * (chemicalTubeRadius C L + 1) + 1) ^ d)
    have hA : (0 : ℝ) ≤ cprob * q := by positivity
    have hqlog : Real.log ((3 : ℝ) ^ d) + Real.log 2 ≤ cprob * q := hq0s q hq0s'
    refine le_trans (measure_chemicalDistanceFailureEventAt_le_badSites mu hCbox hCprob.le hA
      hqlog hprob z L hbudget) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    -- the entropy factor is bounded by its value at `L0`
    have hcard : (((2 * L + 1) ^ d : ℕ) : ℝ) ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) := by
      have : ((2 * L + 1) ^ d : ℕ) ≤ ((2 * L0 + 1) ^ d : ℕ) :=
        Nat.pow_le_pow_left (by omega) d
      exact_mod_cast this
    -- the rate at a small scale is below `cprob`
    have hlogle : Real.log (L : ℝ) ^ 2 ≤ B := by
      have hLcast : (L : ℝ) ≤ (L0 : ℝ) := by exact_mod_cast hLL0.le
      have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
      have h1 : Real.log (L : ℝ) ≤ Real.log (L0 : ℝ) := Real.log_le_log (by linarith) hLcast
      have h2 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1'
      rw [hB]; nlinarith
    have hrate : c * q * Real.log (L : ℝ) ^ 2 ≤ cprob * q := by
      have h1 : c * Real.log (L : ℝ) ^ 2 ≤ c * B :=
        mul_le_mul_of_nonneg_left hlogle hcpos.le
      have h2 : c * B ≤ cprob := by
        have := mul_le_mul_of_nonneg_right hc2 (by linarith : (0:ℝ) ≤ B)
        rw [div_mul_eq_mul_div, mul_div_assoc, div_self (by linarith : B ≠ 0), mul_one] at this
        linarith
      nlinarith [hqpos.le]
    have hexp : Real.exp (-(cprob * q)) ≤ Real.exp (-(c * q * Real.log (L : ℝ) ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hCf : (((2 * L0 + 1) ^ d : ℕ) : ℝ) * (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)))
        ≤ Cfail := by rw [hCfail]; linarith
    have hnn1 : (0 : ℝ) ≤ 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) := by
      have : (0 : ℝ) ≤ (((3 * Cbox) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
      positivity
    have hexppos : (0 : ℝ) < Real.exp (-(c * q * Real.log (L : ℝ) ^ 2)) := Real.exp_pos _
    have hstep : 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) * Real.exp (-(cprob * q))
        ≤ 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) *
          Real.exp (-(c * q * Real.log (L : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp hnn1
    have hnn2 : (0 : ℝ) ≤ 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) *
        Real.exp (-(cprob * q)) := mul_nonneg hnn1 (Real.exp_pos _).le
    have hnn3 : (0 : ℝ) ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (((2 * L + 1) ^ d : ℕ) : ℝ) *
          (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) * Real.exp (-(cprob * q)))
        ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) *
          (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) *
            Real.exp (-(c * q * Real.log (L : ℝ) ^ 2))) :=
          mul_le_mul hcard hstep hnn2 hnn3
      _ = ((((2 * L0 + 1) ^ d : ℕ) : ℝ) * (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)))) *
            Real.exp (-(c * q * Real.log (L : ℝ) ^ 2)) := by ring
      _ ≤ Cfail * Real.exp (-(c * q * Real.log (L : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hCf hexppos.le

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
