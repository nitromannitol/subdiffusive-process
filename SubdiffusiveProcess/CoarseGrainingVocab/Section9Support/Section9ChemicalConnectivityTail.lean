module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalASDDiameterTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalDistance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimarCycleBoundary

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## Arithmetic: `√L` beats `log L` -/

/-- `log (2 + 2 L) ≤ 8 (L ^ (1/4))`, with the fourth root written as an iterated square root.
The proof is `log t = 4 log t^{1/4} ≤ 4 (t^{1/4} - 1)`. -/
theorem log_two_add_two_mul_le {L : ℕ} (hL : 1 ≤ L) :
    Real.log (2 + 2 * (L : ℝ)) ≤ 8 * Real.sqrt (Real.sqrt (L : ℝ)) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  set t : ℝ := 2 + 2 * (L : ℝ) with ht
  have ht0 : (0 : ℝ) < t := by rw [ht]; linarith
  set u : ℝ := Real.sqrt (Real.sqrt t) with hu
  have hu0 : 0 < u := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ht0)
  have hsq1 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hsq2 : u ^ 2 = Real.sqrt t := Real.sq_sqrt (Real.sqrt_nonneg t)
  have hu4 : u ^ 4 = t := by
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = Real.sqrt t ^ 2 := by rw [hsq2]
      _ = t := hsq1
  have hlogt : Real.log t = 4 * Real.log u := by
    rw [← hu4, Real.log_pow]
    norm_num
  have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu0
  -- `u ≤ 2 √(√L)`
  have hsqrt4 : Real.sqrt (4 * (L : ℝ)) = 2 * Real.sqrt (L : ℝ) := by
    rw [show (4 : ℝ) * (L : ℝ) = 2 ^ 2 * (L : ℝ) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hstep1 : Real.sqrt t ≤ 2 * Real.sqrt (L : ℝ) := by
    rw [← hsqrt4]
    exact Real.sqrt_le_sqrt (by rw [ht]; linarith)
  have hstep2 : u ≤ Real.sqrt (2 * Real.sqrt (L : ℝ)) := Real.sqrt_le_sqrt hstep1
  have hstep3 : Real.sqrt (2 * Real.sqrt (L : ℝ))
      = Real.sqrt 2 * Real.sqrt (Real.sqrt (L : ℝ)) :=
    Real.sqrt_mul (by norm_num) _
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h4 ▸ this]
  have hx0 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (L : ℝ)) := Real.sqrt_nonneg _
  have hule : u ≤ 2 * Real.sqrt (Real.sqrt (L : ℝ)) := by
    refine hstep2.trans ?_
    rw [hstep3]
    exact mul_le_mul_of_nonneg_right hs2 hx0
  calc Real.log t = 4 * Real.log u := hlogt
    _ ≤ 4 * (u - 1) := by linarith
    _ ≤ 4 * u := by linarith
    _ ≤ 8 * Real.sqrt (Real.sqrt (L : ℝ)) := by linarith

/-- **`√L` eventually dominates any fixed multiple of `log L`.**  For every `A` there is a
threshold `L0 ≥ 1` beyond which `A (2 + 2 log (2 + 2 L)) ≤ √L`.  This is the only place the
`L0` of the connectivity tail comes from. -/
theorem exists_threshold_sqrt_dominates_log (A : ℝ) :
    ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L : ℕ, L0 ≤ L →
      A * (2 + 2 * Real.log (2 + 2 * (L : ℝ))) ≤ Real.sqrt (L : ℝ) := by
  classical
  set B : ℝ := max A 1 with hBdef
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hAB : A ≤ B := le_max_left _ _
  refine ⟨max 1 ⌈(18 * B + 1) ^ 4⌉₊, le_max_left _ _, ?_⟩
  intro L hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hceil : ⌈(18 * B + 1) ^ 4⌉₊ ≤ L := le_trans (le_max_right _ _) hL
  have hpow : (18 * B + 1) ^ 4 ≤ (L : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  set x : ℝ := Real.sqrt (Real.sqrt (L : ℝ)) with hxdef
  have hx0 : (0 : ℝ) ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = Real.sqrt (L : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hx4 : x ^ 4 = (L : ℝ) := by
    calc x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = Real.sqrt (L : ℝ) ^ 2 := by rw [hx2]
      _ = (L : ℝ) := Real.sq_sqrt hLnn
  have hxge : 18 * B + 1 ≤ x := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hx0 ?_
    rw [hx4]
    exact hpow
  have hx1 : (1 : ℝ) ≤ x := by nlinarith
  have hlog := log_two_add_two_mul_le (L := L) hL1
  have hlognn : (0 : ℝ) ≤ Real.log (2 + 2 * (L : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hkey : 2 * B + 16 * B * x ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxge) hx0, mul_nonneg (by linarith : (0:ℝ) ≤ B)
      (sub_nonneg.mpr hx1)]
  calc A * (2 + 2 * Real.log (2 + 2 * (L : ℝ)))
      ≤ B * (2 + 2 * Real.log (2 + 2 * (L : ℝ))) := by nlinarith
    _ ≤ B * (2 + 2 * (8 * x)) := by nlinarith
    _ = 2 * B + 16 * B * x := by ring
    _ ≤ x ^ 2 := hkey
    _ = Real.sqrt (L : ℝ) := hx2

/-! ## The deterministic step: the diameter tail is the connectivity tail -/

/-- **S1 at scale `L` from the complement of one diameter-failure event.**

If no bad `J`-step component meeting `B_{2L}(z)` has `ℓ∞` diameter exceeding `L / 100` — that
is, if `ω` avoids `badComponentFailureEvent E Cbox J z (2L) (L/100)` — then the proved Timár
lemma gives the good connectivity of `B_L(z)` inside `B_{2L}(z)` at every diameter threshold
`D ≥ L / 20`, in particular at the threshold `L / 20` of `chemicalDistanceFailureEvent`.

This is `goodConnectedInDoubleBallAt_of_timarBoundaryComponentConnectivity` with its
hypothesis read as the complement of an event. -/
theorem goodConnectedInDoubleBallAt_of_not_mem_badComponentFailureEvent
    (hd : 2 ≤ d) {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} (hJ : 1 ≤ J) {ω : Ω}
    {z : Lattice d} {L : ℕ} {D : ℝ} (hD : (L : ℝ) / 20 ≤ D)
    (h : ω ∉ badComponentFailureEvent E Cbox J z (2 * L : ℝ) ((L : ℝ) / 100)) :
    GoodConnectedInDoubleBallAt E Cbox ω z L D := by
  refine goodConnectedInDoubleBallAt_of_timarBoundaryComponentConnectivity hd
    (timarBoundaryComponentConnectivity d) hJ ω z L hD ?_
  intro v hv hvbad
  by_contra hcon
  exact h ⟨v, hv, hvbad, hcon⟩

/-- The contrapositive, as an inclusion of events. -/
theorem not_goodConnected_subset_badComponentFailureEvent
    (hd : 2 ≤ d) (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (hJ : 1 ≤ J)
    (z : Lattice d) (L : ℕ) {D : ℝ} (hD : (L : ℝ) / 20 ≤ D) :
    {ω : Ω | ¬ GoodConnectedInDoubleBallAt E Cbox ω z L D} ⊆
      badComponentFailureEvent E Cbox J z (2 * L : ℝ) ((L : ℝ) / 100) := by
  intro ω hω
  by_contra hcon
  exact hω (goodConnectedInDoubleBallAt_of_not_mem_badComponentFailureEvent hd hJ hD hcon)

/-! ## The tail of the diameter-failure event at a fixed scale -/

/-- **The bad-component diameter tail at a fixed scale `L`, with rate `exp (-c q √L)`.**

For every dimension `d ≥ 2`, box constant `Cbox ≥ 1`, dependence constant `Cdep` and pair of
positive probability constants `(Cprob, cprob)` there are a threshold `q0`, a scale threshold
`L0 ≥ 1` and a rate `crate > 0`, none of them depending on the field, such that every field
satisfying the multiscale-percolation hypotheses at a parameter `q ≥ q0` obeys

```text
    mu {some bad 1-step component meeting B_{2L}(z) has ℓ∞ diameter > L / 100}
      ≤ exp (-crate * q * √L)                        for every centre z and every L ≥ L0.
```

This is residual 1 of the linear length budget, proved.  The route is *not* the level-adapted contour argument
proposed there: it is the already-proved clause-(ii) estimate
`measure_asdDiameterFailure_le`, evaluated at the largest level `h` whose clause-(ii) diameter
threshold `C (1 + h + q⁻¹ log (2 + 2 L)) ^ 2` still fits under `L / 100`, namely
`h = ⌊√(L / (100 C)) / 2⌋`.  The `√L` rate is what that substitution yields; the contour
argument would give the sharper `exp (-c q L)`, which the consumer does not need. -/
theorem exists_badComponentDiameter_tail (d Cbox Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 L0 : ℕ, ∃ crate : ℝ, 1 ≤ L0 ∧ 0 < crate ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∀ (z : Lattice d) (L : ℕ), L0 ≤ L →
          mu (badComponentFailureEvent E Cbox 1 z (2 * L : ℝ) ((L : ℝ) / 100)) ≤
            ENNReal.ofReal (Real.exp (-(crate * q * Real.sqrt (L : ℝ)))) := by
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
  have hsqrtC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCpos
  obtain ⟨q1, hq1⟩ := exists_uniform_threshold (c := cprob)
    (X := 2 * Real.log ((((3 * Cbox) ^ d : ℕ) : ℝ) * Cprob)) hcprob
  obtain ⟨q2, hq2⟩ := exists_uniform_threshold (c := cprob)
    (X := 2 * (d : ℝ) * Real.log 3) hcprob
  obtain ⟨q3, hq3⟩ := exists_uniform_threshold (c := asdKappa Cbox Cdep cprob)
    (X := 32 * (d : ℝ) * Real.exp 80) hkappa
  obtain ⟨L0, hL0one, hL0⟩ := exists_threshold_sqrt_dominates_log (10 * Real.sqrt C)
  refine ⟨max 1 (max q1 (max q2 q3)), L0,
    asdAlpha Cbox Cdep cprob C / (20 * Real.sqrt C), hL0one, by positivity, ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw z L hLL0
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
  -- the level realising the threshold `L / 100`
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  set Lam : ℝ := Real.sqrt (L : ℝ) / (10 * Real.sqrt C) with hLamdef
  have hLam0 : 0 ≤ Lam := by positivity
  set h : ℕ := ⌊Lam / 2⌋₊ with hhdef
  have hfl : (h : ℝ) ≤ Lam / 2 := Nat.floor_le (by positivity)
  have hfg : Lam / 2 < (h : ℝ) + 1 := Nat.lt_floor_add_one _
  have hhnn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hlognn : (0 : ℝ) ≤ Real.log (2 + 2 * (L : ℝ)) := Real.log_nonneg (by linarith)
  have hlogthr : 2 + 2 * Real.log (2 + 2 * (L : ℝ)) ≤ Lam := by
    have h2 : (2 + 2 * Real.log (2 + 2 * (L : ℝ))) * (10 * Real.sqrt C) ≤
        Real.sqrt (L : ℝ) := by
      rw [mul_comm]; exact hL0 L hLL0
    rw [hLamdef, le_div_iff₀ (by positivity)]
    exact h2
  have hqinv : q⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hqone
  have hqinvnn : (0 : ℝ) ≤ q⁻¹ := by positivity
  have hmix : q⁻¹ * Real.log (2 + 2 * (L : ℝ)) ≤ Real.log (2 + 2 * (L : ℝ)) := by
    nlinarith
  have hmixnn : (0 : ℝ) ≤ q⁻¹ * Real.log (2 + 2 * (L : ℝ)) := mul_nonneg hqinvnn hlognn
  have hS : 1 + (h : ℝ) + q⁻¹ * Real.log (2 + 2 * (L : ℝ)) ≤ Lam := by linarith
  have hSnn : (0 : ℝ) ≤ 1 + (h : ℝ) + q⁻¹ * Real.log (2 + 2 * (L : ℝ)) := by linarith
  have hcast : (((2 * L : ℕ)) : ℝ) = 2 * (L : ℝ) := by push_cast; ring
  have hCLam : C * Lam ^ 2 = (L : ℝ) / 100 := by
    have hsq2 : Real.sqrt (L : ℝ) ^ 2 = (L : ℝ) := Real.sq_sqrt hLnn
    have hsqC : Real.sqrt C ^ 2 = C := Real.sq_sqrt hCpos.le
    rw [hLamdef, div_pow, mul_pow, hsq2, hsqC]
    field_simp
    ring
  have hradius : asdBadRadius C q h (2 * L) ≤ (L : ℝ) / 100 := by
    have hsq : (1 + (h : ℝ) + q⁻¹ * Real.log (2 + 2 * (L : ℝ))) ^ 2 ≤ Lam ^ 2 :=
      pow_le_pow_left₀ hSnn hS 2
    rw [asdBadRadius, hcast, ← hCLam]
    exact mul_le_mul_of_nonneg_left hsq hCpos.le
  have hsub : badComponentFailureEvent E Cbox 1 z (2 * L : ℝ) ((L : ℝ) / 100)
      ⊆ asdDiameterFailure E Cbox C q z h := by
    intro omega homega
    refine Set.mem_iUnion.mpr ⟨2 * L, ?_⟩
    rw [hcast]
    exact badComponentFailureEvent_antitone E Cbox 1 z (2 * (L : ℝ)) hradius homega
  have hLamhalf : Lam / 2 ≤ 1 + (h : ℝ) := by linarith
  have heq : asdAlpha Cbox Cdep cprob C / (20 * Real.sqrt C) * q * Real.sqrt (L : ℝ)
      = asdAlpha Cbox Cdep cprob C * q * (Lam / 2) := by
    rw [hLamdef]
    field_simp
    ring
  have hexp : asdAlpha Cbox Cdep cprob C / (20 * Real.sqrt C) * q * Real.sqrt (L : ℝ)
      ≤ asdAlpha Cbox Cdep cprob C * q * (1 + (h : ℝ)) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left hLamhalf (mul_nonneg halphapos.le hqpos.le)
  calc mu (badComponentFailureEvent E Cbox 1 z (2 * L : ℝ) ((L : ℝ) / 100))
      ≤ mu (asdDiameterFailure E Cbox C q z h) := measure_mono hsub
    _ ≤ ENNReal.ofReal
          (Real.exp (-(asdAlpha Cbox Cdep cprob C * q * (1 + (h : ℝ))))) :=
        measure_asdDiameterFailure_le mu (by omega) hCbox hCprob hcprob hqpos hC3
          hth1 hth2 hgate halpha hlaw.1 hsc hr hprob z h
    _ ≤ ENNReal.ofReal (Real.exp
          (-(asdAlpha Cbox Cdep cprob C / (20 * Real.sqrt C) * q * Real.sqrt (L : ℝ)))) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

/-! ## The connectivity half of `D_L(z)` -/

/-- **The connectivity half of `UniformChemicalDistanceBoundBox`, proved.**

At every fixed scale `L ≥ L0` the good sites of `B_L(z)` lying in good components of diameter
at least `L / 20` are joined inside `B_{2L}(z)`, off an event of probability at most
`exp (-crate q √L)`.  Nothing external is used: the diameter tail is
`exists_badComponentDiameter_tail` and the deterministic step is the proved Timár lemma.

The event is not asserted measurable; `measure_mono` needs only the inclusion, and the bound is
therefore a bound on the outer measure of the failure set, which is what every consumer uses. -/
theorem exists_connectivity_tail (d Cbox Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 L0 : ℕ, ∃ crate : ℝ, 1 ≤ L0 ∧ 0 < crate ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∀ (z : Lattice d) (L : ℕ), L0 ≤ L → ∀ D : ℝ, (L : ℝ) / 20 ≤ D →
          mu {omega | ¬ GoodConnectedInDoubleBallAt E Cbox omega z L D} ≤
            ENNReal.ofReal (Real.exp (-(crate * q * Real.sqrt (L : ℝ)))) := by
  obtain ⟨q0, L0, crate, hL0, hcrate, hbound⟩ :=
    exists_badComponentDiameter_tail d Cbox Cdep Cprob cprob hd hCbox hCprob hcprob
  refine ⟨q0, L0, crate, hL0, hcrate, ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw z L hLL0 D hD
  refine le_trans (measure_mono ?_) (hbound mu E q hq hprob hsc hr hlaw z L hLL0)
  exact not_goodConnected_subset_badComponentFailureEvent hd E Cbox 1 le_rfl z L hD

/-! ## What is left: the length half -/

/-- **The length residual, isolated.**  Two good sites of `B_L(z)`, joined by good sites of
`B_{2L}(z)`, that are *not* joined by a good path with at most `Clen * L` vertices.

`GoodConnectedInDoubleBallAt` supplies the connection; it supplies no length control, and
`Section9ChemicalScheduleLabyrinthRefutation` shows the good chemical distance around an
obstacle can be quadratic in its radius, so the length is not bounded by the diameters of the
bad components that were detoured.  This event is exactly residual 2 of the linear length budget. -/
def chemicalLengthFailureEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (Clen : ℝ)
    (z : Lattice d) (L : ℕ) : Set Ω :=
  {omega | ∃ v w : Lattice d,
      InLatticeBallReal z v L ∧ InLatticeBallReal z w L ∧
      JStepReachableIn 1
        {u | IsPercolationGoodSite E Cbox omega u ∧ InLatticeBallReal z u (2 * L : ℝ)} v w ∧
      ¬ IsShortGoodPath E Cbox omega (Clen * L) v w}



theorem chemicalDistanceFailureEvent_subset_union (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) (z : Lattice d) (L : ℕ) :
    chemicalDistanceFailureEvent E Cbox Clen z L ⊆
      {omega | ¬ GoodConnectedInDoubleBallAt E Cbox omega z L ((L : ℝ) / 20)} ∪
        chemicalLengthFailureEvent E Cbox Clen z L := by
  rintro omega ⟨v, w, hv, hw, hvc, hwc, hshort⟩
  by_cases hconn : GoodConnectedInDoubleBallAt E Cbox omega z L ((L : ℝ) / 20)
  · exact Or.inr ⟨v, w, hv, hw, hconn v w hv hw hvc hwc, hshort⟩
  · exact Or.inl hconn



theorem measure_chemicalDistanceFailureEvent_le_of_length
    [MeasurableSpace Ω] (mu : Measure Ω) {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ}
    {z : Lattice d} {L : ℕ} {a b : ℝ}
    (hconn : mu {omega | ¬ GoodConnectedInDoubleBallAt E Cbox omega z L ((L : ℝ) / 20)}
      ≤ ENNReal.ofReal a)
    (hlen : mu (chemicalLengthFailureEvent E Cbox Clen z L) ≤ ENNReal.ofReal b) :
    mu (chemicalDistanceFailureEvent E Cbox Clen z L) ≤ ENNReal.ofReal a + ENNReal.ofReal b :=
  le_trans (measure_mono (chemicalDistanceFailureEvent_subset_union E Cbox Clen z L))
    (le_trans (measure_union_le _ _) (add_le_add hconn hlen))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
