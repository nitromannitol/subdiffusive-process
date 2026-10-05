module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingExtract

@[expose] public section

/-!
# The bad-component diameter tail, at a linear rate

`Section9ChemicalASDDiameterTail.measure_badComponentFailureEvent_le` bounds
the probability that a bad `1`-step component of `ℓ∞` diameter above `R` meets a ball, at rate
`exp (-c q √R)`: the `[ASD]` route charges the crossing of a box of side `R` to a **single**
level-`k` event with `3 ^ k ≍ R`, and that event's own rate `3 ^ (3k/2)` is only `R ^ (3/2)`
*after* it has paid an entropy that costs a square root.

The contour machinery built for clause (i) of the anchor
(`Section9ChemicalCrossingCells`–`Section9ChemicalCrossingScale`) does strictly better, and it
is already proved.  A bad component of diameter `D` through `x` contains a bad `1`-step path
from `x` to a site at distance `D`; `exists_chain_from_index` reads a **chain of cells** off
that path, and — this is the point — the path has *no good vertex at all*, so the certificate
carries the good-vertex budget `0`.  The radial coverage `crossChain_le_radius_sum` then gives

```text
    D ≤ 6 ∑ (cell radii) + 3 (number of cells) ,
```

and `Section9ChemicalCrossingGain` converts that into the gain `exp (-c q D)`, **linear** in
the diameter.  The entropy is the same polynomial `(D+1) ^ d` as for a crossing, and the
good-budget factor `(4 κ) ^ (N+2)` is a constant because `N = 0`.

## Main results

* `exists_isJStepPath_of_jStepReachableIn` — an indexed path from a list path.
* `badDiameterEvent`, `exists_crossChain_of_badDiameterEvent` — the certificate, with
  `goodCellCount = 0`.
* `measure_le_of_forall_exists_crossChain` — the certificate union bound, with the failure
  event left abstract (the proof of `measure_crossFailEvent_le`, with its one crossing-specific
  step hypothesised).
* `measure_badDiameterEvent_le_exp` — `P[ the bad component of `x` has diameter ≥ D ] ≤
  exp (-c q D)` at the same explicit thresholds on `q` as the crossing estimate.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## Indexed form of a list path -/

/-- A `J`-step connection inside `S` in indexed form. -/
theorem exists_isJStepPath_of_jStepReachableIn {J : ℕ} {S : Set (Lattice d)}
    {x y : Lattice d} (h : JStepReachableIn J S x y) :
    ∃ (p : ℕ → Lattice d) (b : ℕ), IsJStepPath J p b ∧ p 0 = x ∧ p b = y ∧
      ∀ i, i ≤ b → p i ∈ S := by
  classical
  obtain ⟨path, hhead, hlast, hstep, hmem⟩ := h
  have hne : path ≠ [] := by
    intro hc
    rw [hc] at hhead
    simp at hhead
  have hpos : 0 < path.length := List.length_pos_iff.mpr hne
  refine ⟨fun i => path[i]!, path.length - 1, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact hstep i (by omega)
  · show path[0]! = x
    have h0 : path[0]! = path[0] := getElem!_pos path 0 hpos
    rw [h0]
    rw [List.head?_eq_getElem?] at hhead
    have : path[0]? = some x := hhead
    rw [List.getElem?_eq_getElem hpos] at this
    exact Option.some_injective _ this
  · show path[path.length - 1]! = y
    have hlt : path.length - 1 < path.length := by omega
    have h0 : path[path.length - 1]! = path[path.length - 1] :=
      getElem!_pos path (path.length - 1) hlt
    rw [h0]
    rw [List.getLast?_eq_getElem?] at hlast
    have : path[path.length - 1]? = some y := hlast
    rw [List.getElem?_eq_getElem hlt] at this
    exact Option.some_injective _ this
  · intro i hi
    show path[i]! ∈ S
    have hlt : i < path.length := by omega
    have h0 : path[i]! = path[i] := getElem!_pos path i hlt
    rw [h0]
    exact hmem _ (List.getElem_mem hlt)

/-! ## The certificate of a large bad component -/

/-- The event that the bad `1`-step component of `x` reaches `ℓ∞` distance `D`.

Note that this already forces `x` itself to be bad: `jStepComponent` is empty at a good site. -/
def badDiameterEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (x : Lattice d) (D : ℕ) :
    Set Ω :=
  {ω | ∃ y : Lattice d,
      y ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u} x ∧
        D ≤ latticeDist x y}

theorem badDiameterEvent_antitone (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (x : Lattice d)
    {D D' : ℕ} (h : D ≤ D') :
    badDiameterEvent E Cbox x D' ⊆ badDiameterEvent E Cbox x D := by
  rintro ω ⟨y, hy, hD⟩
  exact ⟨y, hy, le_trans (by exact_mod_cast h) hD⟩

/-- **A large bad component is a crossing certificate with no good vertex.**

The certificate is read off the bad path by `exists_chain_from_index` at the centre `x` and
the scale `D`; because every vertex of the path is bad, the walk never emits a good-vertex
cell, so the good budget is `0`. -/
theorem exists_crossChain_of_badDiameterEvent (E : ℕ → Lattice d → Set Ω)
    (Cbox Cdep : ℕ) (ω : Ω) (x : Lattice d) (D : ℕ) (hD : 1 ≤ D)
    (hω : ω ∈ badDiameterEvent E Cbox x D) :
    ∃ L : List (CrossCell d), CrossChain Cbox Cdep 1 x D L ∧ L.Nodup ∧
      ω ∈ chainEvent E Cdep L ∧ goodCellCount L ≤ 0 + 2 := by
  classical
  obtain ⟨y, hy, hdy⟩ := hω
  obtain ⟨p, b, hp, hp0, hpb, hpmem⟩ := exists_isJStepPath_of_jStepReachableIn hy
  have hout : 2 * D < 3 * latticeDist x (p b) := by
    rw [hpb]
    omega
  obtain ⟨L, hne, hchain, hev, hhead, hlast, hgc⟩ :=
    exists_chain_from_index E Cbox Cdep 1 ω x D p b hp hout 0 (Nat.zero_le _)
  obtain ⟨L', hchain', hsub', hhead', hlast', hnd'⟩ := exists_nodup_isChain L hchain
  have hne' : L' ≠ [] := by
    intro hc
    rw [hc] at hhead'
    rcases L with _ | ⟨e, Lt⟩
    · exact hne rfl
    · simp at hhead'
  have hnogood : ∀ v : Lattice d, Sum.inr v ∉ L' := by
    intro v hv
    obtain ⟨i, -, hib, rfl, hgood⟩ := hgc v (hsub'.subset hv)
    exact (hpmem i hib) hgood
  refine ⟨L', ⟨hne', hchain', ?_, ?_⟩, hnd', ?_, ?_⟩
  · intro c hc
    rw [hhead'] at hc
    have hcov := hhead c hc
    rw [hp0] at hcov
    omega
  · intro c hc
    rw [hlast'] at hc
    exact hlast c hc
  · intro c hc
    exact hev c (hsub'.subset hc)
  · have hfilter : L'.filter (fun c => c.isRight) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcr
      cases c with
      | inl q => simp at hcr
      | inr v => exact hnogood v hc
    rw [goodCellCount, hfilter]
    simp

/-! ## The certificate union bound, with the failure event abstract -/

/-- **The certificate union bound.**

Verbatim the assembly of `Section9ChemicalCrossingTail.measure_crossFailEvent_le`, with the
one crossing-specific step — that the failure event produces a certificate — taken as a
hypothesis.  Every other ingredient (`measure_chainEvent_le`, the gain split of
`Section9ChemicalCrossingGain`, the certificate weight sum `tsum_crossChain_le`) is
independent of what the certificate certifies. -/
theorem measure_le_of_forall_exists_crossChain [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep J : ℕ)
    {Cprob cprob q : ℝ} (hcq : 0 ≤ cprob * q)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hpi : 8 * crossBranch d J * crossBranch d J *
      crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤ 2 * crossBranch d J)
    (z : Lattice d) (l N : ℕ) (hCbox1 : 1 ≤ Cbox) (A : Set Ω)
    (hA : ∀ ω ∈ A, ∃ L : List (CrossCell d), CrossChain Cbox Cdep J z l L ∧ L.Nodup ∧
      ω ∈ chainEvent E Cdep L ∧ goodCellCount L ≤ N + 2) :
    mu A ≤
      ENNReal.ofReal (Real.exp (-(cprob / 2 / 2 ^ d) * q *
        (((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) /
          (6 * ((Cbox + Cdep : ℕ) : ℝ) + 3 * (J : ℝ))))) *
        ((((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) *
          (2 * (4 * crossBranch d J) ^ (N + 2)) *
          (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q)) := by
  classical
  set gb : ℕ := N + 2 with hgb
  set Ac : ℝ := 6 * ((Cbox + Cdep : ℕ) : ℝ) + 3 * (J : ℝ) with hAc
  have hAcpos : 0 < Ac := by
    have h1 : (1 : ℝ) ≤ ((Cbox + Cdep : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    have h2 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
    rw [hAc]; linarith
  set beta : ℝ := cprob / 2 / 2 ^ d with hbeta
  set G : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-beta * q * (((l : ℝ) -
    3 * (J : ℝ) * ((N : ℝ) + 2)) / Ac))) with hG
  set S : Set (List (CrossCell d)) :=
    {L | CrossChain Cbox Cdep J z l L ∧ L.Nodup ∧ goodCellCount L ≤ gb} with hS
  set w : CrossCell d → ℝ≥0∞ := cellWeight d Cdep Cprob cprob q with hw
  set wh : CrossCell d → ℝ≥0∞ := cellWeight d Cdep Cprob (cprob / 2) q with hwh
  have hsub : A ⊆ ⋃ L ∈ S, chainEvent E Cdep L := by
    intro ω hω
    obtain ⟨L, hcc, hnd, hev, hgc⟩ := hA ω hω
    exact Set.mem_biUnion (show L ∈ S from ⟨hcc, hnd, hgc⟩) hev
  have hgain : ∀ L : List (CrossCell d), L ∈ S →
      (L.map w).prod ≤ G * (L.map wh).prod := by
    intro L hL
    rw [prod_map_cellWeight_eq d Cdep Cprob cprob q L, prod_map_crossGain d cprob q L]
    refine mul_le_mul' ?_ le_rfl
    rw [hG]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hkey := le_sum_cellTau hL.1 hL.2.2
    have hbq : 0 ≤ beta * q := by
      rw [hbeta]
      have h2 : (0 : ℝ) < 2 ^ d := by positivity
      have hrw : cprob / 2 / 2 ^ d * q = cprob * q / 2 / 2 ^ d := by ring
      rw [hrw]
      positivity
    have hdiv : ((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) / Ac ≤ (L.map cellTau).sum := by
      rw [div_le_iff₀ hAcpos]
      have hgbR : ((gb : ℕ) : ℝ) = (N : ℝ) + 2 := by rw [hgb]; push_cast; ring
      rw [hgbR] at hkey
      nlinarith [hkey]
    nlinarith [hdiv, hbq]
  calc mu A
      ≤ mu (⋃ L ∈ S, chainEvent E Cdep L) := measure_mono hsub
    _ ≤ ∑' L : S, mu (chainEvent E Cdep (L : List (CrossCell d))) :=
        measure_biUnion_le mu S.to_countable _
    _ ≤ ∑' L : S, G * ((L : List (CrossCell d)).map wh).prod := by
        refine ENNReal.tsum_le_tsum fun L => ?_
        exact le_trans (measure_chainEvent_le mu Cdep hsc hr hprob
          (L : List (CrossCell d)) L.2.2.1) (hgain _ L.2)
    _ = G * ∑' L : S, ((L : List (CrossCell d)).map wh).prod := ENNReal.tsum_mul_left
    _ ≤ G * ∑' L : List (CrossCell d),
          (if CrossChain Cbox Cdep J z l L ∧ goodCellCount L ≤ gb then
            (L.map wh).prod else 0) := by
        refine mul_le_mul' le_rfl ?_
        rw [tsum_subtype S (fun L => (L.map wh).prod)]
        refine ENNReal.tsum_le_tsum fun L => ?_
        by_cases hLS : L ∈ S
        · rw [Set.indicator_of_mem hLS, ite_eq_left ⟨hLS.1, hLS.2.2⟩]
        · rw [Set.indicator_of_notMem hLS]
          exact zero_le
    _ ≤ G * ((((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) *
          (2 * (4 * crossBranch d J) ^ gb) *
          (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q)) :=
        mul_le_mul' le_rfl (tsum_crossChain_le Cbox Cdep J Cprob (cprob / 2) q z l gb hpi)

/-! ## The diameter tail, at a linear rate -/

/-- **The bad-component diameter tail, linear in the diameter.**

For `q` above the same explicit thresholds as the crossing estimate, and every `D ≥ 24`,

```text
    P[ the bad 1-step component of x reaches distance D ] ≤ exp (-c q D) ,
    c = crossRate d Cbox Cdep 1 cprob .
```

Compare `Section9ChemicalASDDiameterTail.measure_badComponentFailureEvent_le`, whose rate is
`exp (-c q √D)`: the gain here is the *whole* radial coverage of the certificate, because a
bad component contributes no good-vertex cells. -/
theorem measure_badDiameterEvent_le_exp [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep : ℕ)
    {Cprob cprob q : ℝ} (hcprob : 0 < cprob) (hq0 : 0 ≤ q) (hCbox : 1 ≤ Cbox)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ crossBeta d cprob * q)
    (hth2 : Real.log (8 * ((2 ^ d * (1 + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ crossBeta d cprob * q)
    (hth3 : crossEntropy d Cbox Cdep 1 Cprob ≤
      crossBeta d cprob * q / (4 * crossAc Cbox Cdep 1))
    (x : Lattice d) (D : ℕ) (hD : 24 ≤ D) :
    mu (badDiameterEvent E Cbox x D) ≤
      ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q * (D : ℝ))) := by
  classical
  set kn : ℝ := ((2 ^ d * (1 + 1) ^ d : ℕ) : ℝ) with hkn
  set B : ℝ := crossScaleConst d Cbox Cdep Cprob with hB
  set beta : ℝ := crossBeta d cprob with hbeta
  set Ac : ℝ := crossAc Cbox Cdep 1 with hAc
  have hknpos : (1 : ℝ) ≤ kn := by
    rw [hkn]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hBpos : 0 < B := crossScaleConst_pos d Cbox Cdep Cprob
  have hbetapos : 0 < beta := crossBeta_pos hcprob
  have hAcpos : 0 < Ac := crossAc_pos hCbox
  have hbranch : crossBranch d 1 = ENNReal.ofReal kn := by
    rw [crossBranch, hkn, ENNReal.ofReal_natCast]
  have hbq : 0 ≤ beta * q := mul_nonneg hbetapos.le hq0
  have hpi := crossScaleSum_small d Cbox Cdep 1
    (by rw [hbeta] at *; exact hth1) (by rw [hbeta, hkn, hB] at *; exact hth2)
  have hss : crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤
      ENNReal.ofReal (2 * (B * Real.exp (-(beta * q)))) := by
    have h := crossScaleSum_le d Cbox Cdep (Cprob := Cprob) (cprob := cprob / 2)
      (q := q) (by rw [hbeta, crossBeta] at hth1; exact hth1)
    rw [hB, hbeta, crossBeta]
    exact h
  have hD1 : 1 ≤ D := by omega
  have hmain := measure_le_of_forall_exists_crossChain mu E Cbox Cdep 1
    (Cprob := Cprob) (cprob := cprob) (q := q) (mul_nonneg hcprob.le hq0) hsc hr hprob
    hpi x D 0 hCbox (badDiameterEvent E Cbox x D)
    (fun ω hω => exists_crossChain_of_badDiameterEvent E Cbox Cdep ω x D hD1 hω)
  refine hmain.trans ?_
  have hNR : ((0 : ℕ) : ℝ) * (12 * ((1 : ℕ) : ℝ) + 12) ≤ (D : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
    linarith
  have hgain : -beta * q * (((D : ℝ) - 3 * ((1 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) + 2)) / Ac) ≤
      -(beta * q) * (D : ℝ) / (2 * Ac) := by
    rw [hAc]
    exact crossGain_le hbetapos.le hq0 hCbox (by omega) hNR
  have hentropy := crossEntropy_bound d Cbox Cdep 1 Cprob (N := 0) (l := D)
    (by omega) (Nat.zero_le _)
  have hPr : (((2 ^ d * (D + 1) ^ d : ℕ)) : ℝ≥0∞) *
      (2 * (4 * crossBranch d 1) ^ (0 + 2)) *
      (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q) ≤
      ENNReal.ofReal (((2 ^ d * (D + 1) ^ d : ℕ) : ℝ) * 2 *
        (4 * kn) ^ (0 + 2) * (1 + 2 * B)) := by
    have h1 : (1 : ℝ≥0∞) + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤
        ENNReal.ofReal (1 + 2 * B) := by
      refine le_trans (add_le_add le_rfl hss) ?_
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp1 : Real.exp (-(beta * q)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      nlinarith [hBpos, hexp1]
    have h2 : (4 : ℝ≥0∞) * crossBranch d 1 = ENNReal.ofReal (4 * kn) := by
      rw [hbranch, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
    calc (((2 ^ d * (D + 1) ^ d : ℕ)) : ℝ≥0∞) *
          (2 * (4 * crossBranch d 1) ^ (0 + 2)) *
          (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q)
        ≤ (((2 ^ d * (D + 1) ^ d : ℕ)) : ℝ≥0∞) *
            (2 * (4 * crossBranch d 1) ^ (0 + 2)) * ENNReal.ofReal (1 + 2 * B) :=
          mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (((2 ^ d * (D + 1) ^ d : ℕ) : ℝ) * 2 *
            (4 * kn) ^ (0 + 2) * (1 + 2 * B)) := by
          rw [h2, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  refine le_trans (mul_le_mul' le_rfl hPr) ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.exp (-(beta) * q * (((D : ℝ) -
        3 * ((1 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) + 2)) / Ac)) *
        (((2 ^ d * (D + 1) ^ d : ℕ) : ℝ) * 2 * (4 * kn) ^ (0 + 2) * (1 + 2 * B))
      ≤ Real.exp (-(beta * q) * (D : ℝ) / (2 * Ac)) *
          Real.exp (crossEntropy d Cbox Cdep 1 Cprob * (D : ℝ)) := by
        refine mul_le_mul (Real.exp_le_exp.mpr hgain) hentropy (by positivity)
          (Real.exp_pos _).le
    _ = Real.exp (-(beta * q) * (D : ℝ) / (2 * Ac) +
          crossEntropy d Cbox Cdep 1 Cprob * (D : ℝ)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q * (D : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have hlR : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
        have hrate : crossRate d Cbox Cdep 1 cprob = beta / (4 * Ac) := by
          rw [crossRate, hbeta, hAc]
        rw [hrate]
        have hmul := mul_le_mul_of_nonneg_right hth3 hlR
        have hAc4 : (0 : ℝ) < 4 * Ac := by linarith
        have hkey : -(beta * q) * (D : ℝ) / (2 * Ac) +
            beta * q / (4 * Ac) * (D : ℝ) = -(beta * q / (4 * Ac)) * (D : ℝ) := by
          field_simp
          ring
        have hgoal : -(beta / (4 * Ac)) * q * (D : ℝ) =
            -(beta * q / (4 * Ac)) * (D : ℝ) := by
          field_simp
        rw [hgoal, ← hkey]
        linarith [hmul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
