module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTranslation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock

@[expose] public section

/-!
# The good-cube provider assembly

This file assembles `SubdiffusiveProcess.Section9.weighted_good_cube_events` from

* the **deterministic** clauses, which are proved:
  `exists_smallness_depth` (clause 5) and `exists_isLocalCubeGeometry`
  (clause 6), packaged as `exists_depth_geometry_of_constant`;
* the **structural probabilistic** clauses, which are proved for the concrete
  field `goodCubeEventField` from clause 7a alone: 7b, 7d, 7e
  (`goodCubeEventField_clauses`) and 7f
  (`translationInvariantEventLaw_goodCubeEventField`);
* clause 7c for every layer `j ≥ 1` (`measure_layerEvent_le_cover`, this
  package, with the covering prefactor);
* one **named hypothesis per remaining clause**: the layer-zero locality
  (7a, with the theta-ladder refinement of §5), the
  layer-zero tail (7c at `j = 0`), the layer-zero covariance
  (part of 7f), and the eight analytic displays of clause 7g (the seven Section 8
  support-input anchors plus the Section 6 oscillation).

## The two constants (finding P343-F1)

The statement uses a single `C` both as the *box factor* of clauses
7a/7b and as the *tail prefactor* of clause 7c.  The covering count of the
layer tail is a function of the box factor, so a provider may not identify
them.  The assembly therefore separates them: the events are constructed with
a box factor `B`, and `C` is any constant dominating `B`, the covering count
`card (shellCoverShifts d r)` (for a depth `r` with `B < 3^r`) and the
analytic/tail constants.  Every clause is monotone in `C` in the easy
direction, and `Cdep` is only constrained from below by `B + √d`.

## The constants and their `j1, j2`-independent
(P338-F1)

`c, C, eps0, p0, Cdep, B, eps1, r` are inputs of `..._of_supportInputs`, and
none of the hypotheses that constrain them mentions `j1` or `j2` except
`hsmall` and `hgeom`.  The corollary
`weighted_good_cube_events_of_supportInputs_depths` discharges exactly those
two by `exists_depth_geometry_of_constant` *after* `C` is fixed, which is the
binder order the anchor requires.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Homogenization MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open _root_.SubdiffusiveProcess.Model

variable {d : ℕ}

/-! ## Two arithmetic inputs -/

theorem exists_zpow_gt (C : ℝ) : ∃ r : ℤ, C < (3 : ℝ) ^ r := by
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  refine hn.trans_le ?_
  exact_mod_cast (Nat.lt_pow_self (by norm_num)).le

/-- **The exponent transfer of clause 7c.**  The layer tail is proved with the
exponent `layerTailConstant · ε₁² δ^{-2}`; the anchor prints
`c · (c / (δ² log²δ))`.  The second is below the first for every admissible
`δ ≤ c` as soon as `c ≤ 1/3` and `c ≤ √(layerTailConstant)·ε₁`: the first
condition forces `|log δ| ≥ 1`, and the second is `c² ≤ layerTailConstant·ε₁²`. -/
theorem tail_exponent_transfer {delta c eps1 K : ℝ}
    (hK : 0 < K) (hdelta0 : 0 < delta) (hdelta : delta ≤ c)
    (hc3 : c ≤ 1 / 3) (hcK : c ≤ Real.sqrt K * eps1) :
    c * (c / (delta ^ 2 * Real.log delta ^ 2)) ≤ K * (eps1 ^ 2 / delta ^ 2) := by
  have hd2 : (0 : ℝ) < delta ^ 2 := by positivity
  have hexp3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hmul : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  have hepos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have h13 : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  have hde : delta ≤ Real.exp (-1) := (hdelta.trans hc3).trans h13
  have hlog : Real.log delta ≤ -1 := by
    have h := Real.log_le_log hdelta0 hde
    rwa [Real.log_exp] at h
  have hlogsq : (1 : ℝ) ≤ Real.log delta ^ 2 := by nlinarith [hlog]
  have hcsq : c ^ 2 ≤ K * eps1 ^ 2 := by
    have hsq : (Real.sqrt K * eps1) ^ 2 = K * eps1 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK.le]
    have heps : 0 < eps1 := by
      by_contra hcon
      push Not at hcon
      nlinarith [Real.sqrt_nonneg K]
    nlinarith [Real.sqrt_nonneg K]
  have key : c ^ 2 / (delta ^ 2 * Real.log delta ^ 2) ≤ K * eps1 ^ 2 / delta ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hd2]
    nlinarith [mul_le_mul_of_nonneg_right hcsq hd2.le,
      mul_le_mul_of_nonneg_left hlogsq
        (mul_nonneg (mul_nonneg hK.le (sq_nonneg eps1)) hd2.le)]
  calc c * (c / (delta ^ 2 * Real.log delta ^ 2))
      = c ^ 2 / (delta ^ 2 * Real.log delta ^ 2) := by ring
    _ ≤ K * eps1 ^ 2 / delta ^ 2 := key
    _ = K * (eps1 ^ 2 / delta ^ 2) := by ring

/-- Ambient measurability of a cutoff evaluation.  (`ACutoffRange.lean` has the
`localSigma` version, but `measurable_aCutoff_eval_local` there is `private`;
this is the ambient re-derivation.) -/
theorem measurable_aCutoff_eval (M : GMCModel d) (n : ℕ) (x : Vec d) :
    Measurable fun omega : PotentialSample d => aCutoff M n omega x := by
  unfold _root_.SubdiffusiveProcess.Model.aCutoff
  refine Measurable.exp (Finset.measurable_sum _ fun k _ => ?_)
  exact ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
    (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)).sub_const _

theorem measurableSet_of_restrictedCoefficientSigma {M : GMCModel d} {n : ℕ}
    {Bset : Set (Vec d)} {s : Set (PotentialSample d)}
    (h : MeasurableSet[restrictedCoefficientSigma
      (fun omega : PotentialSample d => aCutoff M n omega) Bset] s) :
    MeasurableSet s :=
  SubdiffusiveProcess.CoarseGrainingVocab.restrictedCoefficientSigma_le
    (fun x _ => measurable_aCutoff_eval M n x) _ h

/-! ## Choosing the constants -/

/-- **The admissible smallness constant.**  For any construction box factor `B`
and any layer threshold `ε₁` there is a cover depth `r` and a smallness constant
`c` satisfying every constraint the assembly puts on them.  None of the four
conclusions mentions `j1` or `j2`. -/
theorem exists_goodCubeConstants (B eps1 : ℝ) (heps1 : 0 < eps1) :
    ∃ (r : ℤ) (c : ℝ), 0 < c ∧ B < (3 : ℝ) ^ r ∧ c ≤ 1 / 3 ∧
      c ≤ Real.sqrt layerTailConstant * eps1 ∧
      2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * c) ≤ eps1 := by
  obtain ⟨r, hr⟩ := exists_zpow_gt B
  have hK : (0 : ℝ) < Real.sqrt layerTailConstant :=
    Real.sqrt_pos.mpr layerTailConstant_pos
  have hlog : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (by positivity) _
  refine ⟨r, min (1 / 3) (min (Real.sqrt layerTailConstant * eps1)
    (eps1 / (2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹))), ?_, hr, min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  · exact lt_min (by norm_num) (lt_min (mul_pos hK heps1) (by positivity))
  · have hle : min (1 / 3 : ℝ) (min (Real.sqrt layerTailConstant * eps1)
        (eps1 / (2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹))) ≤
        eps1 / (2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹) :=
      (min_le_right (1 / 3 : ℝ) (min (Real.sqrt layerTailConstant * eps1)
        (eps1 / (2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹)))).trans
        (min_le_right (Real.sqrt layerTailConstant * eps1)
          (eps1 / (2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹)))
    have hstep : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ *
        (eps1 / (2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹))) = eps1 := by
      field_simp
    have hmul := mul_le_mul_of_nonneg_left hle hlog.le
    linarith

/-- **P338-F1, mechanically.**  The depths `j1, j2` are produced *after* the
constant `C`, from `C` and `eta` alone: this is exactly the hypothesis pair
`hsmall`/`hgeom` of the assembly, and it is `exists_depth_geometry_of_constant`. -/
theorem exists_depths_for_constant (C eta : ℝ) (hC : 0 < C) (heta : 0 < eta) :
    ∃ j1 j2 : ℕ, 2 ≤ j1 ∧ 1 ≤ j2 ∧
      C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 ∧
      ∀ (n : ℕ) (z : Lattice d),
        ∃ (grid : Finset (Vec d)) (Pfam : Set (Cube d × Cube d))
          (Qfam Afam : Set (Cube d)),
          IsLocalCubeGeometry grid j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
            Pfam Qfam Afam :=
  exists_depth_geometry_of_constant d C eta hC heta

/-! ## The quantifier prefix of the analytic displays -/

/-- The data every display of clause 7g is quantified over: a model with
`δ ≤ c`, a scale, a site, an admissible local geometry at that site, a sample
in the good event of the constructed field, and a local diffusion for the
cutoff coefficient.  Each of the eight hypotheses of the assembly is one
instance of this shape, so that the remaining obligation is visible display by
display. -/
def GoodCubeDisplay (d : ℕ) (c eps1 B : ℝ) (j1 j2 : ℕ)
    (E0 : GMCModel d → ℕ → Lattice d → Set (PotentialSample d))
    (P : GMCModel d → ℕ → Lattice d → PotentialSample d →
      Kernel (Vec d) (Path d) → Set (Cube d × Cube d) → Set (Cube d) →
      Set (Cube d) → Prop) : Prop :=
  ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (grid : Finset (Vec d)) (z : Lattice d)
    (Pfam : Set (Cube d × Cube d)) (Qfam Afam : Set (Cube d)),
    IsLocalCubeGeometry grid j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n) Pfam Qfam Afam →
    ∀ omega ∈ goodCubeEvent (goodCubeEventField n B eps1 (E0 M n)) z,
    ∀ law : Kernel (Vec d) (Path d),
      LocalDiffusion (aCutoff M n omega) (aCutoff M n omega) law →
      P M n z omega law Pfam Qfam Afam

/-! ## The assembly -/

/-- **The good-cube provider, with every remaining obligation as a named
hypothesis.**

Proved outright here: clause 5 (`hsmall`), clause 6 (`hgeom`), clauses 7b, 7d,
7e (`goodCubeEventField_clauses`), clause 7f from `hE0cov` alone
(`translationInvariantEventLaw_goodCubeEventField`), and clause 7c for every
`j ≥ 1` (`measure_layerEvent_le_cover`).

Remaining, one per hypothesis:

| hypothesis | obligation | tex pin |
|---|---|---|
| `hE0meas` | 7a: `restrictedCoefficientSigma (aCutoff M n)`-measurability of `G(U)^c` — with the theta-ladder refinement of §5 |,  |
| `hE0tail` | 7c at `j = 0` (`L^{4q}` bound on `𝒵(U)`) |  |
| `hE0cov` | the layer-zero half of 7f; `covariant_of_recentredFunctional` supplies it for any recentred functional of the cutoff |  |
| `hexit_lower`, `hexit_upper`, `hdescendant` | Step 5, from `local_torsion_survival`, `local_killed_lower`, `local_resolvent_exit_upper` |  |
| `hmass_quarter`, `hmass_descendant`, `hmass_overlap` | the mass tests of `F(U)` |  |
| `hsobolev` | `weighted_local_sobolev` above scale one |  |
| `hoscillation` | `cutoff_holder_bounded_multiplier` through `localHarmonicOscillation_of_depthDecay` |  |
-/
theorem weighted_good_cube_events_of_supportInputs
    [NeZero d] (c C eps0 p0 eps1 B : ℝ) (Cdep j1 j2 : ℕ) (r : ℤ)
    (hc : 0 < c) (hC : 0 < C) (heps0 : 0 < eps0) (hp0 : 2 < p0)
    (hB : 0 ≤ B)
    (hBr : B < (3 : ℝ) ^ r)
    (hNC : ((shellCoverShifts d r).card : ℝ) ≤ C)
    (hBC : B ≤ C)
    (hCdep : B + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ))
    (hc3 : c ≤ 1 / 3)
    (hcK : c ≤ Real.sqrt layerTailConstant * eps1)
    (hcdelta : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * c) ≤ eps1)
    (eta : ℝ)
    (hsmall : C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2)
    (hgeom : ∀ (n : ℕ) (z : Lattice d),
      ∃ (grid : Finset (Vec d)) (Pfam : Set (Cube d × Cube d))
        (Qfam Afam : Set (Cube d)),
        IsLocalCubeGeometry grid j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n) Pfam Qfam Afam)
    (E0 : GMCModel d → ℕ → Lattice d → Set (PotentialSample d))
    (hE0meas : ∀ (M : GMCModel d) (n : ℕ) (z : Lattice d),
      MeasurableSet[restrictedCoefficientSigma
        (fun omega : PotentialSample d => aCutoff M n omega) (nativeBox n B z)] (E0 M n z))
    (hE0tail : ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
      M.P.toMeasure (E0 M n z) ≤ ENNReal.ofReal
        (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2))))))
    (hE0cov : ∀ (M : GMCModel d) (n : ℕ) (z a : Lattice d),
      E0 M n (z + a) =
        (translatePotentialSequence (goodCubeCentre n a)) ⁻¹' (E0 M n z))
    (hexit_lower : GoodCubeDisplay d c eps1 B j1 j2 E0
      (fun M n z _ law _ _ _ =>
        ∀ x ∈ middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n),
          ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) ((3 : ℝ) ^ n)) ≤
            meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x))
    (hexit_upper : GoodCubeDisplay d c eps1 B j1 j2 E0
      (fun M n z _ law _ _ _ =>
        ∀ x ∈ cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n),
          meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x ≤
            ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) ((3 : ℝ) ^ n))))
    (hdescendant : GoodCubeDisplay d c eps1 B j1 j2 E0
      (fun M _ _ _ law _ Qfam _ =>
        ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
          (∀ x ∈ cubeSet B',
            ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2) ≤
              meanExit law (cubeSet Bq) x) ∧
          (∀ x ∈ cubeSet Bq,
            meanExit law (cubeSet Bq) x ≤
              ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2))))
    (hmass_quarter : GoodCubeDisplay d c eps1 B j1 j2 E0
      (fun M n z omega _ _ _ _ =>
        ENNReal.ofReal c *
            weightedMeasure (aCutoff M n omega)
              (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) ≤
          weightedMeasure (aCutoff M n omega)
            (middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n))))
    (hmass_descendant : GoodCubeDisplay d c eps1 B j1 j2 E0
      (fun M n _ omega _ _ Qfam _ =>
        ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
          ENNReal.ofReal c * weightedMeasure (aCutoff M n omega) (cubeSet Bq) ≤
            weightedMeasure (aCutoff M n omega) (cubeSet B')))
    (hmass_overlap : GoodCubeDisplay d c eps1 B j1 j2 E0
      (fun M n z omega _ _ _ Afam =>
        ∀ A ∈ Afam,
          ENNReal.ofReal c *
              weightedMeasure (aCutoff M n omega)
                (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) ≤
            weightedMeasure (aCutoff M n omega) (cubeSet A)))
    (hsobolev : GoodCubeDisplay d c eps1 B j1 j2 E0
      (fun M n _ omega _ _ Qfam _ =>
        ∀ Q ∈ Qfam, ∀ f : H10Function (cubeSet Q),
          lpSq (aCutoff M n omega) (cubeSet Q) p0 f.toH1Function.toFun ≤
            ENNReal.ofReal C *
              weightedMeasure (aCutoff M n omega) (cubeSet Q) ^ (-(1 - 2 / p0)) *
              ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Q.2 *
                energy (aCutoff M n omega) (cubeSet Q) f.toH1Function)))
    (hoscillation : GoodCubeDisplay d c eps1 B j1 j2 E0
      (fun M n _ omega _ Pfam _ _ =>
        LocalHarmonicOscillation (aCutoff M n omega) eps0 Pfam)) :
    ∃ (c' C' eps0' p0' : ℝ) (Cdep' j1' j2' : ℕ),
      0 < c' ∧ 0 < C' ∧ 0 < eps0' ∧ 2 < p0' ∧
      C' * (3 : ℝ) ^ (-(3 * (j1' : ℝ) / 2)) ≤ eta / 2 ∧
      (∀ (n : ℕ) (z : Lattice d),
        ∃ (grid : Finset (Vec d)) (Pfam : Set (Cube d × Cube d))
          (Qfam Afam : Set (Cube d)),
          IsLocalCubeGeometry grid j1' j2' (goodCubeCentre n z, (3 : ℝ) ^ n)
            Pfam Qfam Afam) ∧
      ∀ M : GMCModel d, M.delta ≤ c' →
        ∀ n : ℕ, ∀ grid : Finset (Vec d),
        ∃ E : ℕ → Lattice d → Set (PotentialSample d),
          (∀ z : Lattice d,
            MeasurableSet[restrictedCoefficientSigma
              (fun omega : PotentialSample d => aCutoff M n omega)
              (centeredAxisCube (goodCubeCentre n z) (C' * (3 : ℝ) ^ n))] (E 0 z)) ∧
          (∀ j : ℕ, 1 ≤ j → ∀ z : Lattice d,
            MeasurableSet[shellLocalSigma (n + j)
              (centeredAxisCube (goodCubeCentre n z) (C' * (3 : ℝ) ^ (n + j)))] (E j z)) ∧
          (∀ (j : ℕ) (z : Lattice d),
            M.P.toMeasure (E j z) ≤
              ENNReal.ofReal (C' * Real.exp (-(c' * (c' / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
                (3 : ℝ) ^ (3 * (j : ℝ) / 2))))) ∧
          IndependentEventScales M.P.toMeasure E ∧
          MultiscaleFiniteRangeIndependentEvents M.P.toMeasure (fun j => Cdep' * 3 ^ j) E ∧
          TranslationInvariantEventLaw M.P.toMeasure E ∧
          (∀ (z : Lattice d) (Pfam : Set (Cube d × Cube d)) (Qfam Afam : Set (Cube d)),
            IsLocalCubeGeometry grid j1' j2' (goodCubeCentre n z, (3 : ℝ) ^ n) Pfam Qfam Afam →
            ∀ omega ∈ goodCubeEvent E z,
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusion (aCutoff M n omega) (aCutoff M n omega) law →
                LocalTorsionEstimates (aCutoff M n omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) p0' c' C'
                    (goodCubeCentre n z, (3 : ℝ) ^ n) Qfam Afam ∧
                  LocalHarmonicOscillation (aCutoff M n omega) eps0' Pfam) := by
  refine ⟨c, C, eps0, p0, Cdep, j1, j2, hc, hC, heps0, hp0, hsmall, hgeom, ?_⟩
  intro M hdelta n grid
  refine ⟨goodCubeEventField n B eps1 (E0 M n), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- clause 7a, on the enlarged box
  · intro z
    have hbox : nativeBox n B z ⊆ centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ n) :=
      centeredAxisCube_mono (mul_le_mul_of_nonneg_right hBC (by positivity))
    exact SubdiffusiveProcess.CoarseGrainingVocab.restrictedCoefficientSigma_mono _ hbox _ (hE0meas M n z)
  -- clause 7b, on the enlarged box
  · intro j hj z
    have hbox : layerBox n j B z ⊆
        centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ (n + j)) :=
      centeredAxisCube_mono (mul_le_mul_of_nonneg_right hBC (by positivity))
    refine shellLocalSigma_mono (n + j) hbox _ ?_
    match j with
    | 0 => exact absurd hj (by omega)
    | (i + 1) => exact measurableSet_layerEvent hB n (i + 1) eps1 z
  -- clause 7c
  · intro j z
    have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
    match j with
    | 0 =>
        have h := hE0tail M hdelta n z
        have hrw : (3 : ℝ) ^ (3 * ((0 : ℕ) : ℝ) / 2) = 1 := by
          norm_num
        simpa only [goodCubeEventField, hrw, mul_one] using h
    | (i + 1) =>
        have hdlt : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) ≤ eps1 := by
          refine le_trans ?_ hcdelta
          have hpos : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
            Real.rpow_pos_of_pos (by positivity) _
          nlinarith
        have hlayer := measure_layerEvent_le_cover M n (i + 1) hB hBr hdlt z
        refine hlayer.trans (ENNReal.ofReal_le_ofReal ?_)
        have hexp : c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
            (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2) ≤
            layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) *
              (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _)
          exact tail_exponent_transfer layerTailConstant_pos hdpos hdelta hc3 hcK
        have hmono : Real.exp (-(layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) *
              (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2))) ≤
            Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
              (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2))) :=
          Real.exp_le_exp.mpr (by linarith)
        exact mul_le_mul hNC hmono (Real.exp_pos _).le hC.le
  -- clause 7d
  · exact (goodCubeEventField_clauses M n hB hCdep (E0 M n) (hE0meas M n)).2.1
  -- clause 7e
  · exact (goodCubeEventField_clauses M n hB hCdep (E0 M n) (hE0meas M n)).2.2
  -- clause 7f
  · exact translationInvariantEventLaw_goodCubeEventField M n hB (E0 M n)
      (fun z => measurableSet_of_restrictedCoefficientSigma (hE0meas M n z))
      (fun z a => hE0cov M n z a)
  -- clause 7g
  · intro z Pfam Qfam Afam hgeo omega hom law hdiff
    exact goodCubeAnalyticPackage_of_supportInputs (aCutoff M n omega) law
      (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) p0 c C eps0
      (goodCubeCentre n z, (3 : ℝ) ^ n) Pfam Qfam Afam
      (hexit_lower M hdelta n grid z Pfam Qfam Afam hgeo omega hom law hdiff)
      (hexit_upper M hdelta n grid z Pfam Qfam Afam hgeo omega hom law hdiff)
      (hdescendant M hdelta n grid z Pfam Qfam Afam hgeo omega hom law hdiff)
      (hmass_quarter M hdelta n grid z Pfam Qfam Afam hgeo omega hom law hdiff)
      (hmass_descendant M hdelta n grid z Pfam Qfam Afam hgeo omega hom law hdiff)
      (hmass_overlap M hdelta n grid z Pfam Qfam Afam hgeo omega hom law hdiff)
      (hsobolev M hdelta n grid z Pfam Qfam Afam hgeo omega hom law hdiff)
      (hoscillation M hdelta n grid z Pfam Qfam Afam hgeo omega hom law hdiff)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
