module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.ProbeMomentUniform
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.AnnealedProbeDecay
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CenteredAverageDeviation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.LpMoment

@[expose] public section

/-!
# The quenched step: an `L^xi` bound whose rate does not degrade with `xi`

This is the mathematical heart of the in-house route.  Combining

* **subadditivity** (`finiteProbeSum_le_descendantsAverage`): the probe sum on
  the scale-`m` cube is below the average of the probe sums on its scale-`n`
  descendants,
* the **annealed** value of that average (a deterministic constant), and
* the **Rosenthal deviation** of the average from its mean
  (`centeredCutoffResponseAverage_le_of_moments`, §57), which carries the
  dimensional gain `3 ^ (-(d/2)(m-n))`,

gives, for every `L ≤ n ≤ m` and every order `xi ≥ 2`,

    `‖F_m‖_{L^xi} ≤ E[F_n] + C xi B_xi 3^{-(d/2)(m-n)}`

with `B_xi` a **scale-independent** constant (`ProbeMomentUniform.lean`).  Since
`E[F_n]` decays algebraically in `n` (`AnnealedProbeDecay.lean`), optimizing `n`
against `m` produces an `L^xi` decay rate that is bounded below independently of
`xi` — which is exactly what the supply interface needs, since its exponent
`theta` is fixed before the integrability order `q`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Averaging identities -/

theorem descendantsAverage_sub_const (Q : TriadicCube d) (j : ℕ)
    (f : TriadicCube d → ℝ) (c : ℝ) :
    Homogenization.descendantsAverage Q j (fun R => f R - c) =
      Homogenization.descendantsAverage Q j f - c := by
  have hcard : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    have := Homogenization.descendantsAtDepth_card Q j
    rw [this]
    positivity
  simp only [Homogenization.descendantsAverage, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  field_simp

/-! ## The centered descendant average -/

/-- The deviation of the scale-`n` descendant average of the probe form from its
annealed value. -/
def probeDeviation (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n m : ℕ)
    (alpha : ℝ) (u : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
    (fun R => centeredCutoffResponseOnCube M L n ((Real.sqrt alpha)⁻¹ • u)
      (Real.sqrt alpha • u) R omega)

/-- The descendant average of the probe form splits into its annealed value and
the deviation. -/
theorem descendantsAverage_cutoffProbeForm_eq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n m : ℕ) (alpha : ℝ)
    (u : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
        (fun R => cutoffProbeForm M L alpha R omega u) =
      (∫ eta, cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta u
        ∂M.P.toMeasure) + probeDeviation M L n m alpha u omega := by
  have hrw : (fun R : TriadicCube d =>
      centeredCutoffResponseOnCube M L n ((Real.sqrt alpha)⁻¹ • u)
        (Real.sqrt alpha • u) R omega) =
      fun R : TriadicCube d => cutoffProbeForm M L alpha R omega u -
        ∫ eta, cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta u
          ∂M.P.toMeasure := by
    funext R
    rfl
  rw [probeDeviation, hrw, descendantsAverage_sub_const]
  ring

/-- `probeDeviation` in the shape the Rosenthal bound consumes. -/
theorem probeDeviation_eq_scaleAverage
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n m : ℕ) (alpha : ℝ)
    (u : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hnm : n ≤ m) :
    probeDeviation M L n m alpha u omega =
      (((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
          centeredCutoffResponseOnCube M L n ((Real.sqrt alpha)⁻¹ • u)
            (Real.sqrt alpha • u) R omega := by
  have hscale : (originCube d (m : ℤ)).scale = (m : ℤ) := rfl
  have hle : (n : ℤ) ≤ (originCube d (m : ℤ)).scale := by
    rw [hscale]; exact_mod_cast hnm
  have hset : descendantsAtScale (originCube d (m : ℤ)) (n : ℤ) =
      descendantsAtDepth (originCube d (m : ℤ)) (m - n) := by
    rw [Homogenization.descendantsAtScale_eq_descendantsAtDepth _ hle, hscale]
    congr 1
    omega
  rw [probeDeviation, Homogenization.descendantsAverage, hset]

/-! ## The pathwise splitting of the probe sum -/

/-- The finite probe sum on the scale-`m` cube is below its annealed value at
scale `n` plus the finite sum of deviations. -/
theorem finiteProbeSum_le_annealed_add_deviation [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n m : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    finiteProbeSum M L alpha (originCube d (m : ℤ)) omega ≤
      (∫ eta, finiteProbeSum M L alpha (originCube d (n : ℤ)) eta
        ∂M.P.toMeasure) +
        ∑ i : Fin d, ∑ j : Fin d, (1 / 2 : ℝ) *
          (probeDeviation M L n m alpha
              ((Pi.single i (1 : ℝ) : Vec d) +
                (Pi.single j (1 : ℝ) : Vec d)) omega +
            probeDeviation M L n m alpha (Pi.single i (1 : ℝ) : Vec d) omega +
            probeDeviation M L n m alpha
              (Pi.single j (1 : ℝ) : Vec d) omega) := by
  classical
  have hsub := finiteProbeSum_le_descendantsAverage M L halpha
    (originCube d (m : ℤ)) (m - n) omega
  have hexpand : Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
      (fun R => finiteProbeSum M L alpha R omega) =
      ∑ i : Fin d, ∑ j : Fin d,
        Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
          (fun R => (1 / 2 : ℝ) *
            (cutoffProbeForm M L alpha R omega
                ((Pi.single i (1 : ℝ) : Vec d) +
                  (Pi.single j (1 : ℝ) : Vec d)) +
              cutoffProbeForm M L alpha R omega
                (Pi.single i (1 : ℝ) : Vec d) +
              cutoffProbeForm M L alpha R omega
                (Pi.single j (1 : ℝ) : Vec d))) := by
    rw [show (fun R : TriadicCube d => finiteProbeSum M L alpha R omega) =
        fun R : TriadicCube d => ∑ i : Fin d, ∑ j : Fin d, (1 / 2 : ℝ) *
          (cutoffProbeForm M L alpha R omega
              ((Pi.single i (1 : ℝ) : Vec d) +
                (Pi.single j (1 : ℝ) : Vec d)) +
            cutoffProbeForm M L alpha R omega
              (Pi.single i (1 : ℝ) : Vec d) +
            cutoffProbeForm M L alpha R omega
              (Pi.single j (1 : ℝ) : Vec d)) from rfl]
    rw [descendantsAverage_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact descendantsAverage_finsetSum _ _ Finset.univ _
  rw [hexpand] at hsub
  refine hsub.trans (le_of_eq ?_)
  have hterm : ∀ i j : Fin d,
      Homogenization.descendantsAverage (originCube d (m : ℤ)) (m - n)
          (fun R => (1 / 2 : ℝ) *
            (cutoffProbeForm M L alpha R omega
                ((Pi.single i (1 : ℝ) : Vec d) +
                  (Pi.single j (1 : ℝ) : Vec d)) +
              cutoffProbeForm M L alpha R omega
                (Pi.single i (1 : ℝ) : Vec d) +
              cutoffProbeForm M L alpha R omega
                (Pi.single j (1 : ℝ) : Vec d))) =
        (1 / 2 : ℝ) *
            ((∫ eta, cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
                ((Pi.single i (1 : ℝ) : Vec d) +
                  (Pi.single j (1 : ℝ) : Vec d)) ∂M.P.toMeasure) +
              (∫ eta, cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
                (Pi.single i (1 : ℝ) : Vec d) ∂M.P.toMeasure) +
              (∫ eta, cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
                (Pi.single j (1 : ℝ) : Vec d) ∂M.P.toMeasure)) +
          (1 / 2 : ℝ) *
            (probeDeviation M L n m alpha
                ((Pi.single i (1 : ℝ) : Vec d) +
                  (Pi.single j (1 : ℝ) : Vec d)) omega +
              probeDeviation M L n m alpha (Pi.single i (1 : ℝ) : Vec d) omega +
              probeDeviation M L n m alpha
                (Pi.single j (1 : ℝ) : Vec d) omega) := by
    intro i j
    rw [descendantsAverage_half_sum,
      descendantsAverage_cutoffProbeForm_eq M L n m alpha _ omega,
      descendantsAverage_cutoffProbeForm_eq M L n m alpha _ omega,
      descendantsAverage_cutoffProbeForm_eq M L n m alpha _ omega]
    ring
  rw [Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => hterm i j]
  have hintsplit : ∀ i j : Fin d,
      Integrable (fun eta => cutoffProbeForm M L alpha
        (originCube d (n : ℤ)) eta (Pi.single i (1 : ℝ) : Vec d))
        M.P.toMeasure := fun i j =>
    integrable_cutoffResponseOnCube M L _ _ _
  have hIF : (∫ eta, finiteProbeSum M L alpha (originCube d (n : ℤ)) eta
        ∂M.P.toMeasure) =
      ∑ i : Fin d, ∑ j : Fin d, (1 / 2 : ℝ) *
        ((∫ eta, cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
            ((Pi.single i (1 : ℝ) : Vec d) +
              (Pi.single j (1 : ℝ) : Vec d)) ∂M.P.toMeasure) +
          (∫ eta, cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
            (Pi.single i (1 : ℝ) : Vec d) ∂M.P.toMeasure) +
          (∫ eta, cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
            (Pi.single j (1 : ℝ) : Vec d) ∂M.P.toMeasure)) := by
    have hint : ∀ u : Vec d,
        Integrable (fun eta => cutoffProbeForm M L alpha
          (originCube d (n : ℤ)) eta u) M.P.toMeasure := fun u =>
      integrable_cutoffResponseOnCube M L _ _ _
    have hij : ∀ i j : Fin d,
        Integrable (fun eta => (1 / 2 : ℝ) *
          (cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
              ((Pi.single i (1 : ℝ) : Vec d) +
                (Pi.single j (1 : ℝ) : Vec d)) +
            cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
              (Pi.single i (1 : ℝ) : Vec d) +
            cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
              (Pi.single j (1 : ℝ) : Vec d))) M.P.toMeasure :=
      fun i j => (((hint _).add (hint _)).add (hint _)).const_mul _
    have hi : ∀ i : Fin d,
        Integrable (fun eta => ∑ j : Fin d, (1 / 2 : ℝ) *
          (cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
              ((Pi.single i (1 : ℝ) : Vec d) +
                (Pi.single j (1 : ℝ) : Vec d)) +
            cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
              (Pi.single i (1 : ℝ) : Vec d) +
            cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
              (Pi.single j (1 : ℝ) : Vec d))) M.P.toMeasure :=
      fun i => integrable_finset_sum _ fun j _ => hij i j
    simp only [finiteProbeSum]
    rw [integral_finset_sum _ fun i _ => hi i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hij i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hadd12 : Integrable (fun eta =>
        cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta
            (Pi.single i (1 : ℝ) : Vec d)) M.P.toMeasure :=
      (hint _).add (hint _)
    rw [integral_const_mul, integral_add hadd12 (hint _),
      integral_add (hint _) (hint _)]
  rw [hIF, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]


/-! ## `L^xi` bounds -/

/-- The scale-independent unit-cube constant attached to a probe direction. -/
def probeUnitConst (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (alpha xi : ℝ) (u : Vec d) : ℝ :=
  lpMoment M.P.toMeasure xi
      (fun omega => cutoffProbeForm M L alpha (originCube d (0 : ℤ)) omega u) +
    ∫ omega, cutoffProbeForm M L alpha (originCube d (0 : ℤ)) omega u
      ∂M.P.toMeasure

theorem probeUnitConst_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (alpha xi : ℝ) (u : Vec d) : 0 ≤ probeUnitConst M L alpha xi u :=
  add_nonneg (lpMoment_nonneg _ _ _)
    (integral_nonneg fun omega => cutoffProbeForm_nonneg M L alpha _ omega u)

/-- The scale-independent unit-cube constant attached to the whole finite probe
family. -/
def probeSumUnitConst (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (alpha xi : ℝ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, (1 / 2 : ℝ) *
    (probeUnitConst M L alpha xi
        ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
      probeUnitConst M L alpha xi (Pi.single i (1 : ℝ) : Vec d) +
      probeUnitConst M L alpha xi (Pi.single j (1 : ℝ) : Vec d))

theorem probeSumUnitConst_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (alpha xi : ℝ) : 0 ≤ probeSumUnitConst M L alpha xi := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have h1 := probeUnitConst_nonneg M L alpha xi
    ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d))
  have h2 := probeUnitConst_nonneg M L alpha xi (Pi.single i (1 : ℝ) : Vec d)
  have h3 := probeUnitConst_nonneg M L alpha xi (Pi.single j (1 : ℝ) : Vec d)
  linarith

/-- The `L^xi` moment of the centered probe form at scale `n` is bounded by the
unit-cube constant, uniformly in `n`. -/
theorem lpMoment_centered_le_probeUnitConst [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (u : Vec d) {xi : ℝ} (hxi : 1 ≤ xi) :
    lpMoment M.P.toMeasure xi
        (centeredCutoffResponseOnCube M L n ((Real.sqrt alpha)⁻¹ • u)
          (Real.sqrt alpha • u) (originCube d (n : ℤ))) ≤
      probeUnitConst M L alpha xi u := by
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  set cn : ℝ := ∫ eta, cutoffProbeForm M L alpha (originCube d (n : ℤ)) eta u
    ∂M.P.toMeasure with hcn
  have hsplit : centeredCutoffResponseOnCube M L n ((Real.sqrt alpha)⁻¹ • u)
      (Real.sqrt alpha • u) (originCube d (n : ℤ)) =
      fun omega =>
        cutoffProbeForm M L alpha (originCube d (n : ℤ)) omega u + (-cn) := by
    funext omega
    show cutoffProbeForm M L alpha (originCube d (n : ℤ)) omega u - cn = _
    ring
  rw [hsplit]
  have hmemf : MemLp (fun omega =>
      cutoffProbeForm M L alpha (originCube d (n : ℤ)) omega u)
      (ENNReal.ofReal xi) M.P.toMeasure :=
    memLp_cutoffResponseOnCube M L _ _ _ hxi
  have hmemc : MemLp (fun _ : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => (-cn))
      (ENNReal.ofReal xi) M.P.toMeasure := memLp_const _
  have htri := lpMoment_add_le (mu := M.P.toMeasure) hxi hmemf hmemc
  refine htri.trans ?_
  rw [lpMoment_const hxi0 (-cn)]
  -- the two pieces
  have hmom : lpMoment M.P.toMeasure xi
      (fun omega => cutoffProbeForm M L alpha (originCube d (n : ℤ)) omega u) ≤
      lpMoment M.P.toMeasure xi
        (fun omega => cutoffProbeForm M L alpha (originCube d (0 : ℤ)) omega u) := by
    have habs : ∀ (Q : TriadicCube d)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        |cutoffProbeForm M L alpha Q omega u| ^ xi =
          (cutoffProbeForm M L alpha Q omega u) ^ xi := by
      intro Q omega
      rw [abs_of_nonneg (cutoffProbeForm_nonneg M L alpha Q omega u)]
    simp only [lpMoment, habs]
    exact Real.rpow_le_rpow
      (integral_nonneg fun omega =>
        Real.rpow_nonneg (cutoffProbeForm_nonneg M L alpha _ omega u) _)
      (integral_cutoffProbeForm_rpow_originCube_le M L halpha n u hxi)
      (by positivity)
  have hmean : |(-cn)| ≤
      ∫ omega, cutoffProbeForm M L alpha (originCube d (0 : ℤ)) omega u
        ∂M.P.toMeasure := by
    have hcn0 : 0 ≤ cn := integral_nonneg fun omega =>
      cutoffProbeForm_nonneg M L alpha _ omega u
    rw [abs_neg, abs_of_nonneg hcn0, hcn]
    have hone := integral_cutoffProbeForm_rpow_originCube_le M L halpha n u
      (le_refl (1 : ℝ))
    simpa only [Real.rpow_one] using hone
  rw [probeUnitConst]
  linarith

/-- `probeDeviation` has every moment. -/
theorem memLp_probeDeviation [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n m : ℕ) (alpha : ℝ)
    (u : Vec d) {xi : ℝ} (hxi : 1 ≤ xi) :
    MemLp (probeDeviation M L n m alpha u) (ENNReal.ofReal xi)
      M.P.toMeasure := by
  have hterm : ∀ R : TriadicCube d,
      MemLp (fun omega => centeredCutoffResponseOnCube M L n
        ((Real.sqrt alpha)⁻¹ • u) (Real.sqrt alpha • u) R omega)
        (ENNReal.ofReal xi) M.P.toMeasure :=
    fun R => memLp_centeredCutoffResponseOnCube M L n _ _ R hxi
  have hsum : MemLp (fun omega =>
      ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
        centeredCutoffResponseOnCube M L n ((Real.sqrt alpha)⁻¹ • u)
          (Real.sqrt alpha • u) R omega) (ENNReal.ofReal xi) M.P.toMeasure :=
    memLp_finset_sum _ fun R _ => hterm R
  exact hsum.const_mul _

/-- **The Rosenthal bound for the probe deviation.** -/
theorem lpMoment_probeDeviation_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n m : ℕ),
        L ≤ n → n ≤ m → ∀ {alpha : ℝ}, 0 < alpha → ∀ (u : Vec d) (xi : ℝ),
          2 ≤ xi →
          lpMoment M.P.toMeasure xi (probeDeviation M L n m alpha u) ≤
            C * xi * probeUnitConst M L alpha xi u *
              Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) := by
  obtain ⟨C, hC, hmain⟩ := centeredCutoffResponseAverage_le_of_moments d
  refine ⟨C, hC, ?_⟩
  intro _ M L n m hLn hnm alpha halpha u xi hxi
  have hxi1 : (1 : ℝ) ≤ xi := le_trans (by norm_num) hxi
  have hrw : lpMoment M.P.toMeasure xi (probeDeviation M L n m alpha u) =
      (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            centeredCutoffResponseOnCube M L n ((Real.sqrt alpha)⁻¹ • u)
              (Real.sqrt alpha • u) R omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ := by
    simp only [lpMoment]
    congr 2
    funext omega
    rw [probeDeviation_eq_scaleAverage M L n m alpha u omega hnm]
  rw [hrw]
  refine (hmain M L n m hLn hnm ((Real.sqrt alpha)⁻¹ • u)
    (Real.sqrt alpha • u) xi hxi).trans ?_
  have hbase : (∫ omega,
      |centeredCutoffResponseOnCube M L n ((Real.sqrt alpha)⁻¹ • u)
        (Real.sqrt alpha • u) (originCube d (n : ℤ)) omega| ^ xi
        ∂M.P.toMeasure) ^ xi⁻¹ ≤ probeUnitConst M L alpha xi u :=
    lpMoment_centered_le_probeUnitConst M L n halpha u hxi1
  have hCxi : 0 ≤ C * xi := by positivity
  have hpow : (0 : ℝ) ≤ Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have := mul_le_mul_of_nonneg_left hbase hCxi
  nlinarith [this, hpow]


/-- The finite probe sum has every moment. -/
theorem memLp_finiteProbeSum [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) {xi : ℝ} (hxi : 1 ≤ xi) :
    MemLp (fun omega => finiteProbeSum M L alpha R omega)
      (ENNReal.ofReal xi) M.P.toMeasure := by
  have hcpf : ∀ u : Vec d, MemLp (fun omega =>
      cutoffProbeForm M L alpha R omega u) (ENNReal.ofReal xi) M.P.toMeasure :=
    fun u => memLp_cutoffResponseOnCube M L _ _ _ hxi
  have hij : ∀ i j : Fin d, MemLp (fun omega => (1 / 2 : ℝ) *
      (cutoffProbeForm M L alpha R omega
          ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
        cutoffProbeForm M L alpha R omega (Pi.single i (1 : ℝ) : Vec d) +
        cutoffProbeForm M L alpha R omega (Pi.single j (1 : ℝ) : Vec d)))
      (ENNReal.ofReal xi) M.P.toMeasure :=
    fun i j => (((hcpf _).add (hcpf _)).add (hcpf _)).const_mul _
  exact memLp_finset_sum _ fun i _ => memLp_finset_sum _ fun j _ => hij i j

/-- **The quenched `L^xi` step.** -/
theorem lpMoment_finiteProbeSum_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n m : ℕ),
        L ≤ n → n ≤ m → ∀ {alpha : ℝ}, 0 < alpha → ∀ xi : ℝ, 2 ≤ xi →
          lpMoment M.P.toMeasure xi
              (fun omega =>
                finiteProbeSum M L alpha (originCube d (m : ℤ)) omega) ≤
            (∫ eta, finiteProbeSum M L alpha (originCube d (n : ℤ)) eta
              ∂M.P.toMeasure) +
              C * xi * probeSumUnitConst M L alpha xi *
                Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) := by
  classical
  obtain ⟨C, hC, hdev⟩ := lpMoment_probeDeviation_le d
  refine ⟨C, hC, ?_⟩
  intro _ M L n m hLn hnm alpha halpha xi hxi
  have hxi1 : (1 : ℝ) ≤ xi := le_trans (by norm_num) hxi
  have hxi0 : (0 : ℝ) < xi := lt_of_lt_of_le zero_lt_one hxi1
  set K : ℝ := ∫ eta, finiteProbeSum M L alpha (originCube d (n : ℤ)) eta
    ∂M.P.toMeasure with hK
  have hK0 : 0 ≤ K :=
    integral_nonneg fun eta => finiteProbeSum_nonneg M L alpha _ eta
  set G : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega =>
    ∑ i : Fin d, ∑ j : Fin d, (1 / 2 : ℝ) *
      (probeDeviation M L n m alpha
          ((Pi.single i (1 : ℝ) : Vec d) +
            (Pi.single j (1 : ℝ) : Vec d)) omega +
        probeDeviation M L n m alpha (Pi.single i (1 : ℝ) : Vec d) omega +
        probeDeviation M L n m alpha (Pi.single j (1 : ℝ) : Vec d) omega)
    with hG
  have hdevmem : ∀ u : Vec d, MemLp (probeDeviation M L n m alpha u)
      (ENNReal.ofReal xi) M.P.toMeasure :=
    fun u => memLp_probeDeviation M L n m alpha u hxi1
  have hijmem : ∀ i j : Fin d, MemLp (fun omega => (1 / 2 : ℝ) *
      (probeDeviation M L n m alpha
          ((Pi.single i (1 : ℝ) : Vec d) +
            (Pi.single j (1 : ℝ) : Vec d)) omega +
        probeDeviation M L n m alpha (Pi.single i (1 : ℝ) : Vec d) omega +
        probeDeviation M L n m alpha (Pi.single j (1 : ℝ) : Vec d) omega))
      (ENNReal.ofReal xi) M.P.toMeasure :=
    fun i j => (((hdevmem _).add (hdevmem _)).add (hdevmem _)).const_mul _
  have himem : ∀ i : Fin d, MemLp (fun omega => ∑ j : Fin d, (1 / 2 : ℝ) *
      (probeDeviation M L n m alpha
          ((Pi.single i (1 : ℝ) : Vec d) +
            (Pi.single j (1 : ℝ) : Vec d)) omega +
        probeDeviation M L n m alpha (Pi.single i (1 : ℝ) : Vec d) omega +
        probeDeviation M L n m alpha (Pi.single j (1 : ℝ) : Vec d) omega))
      (ENNReal.ofReal xi) M.P.toMeasure :=
    fun i => memLp_finset_sum _ fun j _ => hijmem i j
  have hGmem : MemLp G (ENNReal.ofReal xi) M.P.toMeasure :=
    memLp_finset_sum _ fun i _ => himem i
  have hFmem : MemLp (fun omega =>
      finiteProbeSum M L alpha (originCube d (m : ℤ)) omega)
      (ENNReal.ofReal xi) M.P.toMeasure :=
    memLp_finiteProbeSum M L alpha _ hxi1
  have hsummem : MemLp (fun omega => K + G omega) (ENNReal.ofReal xi)
      M.P.toMeasure := (memLp_const K).add hGmem
  -- step 1: monotonicity
  have hstep1 : lpMoment M.P.toMeasure xi
      (fun omega => finiteProbeSum M L alpha (originCube d (m : ℤ)) omega) ≤
      lpMoment M.P.toMeasure xi (fun omega => K + G omega) := by
    refine lpMoment_mono hxi0
      (integrable_abs_rpow_of_memLp hxi0 hFmem)
      (integrable_abs_rpow_of_memLp hxi0 hsummem) ?_
    intro omega
    have hle := finiteProbeSum_le_annealed_add_deviation M L n m halpha omega
    have hnn := finiteProbeSum_nonneg M L alpha (originCube d (m : ℤ)) omega
    rw [abs_of_nonneg hnn]
    refine le_trans hle ?_
    exact le_abs_self _
  -- step 2: split off the constant
  have hstep2 : lpMoment M.P.toMeasure xi (fun omega => K + G omega) ≤
      K + lpMoment M.P.toMeasure xi G := by
    have := lpMoment_add_le (mu := M.P.toMeasure) hxi1 (memLp_const K) hGmem
    rw [lpMoment_const hxi0 K, abs_of_nonneg hK0] at this
    exact this
  -- step 3: Minkowski across the finite probe family
  have hdevbound : ∀ u : Vec d,
      lpMoment M.P.toMeasure xi (probeDeviation M L n m alpha u) ≤
        C * xi * probeUnitConst M L alpha xi u *
          Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) :=
    fun u => hdev M L n m hLn hnm halpha u xi hxi
  have hstep3 : lpMoment M.P.toMeasure xi G ≤
      C * xi * probeSumUnitConst M L alpha xi *
        Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) := by
    have houter := lpMoment_finsetSum_le (mu := M.P.toMeasure)
      (Finset.univ : Finset (Fin d))
      (F := fun i omega => ∑ j : Fin d, (1 / 2 : ℝ) *
        (probeDeviation M L n m alpha
            ((Pi.single i (1 : ℝ) : Vec d) +
              (Pi.single j (1 : ℝ) : Vec d)) omega +
          probeDeviation M L n m alpha (Pi.single i (1 : ℝ) : Vec d) omega +
          probeDeviation M L n m alpha (Pi.single j (1 : ℝ) : Vec d) omega))
      hxi1 (fun i _ => himem i)
    refine le_trans houter ?_
    have hrhs : C * xi * probeSumUnitConst M L alpha xi *
        Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) =
        ∑ i : Fin d, ∑ j : Fin d, C * xi * ((1 / 2 : ℝ) *
          (probeUnitConst M L alpha xi
              ((Pi.single i (1 : ℝ) : Vec d) +
                (Pi.single j (1 : ℝ) : Vec d)) +
            probeUnitConst M L alpha xi (Pi.single i (1 : ℝ) : Vec d) +
            probeUnitConst M L alpha xi (Pi.single j (1 : ℝ) : Vec d))) *
          Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) := by
      simp only [probeSumUnitConst, Finset.mul_sum, Finset.sum_mul]
    rw [hrhs]
    refine Finset.sum_le_sum fun i _ => ?_
    have hinner := lpMoment_finsetSum_le (mu := M.P.toMeasure)
      (Finset.univ : Finset (Fin d))
      (F := fun j omega => (1 / 2 : ℝ) *
        (probeDeviation M L n m alpha
            ((Pi.single i (1 : ℝ) : Vec d) +
              (Pi.single j (1 : ℝ) : Vec d)) omega +
          probeDeviation M L n m alpha (Pi.single i (1 : ℝ) : Vec d) omega +
          probeDeviation M L n m alpha (Pi.single j (1 : ℝ) : Vec d) omega))
      hxi1 (fun j _ => hijmem i j)
    refine le_trans hinner ?_
    refine Finset.sum_le_sum fun j _ => ?_
    have hhalf : lpMoment M.P.toMeasure xi (fun omega => (1 / 2 : ℝ) *
        (probeDeviation M L n m alpha
            ((Pi.single i (1 : ℝ) : Vec d) +
              (Pi.single j (1 : ℝ) : Vec d)) omega +
          probeDeviation M L n m alpha (Pi.single i (1 : ℝ) : Vec d) omega +
          probeDeviation M L n m alpha (Pi.single j (1 : ℝ) : Vec d) omega)) =
        (1 / 2 : ℝ) * lpMoment M.P.toMeasure xi (fun omega =>
          probeDeviation M L n m alpha
              ((Pi.single i (1 : ℝ) : Vec d) +
                (Pi.single j (1 : ℝ) : Vec d)) omega +
            probeDeviation M L n m alpha (Pi.single i (1 : ℝ) : Vec d) omega +
            probeDeviation M L n m alpha (Pi.single j (1 : ℝ) : Vec d) omega) := by
      rw [lpMoment_const_mul hxi0]
      norm_num
    rw [hhalf]
    have hadd12 : MemLp (fun omega =>
        probeDeviation M L n m alpha
            ((Pi.single i (1 : ℝ) : Vec d) +
              (Pi.single j (1 : ℝ) : Vec d)) omega +
          probeDeviation M L n m alpha (Pi.single i (1 : ℝ) : Vec d) omega)
        (ENNReal.ofReal xi) M.P.toMeasure := (hdevmem _).add (hdevmem _)
    have htri1 := lpMoment_add_le (mu := M.P.toMeasure) hxi1 hadd12
      (hdevmem (Pi.single j (1 : ℝ) : Vec d))
    have htri2 := lpMoment_add_le (mu := M.P.toMeasure) hxi1
      (hdevmem ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)))
      (hdevmem (Pi.single i (1 : ℝ) : Vec d))
    have hb1 := hdevbound ((Pi.single i (1 : ℝ) : Vec d) +
      (Pi.single j (1 : ℝ) : Vec d))
    have hb2 := hdevbound (Pi.single i (1 : ℝ) : Vec d)
    have hb3 := hdevbound (Pi.single j (1 : ℝ) : Vec d)
    nlinarith [htri1, htri2, hb1, hb2, hb3]
  linarith [hstep1, hstep2, hstep3]


/-! ## Optimizing the split scale -/

/-- **The quenched algebraic decay of the probe sum in every `L^xi`, at a rate
independent of `xi`.**

Choosing the split scale `n = m / 2` balances the annealed decay against the
Rosenthal gain; the resulting exponent `rho = min (alpha/2) (d/4)` does not
depend on the integrability order, which is what the supply interface requires
(its exponent `theta` is fixed before `q`). -/
theorem exists_lpMoment_finiteProbeSum_decay [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    ∃ (m₀ : ℕ) (rho : ℝ) (Cst : ℝ → ℝ), 0 < rho ∧
      ∀ xi : ℝ, 2 ≤ xi → ∀ m : ℕ, m₀ ≤ m →
        lpMoment M.P.toMeasure xi
            (fun omega =>
              finiteProbeSum M L (ahom M L) (originCube d (m : ℤ)) omega) ≤
          Cst xi * Real.rpow (3 : ℝ) (-rho * (m : ℝ)) := by
  classical
  have halpha : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L)
  obtain ⟨k₀, alpha, halpha0, hann⟩ := exists_annealed_finiteProbeSum_decay M L
  obtain ⟨C, hC, hstep⟩ := lpMoment_finiteProbeSum_le d
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : d ≠ 0 := NeZero.ne d
    positivity
  refine ⟨2 * (max L k₀ + 1), min (alpha / 2) ((d : ℝ) / 4),
    fun xi => 3 * (d : ℝ) ^ 2 *
        Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) +
      C * xi * probeSumUnitConst M L (ahom M L) xi,
    lt_min (by positivity) (by positivity), ?_⟩
  intro xi hxi m hm
  set n : ℕ := m / 2 with hn
  have hNn : max L k₀ ≤ n := by omega
  have hLn : L ≤ n := le_trans (le_max_left _ _) hNn
  have hk₀n : k₀ ≤ n := le_trans (le_max_right _ _) hNn
  have hnm : n ≤ m := by omega
  -- the quenched step
  have hmain := hstep M L n m hLn hnm halpha xi hxi
  -- the annealed term
  have hcube : originCube d ((k₀ + (n - k₀) : ℕ) : ℤ) = originCube d (n : ℤ) := by
    congr 2
    omega
  have hannbound : (∫ eta, finiteProbeSum M L (ahom M L)
      (originCube d (n : ℤ)) eta ∂M.P.toMeasure) ≤
      3 * (d : ℝ) ^ 2 * Real.rpow (3 : ℝ) (-alpha * ((n - k₀ : ℕ) : ℝ)) := by
    have := hann (n - k₀)
    rwa [hcube] at this
  -- exponent comparisons
  have h3 : (1 : ℝ) ≤ 3 := by norm_num
  have hnreal : (m : ℝ) / 2 - 1 / 2 ≤ (n : ℝ) := by
    have h2 : 2 * n + 1 ≥ m := by omega
    have hcast : (2 : ℝ) * (n : ℝ) + 1 ≥ (m : ℝ) := by exact_mod_cast h2
    linarith
  have hsub : ((n - k₀ : ℕ) : ℝ) = (n : ℝ) - (k₀ : ℝ) := by
    push_cast [Nat.cast_sub hk₀n]
    ring
  have hexp1 : -alpha * ((n - k₀ : ℕ) : ℝ) ≤
      alpha * ((1 : ℝ) / 2 + (k₀ : ℝ)) + (-(alpha / 2) * (m : ℝ)) := by
    rw [hsub]
    nlinarith [hnreal, halpha0]
  have hterm1 : Real.rpow (3 : ℝ) (-alpha * ((n - k₀ : ℕ) : ℝ)) ≤
      Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) *
        Real.rpow (3 : ℝ) (-(alpha / 2) * (m : ℝ)) := by
    have heq : Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) *
        Real.rpow (3 : ℝ) (-(alpha / 2) * (m : ℝ)) =
        Real.rpow (3 : ℝ)
          (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ)) + (-(alpha / 2) * (m : ℝ))) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le h3 hexp1
  have hmn : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    push_cast [Nat.cast_sub hnm]
    ring
  have hnhalf : (n : ℝ) ≤ (m : ℝ) / 2 := by
    have h2 : 2 * n ≤ m := by omega
    have : (2 : ℝ) * (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2
    linarith
  have hexp2 : -((d : ℝ) / 2) * ((m - n : ℕ) : ℝ) ≤
      -((d : ℝ) / 4) * (m : ℝ) := by
    rw [hmn]
    nlinarith [hnhalf, hdpos]
  have hterm2 : Real.rpow (3 : ℝ) (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) ≤
      Real.rpow (3 : ℝ) (-((d : ℝ) / 4) * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le h3 hexp2
  -- collapse both to the common rate
  set rho : ℝ := min (alpha / 2) ((d : ℝ) / 4) with hrho
  have hrho1 : Real.rpow (3 : ℝ) (-(alpha / 2) * (m : ℝ)) ≤
      Real.rpow (3 : ℝ) (-rho * (m : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le h3 ?_
    have : rho ≤ alpha / 2 := min_le_left _ _
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hrho2 : Real.rpow (3 : ℝ) (-((d : ℝ) / 4) * (m : ℝ)) ≤
      Real.rpow (3 : ℝ) (-rho * (m : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le h3 ?_
    have : rho ≤ (d : ℝ) / 4 := min_le_right _ _
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hA : (0 : ℝ) ≤ 3 * (d : ℝ) ^ 2 := by positivity
  have hB : (0 : ℝ) ≤ C * xi * probeSumUnitConst M L (ahom M L) xi := by
    have hxi0 : (0 : ℝ) ≤ xi := by linarith
    have := probeSumUnitConst_nonneg M L (ahom M L) xi
    positivity
  have hchain1 : (∫ eta, finiteProbeSum M L (ahom M L)
      (originCube d (n : ℤ)) eta ∂M.P.toMeasure) ≤
      3 * (d : ℝ) ^ 2 * Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) *
        Real.rpow (3 : ℝ) (-rho * (m : ℝ)) := by
    refine hannbound.trans ?_
    have := (hterm1.trans (mul_le_mul_of_nonneg_left hrho1
      (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)))
    calc 3 * (d : ℝ) ^ 2 * Real.rpow (3 : ℝ) (-alpha * ((n - k₀ : ℕ) : ℝ))
        ≤ 3 * (d : ℝ) ^ 2 *
            (Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) *
              Real.rpow (3 : ℝ) (-rho * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left this hA
      _ = _ := by ring
  have hchain2 : C * xi * probeSumUnitConst M L (ahom M L) xi *
      Real.rpow (3 : ℝ) (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) ≤
      C * xi * probeSumUnitConst M L (ahom M L) xi *
        Real.rpow (3 : ℝ) (-rho * (m : ℝ)) :=
    mul_le_mul_of_nonneg_left (hterm2.trans hrho2) hB
  have hfinal := hmain.trans (add_le_add hchain1 hchain2)
  refine hfinal.trans (le_of_eq ?_)
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
