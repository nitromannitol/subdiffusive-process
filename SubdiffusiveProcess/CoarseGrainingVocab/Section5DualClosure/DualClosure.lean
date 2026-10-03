module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.DualPrincipalMajorant
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.DualPrincipalBudgets
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.DualOscillatoryMajorant
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.PaperSourceWeight
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceThermodynamic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteReadoutComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepVariationalClosure

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book Filter
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The two Neumann carrier facts the dual closure still needs: an almost-sure
competitor bounding the random inverse-star quadratic by the normalized
three-term majorant sum, and a `delta ^ 30` finite budget for the oscillatory
envelope.

The competitor's boundary summand is a **random variable** `boundary` with a
deterministic bound on its expectation.  It has to be: on the discarded strip
the glued competitor is the ambient manuscript flux
(`oneStepSelectedRetainedGluedNeumannTwoFlux_eq_background_of_not_mem`), whose
energy has no deterministic essential supremum — `aCutoff` carries no
deterministic two-sided bounds.  Only its *expectation* vanishes, through
`inv_cubeVolume_integral_strip_le` against a `oneStepRetainedBoundaryFraction`.
The closure only ever integrates the competitor, so this is exactly what it
consumes.

For the same reason the `K` quantifier is `∀ᶠ K in atTop` rather than
`∀ K ≥ oneStepLocalizationScale n M.delta`: the covered cell family of the
`delta ^ 30` envelope is non-vacuous only for large `K`, and the closure takes
`K → ∞` under `filter_upwards` anyway. -/
def DualCellMajorantInputs (d : ℕ) [NeZero d] : Prop :=
  ∃ deltaO O : ℝ, 0 < deltaO ∧ 0 < O ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaO →
      ∀ (n h : ℕ) (q : Homogenization.Vec d),
        vecNormSq q = 1 → ∀ hh : 0 < h, (h : ℝ) ≤ M.delta⁻¹ →
        16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
        ∃ boundaryBound : ℕ → ℝ,
          Filter.Tendsto boundaryBound Filter.atTop (nhds 0) ∧
          ∀ᶠ K : ℕ in Filter.atTop,
            ∃ (oscillatory : Homogenization.TriadicCube d → Sample d → ℝ)
              (boundary : Sample d → ℝ),
              Integrable boundary M.P.toMeasure ∧
              (∫ omega, boundary omega ∂M.P.toMeasure ≤ boundaryBound K) ∧
              (∀ R ∈ oneStepSourceCells d K n M.delta,
                Integrable (oscillatory R) M.P.toMeasure) ∧
              (∀ R ∈ oneStepSourceCells d K n M.delta,
                ∀ omega, 0 ≤ oscillatory R omega) ∧
              (∀ᵐ omega ∂M.P.toMeasure,
                (1 / 2 : ℝ) * vecDot q
                    (matVecMul ((randomAStarMatrix M (n + h)
                      (Ch02.cubeDomain (originCube d (K : ℤ))) omega)⁻¹) q) ≤
                  (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
                    ∑ R ∈ oneStepSourceCells d K n M.delta,
                      ((1 / 2 : ℝ) *
                          oneStepDualPrincipalMajorant
                            (K := K) M n h q R omega hh +
                        Real.sqrt (oneStepDualPrincipalMajorant
                          (K := K) M n h q R omega hh) *
                          Real.sqrt (oscillatory R omega) +
                        (1 / 2 : ℝ) * oscillatory R omega) +
                    boundary omega) ∧
              ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
                  ∑ R ∈ oneStepSourceCells d K n M.delta,
                    ∫ omega, oscillatory R omega ∂M.P.toMeasure ≤
                O * M.delta ^ (30 : ℕ) * (ahom M n)⁻¹)

/-- Integrability of the random inverse-star quadratic probe. -/
theorem integrable_randomAStarInv_quadratic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (q : Homogenization.Vec d) :
    Integrable (fun omega : Sample d ↦ vecDot q
      (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q)) M.P.toMeasure := by
  have h := integrable_weight_mul_vecDot_randomAStarInv_suffix M L U
    (fun _ ↦ (1 : ℝ)) (fun _ ↦ q) measurable_const measurable_const
    (fun i j ↦ integrable_const _)
  simpa only [one_mul] using h

/-- **The dual one-step closure.**  Byte-exact
`SharpOneStepLowerConclusion d`, reduced to the two Neumann carrier facts. -/
theorem sharpOneStepLowerConclusion_of_dualCellMajorants
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) (hinputs : DualCellMajorantInputs d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ),
        (h : ℝ) ≤ M.delta⁻¹ →
        16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
        (ahom M (n + h))⁻¹ ≤ (ahom M n)⁻¹ *
          (1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / d +
            C * M.delta ^ 4 * (h : ℝ) ^ 2 +
            C * M.delta ^ 2 * |Real.log M.delta|) := by
  obtain ⟨deltaO, O, hdeltaO, hO, hosc⟩ := hinputs
  obtain ⟨Cw, hCw, hweight⟩ :=
    exists_eventually_normalized_sum_integral_oneStepPaperNeumannSourceCellWeight_le
      d
  obtain ⟨deltaB, B, hdeltaB, hB, hreadout⟩ :=
    exists_source_readouts_le_ahom d
  let P : ℝ := (3 + 2 * Cw) * (1 + B)
  let A0 : ℝ := Cw * (1 + B)
  let A : ℝ := 1 + A0 + O + Real.sqrt P * Real.sqrt O
  let Afinal : ℝ := 4 * A
  let deltaSmall : ℝ := min deltaO deltaB
  let Csmall : ℝ := oneStepVariationalConst Afinal B
  let Cbig : ℝ := 6 * deltaSmall⁻¹ ^ (2 : ℕ)
  let C : ℝ := max Csmall Cbig
  have hP : 0 < P := by dsimp only [P]; positivity
  have hA0 : 0 < A0 := by dsimp only [A0]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAfinal : 0 < Afinal := by dsimp only [Afinal]; positivity
  have hdeltaSmall : 0 < deltaSmall := by
    dsimp only [deltaSmall]; positivity
  have hCsmall : 0 < Csmall := oneStepVariationalConst_pos hAfinal hB.le
  have hCbig : 0 < Cbig := by dsimp only [Cbig]; positivity
  have hC : 0 < C := hCsmall.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro M n h hblock hsource
  have hdeltaOne : M.delta ≤ 1 :=
    M.shellPrefix.delta_le_half.trans (by norm_num)
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ M.delta ^ 2 := by
    exact (tauSq_le_delta_sq M).trans <| by
      have hlog : Real.log 2 / 2 ≤ 1 := by
        linarith [Real.log_two_lt_d9]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta)
  by_cases hh0 : h = 0
  · subst h
    have hzero : (ahom M n)⁻¹ ≤ (ahom M n)⁻¹ *
        (1 + C * M.delta ^ 2 * |Real.log M.delta|) := by
      calc
        (ahom M n)⁻¹ = (ahom M n)⁻¹ * 1 := by ring
        _ ≤ (ahom M n)⁻¹ * (1 + C * M.delta ^ 2 * |Real.log M.delta|) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (by positivity))
            (inv_nonneg.mpr (ahom_pos M n).le)
    simpa only [Nat.add_zero, Nat.cast_zero, mul_zero, zero_div,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_pow (by norm_num : (4 : ℕ) ≠ 0), add_zero] using hzero
  have hh : 0 < h := Nat.pos_of_ne_zero hh0
  have hscale : M.delta * (h : ℝ) ≤ 1 := by
    calc
      M.delta * (h : ℝ) ≤ M.delta * M.delta⁻¹ :=
        mul_le_mul_of_nonneg_left hblock M.shellPrefix.delta_pos.le
      _ = 1 := mul_inv_cancel₀ M.shellPrefix.delta_pos.ne'
  by_cases hsmall : M.delta ≤ deltaSmall
  · have hMO : M.delta ≤ deltaO := hsmall.trans (min_le_left _ _)
    have hMB : M.delta ≤ deltaB := hsmall.trans (min_le_right _ _)
    have hcell := (hreadout M n hMB hsource).2
    let cell := oneStepAnnealedDualReadout M n (oneStepLocalizationScale n M.delta)
    let previous := (ahom M n)⁻¹
    have hcell0 : 0 ≤ cell :=
      oneStepAnnealedDualReadout_nonneg M n _
    have hprevious0 : 0 ≤ previous := inv_nonneg.mpr (ahom_pos M n).le
    let q : Homogenization.Vec d := basisVec ⟨0, by omega⟩
    have hq : vecNormSq q = 1 := vecNormSq_basisVec _
    have hy : M.delta ^ 2 * |Real.log M.delta| ≤ 1 :=
      (delta_sq_mul_abs_log_le_self M.shellPrefix.delta_pos hdeltaOne).trans
        hdeltaOne
    have hcell' : cell ≤
        (1 + B * (M.delta ^ 2 * |Real.log M.delta|)) * previous := by
      simpa only [cell, previous, mul_assoc] using hcell
    have hsqrtPO0 : 0 ≤ Real.sqrt P * Real.sqrt O := by positivity
    have hA0A : A0 ≤ A := by dsimp only [A]; linarith [hO, hsqrtPO0]
    have hOA : O ≤ A := by dsimp only [A]; linarith [hA0, hsqrtPO0]
    have hPOA : Real.sqrt P * Real.sqrt O ≤ A := by
      dsimp only [A]; linarith [hA0, hO]
    have hdreal1 : (1 : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hd)
    obtain ⟨boundaryBound, hboundary0, hoscK⟩ :=
      hosc M hMO n h q hq hh hblock hsource
    have hfinite : ∀ᶠ K : ℕ in atTop,
        oneStepDualFiniteVolumeReadout M (n + h) K q ≤
          ((1 / 2 + SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
              Afinal * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
            Afinal * M.delta ^ 15 * previous) + boundaryBound K := by
      filter_upwards [hweight M n h q hsource hh hq hblock, hoscK,
        eventually_atTop.2 ⟨oneStepLocalizationScale n M.delta,
          fun K hK ↦ hK⟩] with K hweightK hoscKK hK
      obtain ⟨oscillatory, boundary, hbInt, hbBound, hEint, hE0, hpointwise,
        hEbudget⟩ := hoscKK
      let principal := fun R omega ↦
        oneStepDualPrincipalMajorant (K := K) M n h q R omega hh
      let quad := fun omega ↦ vecDot q
        (matVecMul ((randomAStarMatrix M (n + h)
          (Ch02.cubeDomain (originCube d (K : ℤ))) omega)⁻¹) q)
      let target := fun omega ↦ quad omega - 2 * boundary omega
      let weightAverage : ℝ :=
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, oneStepLowerSourceCellWeight M n h R omega *
              vecNormSq (oneStepPaperNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure
      let principalAverage : ℝ :=
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, principal R omega ∂M.P.toMeasure
      have hprincipalEq : principalAverage = cell * weightAverage := by
        simpa only [principalAverage, principal, cell, weightAverage,
          oneStepDualPrincipalMajorant] using
          normalized_sum_integral_lowerWeight_mul_oneStepPaperNeumannCellSlope_randomAStarInv_eq
            M n h q hK hh hq
      obtain ⟨hprincipalRough, hprincipalSharp0⟩ :=
        dual_principal_budgets_of_weight
          M.shellPrefix.delta_pos.le hdeltaOne M.G4.tauSq_pos.le htau
          (Nat.cast_nonneg h) hdreal1
          hscale hCw hB.le hcell0 hprevious0 hy hcell' hprincipalEq hweightK
      have hprincipalSharp : principalAverage ≤
          (1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
              A * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
            A * M.delta ^ 15 * previous := by
        refine hprincipalSharp0.trans (add_le_add ?_ ?_)
        · have hErr : A0 * (M.delta ^ 4 * (h : ℝ) ^ 2) ≤
              A * (M.delta ^ 4 * (h : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hA0A
              (mul_nonneg (pow_nonneg M.shellPrefix.delta_pos.le 4)
                (sq_nonneg (h : ℝ)))
          exact mul_le_mul_of_nonneg_right (by linarith) hcell0
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hA0A
              (pow_nonneg M.shellPrefix.delta_pos.le 15)) hprevious0
      have hquadInt : Integrable quad M.P.toMeasure :=
        integrable_randomAStarInv_quadratic M (n + h) _ q
      have htargetInt : Integrable target M.P.toMeasure :=
        hquadInt.sub (hbInt.const_mul 2)
      have hprincipalInt : ∀ R ∈ oneStepSourceCells d K n M.delta,
          Integrable (principal R) M.P.toMeasure := by
        intro R _hR
        simpa only [principal] using
          integrable_oneStepDualPrincipalMajorant M n h q R hh hq
      have hprincipal0 : ∀ R ∈ oneStepSourceCells d K n M.delta,
          0 ≤ᵐ[M.P.toMeasure] principal R := by
        intro R _hR
        exact Filter.Eventually.of_forall fun omega ↦ by
          simpa only [principal, Pi.zero_apply] using!
            oneStepDualPrincipalMajorant_nonneg M n h q R omega hh
      have hoscillatory0 : ∀ R ∈ oneStepSourceCells d K n M.delta,
          0 ≤ᵐ[M.P.toMeasure] oscillatory R := fun R hR ↦
        Filter.Eventually.of_forall (hE0 R hR)
      have hpenultimate := one_step_lower_penultimate_of_ae_finite_majorants
        (oneStepSourceCells d K n M.delta)
        (oneStepSourceCells_nonempty d K n M.delta)
        target principal oscillatory htargetInt hprincipalInt hEint
        hprincipal0 hoscillatory0
        (by
          filter_upwards [hpointwise] with omega hom
          simp only [target, quad, principal]
          linarith)
        M.shellPrefix.delta_pos.le hdeltaOne hA.le hP.le hO.le
        hcell0 hprevious0 hPOA hOA
        (by simpa only [principalAverage, P, previous] using hprincipalRough)
        (by simpa only [principalAverage] using hprincipalSharp)
        (by simpa only [previous] using hEbudget)
      have hpen : (1 / 2 : ℝ) * ∫ omega, target omega ∂M.P.toMeasure ≤
          (1 / 2 + SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
              Afinal * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
            Afinal * M.delta ^ 15 * previous := by
        simpa only [Afinal] using hpenultimate
      have hsplit : ∫ omega, target omega ∂M.P.toMeasure =
          (∫ omega, vecDot q (matVecMul ((randomAStarMatrix M (n + h)
            (Ch02.cubeDomain (originCube d (K : ℤ))) omega)⁻¹) q)
            ∂M.P.toMeasure) -
            2 * ∫ omega, boundary omega ∂M.P.toMeasure := by
        simp only [target, quad]
        rw [integral_sub hquadInt (hbInt.const_mul 2), integral_const_mul]
      rw [oneStepDualFiniteVolumeReadout_eq_integral, integral_const_mul]
      rw [hsplit] at hpen
      linarith
    have hlimit : (1 / 2 : ℝ) * (ahom M (n + h))⁻¹ ≤
        (1 / 2 + SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
            Afinal * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
          Afinal * M.delta ^ 15 * previous := by
      have hread : Filter.Tendsto
          (fun K : ℕ ↦ oneStepDualFiniteVolumeReadout M (n + h) K q)
          atTop (nhds ((1 / 2 : ℝ) * (ahom M (n + h))⁻¹)) := by
        simpa only [hq, mul_one] using
          tendsto_oneStepDualFiniteVolumeReadout M (n + h) q
      have hbound : Filter.Tendsto
          (fun K : ℕ ↦ ((1 / 2 +
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
                Afinal * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
              Afinal * M.delta ^ 15 * previous) + boundaryBound K)
          atTop (nhds (((1 / 2 +
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
                Afinal * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
              Afinal * M.delta ^ 15 * previous) + 0)) :=
        Filter.Tendsto.add tendsto_const_nhds hboundary0
      simpa using le_of_tendsto_of_tendsto hread hbound hfinite
    have hclosed := one_step_lower_of_penultimate
      M.shellPrefix.delta_pos M.shellPrefix.delta_le_half M.G4.tauSq_pos.le htau
      (Nat.cast_nonneg h) hscale
      (half_le_abs_log_delta M.shellPrefix.delta_pos M.shellPrefix.delta_le_half)
      (by exact_mod_cast (le_trans (by norm_num : 2 ≤ 3) hd))
      hAfinal hB.le hprevious0 (le_refl ((ahom M (n + h))⁻¹))
      (by simpa [mul_assoc] using hcell') hlimit
    have hCsmallC : Csmall ≤ C := le_max_left _ _
    calc
      (ahom M (n + h))⁻¹ ≤ (ahom M n)⁻¹ *
          (1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
            Csmall * M.delta ^ 4 * (h : ℝ) ^ 2 +
            Csmall * M.delta ^ 2 * |Real.log M.delta|) := by
        simpa only [Csmall, Afinal, cell, previous] using hclosed
      _ ≤ (ahom M n)⁻¹ *
          (1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
            C * M.delta ^ 4 * (h : ℝ) ^ 2 +
            C * M.delta ^ 2 * |Real.log M.delta|) := by
        apply mul_le_mul_of_nonneg_left _ hprevious0
        have hsum0 : 0 ≤ M.delta ^ 4 * (h : ℝ) ^ 2 +
            M.delta ^ 2 * |Real.log M.delta| := by positivity
        have hmul := mul_le_mul_of_nonneg_right hCsmallC hsum0
        nlinarith
  · have hdeltaLower : deltaSmall ≤ M.delta := le_of_not_ge hsmall
    have hlogHalf : (1 / 2 : ℝ) ≤ |Real.log M.delta| :=
      half_le_abs_log_delta M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
    have hsq : deltaSmall ^ 2 ≤ M.delta ^ 2 :=
      pow_le_pow_left₀ hdeltaSmall.le hdeltaLower 2
    have hCbigC : Cbig ≤ C := le_max_right _ _
    have hidentity : Cbig * deltaSmall ^ 2 * (1 / 2 : ℝ) = 3 := by
      dsimp only [Cbig]
      field_simp [hdeltaSmall.ne']
      ring
    have hcomp : Cbig * deltaSmall ^ 2 ≤ C * M.delta ^ 2 :=
      mul_le_mul hCbigC hsq (sq_nonneg deltaSmall) hC.le
    have hcomp' : Cbig * deltaSmall ^ 2 * (1 / 2 : ℝ) ≤
        C * M.delta ^ 2 * |Real.log M.delta| :=
      mul_le_mul hcomp hlogHalf (by norm_num)
        (mul_nonneg hC.le (sq_nonneg M.delta))
    have herrorThree : 3 ≤ C * M.delta ^ 2 * |Real.log M.delta| := by
      rw [← hidentity]; exact hcomp'
    have htauh : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) ≤ M.delta := by
      calc
        _ ≤ M.delta ^ 2 * (h : ℝ) :=
          mul_le_mul_of_nonneg_right htau (Nat.cast_nonneg h)
        _ ≤ M.delta ^ 2 * M.delta⁻¹ :=
          mul_le_mul_of_nonneg_left hblock (sq_nonneg M.delta)
        _ = M.delta := by field_simp [M.shellPrefix.delta_pos.ne']
    have hexpArg : 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) ≤ 1 := by
      have := M.shellPrefix.delta_le_half
      nlinarith
    have hexpLe : Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ)) ≤ 3 := by
      calc
        Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ))
            ≤ Real.exp 1 := Real.exp_le_exp.2 hexpArg
        _ ≤ 3 := by
          have := Real.exp_one_lt_d9
          linarith
    have htwosided := ((SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).2
      M (n + h) n (Nat.lt_add_of_pos_right hh)).2
    have hsubcast : ((n + h - n : ℕ) : ℝ) = (h : ℝ) := by
      simp
    have hlower : ahom M n ≤
        Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ)) *
          ahom M (n + h) := by
      simpa only [hsubcast] using htwosided
    have hinvLe : (ahom M (n + h))⁻¹ ≤
        Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ)) *
          (ahom M n)⁻¹ := by
      have hpos1 : 0 < ahom M (n + h) := ahom_pos M (n + h)
      have hpos2 : 0 < ahom M n := ahom_pos M n
      have hstep := mul_le_mul_of_nonneg_right hlower
        (mul_nonneg (inv_nonneg.mpr hpos1.le) (inv_nonneg.mpr hpos2.le))
      calc
        (ahom M (n + h))⁻¹
            = ahom M n * ((ahom M (n + h))⁻¹ * (ahom M n)⁻¹) := by
              field_simp
        _ ≤ (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ)) *
              ahom M (n + h)) *
            ((ahom M (n + h))⁻¹ * (ahom M n)⁻¹) := hstep
        _ = Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ)) *
            (ahom M n)⁻¹ := by field_simp
    have hfactor : Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ)) ≤
        1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          C * M.delta ^ 4 * (h : ℝ) ^ 2 +
          C * M.delta ^ 2 * |Real.log M.delta| := by
      have hdpos : (0 : ℝ) < d := by
        have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      have hterm0 : 0 ≤ 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) := by
        have := M.G4.tauSq_pos.le
        positivity
      have herr0 : 0 ≤ C * M.delta ^ 4 * (h : ℝ) ^ 2 := by positivity
      linarith
    calc
      (ahom M (n + h))⁻¹ ≤
          Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ)) *
            (ahom M n)⁻¹ := hinvLe
      _ ≤ (1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
            C * M.delta ^ 4 * (h : ℝ) ^ 2 +
            C * M.delta ^ 2 * |Real.log M.delta|) * (ahom M n)⁻¹ :=
        mul_le_mul_of_nonneg_right hfactor (inv_nonneg.mpr (ahom_pos M n).le)
      _ = (ahom M n)⁻¹ *
          (1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
            C * M.delta ^ 4 * (h : ℝ) ^ 2 +
            C * M.delta ^ 2 * |Real.log M.delta|) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
