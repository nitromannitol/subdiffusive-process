module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ExpectationVarianceAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.CombineFiniteClosure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.CombineAssemblySeams
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.BadEventLane

@[expose] public section

/-!
# Final finite assembly for the Section 4 combine recursion

This module closes the three finite seams left after the corridor integration:
the cutoff-scale base case, the comparison of the two exponential gates, and
the bad-event response at the preceding cube.

PROVENANCE: the separation choice and finite small-gap exclusion mirror
`Algsuperdiff/Section3/Provider/Homogenization/FiniteRecurrence.lean`; the
bad-event constant coordination mirrors
`Algsuperdiff/Section3/Provider/Homogenization/CombineBadEvent.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The Chapter-4 restriction response is the literal cutoff response on the
potential sample. -/
theorem restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) (omega : Sample d) :
    Ch04.restrictionResponseJObservableCubeSet R p q
        (aCutoffRegCoeffField M L omega) =
      cutoffResponseOnCube M L p q R omega := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d116_restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube (d := d) (M := M) (L := L) (p := p) (q := q) (R := R) (omega := omega)

/-- At the cutoff scale, the induction-hypothesis defect bound controls every
headline response load with constant one. -/
theorem expectedJ_base_le_delta_of_inductionHypothesis
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {xi delta1 : ℝ}
    (hxi : 2 ≤ xi) (hS : inductionHypothesis M L xi delta1)
    (p q : Vec d) (hq : q = ahom M L • p)
    (hqNorm : vecNormSq q ≤ ahom M L) :
    expectedJ M L L p q ≤ delta1 := by
  let Y : Sample d → ℝ :=
    cutoffResponseOnCube M L p q (originCube d (L : ℤ))
  have hsq :=
    cutoffResponseOnCube_sq_integrable_and_integral_le_of_inductionHypothesis
      M hxi hS le_rfl le_rfl p q hq hqNorm
  have hYmeas : AEStronglyMeasurable Y M.P.toMeasure := by
    exact (measurable_cutoffResponseOnCube M L p q
      (originCube d (L : ℤ))).aestronglyMeasurable
  have hYnonneg : 0 ≤ᵐ[M.P.toMeasure] Y :=
    Filter.Eventually.of_forall fun omega =>
      Ch02.responseJ_nonneg
        (Ch02.cubeDomain (originCube d (L : ℤ)))
        (aCutoffCoeffOnData M L omega
          (Ch02.cubeDomain (originCube d (L : ℤ)))).toCoeffOn p q
  have hcs := integral_indicator_le_sqrt_sq_mul_sqrt_measureReal
    (mu := M.P.toMeasure) (B := Set.univ) MeasurableSet.univ hYmeas
    hYnonneg (by simpa only [Y] using hsq.1)
  have hsqrt : Real.sqrt (∫ omega, Y omega ^ 2 ∂M.P.toMeasure) ≤ delta1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨hS.2.1.le, by simpa only [Y] using hsq.2⟩
  have hmean : ∫ omega, Y omega ∂M.P.toMeasure ≤ delta1 := by
    rw [Measure.restrict_univ, probReal_univ, Real.sqrt_one, mul_one] at hcs
    exact hcs.trans hsqrt
  simpa only [expectedJ, Y, cutoffResponseOnCube, aCutoffFamily,
    aCutoffTriadicData] using hmean

/-- A sufficiently large coefficient in the frozen `3⁻ᵗ` gate excludes the
finite set of small gaps and hence supplies the source `3⁻³ᵗ⁄⁴` gate. -/
theorem exists_full_gate_implies_three_quarter_gate (C0 : ℝ) (hC0 : 0 < C0) :
    ∃ Cgate : ℝ, 1 ≤ Cgate ∧
      ∀ t : ℕ,
        Cgate * Real.rpow 3 (-(t : ℝ)) ≤ 1 / 4 →
          C0 * Real.rpow 3 (-(3 / 4 : ℝ) * (t : ℝ)) ≤ 1 / 4 := by
  let rho : ℝ := Real.rpow 3 (-(3 / 4 : ℝ))
  have hrho0 : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _
  have hrho1 : rho < 1 := by
    dsimp only [rho]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < 1 / (4 * C0)) hrho1
  let Cgate : ℝ := (3 : ℝ) ^ N
  have hCgate : 1 ≤ Cgate := by
    dsimp only [Cgate]
    exact one_le_pow₀ (by norm_num)
  refine ⟨Cgate, hCgate, ?_⟩
  intro t hgate
  have hNt : N ≤ t := by
    by_contra hnot
    have htN : t < N := Nat.lt_of_not_ge hnot
    have hmono : (1 / 3 : ℝ) ^ N ≤ (1 / 3 : ℝ) ^ t :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_of_lt htN)
    have hone : Cgate * (1 / 3 : ℝ) ^ N = 1 := by
      dsimp only [Cgate]
      rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, ← mul_pow]
      norm_num
    have hcontra : 1 ≤ Cgate * Real.rpow 3 (-(t : ℝ)) := by
      rw [rpow_three_neg_nat_eq_pow]
      calc
        1 = Cgate * (1 / 3 : ℝ) ^ N := hone.symm
        _ ≤ Cgate * (1 / 3 : ℝ) ^ t :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
    linarith
  have hpow : Real.rpow 3 (-(3 / 4 : ℝ) * (t : ℝ)) =
      (fun n : ℕ => rho ^ n) t := by
    calc
      Real.rpow 3 (-(3 / 4 : ℝ) * (t : ℝ)) =
          Real.rpow rho (t : ℝ) := by
        dsimp only [rho]
        exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
      _ = (fun n : ℕ => rho ^ n) t := Real.rpow_natCast rho t
  have hmono : rho ^ t ≤ rho ^ N :=
    pow_le_pow_of_le_one hrho0.le hrho1.le hNt
  rw [hpow]
  exact (calc
      C0 * rho ^ t ≤ C0 * rho ^ N := mul_le_mul_of_nonneg_left hmono hC0.le
      _ < C0 * (1 / (4 * C0)) := mul_lt_mul_of_pos_left hN hC0
      _ = 1 / 4 := by field_simp).le

/-- The concrete Step-4 close at cube `m - 1`, with every probabilistic and
moment input discharged from the proved large-cube anchor and the induction
hypothesis. -/
theorem exists_badEvent_previousCube_response_le_delta_sq (d : ℕ) :
    ∃ c Cbad : ℝ, 0 < c ∧ 1 ≤ Cbad ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
        (xi delta1 : ℝ),
        16 * (d : ℝ) ≤ xi →
        Cbad * xi * M.delta ^ 2 ≤ delta1 → delta1 ≤ c →
        inductionHypothesis M L xi delta1 → 0 < m → L ≤ m - 1 →
        ∀ p q : Vec d, q = ahom M L • p → vecNormSq q ≤ ahom M L →
          ∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d in
              (coarseEllipticityGoodEvent M L m)ᶜ,
              Ch04.restrictionResponseJObservableCubeSet
                (originCube d ((m : ℤ) - 1)) p q
                (aCutoffRegCoeffField M L omega) ∂M.P.toMeasure ≤
            Cbad * delta1 ^ 2 := by
  by_cases hd : d = 0
  · subst d
    refine ⟨1, 1, by norm_num, le_rfl, ?_⟩
    intro M
    have hdim := M.shellPrefix.dimension
    omega
  letI : NeZero d := ⟨hd⟩
  let hLarge : MultiscaleResponseLargeCubesConclusion d :=
    SubdiffusiveProcess.Frozen.Section4.multiscale_response_large_cubes
  obtain ⟨cProb, CB, hcProb, hCB, hprob⟩ :=
    coarseEllipticityBadEvent_probability_le_of_multiscaleResponseLargeCubes
      hLarge
  let c : ℝ := min (1 / 2) CB⁻¹
  let Cbad : ℝ := max 1 (max CB (4 * cProb⁻¹))
  have hc : 0 < c := lt_min (by norm_num) (inv_pos.mpr hCB)
  have hCbad : 1 ≤ Cbad := le_max_left _ _
  refine ⟨c, Cbad, hc, hCbad, ?_⟩
  intro M L m xi delta1 hxi hgate hdelta hS hm hLm p q hq hqNorm
  have hdTwo : 2 ≤ d := M.shellPrefix.dimension
  have hxiTwo : 2 ≤ xi := by
    have hdCast : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdTwo
    nlinarith
  have hxiFour : 4 ≤ xi := by
    have hdCast : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdTwo
    nlinarith
  have hdelta0 : 0 ≤ delta1 := hS.2.1.le
  have hdeltaSq : 0 < M.delta ^ 2 := sq_pos_of_pos M.shellPrefix.delta_pos
  have hCbadProb : CB ≤ Cbad := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCbadGate : 4 * cProb⁻¹ ≤ Cbad :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hrawGate : (4 * cProb⁻¹) * xi * M.delta ^ 2 ≤ delta1 := by
    have hxi0 : 0 ≤ xi := by linarith
    calc
      (4 * cProb⁻¹) * xi * M.delta ^ 2 ≤
          Cbad * xi * M.delta ^ 2 := by
        gcongr
      _ ≤ delta1 := hgate
  have hupper : xi ≤ cProb * (1 / 4 : ℝ) * (M.delta ^ 2)⁻¹ * delta1 := by
    calc
      xi = cProb * (1 / 4 : ℝ) * (M.delta ^ 2)⁻¹ *
          ((4 * cProb⁻¹) * xi * M.delta ^ 2) := by
        field_simp [hcProb.ne', M.shellPrefix.delta_pos.ne']
      _ ≤ cProb * (1 / 4 : ℝ) * (M.delta ^ 2)⁻¹ * delta1 :=
        mul_le_mul_of_nonneg_left hrawGate (by positivity)
  have hdeltaLower : M.delta ^ 2 ≤ delta1 := by
    have hfactor : 1 ≤ Cbad * xi := by
      calc
        1 ≤ Cbad := hCbad
        _ ≤ Cbad * xi := by
          nlinarith [mul_nonneg (le_trans zero_le_one hCbad) (by linarith : 0 ≤ xi)]
    calc
      M.delta ^ 2 = 1 * M.delta ^ 2 := by ring
      _ ≤ (Cbad * xi) * M.delta ^ 2 :=
        mul_le_mul_of_nonneg_right hfactor (sq_nonneg M.delta)
      _ = Cbad * xi * M.delta ^ 2 := by ring
      _ ≤ delta1 := hgate
  have hprobability := hprob M L L m delta1 xi hdeltaLower hS.2.2.1
    le_rfl (by omega) hxi hupper hS
  have hCBsmall : CB * delta1 ≤ 1 := by
    have hcInv : c ≤ CB⁻¹ := min_le_right _ _
    calc
      CB * delta1 ≤ CB * c := mul_le_mul_of_nonneg_left hdelta hCB.le
      _ ≤ CB * CB⁻¹ := mul_le_mul_of_nonneg_left hcInv hCB.le
      _ = 1 := mul_inv_cancel₀ hCB.ne'
  have hsq :=
    cutoffResponseOnCube_sq_integrable_and_integral_le_of_inductionHypothesis
      M hxiTwo hS hLm le_rfl p q hq hqNorm
  let Y : Sample d → ℝ :=
    cutoffResponseOnCube M L p q (originCube d ((m - 1 : ℕ) : ℤ))
  have hbad := badEvent_response_le_delta_sq
    (mu := M.P.toMeasure) (B := (coarseEllipticityGoodEvent M L m)ᶜ)
    (J := Y) (C := 1) (CB := CB) (delta1 := delta1) (xi := xi)
    (measurableSet_coarseEllipticityGoodEvent M L m).compl
    (measurable_cutoffResponseOnCube M L p q
      (originCube d ((m - 1 : ℕ) : ℤ))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega =>
      Ch02.responseJ_nonneg
        (Ch02.cubeDomain (originCube d ((m - 1 : ℕ) : ℤ)))
        (aCutoffCoeffOnData M L omega
          (Ch02.cubeDomain (originCube d ((m - 1 : ℕ) : ℤ)))).toCoeffOn p q)
    (by norm_num) hCB.le hdelta0 hxiFour hCBsmall
    (by simpa only [Y] using hsq.1)
    (by simpa only [Y, one_pow, one_mul] using hsq.2)
    hprobability
  have hscale : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  have hconvert :
      (∫ omega : Sample d in (coarseEllipticityGoodEvent M L m)ᶜ,
          Ch04.restrictionResponseJObservableCubeSet
            (originCube d ((m : ℤ) - 1)) p q
            (aCutoffRegCoeffField M L omega) ∂M.P.toMeasure) =
        ∫ omega : Sample d in (coarseEllipticityGoodEvent M L m)ᶜ,
          Y omega ∂M.P.toMeasure := by
    apply integral_congr_ae
    filter_upwards with omega
    rw [← hscale,
      restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube M L p q]
  rw [hconvert]
  have hbad' : ∫ omega : Sample d in (coarseEllipticityGoodEvent M L m)ᶜ,
      Y omega ∂M.P.toMeasure ≤ CB * delta1 ^ 2 := by
    simpa only [one_mul] using hbad
  exact hbad'.trans
    (mul_le_mul_of_nonneg_right hCbadProb (sq_nonneg delta1))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
