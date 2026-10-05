module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductStoppedIteration
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.GammaOneCalibration

@[expose] public section

/-!
# Theta ladder: ambient centered Campanato contract

This module turns the stopped product recurrence into its affine-safe
centered normalized-`L²` decay row and packages that row on the ambient
translated stopping event.  No cell-to-parent mean is assigned a decaying
factor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

/-- Removing the scale normalization leaves a genuine `3^{-j/2}` decay once
the iteration exponential costs at most `3^{j/16}`. -/
theorem normalizedL2_decay_of_scaled_product
    {n top : ℕ} {inner outer A C : ℝ} (hntop : n ≤ top)
    (houter : 0 ≤ outer) (hC : 0 ≤ C)
    (hscaled : (3 : ℝ) ^ (-(n : ℤ)) * inner ≤
      Real.exp A * ((3 : ℝ) ^ (-(top : ℤ)) * outer))
    (hexp : Real.exp A ≤
      C * (3 : ℝ) ^ (((top : ℝ) - (n : ℝ)) / 16)) :
    inner ≤ C * (3 : ℝ) ^
        (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ))) * outer := by
  have hpowN : 0 < (3 : ℝ) ^ (-(n : ℤ)) := zpow_pos (by norm_num) _
  have hntopR : (n : ℝ) ≤ (top : ℝ) := by exact_mod_cast hntop
  have hgap : 0 ≤ (top : ℝ) - (n : ℝ) := sub_nonneg.mpr hntopR
  have hscaled' : inner * (3 : ℝ) ^ (-(n : ℤ)) ≤
      Real.exp A * ((3 : ℝ) ^ (-(top : ℤ)) * outer) := by
    simpa only [mul_comm] using hscaled
  have hdiv := (le_div_iff₀ hpowN).2 hscaled'
  have hpowRatio :
      (3 : ℝ) ^ (-(top : ℤ)) / (3 : ℝ) ^ (-(n : ℤ)) =
        (3 : ℝ) ^ (-((top : ℝ) - (n : ℝ))) := by
    rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    rw [← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hratio :
      (Real.exp A * ((3 : ℝ) ^ (-(top : ℤ)) * outer)) /
          (3 : ℝ) ^ (-(n : ℤ)) =
        Real.exp A *
          (3 : ℝ) ^ (-((top : ℝ) - (n : ℝ))) * outer := by
    rw [div_eq_mul_inv]
    calc
      Real.exp A * ((3 : ℝ) ^ (-(top : ℤ)) * outer) *
          ((3 : ℝ) ^ (-(n : ℤ)))⁻¹ =
        Real.exp A *
          ((3 : ℝ) ^ (-(top : ℤ)) / (3 : ℝ) ^ (-(n : ℤ))) * outer := by
            rw [div_eq_mul_inv]
            ring
      _ = _ := by rw [hpowRatio]
  rw [hratio] at hdiv
  have hpowGap : 0 ≤ (3 : ℝ) ^ (-((top : ℝ) - (n : ℝ))) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hexp
    (mul_nonneg hpowGap houter)
  have hmul' : Real.exp A *
      (3 : ℝ) ^ (-((top : ℝ) - (n : ℝ))) * outer ≤
    (C * (3 : ℝ) ^ (((top : ℝ) - (n : ℝ)) / 16)) *
      (3 : ℝ) ^ (-((top : ℝ) - (n : ℝ))) * outer := by
    simpa only [mul_assoc] using hmul
  refine hdiv.trans (hmul'.trans ?_)
  have hexponent :
      ((top : ℝ) - (n : ℝ)) / 16 - ((top : ℝ) - (n : ℝ)) ≤
        -(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ)) := by
    linarith
  have hpowLe :
      (3 : ℝ) ^ (((top : ℝ) - (n : ℝ)) / 16 -
          ((top : ℝ) - (n : ℝ))) ≤
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hmulLe := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpowLe hC) houter
  have hpowEq :
      (3 : ℝ) ^ (((top : ℝ) - (n : ℝ)) / 16) *
          (3 : ℝ) ^ (-((top : ℝ) - (n : ℝ))) =
        (3 : ℝ) ^ (((top : ℝ) - (n : ℝ)) / 16 -
          ((top : ℝ) - (n : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
  simpa only [hpowEq, mul_assoc] using hmulLe

/-- The stopped bad-cardinality and slope-error budgets cost at most the
quarter-reserve `3^{j/16}` at the fixed exponent `3/4`. -/
theorem product_iteration_exponential_le
    {Citer C₁ Cabs : ℝ} (hCiter : 0 < Citer) (hC₁ : 0 < C₁)
    {k badCard n top : ℕ} (hntop : n ≤ top)
    (habs : ∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
      Real.exp
          (Citer * (k + 1) * (k + 2) +
            (Citer * (k + 2)) * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
        Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4))
    {epsCoeff : ℝ}
    (heps : epsCoeff ≤ C₁⁻¹ * (1 - thetaLadderExponent))
    (hcard : (badCard : ℝ) < (k : ℝ) + 1 +
      C₁⁻¹ * (1 - thetaLadderExponent) *
        ((top : ℝ) - (n : ℝ))) :
    Real.exp
        (Citer * (k + 1) * (badCard + 1) +
          Citer * (((top : ℝ) - (n : ℝ)) + 1) * epsCoeff) ≤
      Cabs * (3 : ℝ) ^ (((top : ℝ) - (n : ℝ)) / 16) := by
  have hgap : 0 ≤ (top : ℝ) - (n : ℝ) := by
    have : (n : ℝ) ≤ (top : ℝ) := by exact_mod_cast hntop
    linarith
  have hlambda : 0 ≤ C₁⁻¹ * (1 - thetaLadderExponent) := by
    have htheta := thetaLadderExponent_mem
    exact mul_nonneg (inv_nonneg.mpr hC₁.le) (sub_nonneg.mpr htheta.2.le)
  have hA :
      Citer * (k + 1) * (badCard + 1) +
          Citer * (((top : ℝ) - (n : ℝ)) + 1) * epsCoeff ≤
        Citer * (k + 1) * (k + 2) +
          (Citer * (k + 2)) *
            (C₁⁻¹ * (1 - thetaLadderExponent)) *
              (((top : ℝ) - (n : ℝ)) + 1) := by
    have hcard' : (badCard : ℝ) + 1 ≤ (k : ℝ) + 2 +
        C₁⁻¹ * (1 - thetaLadderExponent) *
          ((top : ℝ) - (n : ℝ)) := by linarith
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    have hfirst := mul_le_mul_of_nonneg_left hcard'
      (mul_nonneg hCiter.le (by positivity : (0 : ℝ) ≤ k + 1))
    have hsecond := mul_le_mul_of_nonneg_left heps
      (mul_nonneg hCiter.le (by positivity :
        (0 : ℝ) ≤ (top : ℝ) - (n : ℝ) + 1))
    have hsum := add_le_add hfirst hsecond
    have hsum' :
        Citer * (k + 1) * (badCard + 1) +
            Citer * (((top : ℝ) - (n : ℝ)) + 1) * epsCoeff ≤
          Citer * (k + 1) *
              (k + 2 + C₁⁻¹ * (1 - thetaLadderExponent) *
                ((top : ℝ) - (n : ℝ))) +
            Citer * (((top : ℝ) - (n : ℝ)) + 1) *
              (C₁⁻¹ * (1 - thetaLadderExponent)) := by
      simpa only [mul_assoc] using hsum
    refine hsum'.trans ?_
    have hslack : 0 ≤ Citer * (k + 1) *
        (C₁⁻¹ * (1 - thetaLadderExponent)) := by positivity
    nlinarith only [hslack]
  have hexp := Real.exp_le_exp.mpr hA
  have hthetaIcc : thetaLadderExponent ∈ Set.Icc (1 / 2 : ℝ) 1 :=
    ⟨thetaLadderExponent_mem.1, thetaLadderExponent_mem.2.le⟩
  have habs' := habs thetaLadderExponent hthetaIcc
    ((top : ℝ) - (n : ℝ)) hgap
  have hquarter :
      (1 - thetaLadderExponent) * ((top : ℝ) - (n : ℝ)) / 4 =
        ((top : ℝ) - (n : ℝ)) / 16 := by
    rw [thetaLadderExponent]
    ring
  rw [hquarter] at habs'
  exact hexp.trans habs'

/-- A constant sum on an integer interval has the expected real cardinality. -/
theorem sum_const_Icc_intCast {n top : ℕ} (hntop : n ≤ top) (e : ℝ) :
    ∑ _i ∈ Finset.Icc (n : ℤ) (top : ℤ), e =
      (((top : ℝ) - (n : ℝ)) + 1) * e := by
  rw [Finset.sum_const, Int.card_Icc]
  have hnonneg : 0 ≤ (top : ℤ) + 1 - (n : ℤ) := by
    have : (n : ℤ) ≤ (top : ℤ) := by exact_mod_cast hntop
    omega
  rw [nsmul_eq_mul]
  have hcast : (((top : ℤ) + 1 - (n : ℤ)).toNat : ℝ) =
      (top : ℝ) + 1 - (n : ℝ) := by
    have hz := Int.toNat_of_nonneg hnonneg
    exact_mod_cast hz
  rw [hcast]
  ring

/-- The stopped product recurrence, with its numerical budget exposed, gives
the genuine centered `3^{-j/2}` Campanato decay. -/
theorem exists_productStoppedCampanatoDecay (d : ℕ) [NeZero d] :
    ∃ Kbase Cgain Citer : ℝ,
      0 < Kbase ∧ 0 < Cgain ∧ 0 < Citer ∧
      ∀ C₁ Cabs : ℝ, 0 < C₁ → 0 ≤ Cabs →
      ∀ k : ℕ, 6 ≤ k →
      (∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
        Real.exp
            (Citer * (k + 1) * (k + 2) +
              (Citer * (k + 2)) * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
          Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4)) →
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) →
      ∀ L n top : ℕ, ∀ C₂ : ℝ, ∀ step j0 : ℕ,
      n < top → j0 ≤ top - n →
      ∀ z q : Vec d, OnTriadicGrid n q → q ∈ cube d top →
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      omega ∈ translatedThetaLadderStoppingEvent
        M L C₁ C₂ step top j0 z →
      let eta := Section6Stopping.holderStoppingEpsilon
        C₂ thetaLadderExponent
      ∀ _heta : eta ∈ Set.Icc ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) 1,
      ∀ b epsilon : ℝ, 0 < b → 0 < epsilon → epsilon ≤ 1 / 2 →
      Kbase * eta + Cgain * Real.sqrt epsilon ≤ 1 →
      productIterationSlopeCoefficient d M.shellPrefix.dimension k
          (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
        C₁⁻¹ * (1 - thetaLadderExponent) →
      ∀ theta : Vec d → ℝ,
      ContinuousOn theta (translatedCube d (top : ℤ) (z + q)) →
      (∀ x ∈ translatedCube d (top : ℤ) (z + q),
        |b⁻¹ * theta x - 1| ≤ epsilon) →
      let contraction := (3 : ℝ) ^ (-(1 / 4 : ℝ))
      contraction ∈ Set.Ioo (0 : ℝ) 1 →
      contraction ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) +
        productOriginRecurrenceErrorConstant d M.shellPrefix.dimension k *
          (Kbase * eta + Cgain * Real.sqrt epsilon) ≤ contraction ^ k →
      ∀ u : H1Function (translatedCube d (top : ℤ) (z + q)),
      IsWeaklyHarmonicOn
          (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * theta x)
          (translatedCube d (top : ℤ) (z + q)) u →
      normalizedL2On (translatedCube d (n : ℤ) (z + q))
          (fun x ↦ u.toFun x -
            averageOn (translatedCube d (n : ℤ) (z + q)) u.toFun) ≤
        Cabs * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ))) *
          normalizedL2On (translatedCube d (top : ℤ) (z + q))
            (fun x ↦ u.toFun x -
              averageOn (translatedCube d (top : ℤ) (z + q)) u.toFun) := by
  obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, hstop⟩ :=
    exists_productStoppedIteration d
  refine ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, ?_⟩
  intro C₁ Cabs hC₁ hCabs k hk habs M hsmall L n top C₂ step j0 hntop hj0
    z q hqgrid hqmem omega homega
  dsimp only
  intro heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff theta
    htheta hnear hcontraction hcontractionPow hcontract u hu
  let contraction : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ))
  have hcore := hstop M hsmall L top n top k hntop le_rfl hk
    C₁ C₂ step j0 hj0 z q hqgrid hqmem omega homega heta b epsilon hb
    hepsilon hepsilonHalf herrorOne theta htheta hnear contraction
    hcontraction hcontractionPow hcontract u hu
  dsimp only at hcore
  let error := Kbase *
      Section6Stopping.holderStoppingEpsilon C₂ thetaLadderExponent +
    Cgain * Real.sqrt epsilon
  let epsRow : ℤ → ℝ := fun _ ↦
    productIterationSlopeCoefficient d M.shellPrefix.dimension k error
  let bad := productBadScales M L
    (Section6Stopping.holderStoppingEpsilon C₂ thetaLadderExponent)
    (1 / 32 : ℝ) n top k (z + q) omega
  let A := Citer * (k + 1) * (bad.card + 1) +
    Citer * ∑ i ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow i
  have hcard : (bad.card : ℝ) < (k : ℝ) + 1 +
      C₁⁻¹ * (1 - thetaLadderExponent) *
        ((top : ℝ) - (n : ℝ)) := by
    dsimp only [bad]
    simpa only [Nat.cast_ofNat, add_assoc] using! hcore.1
  have hsum : (∑ i ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow i) =
      (((top : ℝ) - (n : ℝ)) + 1) *
        productIterationSlopeCoefficient d M.shellPrefix.dimension k error := by
    exact sum_const_Icc_intCast (Nat.le_of_lt hntop) _
  have hExp : Real.exp A ≤
      Cabs * (3 : ℝ) ^ (((top : ℝ) - (n : ℝ)) / 16) := by
    dsimp only [A]
    rw [hsum]
    simpa only [error, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, mul_assoc]
      using product_iteration_exponential_le hCiter hC₁ (k := k)
        (hntop := Nat.le_of_lt hntop) habs hepsCoeff hcard
  have hscaled : (3 : ℝ) ^ (-(n : ℤ)) *
        normalizedL2On (translatedCube d (n : ℤ) (z + q))
          (fun x ↦ u.toFun x -
            averageOn (translatedCube d (n : ℤ) (z + q)) u.toFun) ≤
      Real.exp A * ((3 : ℝ) ^ (-(top : ℤ)) *
        normalizedL2On (translatedCube d (top : ℤ) (z + q))
          (fun x ↦ u.toFun x -
            averageOn (translatedCube d (top : ℤ) (z + q)) u.toFun)) := by
    simpa only [A, bad, epsRow, error] using hcore.2
  exact normalizedL2_decay_of_scaled_product (Nat.le_of_lt hntop)
    (Section6Iteration.normalizedL2On_nonneg _ _) hCabs hscaled hExp

/-- Ambient bad-event package for the centered stopped theta-Campanato row.
The event is independent of the multiplier and of the translated grid cell. -/
theorem exists_ambientProductCampanatoContract (d : ℕ) [NeZero d]
    (step : ℕ) :
    ∃ Kbase Cgain Citer : ℝ,
      0 < Kbase ∧ 0 < Cgain ∧ 0 < Citer ∧
      ∀ C₁ C₂ Cabs : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 0 ≤ Cabs →
      ∀ k : ℕ, 6 ≤ k →
      (∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
        Real.exp
            (Citer * (k + 1) * (k + 2) +
              (Citer * (k + 2)) * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
          Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4)) →
      ∃ c Ctail : ℝ, 0 < c ∧ 0 < Ctail ∧ c ≤ 1 ∧
        ∃ j0 : ℕ, 0 < j0 ∧
          ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ c →
          64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) →
          ∀ L top : ℕ, ∀ z : Vec d,
            ∃ badTheta : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d),
              MeasurableSet badTheta ∧
              M.P.toMeasure badTheta ≤ ENNReal.ofReal
                (Ctail * Real.exp
                  (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
              ∀ omega ∉ badTheta, ∀ n : ℕ, n < top → j0 ≤ top - n →
              ∀ q : Vec d, OnTriadicGrid n q → q ∈ cube d top →
              let eta := Section6Stopping.holderStoppingEpsilon
                C₂ thetaLadderExponent
              ∀ _heta : eta ∈
                Set.Icc ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) 1,
              ∀ b epsilon : ℝ, 0 < b → 0 < epsilon → epsilon ≤ 1 / 2 →
              Kbase * eta + Cgain * Real.sqrt epsilon ≤ 1 →
              productIterationSlopeCoefficient d M.shellPrefix.dimension k
                  (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
                C₁⁻¹ * (1 - thetaLadderExponent) →
              ∀ theta : Vec d → ℝ,
              ContinuousOn theta
                (translatedCube d (top : ℤ) (z + q)) →
              (∀ x ∈ translatedCube d (top : ℤ) (z + q),
                |b⁻¹ * theta x - 1| ≤ epsilon) →
              let contraction := (3 : ℝ) ^ (-(1 / 4 : ℝ))
              contraction ∈ Set.Ioo (0 : ℝ) 1 →
              contraction ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
              oneStepContractionConst d *
                    Section6Schauder.schauderInteriorConst d *
                    ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) +
                  productOriginRecurrenceErrorConstant d
                    M.shellPrefix.dimension k *
                    (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
                contraction ^ k →
              ∀ u : H1Function
                (translatedCube d (top : ℤ) (z + q)),
              IsWeaklyHarmonicOn
                  (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * theta x)
                  (translatedCube d (top : ℤ) (z + q)) u →
              normalizedL2On (translatedCube d (n : ℤ) (z + q))
                  (fun x ↦ u.toFun x - averageOn
                    (translatedCube d (n : ℤ) (z + q)) u.toFun) ≤
                Cabs * (3 : ℝ) ^
                    (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ))) *
                  normalizedL2On (translatedCube d (top : ℤ) (z + q))
                    (fun x ↦ u.toFun x - averageOn
                      (translatedCube d (top : ℤ) (z + q)) u.toFun) := by
  obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, hdecay⟩ :=
    exists_productStoppedCampanatoDecay d
  refine ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, ?_⟩
  intro C₁ C₂ Cabs hC₁ hC₂ hCabs k hk habs
  obtain ⟨c, Ctail, hc, hCtail, hcOne, j0, hj0, htail⟩ :=
    exists_translatedThetaLadderGammaOneCalibration d step hC₁ hC₂
  refine ⟨c, Ctail, hc, hCtail, hcOne, j0, hj0, ?_⟩
  intro M hdelta hsmall L top z
  let good := translatedThetaLadderStoppingEvent
    M L C₁ C₂ step top j0 z
  refine ⟨goodᶜ,
    (measurableSet_translatedThetaLadderStoppingEvent
      M L C₁ C₂ step top j0 z).compl, ?_, ?_⟩
  · exact htail M hdelta L top z
  · intro omega homega n hntop hdepth q hqgrid hqmem
    have homegaGood : omega ∈ good := by
      simpa only [Set.mem_compl_iff, not_not] using homega
    dsimp only
    intro heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff theta
      htheta hnear hcontraction hcontractionPow hcontract u hu
    exact hdecay C₁ Cabs (zero_lt_one.trans_le hC₁) hCabs k hk habs M hsmall
      L n top C₂ step j0 hntop hdepth z q hqgrid hqmem omega homegaGood heta b epsilon
      hb hepsilon hepsilonHalf herrorOne hepsCoeff theta htheta hnear
      hcontraction hcontractionPow hcontract u hu

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
