import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.AmbientParentCampanatoContract

/-!
# Theta ladder: intermediate rows from a fine-grid stopping certificate

The off-grid Campanato readout selects a centre on the scale-`n` grid, but
uses the centred row on the containing scale-`n+1` cube.  A scale-`n` grid
point need not lie on the scale-`n+1` grid.  This file therefore extracts an
intermediate row from the stopped recurrence while retaining the original
fine-grid certificate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A stopping certificate at a fine grid scale controls every intermediate
centred row.  The constant records only the unused part of the parent gap;
when `ell = n+1` and `top = parent-2`, this is the fixed price `3^(3/16)`. -/
theorem exists_productStoppedIntermediateCampanatoDecayOnParent
    (d : ℕ) [NeZero d] :
    ∃ Kbase Cgain Citer : ℝ,
      0 < Kbase ∧ 0 < Cgain ∧ 0 < Citer ∧
      ∀ C₁ Cabs : ℝ, 0 < C₁ → 0 ≤ Cabs →
      ∀ k : ℕ, 6 ≤ k →
      (∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
        Real.exp
            (Citer * (k + 1) * (k + 2) +
              (Citer * (k + 2)) * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
          Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4)) →
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) →
      ∀ L n ell top parent : ℕ, n ≤ ell → ell < top → top ≤ parent →
      ∀ C₂ : ℝ, ∀ step j0 : ℕ, j0 ≤ parent - n →
      ∀ z q : Vec d, OnTriadicGrid n q → q ∈ cube d parent →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      omega ∈ translatedThetaLadderStoppingEvent
        M L C₁ C₂ step parent j0 z →
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
            (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
        contraction ^ k →
      ∀ u : H1Function (translatedCube d (top : ℤ) (z + q)),
      IsWeaklyHarmonicOn
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
          (translatedCube d (top : ℤ) (z + q)) u →
      normalizedL2On (translatedCube d (ell : ℤ) (z + q))
          (fun x ↦ u.toFun x - averageOn
            (translatedCube d (ell : ℤ) (z + q)) u.toFun) ≤
        (Cabs * (3 : ℝ) ^
            ((((parent : ℝ) - (n : ℝ)) -
              ((top : ℝ) - (ell : ℝ))) / 16)) *
          (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((top : ℝ) - (ell : ℝ))) *
          normalizedL2On (translatedCube d (top : ℤ) (z + q))
            (fun x ↦ u.toFun x - averageOn
              (translatedCube d (top : ℤ) (z + q)) u.toFun) := by
  obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, happly⟩ :=
    exists_productIterationApplied d
  refine ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, ?_⟩
  intro C₁ Cabs hC₁ hCabs k hk habs M hsmall L n ell top parent hnell
    helltop htop C₂ step j0 hj0 z q hqgrid hqmem omega hstop
  dsimp only
  intro heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff theta
    htheta hnear hcontraction hcontractionPow hcontract u hu
  let eta := Section6Stopping.holderStoppingEpsilon C₂ thetaLadderExponent
  let error := Kbase * eta + Cgain * Real.sqrt epsilon
  let epsCoeff := productIterationSlopeCoefficient d
    M.shellPrefix.dimension k error
  let bad := productBadScales M L eta (1 / 32 : ℝ)
    ell top k (z + q) omega
  let A := Citer * (k + 1) * (bad.card + 1) +
    Citer * ∑ i ∈ Finset.Icc (ell : ℤ) (top : ℤ), epsCoeff
  have hfailureFull := translatedThetaLadder_stopped_goodFailure_interval
    M L C₁ C₂ step parent n top j0 z omega hstop hj0 htop q hqgrid hqmem
  have hsub : Finset.Icc ell top ⊆ Finset.Icc n top := by
    intro i hi
    exact Finset.mem_Icc.2 ⟨hnell.trans (Finset.mem_Icc.1 hi).1,
      (Finset.mem_Icc.1 hi).2⟩
  have hfailure :
      (∑ i ∈ Finset.Icc ell top,
          ((1 : ℝ) - if omega ∈ goodEvent M (some L) i (z + q) eta
            (1 / 32 : ℝ) then 1 else 0)) <
        1 + Section6Stopping.holderStoppingLambda C₁ thetaLadderExponent *
          ((parent : ℝ) - (n : ℝ)) := by
    have hle :
      (∑ i ∈ Finset.Icc ell top,
          ((1 : ℝ) - if omega ∈ goodEvent M (some L) i (z + q) eta
            (1 / 32 : ℝ) then 1 else 0)) ≤
        ∑ i ∈ Finset.Icc n top,
          ((1 : ℝ) - if omega ∈ goodEvent M (some L) i (z + q) eta
            (1 / 32 : ℝ) then 1 else 0) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro i _ _
        split_ifs <;> norm_num)
    exact hle.trans_lt (by simpa only [eta] using hfailureFull)
  have hcore := happly M hsmall L ell top k helltop hk (z + q) omega eta heta
    b epsilon hb hepsilon hepsilonHalf herrorOne theta htheta hnear
    ((3 : ℝ) ^ (-(1 / 4 : ℝ))) hcontraction hcontractionPow hcontract
    (1 + Section6Stopping.holderStoppingLambda C₁ thetaLadderExponent *
      ((parent : ℝ) - (n : ℝ))) hfailure u hu
  dsimp only at hcore
  have hcard : (bad.card : ℝ) < (k : ℝ) + 1 +
      C₁⁻¹ * (1 - thetaLadderExponent) *
        ((parent : ℝ) - (n : ℝ)) := by
    dsimp only [bad]
    simpa only [Section6Stopping.holderStoppingLambda, add_assoc] using hcore.1
  have hparentGap : n ≤ parent := hnell.trans (Nat.le_trans
    (Nat.le_of_lt helltop) htop)
  have hExpParent : Real.exp
      (Citer * (k + 1) * (bad.card + 1) +
        Citer * ((((parent : ℝ) - (n : ℝ)) + 1) * epsCoeff)) ≤
      Cabs * (3 : ℝ) ^ (((parent : ℝ) - (n : ℝ)) / 16) := by
    simpa only [epsCoeff, error, eta, mul_assoc] using
      (product_iteration_exponential_le hCiter hC₁
        hparentGap habs
          (by simpa only [epsCoeff, error, eta] using hepsCoeff) hcard)
  have heps0 : 0 ≤ epsCoeff := by
    apply productIterationSlopeCoefficient_nonneg
    dsimp only [error, eta]
    exact add_nonneg
      (mul_nonneg hKbase.le
        ((by positivity : 0 ≤ (1 / 32 : ℝ)⁻¹ * M.delta ^ 2).trans heta.1))
      (mul_nonneg hCgain.le (Real.sqrt_nonneg _))
  have hlength : (top : ℝ) - (ell : ℝ) + 1 ≤
      (parent : ℝ) - (n : ℝ) + 1 := by
    have htopR : (top : ℝ) ≤ (parent : ℝ) := by exact_mod_cast htop
    have hnellR : (n : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hnell
    linarith
  have hsum : (∑ _i ∈ Finset.Icc (ell : ℤ) (top : ℤ), epsCoeff) =
      (((top : ℝ) - (ell : ℝ)) + 1) * epsCoeff :=
    sum_const_Icc_intCast (Nat.le_of_lt helltop) epsCoeff
  have hAupper : A ≤ Citer * (k + 1) * (bad.card + 1) +
      Citer * ((((parent : ℝ) - (n : ℝ)) + 1) * epsCoeff) := by
    dsimp only [A]
    rw [hsum]
    gcongr
  have hExp : Real.exp A ≤
      Cabs * (3 : ℝ) ^ (((parent : ℝ) - (n : ℝ)) / 16) :=
    (Real.exp_le_exp.mpr hAupper).trans hExpParent
  have hsplit : ((parent : ℝ) - (n : ℝ)) / 16 =
      (((parent : ℝ) - (n : ℝ)) - ((top : ℝ) - (ell : ℝ))) / 16 +
        ((top : ℝ) - (ell : ℝ)) / 16 := by ring
  have hExpSplit : Real.exp A ≤
      (Cabs * (3 : ℝ) ^
          ((((parent : ℝ) - (n : ℝ)) -
            ((top : ℝ) - (ell : ℝ))) / 16)) *
        (3 : ℝ) ^ (((top : ℝ) - (ell : ℝ)) / 16) := by
    calc
      Real.exp A ≤ Cabs * (3 : ℝ) ^
          (((parent : ℝ) - (n : ℝ)) / 16) := hExp
      _ = _ := by
        rw [hsplit, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        ring
  have hCsplit : 0 ≤ Cabs * (3 : ℝ) ^
      ((((parent : ℝ) - (n : ℝ)) -
        ((top : ℝ) - (ell : ℝ))) / 16) :=
    mul_nonneg hCabs (Real.rpow_nonneg (by norm_num) _)
  have hscaled : (3 : ℝ) ^ (-(ell : ℤ)) *
        normalizedL2On (translatedCube d (ell : ℤ) (z + q))
          (fun x ↦ u.toFun x - averageOn
            (translatedCube d (ell : ℤ) (z + q)) u.toFun) ≤
      Real.exp A * ((3 : ℝ) ^ (-(top : ℤ)) *
        normalizedL2On (translatedCube d (top : ℤ) (z + q))
          (fun x ↦ u.toFun x - averageOn
            (translatedCube d (top : ℤ) (z + q)) u.toFun)) := by
    simpa only [A, bad, epsCoeff, error, eta] using hcore.2
  exact normalizedL2_decay_of_scaled_product (Nat.le_of_lt helltop)
    (Section6Iteration.normalizedL2On_nonneg _ _) hCsplit hscaled hExpSplit

/-- Ambient event package for all intermediate rows.  The selected event is
the same parent stopping event used by the endpoint row. -/
theorem exists_ambientProductIntermediateCampanatoContractOnParent
    (d : ℕ) [NeZero d] (step : ℕ) :
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
          ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ c →
          64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) →
          ∀ L parent : ℕ, ∀ z : Vec d,
            ∃ badTheta : Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
              MeasurableSet badTheta ∧
              M.P.toMeasure badTheta ≤ ENNReal.ofReal
                (Ctail * Real.exp
                  (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
              ∀ omega ∉ badTheta, ∀ n ell top : ℕ,
              n ≤ ell → ell < top → top ≤ parent → j0 ≤ parent - n →
              ∀ q : Vec d, OnTriadicGrid n q → q ∈ cube d parent →
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
                  (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
                  (translatedCube d (top : ℤ) (z + q)) u →
              normalizedL2On (translatedCube d (ell : ℤ) (z + q))
                  (fun x ↦ u.toFun x - averageOn
                    (translatedCube d (ell : ℤ) (z + q)) u.toFun) ≤
                (Cabs * (3 : ℝ) ^
                    ((((parent : ℝ) - (n : ℝ)) -
                      ((top : ℝ) - (ell : ℝ))) / 16)) *
                  (3 : ℝ) ^
                    (-(1 / 2 : ℝ) * ((top : ℝ) - (ell : ℝ))) *
                  normalizedL2On (translatedCube d (top : ℤ) (z + q))
                    (fun x ↦ u.toFun x - averageOn
                      (translatedCube d (top : ℤ) (z + q)) u.toFun) := by
  obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, hdecay⟩ :=
    exists_productStoppedIntermediateCampanatoDecayOnParent d
  refine ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, ?_⟩
  intro C₁ C₂ Cabs hC₁ hC₂ hCabs k hk habs
  obtain ⟨c, Ctail, hc, hCtail, hcOne, j0, hj0, htail⟩ :=
    exists_translatedThetaLadderGammaOneCalibration d step hC₁ hC₂
  refine ⟨c, Ctail, hc, hCtail, hcOne, j0, hj0, ?_⟩
  intro M hdelta hsmall L parent z
  let good := translatedThetaLadderStoppingEvent
    M L C₁ C₂ step parent j0 z
  refine ⟨goodᶜ,
    (measurableSet_translatedThetaLadderStoppingEvent
      M L C₁ C₂ step parent j0 z).compl, htail M hdelta L parent z, ?_⟩
  intro omega homega n ell top hnell helltop htop hdepth q hqgrid hqmem
  have homegaGood : omega ∈ good := by
    simpa only [Set.mem_compl_iff, not_not] using homega
  dsimp only
  intro heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff theta
    htheta hnear hcontraction hcontractionPow hcontract u hu
  exact hdecay C₁ Cabs (zero_lt_one.trans_le hC₁) hCabs k hk habs M hsmall
    L n ell top parent hnell helltop htop C₂ step j0 hdepth z q hqgrid hqmem
    omega homegaGood heta b epsilon hb hepsilon hepsilonHalf herrorOne
    hepsCoeff theta htheta hnear hcontraction hcontractionPow hcontract u hu

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
