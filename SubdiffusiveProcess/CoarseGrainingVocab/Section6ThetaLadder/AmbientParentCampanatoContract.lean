import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.AmbientCampanatoContract

/-!
# Theta ladder: parent-uniform ambient Campanato contract

The stopping event is selected on a parent cube of scale `parent`, while the
actual recurrence may run on a smaller comparison cube of scale `top`.  This
distinction is needed for target cubes away from the parent centre.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

/-- The stopped centered Campanato estimate with the stopping parent kept
separate from the comparison cube on which the weak equation is posed. -/
theorem exists_productStoppedCampanatoDecayOnParent (d : ℕ) [NeZero d] :
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
      ∀ L n top parent : ℕ, n < top → top ≤ parent →
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
          (Kbase * eta + Cgain * Real.sqrt epsilon) ≤ contraction ^ k →
      ∀ u : H1Function (translatedCube d (top : ℤ) (z + q)),
      IsWeaklyHarmonicOn
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
          (translatedCube d (top : ℤ) (z + q)) u →
      normalizedL2On (translatedCube d (n : ℤ) (z + q))
          (fun x ↦ u.toFun x -
            averageOn (translatedCube d (n : ℤ) (z + q)) u.toFun) ≤
        (Cabs * (3 : ℝ) ^ (((parent : ℝ) - (top : ℝ)) / 16)) * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ))) *
          normalizedL2On (translatedCube d (top : ℤ) (z + q))
            (fun x ↦ u.toFun x -
              averageOn (translatedCube d (top : ℤ) (z + q)) u.toFun) := by
  obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, hstop⟩ :=
    exists_productStoppedIteration d
  refine ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, ?_⟩
  intro C₁ Cabs hC₁ hCabs k hk habs M hsmall L n top parent hntop htop
    C₂ step j0 hj0 z q hqgrid hqmem omega homega
  dsimp only
  intro heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff theta
    htheta hnear hcontraction hcontractionPow hcontract u hu
  have hcore := hstop M hsmall L parent n top k hntop htop hk
    C₁ C₂ step j0 hj0 z q hqgrid hqmem omega homega heta b epsilon hb
    hepsilon hepsilonHalf herrorOne theta htheta hnear
    ((3 : ℝ) ^ (-(1 / 4 : ℝ))) hcontraction hcontractionPow hcontract u hu
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
        ((parent : ℝ) - (n : ℝ)) := by
    dsimp only [bad]
    simpa only [Nat.cast_ofNat, add_assoc] using hcore.1
  have hsum : (∑ i ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow i) =
      (((top : ℝ) - (n : ℝ)) + 1) *
        productIterationSlopeCoefficient d M.shellPrefix.dimension k error := by
    exact sum_const_Icc_intCast (Nat.le_of_lt hntop) _
  have hgapParent : 0 ≤ (parent : ℝ) - (n : ℝ) := by
    have : (n : ℝ) ≤ (parent : ℝ) := by
      exact_mod_cast (Nat.le_trans (Nat.le_of_lt hntop) htop)
    linarith
  have hAupper : Real.exp A ≤
      Cabs * (3 : ℝ) ^
        ((1 - thetaLadderExponent) * ((parent : ℝ) - (n : ℝ)) / 4) := by
    have hraw := habs thetaLadderExponent
      ⟨thetaLadderExponent_mem.1, thetaLadderExponent_mem.2.le⟩
      ((parent : ℝ) - (n : ℝ)) hgapParent
    have hCiter0 : 0 ≤ Citer := hCiter.le
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    have hgapTop : 0 ≤ (top : ℝ) - (n : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast (Nat.le_of_lt hntop))
    have hgapLe : (top : ℝ) - (n : ℝ) ≤
        (parent : ℝ) - (n : ℝ) := by exact sub_le_sub_right (by exact_mod_cast htop) _
    have heps0 : 0 ≤ C₁⁻¹ * (1 - thetaLadderExponent) := by
      exact mul_nonneg (inv_nonneg.mpr hC₁.le)
        (sub_nonneg.mpr thetaLadderExponent_mem.2.le)
    have hcardLe : (bad.card : ℝ) + 1 ≤ (k : ℝ) + 2 +
        C₁⁻¹ * (1 - thetaLadderExponent) *
          ((parent : ℝ) - (n : ℝ)) := by linarith [hcard]
    have hfirst := mul_le_mul_of_nonneg_left hcardLe
      (mul_nonneg hCiter0 (by positivity : (0 : ℝ) ≤ k + 1))
    have hsecond0 : productIterationSlopeCoefficient d
        M.shellPrefix.dimension k error ≤
          C₁⁻¹ * (1 - thetaLadderExponent) := hepsCoeff
    have hsecond := mul_le_mul_of_nonneg_left hsecond0
      (mul_nonneg hCiter0 (by positivity :
        (0 : ℝ) ≤ (top : ℝ) - (n : ℝ) + 1))
    have hbudget : A ≤
        Citer * (k + 1) * (k + 2) +
          (Citer * (k + 2)) *
            (C₁⁻¹ * (1 - thetaLadderExponent)) *
              (((parent : ℝ) - (n : ℝ)) + 1) := by
      dsimp only [A]
      rw [hsum]
      have hsumLe := add_le_add hfirst hsecond
      nlinarith only [hsumLe,
        mul_nonneg hCiter0 (mul_nonneg (by positivity : (0 : ℝ) ≤ k + 1) heps0),
        mul_nonneg hCiter0 (mul_nonneg (by positivity : (0 : ℝ) ≤ k + 2) heps0),
        hgapTop, hgapLe]
    exact (Real.exp_le_exp.mpr hbudget).trans hraw
  have hExp : Real.exp A ≤
      Cabs * (3 : ℝ) ^ (((parent : ℝ) - (n : ℝ)) / 16) := by
    have hquarter :
        (1 - thetaLadderExponent) * ((parent : ℝ) - (n : ℝ)) / 4 =
          ((parent : ℝ) - (n : ℝ)) / 16 := by
      rw [thetaLadderExponent]
      ring
    rwa [hquarter] at hAupper
  have hscaled : (3 : ℝ) ^ (-(n : ℤ)) *
        normalizedL2On (translatedCube d (n : ℤ) (z + q))
          (fun x ↦ u.toFun x -
            averageOn (translatedCube d (n : ℤ) (z + q)) u.toFun) ≤
      Real.exp A * ((3 : ℝ) ^ (-(top : ℤ)) *
        normalizedL2On (translatedCube d (top : ℤ) (z + q))
          (fun x ↦ u.toFun x -
            averageOn (translatedCube d (top : ℤ) (z + q)) u.toFun)) := by
    simpa only [A, bad, epsRow, error] using hcore.2
  have hExpTop : Real.exp A ≤
      (Cabs * (3 : ℝ) ^ (((parent : ℝ) - (top : ℝ)) / 16)) *
        (3 : ℝ) ^ (((top : ℝ) - (n : ℝ)) / 16) := by
    have hsplit : ((parent : ℝ) - (n : ℝ)) / 16 =
        ((parent : ℝ) - (top : ℝ)) / 16 +
          ((top : ℝ) - (n : ℝ)) / 16 := by ring
    calc
      Real.exp A ≤ Cabs * (3 : ℝ) ^ (((parent : ℝ) - (n : ℝ)) / 16) := hExp
      _ = (Cabs * (3 : ℝ) ^ (((parent : ℝ) - (top : ℝ)) / 16)) *
          (3 : ℝ) ^ (((top : ℝ) - (n : ℝ)) / 16) := by
        rw [hsplit, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        ring
  exact normalizedL2_decay_of_scaled_product (Nat.le_of_lt hntop)
    (Section6Iteration.normalizedL2On_nonneg _ _)
    (mul_nonneg hCabs (Real.rpow_nonneg (by norm_num) _)) hscaled hExpTop

/-- Ambient event package for the parent-uniform stopped estimate.  Unlike
`exists_ambientProductCampanatoContract`, the stopping parent is not forced
to equal the local comparison top. -/
theorem exists_ambientProductCampanatoContractOnParent
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
              ∀ omega ∉ badTheta, ∀ n top : ℕ,
              n < top → top ≤ parent → j0 ≤ parent - n →
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
              normalizedL2On (translatedCube d (n : ℤ) (z + q))
                  (fun x ↦ u.toFun x - averageOn
                    (translatedCube d (n : ℤ) (z + q)) u.toFun) ≤
                (Cabs * (3 : ℝ) ^
                    (((parent : ℝ) - (top : ℝ)) / 16)) *
                  (3 : ℝ) ^
                    (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ))) *
                  normalizedL2On (translatedCube d (top : ℤ) (z + q))
                    (fun x ↦ u.toFun x - averageOn
                      (translatedCube d (top : ℤ) (z + q)) u.toFun) := by
  obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, hdecay⟩ :=
    exists_productStoppedCampanatoDecayOnParent d
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
      M L C₁ C₂ step parent j0 z).compl, ?_, ?_⟩
  · exact htail M hdelta L parent z
  · intro omega homega n top hntop htop hdepth q hqgrid hqmem
    have homegaGood : omega ∈ good := by
      simpa only [Set.mem_compl_iff, not_not] using homega
    dsimp only
    intro heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff theta
      htheta hnear hcontraction hcontractionPow hcontract u hu
    exact hdecay C₁ Cabs (zero_lt_one.trans_le hC₁) hCabs k hk habs M hsmall
      L n top parent hntop htop C₂ step j0 hdepth z q hqgrid hqmem omega
      homegaGood heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff
      theta htheta hnear hcontraction hcontractionPow hcontract u hu

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
