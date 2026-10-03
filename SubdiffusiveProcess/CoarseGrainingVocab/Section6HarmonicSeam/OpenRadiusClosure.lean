module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryLocalizedHalfSteps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.BudgetedRadiusIteration

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicSeam

open SubdiffusiveProcess.CoarseGrainingVocab MeasureTheory Homogenization

noncomputable section

/-- Halving a positive gap multiplies its negative power by `2 ^ beta`. -/
theorem rpow_half_gap (beta : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.rpow (t / 2) (-beta) = Real.rpow 2 beta * Real.rpow t (-beta) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hinv : Real.rpow ((2 : ℝ)⁻¹) (-beta) = (Real.rpow (2 : ℝ) (-beta))⁻¹ :=
    Real.inv_rpow h2 (-beta)
  have hneg : Real.rpow (2 : ℝ) (-beta) = (Real.rpow (2 : ℝ) beta)⁻¹ :=
    Real.rpow_neg h2 beta
  have hhalf : Real.rpow ((2 : ℝ)⁻¹) (-beta) = Real.rpow 2 beta := by
    rw [hinv, hneg, inv_inv]
  have hsplit : Real.rpow (t * (2 : ℝ)⁻¹) (-beta) =
      Real.rpow t (-beta) * Real.rpow ((2 : ℝ)⁻¹) (-beta) :=
    Real.mul_rpow ht.le (by norm_num)
  calc
    Real.rpow (t / 2) (-beta) = Real.rpow (t * (2 : ℝ)⁻¹) (-beta) := by
      rw [div_eq_mul_inv]
    _ = Real.rpow t (-beta) * Real.rpow ((2 : ℝ)⁻¹) (-beta) := hsplit
    _ = Real.rpow 2 beta * Real.rpow t (-beta) := by rw [hhalf]; ring

/-- **Open-to-closed radius closure.**

A contraction row available only for `R < 1`, together with monotonicity of the
profile, gives the closed-range `BudgetedRadiusRecurrence` with the same
contraction and an inverse-gap price inflated by `2 ^ beta`. -/
theorem budgetedRadiusRecurrence_of_openHalfSteps
    {F : ℝ → ℝ} {theta A B beta : ℝ}
    (htheta : 0 ≤ theta)
    (hmono : ∀ r₁ r₂ : ℝ, (1 / 3 : ℝ) ≤ r₁ → r₁ ≤ r₂ → r₂ ≤ 1 → F r₁ ≤ F r₂)
    (hstep : ∀ r₁ r₂ : ℝ, (1 / 3 : ℝ) ≤ r₁ → r₁ < r₂ → r₂ < 1 →
      F r₁ ≤ theta * F r₂ + A * Real.rpow (r₂ - r₁) (-beta) + B) :
    Section6HarmonicLocalRow.BudgetedRadiusRecurrence F theta
      (Real.rpow 2 beta * A) B beta := by
  intro rho R hrho hgap hR
  set m : ℝ := (rho + R) / 2 with hmdef
  have hrhom : rho < m := by dsimp [m]; linarith
  have hmR : m < R := by dsimp [m]; linarith
  have hm1 : m < 1 := lt_of_lt_of_le hmR hR
  have hrhom' : (1 / 3 : ℝ) ≤ rho := hrho
  have hgapm : m - rho = (R - rho) / 2 := by dsimp [m]; ring
  have hgap0 : 0 < R - rho := sub_pos.mpr hgap
  have hstep' := hstep rho m hrhom' hrhom hm1
  have hprice : Real.rpow (m - rho) (-beta) =
      Real.rpow 2 beta * Real.rpow (R - rho) (-beta) := by
    rw [hgapm]
    exact rpow_half_gap beta hgap0
  have hmid : F m ≤ F R :=
    hmono m R (le_trans hrho hrhom.le) hmR.le hR
  have hcontract : theta * F m ≤ theta * F R :=
    mul_le_mul_of_nonneg_left hmid htheta
  calc
    F rho ≤ theta * F m + A * Real.rpow (m - rho) (-beta) + B := hstep'
    _ = theta * F m + (Real.rpow 2 beta * A) * Real.rpow (R - rho) (-beta) + B := by
      rw [hprice]; ring
    _ ≤ theta * F R + (Real.rpow 2 beta * A) * Real.rpow (R - rho) (-beta) + B := by
      linarith only [hcontract]

variable {d : ℕ}

/-- The cross-scale profile of a nonnegative integrable energy is monotone on
the closed radius range, in the exact shape consumed by
`budgetedRadiusRecurrence_of_openHalfSteps`. -/
theorem boundaryCrossScaleEnergyProfile_monotone_on
    {Q R : TriadicCube d} {center : Vec d} {energy : Vec d → ℝ}
    (henergyNonneg : ∀ x ∈ openCubeSet Q, 0 ≤ energy x)
    (henergy : IntegrableOn energy (openCubeSet Q) volume) :
    ∀ r₁ r₂ : ℝ, (1 / 3 : ℝ) ≤ r₁ → r₁ ≤ r₂ → r₂ ≤ 1 →
      Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile
          Q R center r₁ energy ≤
        Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile
          Q R center r₂ energy := by
  intro r₁ r₂ _ hr _
  exact Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile_mono
    hr henergyNonneg henergy

/-- **The boundary radius recurrence carried by the landed half-step.**

The abstract closure specialized to the cross-scale energy profile: an
arbitrary-radius half-step on the open range yields the closed-range
`BudgetedRadiusRecurrence` at contraction `1/2`, with the inverse-gap price
inflated by `2 ^ beta`. -/
theorem budgetedRadiusRecurrence_profile_of_openHalfSteps
    {Q R : TriadicCube d} {center : Vec d} {energy : Vec d → ℝ}
    {A B beta : ℝ}
    (henergyNonneg : ∀ x ∈ openCubeSet Q, 0 ≤ energy x)
    (henergy : IntegrableOn energy (openCubeSet Q) volume)
    (hstep : ∀ r₁ r₂ : ℝ, (1 / 3 : ℝ) ≤ r₁ → r₁ < r₂ → r₂ < 1 →
      Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile
          Q R center r₁ energy ≤
        (1 / 2 : ℝ) *
            Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile
              Q R center r₂ energy +
          A * Real.rpow (r₂ - r₁) (-beta) + B) :
    Section6HarmonicLocalRow.BudgetedRadiusRecurrence
      (fun rho ↦ Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile
        Q R center rho energy)
      (1 / 2 : ℝ) (Real.rpow 2 beta * A) B beta :=
  budgetedRadiusRecurrence_of_openHalfSteps (by norm_num)
    (boundaryCrossScaleEnergyProfile_monotone_on henergyNonneg henergy) hstep

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicSeam
