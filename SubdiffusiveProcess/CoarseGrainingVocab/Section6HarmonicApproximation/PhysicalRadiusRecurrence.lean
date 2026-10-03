module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.AdjustableRadiusReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProfileReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryRegularity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalPDEEnergyAssembly

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The four squared manuscript budgets on the scale-`n` parent window. -/
noncomputable def harmonicPhysicalFourBudgets {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m n : ℕ)
    (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (s : ℝ) (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d) : ℝ :=
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
      normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
    (if BoundaryTouches U (cube d (m : ℤ)) then
      sigma * vecNormSq (averageVecOn U h.grad) else 0) +
    Real.rpow s (-12 : ℝ) * sigma⁻¹ *
      Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
      (fractionalSeminormOn U s g).toReal ^ 2 +
    (if BoundaryTouches U (cube d (m : ℤ)) then
      sigma * Real.rpow s (-4 : ℝ) *
        Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
        (fractionalSeminormOn U s h.grad).toReal ^ 2 else 0)



def HarmonicPhysicalRadiusRecurrence (d : ℕ)
    (theta CA CB beta : ℝ) : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sOrder : FractionalOrder),
    sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
  ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
  ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
    x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
    q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
    ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
    omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
  ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
      (g : Vec d → Vec d),
    IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (originCube d (m : ℤ)) u h g →
    Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
    MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
    let k : ℤ := (n : ℤ) - 2
    let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
    let Q := originCube d k
    let budgets := harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g
    Section6HarmonicLocalRow.BudgetedRadiusRecurrence
      (fun rho ↦ boundaryCrossScaleEnergyProfile Q Q (q - c) rho (fun y ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L (translatePotentialSample c omega) y *
          vecNormSq (u.grad (y + c))))
      theta (CA * budgets) (CB * budgets) beta

theorem harmonicPhysicalFourBudgets_nonneg
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m n : ℕ)
    (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {s : ℝ} (hs : 0 < s)
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d) :
    0 ≤ harmonicPhysicalFourBudgets M L m n z x omega s u h g := by
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  unfold harmonicPhysicalFourBudgets
  dsimp only
  by_cases ht : BoundaryTouches U (cube d (m : ℤ))
  ·
    have h1 : 0 ≤ sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 := by
      positivity
    have h2 : 0 ≤ sigma * vecNormSq (averageVecOn U h.grad) :=
      mul_nonneg hsigma.le (vecNormSq_nonneg _)
    have h3 : 0 ≤ Real.rpow s (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
        (fractionalSeminormOn U s g).toReal ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hs.le _) (inv_nonneg.mpr hsigma.le))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    have h4 : 0 ≤ sigma * Real.rpow s (-4 : ℝ) *
        Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
        (fractionalSeminormOn U s h.grad).toReal ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hsigma.le (Real.rpow_nonneg hs.le _))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    simpa only [U, sigma, ht, if_true] using
      add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4
  ·
    have h1 : 0 ≤ sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 := by
      positivity
    have h3 : 0 ≤ Real.rpow s (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
        (fractionalSeminormOn U s g).toReal ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hs.le _) (inv_nonneg.mpr hsigma.le))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    simpa only [U, sigma, ht, if_false, add_zero] using add_nonneg h1 h3

/-- A projected-cell physical recurrence supplies the complete first-order
energy display on the translated harmonic-replacement window.  No local PDE,
cover, or radius premise survives in the conclusion. -/
theorem exists_translatedCubeEnergyReadout_of_physicalRecurrence
    (d : ℕ) [NeZero d]
    {theta tau CA CB beta : ℝ}
    (hbeta : 0 ≤ beta) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (htau0 : 0 < tau) (htau1 : tau < 1)
    (htheta0 : 0 ≤ theta) (hcontract : theta < Real.rpow tau beta)
    (hrec : HarmonicPhysicalRadiusRecurrence d theta CA CB beta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
        let D := translatedCube d ((n : ℤ) - 2) y
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        sigma ^ (-1 / 2 : ℝ) * vectorNormalizedL2On D (fun p ↦
            Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p) ≤
          C * ((3 : ℝ) ^ (-(n : ℤ)) *
                normalizedL2On U
                  (fun q ↦ u.toFun q - averageOn U u.toFun) +
              (if BoundaryTouches U (cube d (m : ℤ)) then
                Real.sqrt (vecNormSq (averageVecOn U h.grad)) else 0) +
              sigma⁻¹ * (Real.rpow sOrder.1 (-6 : ℝ) *
                Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal) +
              (if BoundaryTouches U (cube d (m : ℤ)) then
                Real.rpow sOrder.1 (-2 : ℝ) *
                  Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
                  (fractionalSeminormOn U sOrder.1 h.grad).toReal else 0)) := by
  obtain ⟨Cint, hCint, hcover⟩ :=
    exists_translatedCube_energy_le_of_boundaryCellManuscriptBound d
  let Krad : ℝ :=
    (1 - theta / Real.rpow tau beta)⁻¹ *
        (CA * Real.rpow ((1 - tau) * (2 / 3 : ℝ)) (-beta)) +
      (1 - theta)⁻¹ * CB
  let Cboundary : ℝ := 1 + ((81 : ℝ) ^ d * (18 : ℝ) ^ d) * Krad
  let C : ℝ := Real.sqrt (max Cint Cboundary)
  have htBetaPos : 0 < Real.rpow tau beta := Real.rpow_pos_of_pos htau0 beta
  have htheta1 : theta < 1 := hcontract.trans_le
    (Real.rpow_le_one htau0.le htau1.le hbeta)
  have hKrad0 : 0 ≤ Krad := by
    dsimp [Krad]
    have hden1 : 0 < 1 - theta / Real.rpow tau beta := by
      exact sub_pos.mpr ((div_lt_one htBetaPos).mpr hcontract)
    have hden2 : 0 < 1 - theta := sub_pos.mpr htheta1
    have hbase : 0 ≤ (1 - tau) * (2 / 3 : ℝ) :=
      mul_nonneg (sub_nonneg.mpr htau1.le) (by norm_num)
    exact add_nonneg
      (mul_nonneg (inv_nonneg.mpr hden1.le)
        (mul_nonneg hCA (Real.rpow_nonneg hbase _)))
      (mul_nonneg (inv_nonneg.mpr hden2.le) hCB)
  have hCboundary : 0 < Cboundary := by
    dsimp [Cboundary]
    positivity
  have hCpos : 0 < C := by
    dsimp [C]
    exact Real.sqrt_pos.2 (lt_of_lt_of_le hCint (le_max_left _ _))
  refine ⟨C, hCpos, ?_⟩
  intro M sOrder hs L m n hmL hnm z x y omega hz hx hD hgood u h g
    hdir hg hh
  dsimp only
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let budgets := harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g
  have hbudgets : 0 ≤ budgets :=
    harmonicPhysicalFourBudgets_nonneg M L m n z x omega sOrder.2.1 u h g
  have hhFull : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad := by
    apply memCubeEuclideanFullWsp_grad_of_memFractionalOn
    simpa [cube] using hh
  have hboundary : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Cboundary * budgets := by
    intro q hq hqBoundary
    let k : ℤ := (n : ℤ) - 2
    let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
    let Q := originCube d k
    obtain ⟨g0, u0, h0, v, hg0, hu0val, hgLocal, hu0grad, heq, hv,
        hh0val, hh0grad, hhLocal, htrace, hgReg, hhReg⟩ :=
      exists_projectedBoundaryDatum_regular M L omega m k q sOrder u h g
        hdir hg hhFull (by dsimp [k]; omega)
    let f : ℝ → ℝ := fun rho ↦
      boundaryCrossScaleEnergyProfile Q Q (q - c) rho (fun p ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L (translatePotentialSample c omega) p *
          vecNormSq (u0.grad p))
    have hrow : Section6HarmonicLocalRow.BudgetedRadiusRecurrence f theta
        (CA * budgets) (CB * budgets) beta := by
      have hr := hrec M sOrder hs L m n hmL hnm z x q omega hx hq
        hqBoundary hgood u h g hdir hg hh
      dsimp only at hr
      simpa only [f, Q, c, k, budgets, hu0grad] using hr
    have henergy0 : ∀ p ∈ openCubeSet Q,
        0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
            (translatePotentialSample c omega) p * vecNormSq (u0.grad p) := by
      intro p _
      exact mul_nonneg
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L
          (translatePotentialSample c omega) p).le (vecNormSq_nonneg _)
    have henergyInt : IntegrableOn (fun p ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L (translatePotentialSample c omega) p *
          vecNormSq (u0.grad p)) (openCubeSet Q) :=
      integrableOn_aCutoff_energy M L (translatePotentialSample c omega) Q u0
    have hbdd : CoarseCaccioppoliRadiusBoundedAbove f := by
      simpa only [f] using
        boundaryCrossScaleEnergyProfile_boundedAbove henergy0 henergyInt
    have hprofile : f (1 / 3 : ℝ) ≤ Krad * budgets := by
      have hi := Section6HarmonicLocalRow.budgetedRadius_iteration
        (F := f) (theta := theta) (A := CA * budgets) (B := CB * budgets)
        (beta := beta) (tau := tau) hbeta (mul_nonneg hCA hbudgets)
        (mul_nonneg hCB hbudgets) htau0 htau1 htheta0 hcontract hbdd hrow
      dsimp only [Krad]
      calc
        f (1 / 3 : ℝ) ≤
            (1 - theta / Real.rpow tau beta)⁻¹ *
                (CA * budgets *
                  Real.rpow ((1 - tau) * (2 / 3 : ℝ)) (-beta)) +
              (1 - theta)⁻¹ * (CB * budgets) := hi
        _ = ((1 - theta / Real.rpow tau beta)⁻¹ *
              (CA * Real.rpow ((1 - tau) * (2 / 3 : ℝ)) (-beta)) +
            (1 - theta)⁻¹ * CB) * budgets := by ring
    have hqDomain : q ∈ cube d (m : ℤ) :=
      Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
        ((n : ℤ) - 1) x hq
    have hread := normalizedCutoffEnergy_truncatedCube_le_profile
      M L omega hqDomain (by dsimp [k]; omega) u u0 hu0grad
    have hprofile' : boundaryCrossScaleEnergyProfile Q Q (q - c) (1 / 3 : ℝ)
          (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
            (translatePotentialSample c omega) p * vecNormSq (u0.grad p)) ≤
        Krad * budgets := by
      simpa only [f] using hprofile
    have hcell : normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
        (((81 : ℝ) ^ d * (18 : ℝ) ^ d) * Krad) * budgets := by
      calc
        _ ≤ ((81 : ℝ) ^ d * (18 : ℝ) ^ d) *
            boundaryCrossScaleEnergyProfile Q Q (q - c) (1 / 3 : ℝ)
              (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
                (translatePotentialSample c omega) p * vecNormSq (u0.grad p)) := by
          simpa only [k, Q, c, show k - 2 = (n : ℤ) - 4 by omega] using hread
        _ ≤ ((81 : ℝ) ^ d * (18 : ℝ) ^ d) * (Krad * budgets) :=
          mul_le_mul_of_nonneg_left hprofile' (by positivity)
        _ = (((81 : ℝ) ^ d * (18 : ℝ) ^ d) * Krad) * budgets := by ring
    exact hcell.trans (by
      apply mul_le_mul_of_nonneg_right _ hbudgets
      dsimp [Cboundary]
      linarith)
  have hscalar := hcover M sOrder hs L m n hmL hnm z x y omega hz hx hD hgood
    u h g hdir hg hh Cboundary hCboundary.le
      (by simpa only [budgets, harmonicPhysicalFourBudgets, U, sigma] using hboundary)
  change volumeAverage (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
    _ at hscalar
  let K : ℝ := max Cint Cboundary
  have hK0 : 0 ≤ K := le_trans hCint.le (le_max_left _ _)
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  let O := normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun)
  let G := if BoundaryTouches U (cube d (m : ℤ)) then
    Real.sqrt (vecNormSq (averageVecOn U h.grad)) else 0
  let F := (fractionalSeminormOn U sOrder.1 g).toReal
  let H := if BoundaryTouches U (cube d (m : ℤ)) then
    (fractionalSeminormOn U sOrder.1 h.grad).toReal else 0
  have hO : 0 ≤ O := by
    dsimp [O]
    exact Section6Iteration.normalizedL2On_nonneg _ _
  have hG : 0 ≤ G := by dsimp [G]; split <;> positivity
  have hF : 0 ≤ F := by exact ENNReal.toReal_nonneg
  have hH : 0 ≤ H := by dsimp [H]; split <;> positivity
  have henergy : volumeAverage (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      K * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * O ^ 2 + sigma * G ^ 2 +
        Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
          Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) * F ^ 2 +
        sigma * Real.rpow sOrder.1 (-4 : ℝ) *
          Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) * H ^ 2) := by
    by_cases ht : BoundaryTouches U (cube d (m : ℤ))
    · simpa [K, harmonicPhysicalFourBudgets, U, sigma, O, G, F, H, ht,
        Real.sq_sqrt (vecNormSq_nonneg _)] using hscalar
    · simpa [K, harmonicPhysicalFourBudgets, U, sigma, O, G, F, H, ht]
        using hscalar
  have hout := invSqrt_mul_vectorNormalizedL2On_le_of_manuscriptFourBudgets
    (translatedCube d ((n : ℤ) - 2) y)
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) u.grad
    (K := K) (sigma := sigma) (s := sOrder.1)
    (O := O) (G := G) (F := F) (H := H)
    (nr := (n : ℝ)) (n := (n : ℤ))
    (fun p ↦ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega p).le)
    hK0 hsigma sOrder.2.1 hO hG hF hH henergy
  by_cases ht : BoundaryTouches U (cube d (m : ℤ))
  · simpa [C, K, U, sigma, O, G, F, H, ht] using hout
  · simpa [C, K, U, sigma, O, G, F, H, ht] using hout

/-- The fixed numerical specialization used by the v5 provider.  This is the
literal first-order energy display, with the good-event indicator restored;
outside the event its left side is zero. -/
theorem exists_indicator_translatedCubeEnergyReadout_of_physicalQuarterRecurrence
    (d : ℕ) [NeZero d] {CA CB : ℝ}
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hrec : HarmonicPhysicalRadiusRecurrence d (1 / 4 : ℝ) CA CB 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
        let D := translatedCube d ((n : ℤ) - 2) y
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        indicatorValue (goodEvent M none (n + 2) z 1 (sOrder.1 / 8))
            (fun _ ↦ sigma ^ (-1 / 2 : ℝ) * vectorNormalizedL2On D (fun p ↦
              Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p))
            omega ≤
          C * ((3 : ℝ) ^ (-(n : ℤ)) *
                normalizedL2On U
                  (fun q ↦ u.toFun q - averageOn U u.toFun) +
              (if BoundaryTouches U (cube d (m : ℤ)) then
                Real.sqrt (vecNormSq (averageVecOn U h.grad)) else 0) +
              sigma⁻¹ * (Real.rpow sOrder.1 (-6 : ℝ) *
                Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal) +
              (if BoundaryTouches U (cube d (m : ℤ)) then
                Real.rpow sOrder.1 (-2 : ℝ) *
                  Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
                  (fractionalSeminormOn U sOrder.1 h.grad).toReal else 0)) := by
  obtain ⟨C, hC, henergy⟩ :=
    exists_translatedCubeEnergyReadout_of_physicalRecurrence d
      (theta := (1 / 4 : ℝ)) (tau := (3 / 4 : ℝ))
      (CA := CA) (CB := CB) (beta := 2)
      (by norm_num) hCA hCB (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Real.rpow_two]) hrec
  refine ⟨C, hC, ?_⟩
  intro M sOrder hs L m n hmL hnm z x y omega hz hx hD u h g hdir hg hh
  dsimp only
  by_cases hgood : omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8)
  · rw [Section6ExcessDecay.indicatorValue_of_mem hgood]
    exact henergy M sOrder hs L m n hmL hnm z x y omega hz hx hD hgood
      u h g hdir hg hh
  · rw [Section6ExcessDecay.indicatorValue_of_notMem hgood]
    have hright : 0 ≤
        C * ((3 : ℝ) ^ (-(n : ℤ)) *
              normalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
                (fun q ↦ u.toFun q - averageOn
                  (truncatedCube d (m : ℤ) (n : ℤ) x) u.toFun) +
            (if BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
                (cube d (m : ℤ)) then
              Real.sqrt (vecNormSq (averageVecOn
                (truncatedCube d (m : ℤ) (n : ℤ) x) h.grad)) else 0) +
            (tailAverage M L (n + 2) omega
              (translatedCube d ((n : ℤ) + 2) z))⁻¹ *
              (Real.rpow sOrder.1 (-6 : ℝ) *
                Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn
                  (truncatedCube d (m : ℤ) (n : ℤ) x) sOrder.1 g).toReal) +
            (if BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
                (cube d (m : ℤ)) then
              Real.rpow sOrder.1 (-2 : ℝ) *
                Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn
                  (truncatedCube d (m : ℤ) (n : ℤ) x)
                    sOrder.1 h.grad).toReal else 0)) := by
      have hsigma : 0 < tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z) := by
        rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
        rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
        exact tailCoefficientCubeAverage_pos M L (n + 2)
          (translatePotentialSample z omega)
      apply mul_nonneg hC.le
      by_cases ht : BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ))
      · simp only [ht, if_true]
        have hO := Section6Iteration.normalizedL2On_nonneg
          (truncatedCube d (m : ℤ) (n : ℤ) x)
          (fun q ↦ u.toFun q - averageOn
            (truncatedCube d (m : ℤ) (n : ℤ) x) u.toFun)
        have hFg : 0 ≤ (fractionalSeminormOn
            (truncatedCube d (m : ℤ) (n : ℤ) x) sOrder.1 g).toReal :=
          ENNReal.toReal_nonneg
        have hFh : 0 ≤ (fractionalSeminormOn
            (truncatedCube d (m : ℤ) (n : ℤ) x) sOrder.1 h.grad).toReal :=
          ENNReal.toReal_nonneg
        have ht1 : 0 ≤ (3 : ℝ) ^ (-(n : ℤ)) *
            normalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
              (fun q ↦ u.toFun q - averageOn
                (truncatedCube d (m : ℤ) (n : ℤ) x) u.toFun) := by
          exact mul_nonneg (zpow_nonneg (by norm_num) _) hO
        have ht2 : 0 ≤ Real.sqrt (vecNormSq (averageVecOn
            (truncatedCube d (m : ℤ) (n : ℤ) x) h.grad)) := Real.sqrt_nonneg _
        have ht3 : 0 ≤ (tailAverage M L (n + 2) omega
              (translatedCube d ((n : ℤ) + 2) z))⁻¹ *
            (Real.rpow sOrder.1 (-6 : ℝ) *
              Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn
                (truncatedCube d (m : ℤ) (n : ℤ) x) sOrder.1 g).toReal) := by
          exact mul_nonneg (inv_nonneg.mpr hsigma.le)
            (mul_nonneg
              (mul_nonneg (Real.rpow_nonneg sOrder.2.1.le _)
                (Real.rpow_nonneg (by norm_num) _)) hFg)
        have ht4 : 0 ≤ Real.rpow sOrder.1 (-2 : ℝ) *
            Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn
                (truncatedCube d (m : ℤ) (n : ℤ) x) sOrder.1 h.grad).toReal := by
          exact mul_nonneg
            (mul_nonneg (Real.rpow_nonneg sOrder.2.1.le _)
              (Real.rpow_nonneg (by norm_num) _)) hFh
        linarith
      · simp only [ht, if_false, add_zero]
        have hO := Section6Iteration.normalizedL2On_nonneg
          (truncatedCube d (m : ℤ) (n : ℤ) x)
          (fun q ↦ u.toFun q - averageOn
            (truncatedCube d (m : ℤ) (n : ℤ) x) u.toFun)
        have hFg : 0 ≤ (fractionalSeminormOn
            (truncatedCube d (m : ℤ) (n : ℤ) x) sOrder.1 g).toReal :=
          ENNReal.toReal_nonneg
        have ht1 : 0 ≤ (3 : ℝ) ^ (-(n : ℤ)) *
            normalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
              (fun q ↦ u.toFun q - averageOn
                (truncatedCube d (m : ℤ) (n : ℤ) x) u.toFun) := by
          exact mul_nonneg (zpow_nonneg (by norm_num) _) hO
        have ht3 : 0 ≤ (tailAverage M L (n + 2) omega
              (translatedCube d ((n : ℤ) + 2) z))⁻¹ *
            (Real.rpow sOrder.1 (-6 : ℝ) *
              Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn
                (truncatedCube d (m : ℤ) (n : ℤ) x) sOrder.1 g).toReal) := by
          exact mul_nonneg (inv_nonneg.mpr hsigma.le)
            (mul_nonneg
              (mul_nonneg (Real.rpow_nonneg sOrder.2.1.le _)
                (Real.rpow_nonneg (by norm_num) _)) hFg)
        linarith
    exact hright

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
