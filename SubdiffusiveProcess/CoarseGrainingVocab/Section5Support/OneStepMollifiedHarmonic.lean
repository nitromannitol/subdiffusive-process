module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMollifiedDivergence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryMollifiedPotentialCurl

@[expose] public section

/-!
# Harmonicity of the mollified one-step trace defect

The expanded divergence identity is differentiated once more and the
topology-free mollified curl identity exchanges the two column derivatives.
Summing the resulting diagonal identities produces the stationary Laplacian
equation for the trace defect.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The stationary Laplacian of a smooth scalar mollification. -/
def mollifiedLaplacianL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (kappa : Vec d → ℝ) (X : Stationary.ScalarL2 M.P.toMeasure) :
    Stationary.ScalarL2 M.P.toMeasure :=
  letI := potentialSequenceVAddInvariant M
  ∑ i : Fin d, Stationary.mollifyL2 (mu := M.P.toMeasure)
    (Stationary.kernelDeriv (Stationary.kernelDeriv kappa i) i) X

/-- Twice differentiating the weak divergence identity for one projected
column turns it into the Laplacian of its diagonal entry. -/
theorem sum_mollifyL2_secondDeriv_projectedColumn_diagonal_eq_multiplier
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (j : Fin d) (hh : 0 < h)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    letI := potentialSequenceVAddInvariant M
    (∑ i : Fin d, Stationary.mollifyL2 (mu := M.P.toMeasure)
      (Stationary.kernelDeriv (Stationary.kernelDeriv kappa i) i)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) j
        (oneStepPotentialProjection M n h (Pi.single j 1) hh))) =
      Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv (Stationary.kernelDeriv kappa j) j)
        (oneStepMultiplierAtL2 M n h 0 hh) := by
  letI := potentialSequenceVAddInvariant M
  classical
  let P := oneStepPotentialProjection M n h (Pi.single j 1) hh
  have hPpot : P ∈ Stationary.stationaryPotentialSubspace
      (mu := M.P.toMeasure) (d := d) :=
    oneStepPotentialProjection_mem_stationaryPotentialSubspace
      M n h (Pi.single j 1) hh
  have hP : Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z P) :=
    continuous_koopman_oneStepPotentialProjection M n h (Pi.single j 1) hh
  have hdiv := sum_mollifyL2_kernelDeriv_projectedColumn_eq_multiplier
    M n h j hh
      (Stationary.hasCompactSupport_kernelDeriv hcompact j)
      (Stationary.contDiff_kernelDeriv hkappa j)
  rw [← hdiv]
  apply Finset.sum_congr rfl
  intro i _
  have hcurl :=
    mollifyL2_kernelDeriv_coord_comm_of_mem_potential_of_continuous
      M P hPpot hP
      (Stationary.hasCompactSupport_kernelDeriv hcompact i)
      (Stationary.contDiff_kernelDeriv hkappa i) j i
  dsimp only [P] at hcurl ⊢
  rw [Stationary.kernelDeriv_kernelDeriv_comm hkappa j i]
  exact hcurl.symm

/-- The mollified projected trace and the multiplier have identical
stationary Laplacians. -/
theorem mollifiedLaplacianL2_oneStepPotentialTrace_eq_multiplier
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (hh : 0 < h)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    mollifiedLaplacianL2 M kappa (oneStepPotentialTraceL2 M n h hh) =
      mollifiedLaplacianL2 M kappa
        (oneStepMultiplierAtL2 M n h 0 hh) := by
  letI := potentialSequenceVAddInvariant M
  classical
  let T : Fin d → Stationary.ScalarL2 M.P.toMeasure := fun j =>
    Stationary.vectorL2Coord (mu := M.P.toMeasure) j
      (oneStepPotentialProjection M n h (Pi.single j 1) hh)
  have hT : ∀ j : Fin d, Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z (T j)) := by
    intro j
    have hP := continuous_koopman_oneStepPotentialProjection
      M n h (Pi.single j 1) hh
    have hc := (Stationary.vectorL2Coord
      (mu := M.P.toMeasure) j).continuous.comp hP
    convert hc using 1
    funext z
    exact Stationary.koopman_vectorL2Coord z j
      (oneStepPotentialProjection M n h (Pi.single j 1) hh)
  have htraceLap : mollifiedLaplacianL2 M kappa
      (oneStepPotentialTraceL2 M n h hh) =
      ∑ i : Fin d, ∑ j : Fin d,
        Stationary.mollifyL2 (mu := M.P.toMeasure)
          (Stationary.kernelDeriv (Stationary.kernelDeriv kappa i) i)
          (T j) := by
    unfold mollifiedLaplacianL2 oneStepPotentialTraceL2
    apply Finset.sum_congr rfl
    intro i _
    exact Stationary.mollifyL2_finset_sum_of_continuous Finset.univ T
      (fun j _ => hT j)
      (Stationary.continuous_kernelDeriv
        (Stationary.contDiff_kernelDeriv hkappa i) i)
      (Stationary.hasCompactSupport_kernelDeriv
        (Stationary.hasCompactSupport_kernelDeriv hcompact i) i)
  rw [htraceLap, Finset.sum_comm]
  unfold mollifiedLaplacianL2
  apply Finset.sum_congr rfl
  intro j _
  simpa only [T] using
    sum_mollifyL2_secondDeriv_projectedColumn_diagonal_eq_multiplier
      M n h j hh hcompact hkappa

/-- Every smooth mollification of the one-step trace defect is harmonic. -/
theorem mollifiedLaplacianL2_oneStepTraceDefect_eq_zero
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (hh : 0 < h)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    mollifiedLaplacianL2 M kappa
      (oneStepMultiplierAtL2 M n h 0 hh -
        oneStepPotentialTraceL2 M n h hh) = 0 := by
  letI := potentialSequenceVAddInvariant M
  classical
  have hX := continuous_koopman_oneStepMultiplierAtL2 M n h hh
  have hT := continuous_koopman_oneStepPotentialTraceL2 M n h hh
  unfold mollifiedLaplacianL2
  simp_rw [Stationary.mollifyL2_sub_of_continuous
    (Stationary.continuous_kernelDeriv
      (Stationary.contDiff_kernelDeriv hkappa _ ) _)
    (Stationary.hasCompactSupport_kernelDeriv
      (Stationary.hasCompactSupport_kernelDeriv hcompact _) _) _ _ hX hT,
    Finset.sum_sub_distrib]
  have heq := mollifiedLaplacianL2_oneStepPotentialTrace_eq_multiplier
    M n h hh hcompact hkappa
  unfold mollifiedLaplacianL2 at heq
  rw [heq, sub_self]

/-- Every smooth compactly supported mollification of the one-step trace
defect is globally translation-invariant. -/
theorem isGloballyTranslationInvariant_mollifyL2_oneStepTraceDefect
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (hh : 0 < h)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    letI := potentialSequenceVAddInvariant M
    IsGloballyTranslationInvariant M
      (Stationary.mollifyL2 (mu := M.P.toMeasure) kappa
        (oneStepMultiplierAtL2 M n h 0 hh -
          oneStepPotentialTraceL2 M n h hh)) := by
  letI := potentialSequenceVAddInvariant M
  let Y := oneStepMultiplierAtL2 M n h 0 hh -
    oneStepPotentialTraceL2 M n h hh
  let Z := Stationary.mollifyL2 (mu := M.P.toMeasure) kappa Y
  let G := mollifiedGradientL2 M kappa Y
  have hY : Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z Y) :=
    continuous_koopman_oneStepTraceDefect M n h hh
  have hlap : (∑ i : Fin d, Stationary.mollifyL2 (mu := M.P.toMeasure)
      (Stationary.kernelDeriv (Stationary.kernelDeriv kappa i) i) Y) = 0 := by
    exact mollifiedLaplacianL2_oneStepTraceDefect_eq_zero
      M n h hh hcompact hkappa
  have hGzero : G = 0 :=
    mollifiedGradientL2_eq_zero_of_sum_secondDeriv_eq_zero
      M hcompact hkappa Y hY hlap
  have hZ : Stationary.HasHorizontalGradient (mu := M.P.toMeasure) Z G :=
    hasHorizontalGradient_mollifyL2 M hcompact hkappa Y hY
  apply Stationary.isGloballyTranslationInvariant_of_hasHorizontalGradient_zero
    M Z
  rw [← hGzero]
  exact hZ

/-- The unmollified one-step trace defect is globally invariant.  This is
the approximate-identity closure of the smooth harmonic argument above. -/
theorem isGloballyTranslationInvariant_oneStepTraceDefect
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (hh : 0 < h) :
    IsGloballyTranslationInvariant M
      (oneStepMultiplierAtL2 M n h 0 hh -
        oneStepPotentialTraceL2 M n h hh) := by
  letI := potentialSequenceVAddInvariant M
  let Y := oneStepMultiplierAtL2 M n h 0 hh -
    oneStepPotentialTraceL2 M n h hh
  have hYcont : Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z Y) :=
    continuous_koopman_oneStepTraceDefect M n h hh
  intro z
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  by_contra hne
  have hpos : 0 < ‖Stationary.koopman (mu := M.P.toMeasure) z Y - Y‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  obtain ⟨rho, hrho⟩ :=
    Stationary.exists_mollifier_norm_mollifyL2_sub_lt_of_continuousAt
      (mu := M.P.toMeasure) Y hYcont.continuousAt
      (epsilon := ‖Stationary.koopman (mu := M.P.toMeasure) z Y - Y‖ / 3)
      (div_pos hpos (by norm_num))
  let Z := Stationary.mollifyL2 (mu := M.P.toMeasure) rho.toFun Y
  have hZinv : IsGloballyTranslationInvariant M Z := by
    exact isGloballyTranslationInvariant_mollifyL2_oneStepTraceDefect
      M n h hh rho.compactSupport rho.smooth
  have hdecomp :
      Stationary.koopman (mu := M.P.toMeasure) z Y - Y =
        Stationary.koopman (mu := M.P.toMeasure) z (Y - Z) + (Z - Y) := by
    calc
      Stationary.koopman (mu := M.P.toMeasure) z Y - Y =
          Stationary.koopman (mu := M.P.toMeasure) z Y -
            Stationary.koopman (mu := M.P.toMeasure) z Z + (Z - Y) := by
        rw [hZinv z]
        module
      _ = Stationary.koopman (mu := M.P.toMeasure) z (Y - Z) +
          (Z - Y) := by
        exact congrArg (fun W => W + (Z - Y))
          ((Stationary.koopman (mu := M.P.toMeasure) z).map_sub Y Z).symm
  have hstrict :
      ‖Stationary.koopman (mu := M.P.toMeasure) z Y - Y‖ <
        ‖Stationary.koopman (mu := M.P.toMeasure) z Y - Y‖ := by
    calc
      ‖Stationary.koopman (mu := M.P.toMeasure) z Y - Y‖ =
          ‖Stationary.koopman (mu := M.P.toMeasure) z (Y - Z) +
            (Z - Y)‖ := congrArg norm hdecomp
      _ ≤ ‖Stationary.koopman (mu := M.P.toMeasure) z (Y - Z)‖ +
          ‖Z - Y‖ := norm_add_le _ _
      _ = 2 * ‖Z - Y‖ := by
        rw [LinearIsometry.norm_map, norm_sub_rev]
        ring
      _ < ‖Stationary.koopman (mu := M.P.toMeasure) z Y - Y‖ := by
        change 2 * ‖Stationary.mollifyL2
          (mu := M.P.toMeasure) rho.toFun Y - Y‖ < _
        linarith
  exact (lt_irrefl _ hstrict)

/-- Exact stationary trace identity for the one-step multiplier. -/
theorem oneStepPotentialTraceL2_eq_multiplier
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (hh : 0 < h) :
    oneStepPotentialTraceL2 M n h hh =
      oneStepMultiplierAtL2 M n h 0 hh :=
  oneStepPotentialTraceL2_eq_multiplier_of_invariant_defect M n h hh
    (isGloballyTranslationInvariant_oneStepTraceDefect M n h hh)

/-- The stationary Helmholtz projection has trace one away from the
zero-frequency mode. -/
theorem oneStep_stationaryHelmholtz_trace
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (hh : 0 < h) :
    ∑ i : Fin d,
        ‖oneStepPotentialProjection M n h (Pi.single i 1) hh‖ ^ 2 =
      (oneShellCenteredExpTwoMoment M) ^ h - 1 :=
  oneStep_stationaryHelmholtz_trace_of_invariant_defect M n h hh
    (isGloballyTranslationInvariant_oneStepTraceDefect M n h hh)

/-- Exact projected energy of a deterministic probe. -/
theorem oneStepProjectedEnergy_eq_suffixVariance_div_dimension
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    oneStepProjectedEnergy M n h p hh =
      (((oneShellCenteredExpTwoMoment M) ^ h - 1) / (d : ℝ)) *
        vecNormSq p :=
  oneStepProjectedEnergy_eq_suffixVariance_div_dimension_of_invariant_defect
    M n h p hh
      (isGloballyTranslationInvariant_oneStepTraceDefect M n h hh)

/-- Unit-probe specialization of the exact projected-energy identity. -/
theorem oneStepProjectedEnergy_eq_suffixVariance_div_dimension_unit
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    oneStepProjectedEnergy M n h p hh =
      ((oneShellCenteredExpTwoMoment M) ^ h - 1) / (d : ℝ) :=
  oneStepProjectedEnergy_eq_suffixVariance_div_dimension_unit_of_invariant_defect
    M n h p hh hp
      (isGloballyTranslationInvariant_oneStepTraceDefect M n h hh)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
