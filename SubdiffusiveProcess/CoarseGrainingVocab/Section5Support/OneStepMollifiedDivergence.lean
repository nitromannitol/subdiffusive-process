module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryMollifiedHodge

@[expose] public section

/-!
# Mollified divergence of the one-step solenoidal remainder

Each coordinate forcing column minus its stationary-potential projection is
solenoidal.  Its explicitly established strong orbit continuity therefore lets the
smooth stationary Hodge energy identity identify its mollified divergence as
zero.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The one-step forcing remainder has zero divergence after every smooth
compactly supported stationary mollification. -/
theorem mollifiedDivergenceL2_oneStepSolenoidalRemainder_eq_zero
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    mollifiedDivergenceL2 M kappa
      (oneStepOriginForcingL2 M n h p hh -
        oneStepPotentialProjection M n h p hh) = 0 := by
  apply mollifiedDivergenceL2_eq_zero_of_mem_solenoidal
    M hcompact hkappa
  · exact continuous_koopman_oneStepSolenoidalRemainder M n h p hh
  · exact
      oneStepOriginForcingL2_sub_projection_mem_stationarySolenoidalSubspace
        M n h p hh

/-- Expanded basis-column form of the weak divergence identity. -/
theorem sum_mollifyL2_kernelDeriv_projectedColumn_eq_multiplier {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (j : Fin d) (hh : 0 < h)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    letI := potentialSequenceVAddInvariant M
    (∑ i : Fin d, Stationary.mollifyL2 (mu := M.P.toMeasure)
      (Stationary.kernelDeriv kappa i)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i
        (oneStepPotentialProjection M n h (Pi.single j 1) hh))) =
      Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa j)
        (oneStepMultiplierAtL2 M n h 0 hh) := by
  let := potentialSequenceVAddInvariant M
  classical
  let F := oneStepOriginForcingL2 M n h (Pi.single j 1) hh
  let P := oneStepPotentialProjection M n h (Pi.single j 1) hh
  have hF : Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z F) :=
    continuous_koopman_oneStepOriginForcingL2 M n h (Pi.single j 1) hh
  have hP : Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z P) :=
    continuous_koopman_oneStepPotentialProjection M n h (Pi.single j 1) hh
  have hFcoord : ∀ i : Fin d, Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F)) := by
    intro i
    have hc := (Stationary.vectorL2Coord
      (mu := M.P.toMeasure) i).continuous.comp hF
    convert hc using 1
    funext z
    exact Stationary.koopman_vectorL2Coord z i F
  have hPcoord : ∀ i : Fin d, Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i P)) := by
    intro i
    have hc := (Stationary.vectorL2Coord
      (mu := M.P.toMeasure) i).continuous.comp hP
    convert hc using 1
    funext z
    exact Stationary.koopman_vectorL2Coord z i P
  have hmoll : ∀ i : Fin d,
      Stationary.mollifyL2 (mu := M.P.toMeasure)
          (Stationary.kernelDeriv kappa i)
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) i (F - P)) =
        Stationary.mollifyL2 (mu := M.P.toMeasure)
            (Stationary.kernelDeriv kappa i)
            (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) -
          Stationary.mollifyL2 (mu := M.P.toMeasure)
            (Stationary.kernelDeriv kappa i)
            (Stationary.vectorL2Coord (mu := M.P.toMeasure) i P) := by
    intro i
    rw [map_sub]
    exact Stationary.mollifyL2_sub_of_continuous
      (Stationary.continuous_kernelDeriv hkappa i)
      (Stationary.hasCompactSupport_kernelDeriv hcompact i) _ _
      (hFcoord i) (hPcoord i)
  have hz := mollifiedDivergenceL2_oneStepSolenoidalRemainder_eq_zero
    M n h (Pi.single j 1) hh hcompact hkappa
  change (∑ i : Fin d, Stationary.mollifyL2 (mu := M.P.toMeasure)
      (Stationary.kernelDeriv kappa i)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i (F - P))) = 0 at hz
  simp_rw [hmoll] at hz
  rw [Finset.sum_sub_distrib] at hz
  have hforcing : (∑ i : Fin d,
      Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa i)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F)) =
      Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa j)
        (oneStepMultiplierAtL2 M n h 0 hh) := by
    rw [Finset.sum_eq_single j]
    · dsimp only [F]
      rw [vectorL2Coord_oneStepOriginForcingL2_basis]
      simp
    · intro i _ hij
      dsimp only [F]
      rw [vectorL2Coord_oneStepOriginForcingL2_basis]
      simp [hij, Stationary.mollifyL2]
    · simp
  have hsumEq : (∑ i : Fin d,
      Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa i)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i P)) =
      ∑ i : Fin d, Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa i)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) := by
    exact (sub_eq_zero.mp hz).symm
  rw [hsumEq, hforcing]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
