import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationarySmoothPotentialCurl

/-!
# Curl of a mollified closed stationary-potential field

This file instantiates the topology-free smooth curl energy theorem with the
first and second kernel derivatives of stationary mollification.  It is the
literal-carrier replacement for the generic topological curl theorem.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Mollified curl vanishes for a closed stationary-potential field whose
particular Koopman orbit is strongly continuous. -/
theorem mollifyL2_kernelDeriv_coord_comm_of_mem_potential_of_continuous
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure)
    (hPpot : letI := potentialSequenceVAddInvariant M
      P ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d))
    (hP : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z P))
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) (i j : Fin d) :
    letI := potentialSequenceVAddInvariant M
    Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa i)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) j P) =
      Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa j)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i P) := by
  letI := potentialSequenceVAddInvariant M
  let Q := Stationary.mollifyL2 (mu := M.P.toMeasure) kappa P
  let HQ : Fin d → Stationary.VectorL2 d M.P.toMeasure := fun k =>
    mollifiedGradientL2 M kappa
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) k P)
  let C := Stationary.mollifyL2 (mu := M.P.toMeasure)
      (Stationary.kernelDeriv kappa i)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) j P) -
    Stationary.mollifyL2 (mu := M.P.toMeasure)
      (Stationary.kernelDeriv kappa j)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i P)
  let GC := mollifiedGradientL2 M (Stationary.kernelDeriv kappa i)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) j P) -
    mollifiedGradientL2 M (Stationary.kernelDeriv kappa j)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i P)
  let HGC : Fin d → Stationary.VectorL2 d M.P.toMeasure := fun k =>
    mollifiedHessianRowL2 M (Stationary.kernelDeriv kappa i)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) j P) k -
      mollifiedHessianRowL2 M (Stationary.kernelDeriv kappa j)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i P) k
  have hPcoord : ∀ k : Fin d, Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) k P)) := by
    intro k
    have hc := (Stationary.vectorL2Coord
      (mu := M.P.toMeasure) k).continuous.comp hP
    convert hc using 1
    funext z
    exact Stationary.koopman_vectorL2Coord z k P
  have hQpot : Q ∈ Stationary.stationaryPotentialSubspace
      (mu := M.P.toMeasure) (d := d) := by
    exact Stationary.mollifyL2_mem_stationaryPotentialSubspace_of_continuous
      hkappa.continuous hcompact hPpot hP
  have hQcoord : ∀ k : Fin d,
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) k Q) (HQ k) := by
    intro k
    dsimp only [Q, HQ]
    rw [Stationary.vectorL2Coord_mollifyL2_of_continuous
      (mu := M.P.toMeasure) hkappa.continuous hcompact P hP]
    exact hasHorizontalGradient_mollifyL2 M hcompact hkappa _ (hPcoord k)
  have hCdef : C =
      Stationary.vectorL2Coord (mu := M.P.toMeasure) i (HQ j) -
        Stationary.vectorL2Coord (mu := M.P.toMeasure) j (HQ i) := by
    dsimp only [C, HQ]
    rw [mollifiedGradientL2, mollifiedGradientL2,
      vectorL2Coord_assembleScalarCoordinates,
      vectorL2Coord_assembleScalarCoordinates]
  have hC : Stationary.HasHorizontalGradient (mu := M.P.toMeasure) C GC := by
    dsimp only [C, GC]
    exact (hasHorizontalGradient_mollifyL2 M
      (Stationary.hasCompactSupport_kernelDeriv hcompact i)
      (Stationary.contDiff_kernelDeriv hkappa i) _ (hPcoord j)).sub
      (hasHorizontalGradient_mollifyL2 M
        (Stationary.hasCompactSupport_kernelDeriv hcompact j)
        (Stationary.contDiff_kernelDeriv hkappa j) _ (hPcoord i))
  have hGCcoord : ∀ k : Fin d,
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) k GC) (HGC k) := by
    intro k
    dsimp only [GC, HGC]
    rw [map_sub]
    exact (hasHorizontalGradient_vectorL2Coord_mollifiedGradientL2 M
      (Stationary.hasCompactSupport_kernelDeriv hcompact i)
      (Stationary.contDiff_kernelDeriv hkappa i) _ (hPcoord j) k).sub
      (hasHorizontalGradient_vectorL2Coord_mollifiedGradientL2 M
        (Stationary.hasCompactSupport_kernelDeriv hcompact j)
        (Stationary.contDiff_kernelDeriv hkappa j) _ (hPcoord i) k)
  have hmixed :
      Stationary.vectorL2Coord (mu := M.P.toMeasure) i (HGC j) =
        Stationary.vectorL2Coord (mu := M.P.toMeasure) j (HGC i) := by
    dsimp only [HGC]
    rw [map_sub, map_sub,
      vectorL2Coord_mollifiedHessianRowL2_comm M
        (Stationary.contDiff_kernelDeriv hkappa i) _ i j,
      vectorL2Coord_mollifiedHessianRowL2_comm M
        (Stationary.contDiff_kernelDeriv hkappa j) _ i j]
  have hCzero := curlComponent_eq_zero_of_smooth_mem_stationaryPotentialSubspace
    M Q hQpot HQ hQcoord i j C hCdef GC hC HGC hGCcoord hmixed
  exact sub_eq_zero.mp hCzero

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
