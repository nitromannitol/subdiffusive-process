module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OscillationEnergyFrame
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoRatioScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.TopGoodScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyScaleTransfer

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The top good-scale oscillation estimate for a centre anywhere in the
domain cube. -/
theorem exists_boundaryTopWindowOscillationEnergy (d : ℕ) [NeZero d] :
    ∃ Kosc : ℝ, 0 ≤ Kosc ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ C1 C2 alpha : ℝ,
        0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ≤ 1 →
      ∀ step L m n K : ℕ, m ≤ L →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d (m : ℤ) →
        (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        n + K + 5 ≤ m →
        1 + Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) + 1 →
      ∀ u : H1Function (openCubeSet (originCube d (m : ℤ))),
        ∃ top : ℕ, n ≤ top ∧ top + 5 ≤ m ∧ m ≤ top + K + 5 ∧
          Real.sqrt (tailAverage M L (top + 4) omega
              (translatedCube d ((top : ℤ) + 4) z)) *
              ((3 : ℝ) ^ (-(top : ℤ)) *
                normalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
                  (fun p ↦ u.toFun p - averageOn
                    (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun)) ≤
            Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ)) *
              vectorNormalizedL2On (cube d (m : ℤ))
                (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
                  u.grad p) := by
  classical
  obtain ⟨Kframe, hKframe, hframe⟩ := exists_interiorOscillationEnergyFrame d
  refine ⟨Kframe, hKframe, ?_⟩
  intro M hsmall C1 C2 alpha heps0 heps1 step L m n K hmL omega z hzgrid hz
    hstop hwin hroom u
  obtain ⟨top, hntop, htopm, hmtop, hgood⟩ :=
    exists_topGoodScale M C1 C2 alpha step m n K omega z hzgrid hz hstop
      heps0 heps1 hwin hroom
  refine ⟨top, hntop, htopm, hmtop, ?_⟩
  let y : Vec d := wellPlacedCentre z (m : ℤ) (top : ℤ)
  let W : Set (Vec d) := truncatedCube d (m : ℤ) (top : ℤ) z
  let V : Set (Vec d) := translateSet y (openCubeSet (originCube d (top : ℤ)))
  have htopmZ : (top : ℤ) ≤ (m : ℤ) := by omega
  have hWV : W ⊆ V := by
    simpa only [W, V, y, translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet] using
      (truncatedCube_subset_translatedCube_wellPlacedCentre z htopmZ le_rfl)
  have hVQ : V ⊆ openCubeSet (originCube d (m : ℤ)) := by
    simpa only [V, y, cube, translatedCube,
      Section6SchauderDatum.image_add_eq_translateSet] using
      (translatedCube_wellPlacedCentre_subset_cube z htopmZ)
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact ((Homogenization.isOpenBoundedConvexDomain_openCubeSet
      (originCube d (top : ℤ))).translateSet y).isOpen
  have hzW : z ∈ W := by
    refine ⟨?_, hz⟩
    exact Section6TheoremC.mem_translatedCube_self d (top : ℤ) z
  have hzy : z ∈ V := hWV hzW
  have hcontain :
      translateSet (y - z) (cubeSet (originCube d (top : ℤ))) ⊆
        cubeSet (originCube d ((top : ℤ) + 4)) := by
    intro p hp
    rcases hp with ⟨w, hw, rfl⟩
    rw [mem_cubeSet_originCube_iff] at hw ⊢
    have hzy' : z - y ∈ openCubeSet (originCube d (top : ℤ)) := by
      rcases hzy with ⟨v, hv, hvz⟩
      have : z - y = v := by rw [hvz]; abel
      rwa [this]
    rw [mem_openCubeSet_originCube_iff] at hzy'
    intro i
    have hw' := hw i
    have hc := hzy' i
    simp only [Pi.sub_apply] at hc
    have hc' : -(1 / 2 : ℝ) * (3 : ℝ) ^ (top : ℤ) < y i - z i ∧
        y i - z i < (1 / 2 : ℝ) * (3 : ℝ) ^ (top : ℤ) := by
      constructor <;> linarith only [hc.1, hc.2]
    have hp : (0 : ℝ) < (3 : ℝ) ^ (top : ℤ) := by positivity
    have h4 : (3 : ℝ) ^ ((top : ℤ) + 4) = 81 * (3 : ℝ) ^ (top : ℤ) := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
      ring
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [h4]
    constructor <;> linarith only [hw'.1, hw'.2, hc'.1, hc'.2, hp]
  have hs : (1 / 4 : ℝ) ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) := by
    refine ⟨?_, le_rfl⟩
    rw [Section6Stopping.holderStoppingS] at hsmall
    linarith only [hsmall]
  have hgood' : omega ∈ goodEvent M none ((top + 2) + 2) z 1 ((1 / 4 : ℝ) / 8) := by
    have hsEvent : (1 / 4 : ℝ) / 8 = Section6Stopping.holderStoppingS := by
      norm_num [Section6Stopping.holderStoppingS]
    rw [show (top + 2) + 2 = top + 4 by omega, hsEvent]
    exact hgood
  have hcast1 : (((top + 2 : ℕ) : ℤ) - 2) = (top : ℤ) := by omega
  have hcast2 : (((top + 2 : ℕ) : ℤ) + 2) = (top : ℤ) + 4 := by omega
  have hframe0 := hframe M (1 / 4 : ℝ) hs L (top + 2) (by omega) omega y z
    (by simpa only [show (((top + 2 : ℕ) : ℤ) - 2) = (top : ℤ) by omega,
      show (((top + 2 : ℕ) : ℤ) + 2) = (top : ℤ) + 4 by omega] using hcontain)
    hgood'
  rw [hcast1, hcast2] at hframe0
  have hframe' := hframe0 (u.restrict hVopen hVQ)
  rw [cubeBesovScaleWeight_one_originCube] at hframe'
  change
    Real.sqrt (tailAverage M L (top + 4) omega
        (translatedCube d ((top : ℤ) + 4) z)) *
        ((3 : ℝ) ^ (-(top : ℤ)) *
          normalizedL2On V (fun p ↦ u.toFun p - averageOn V u.toFun)) ≤
      Kframe * vectorNormalizedL2On V
        (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
          u.grad p) at hframe'
  have hWpos : 0 < (volume W).toReal := by
    dsimp only [W]
    exact volume_toReal_truncatedCube_pos z hz (by omega)
  have hWtop : volume W ≠ ⊤ := by
    exact (volume_truncatedCube_lt_top d (m : ℤ) (top : ℤ) z).ne
  have hVreal : (volume V).toReal = ((3 : ℝ) ^ (top : ℤ)) ^ d := by
    dsimp only [V]
    rw [volume_translateSet_eq, volume_openCubeSet_toReal, cubeVolume,
      cubeScaleFactor_originCube]
  have hVpos : 0 < (volume V).toReal := by rw [hVreal]; positivity
  have hVtop : volume V ≠ ⊤ := (ENNReal.toReal_ne_zero.mp hVpos.ne').2
  letI : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hVtop⟩
  have huV : MemLp u.toFun 2 (volume.restrict V) :=
    u.memL2.mono_measure (Measure.restrict_mono_set volume hVQ)
  have hmean : normalizedL2On W (fun p ↦ u.toFun p - averageOn W u.toFun) ≤
      normalizedL2On W (fun p ↦ u.toFun p - averageOn V u.toFun) := by
    apply Section6Iteration.normalizedL2On_sub_volumeAverage_le
      (measurableSet_truncatedCube d (m : ℤ) (top : ℤ) z) hWpos hWtop
    · exact integrableOn_truncatedCube z
        (u.memL2.mono_measure (Measure.restrict_mono_set volume
          (truncatedCube_subset_cube d (m : ℤ) (top : ℤ) z)))
    · exact (u.memL2.mono_measure (Measure.restrict_mono_set volume
          (truncatedCube_subset_cube d (m : ℤ) (top : ℤ) z))).integrable_sq
  have hrestrict := Section6Iteration.normalizedL2On_le_of_subset
    (f := fun p ↦ u.toFun p - averageOn V u.toFun) hWV hVpos hWpos
    (huV.sub (memLp_const (averageOn V u.toFun))).integrable_sq
  have hratioWV : Real.sqrt ((volume V).toReal / (volume W).toReal) ≤
      Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) := by
    apply Real.sqrt_le_sqrt
    have hlo := (volume_toReal_truncatedCube_bounds
      (m := (m : ℤ)) (j := (top : ℤ)) z hz (by omega)).1
    rw [hVreal, div_le_iff₀ hWpos]
    calc
      ((3 : ℝ) ^ (top : ℤ)) ^ d =
          (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
            (((3 : ℝ) ^ ((top : ℤ) - 2)) ^ d) := by
        rw [← mul_pow, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        ring_nf
      _ ≤ (((3 : ℝ) ^ (2 : ℤ)) ^ d) * (volume W).toReal :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
  have hWosc : normalizedL2On W (fun p ↦ u.toFun p - averageOn W u.toFun) ≤
      Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        normalizedL2On V (fun p ↦ u.toFun p - averageOn V u.toFun) :=
    hmean.trans (hrestrict.trans
      (mul_le_mul_of_nonneg_right hratioWV (Section6Iteration.normalizedL2On_nonneg _ _)))
  have hQpos : 0 < (volume (cube d (m : ℤ))).toReal := by
    rw [cube, volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d (m : ℤ))
  have henergyInt : IntegrableOn (fun p ↦
      euclideanNorm (Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
        u.grad p) ^ 2) (cube d (m : ℤ)) := by
    have hraw := integrableOn_weightedGrad_sq M L omega (m : ℤ) u (m : ℤ) 0
    rwa [Section6HolderInterior.truncatedCube_self_zero] at hraw
  have henergyRestrict := Section6Iteration.normalizedL2On_le_of_subset
    hVQ hQpos hVpos henergyInt
  have hratioVQ : Real.sqrt ((volume (cube d (m : ℤ))).toReal /
      (volume V).toReal) ≤ Real.sqrt (((3 : ℝ) ^ ((m : ℤ) - (top : ℤ))) ^ d) := by
    apply Real.sqrt_le_sqrt
    rw [cube, volume_openCubeSet_toReal, cubeVolume, cubeScaleFactor_originCube,
      hVreal, ← div_pow, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have hVenergy : vectorNormalizedL2On V
        (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p) ≤
      Real.sqrt (((3 : ℝ) ^ ((m : ℤ) - (top : ℤ))) ^ d) *
        vectorNormalizedL2On (cube d (m : ℤ))
          (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p) := by
    unfold vectorNormalizedL2On
    exact henergyRestrict.trans
      (mul_le_mul_of_nonneg_right hratioVQ (Section6Iteration.normalizedL2On_nonneg _ _))
  have hcompose :
      Real.sqrt (tailAverage M L (top + 4) omega
          (translatedCube d ((top : ℤ) + 4) z)) *
          ((3 : ℝ) ^ (-(top : ℤ)) *
            normalizedL2On W (fun p ↦ u.toFun p - averageOn W u.toFun)) ≤
        Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (Kframe * vectorNormalizedL2On V
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p)) := by
    calc
      _ ≤ Real.sqrt (tailAverage M L (top + 4) omega
            (translatedCube d ((top : ℤ) + 4) z)) *
          ((3 : ℝ) ^ (-(top : ℤ)) *
            (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
              normalizedL2On V (fun p ↦ u.toFun p - averageOn V u.toFun))) := by
          gcongr
      _ = Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (Real.sqrt (tailAverage M L (top + 4) omega
              (translatedCube d ((top : ℤ) + 4) z)) *
            ((3 : ℝ) ^ (-(top : ℤ)) *
              normalizedL2On V (fun p ↦ u.toFun p - averageOn V u.toFun))) := by ring
      _ ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (Kframe * vectorNormalizedL2On V
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p)) := mul_le_mul_of_nonneg_left hframe' (Real.sqrt_nonneg _)
  refine hcompose.trans ?_
  have hprice :
      Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          Real.sqrt (((3 : ℝ) ^ ((m : ℤ) - (top : ℤ))) ^ d) =
        scaleTransferPrice d ((m : ℤ) - (top : ℤ)) := by
    rw [← Real.sqrt_mul (by positivity :
      0 ≤ (((3 : ℝ) ^ (2 : ℤ)) ^ d))]
    unfold scaleTransferPrice
    congr 2
    rw [← mul_pow, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  calc
    Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (Kframe * vectorNormalizedL2On V
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p)) ≤
        Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (Kframe * (Real.sqrt (((3 : ℝ) ^ ((m : ℤ) - (top : ℤ))) ^ d) *
            vectorNormalizedL2On (cube d (m : ℤ))
              (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
                u.grad p))) := by gcongr
    _ = Kframe * scaleTransferPrice d ((m : ℤ) - (top : ℤ)) *
          vectorNormalizedL2On (cube d (m : ℤ))
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) := by rw [← hprice]; ring

/-- The preceding top-window estimate paired with the gate-scale tail average. -/
theorem exists_boundaryRowTwoTopLegAt (d : ℕ) [NeZero d] :
    ∃ Kosc : ℝ, 0 ≤ Kosc ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ C1 C2 alpha : ℝ,
        0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ≤ 1 →
        0 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingLambda C1 alpha < 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
      ∀ step L m n K p : ℕ, m ≤ L →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d (m : ℤ) →
        (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        n + K + 5 ≤ m →
        1 + Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) + 1 →
        n < m → n ≤ p → p ≤ m →
      ∀ u : H1Function (openCubeSet (originCube d (m : ℤ))),
        ∃ top : ℕ, n ≤ top ∧ top + 5 ≤ m ∧ m ≤ top + K + 5 ∧
          Real.sqrt (tailAverage M L p omega (translatedCube d (p : ℕ) z)) *
              ((3 : ℝ) ^ (-(top : ℤ)) *
                normalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
                  (fun q ↦ u.toFun q - averageOn
                    (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun)) ≤
            rowTwoRatioBound d C1 alpha m n *
              (Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ))) *
              vectorNormalizedL2On (cube d (m : ℤ))
                (fun q ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega q) •
                  u.grad q) := by
  obtain ⟨Kosc, hKosc, hleg⟩ := exists_boundaryTopWindowOscillationEnergy d
  refine ⟨Kosc, hKosc, ?_⟩
  intro M hsmall C1 C2 alpha heps0 heps1 hlam0 hlam1 hdelta step L m n K p hmL
    omega z hzgrid hz hstop hwin hroom hnm hnp hpm u
  obtain ⟨top, hntop, htopm, hmtop, hbound⟩ :=
    hleg M hsmall C1 C2 alpha heps0 heps1 step L m n K hmL omega z hzgrid hz
      hstop hwin hroom u
  refine ⟨top, hntop, htopm, hmtop, ?_⟩
  have hpair := sqrt_tailAverage_pairing_at M C1 C2 alpha step m n p (top + 4) L
    omega z z hzgrid hz hzgrid hz hstop hnm hnp hpm (by omega) (by omega) hmL
    hlam0 hlam1 heps0 hdelta
  have htopSigma : 0 < tailAverage M L (top + 4) omega
      (translatedCube d ((top : ℤ) + 4) z) := by
    rw [show (top : ℤ) + 4 = ((top + 4 : ℕ) : ℤ) by omega]
    exact tailAverage_translatedCube_pos M L (top + 4) omega z
  set X : ℝ := (3 : ℝ) ^ (-(top : ℤ)) *
    normalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
      (fun q ↦ u.toFun q - averageOn
        (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    exact mul_nonneg (by positivity) (Section6Iteration.normalizedL2On_nonneg _ _)
  have hsplit :
      Real.sqrt (tailAverage M L p omega (translatedCube d (p : ℕ) z)) * X =
        (Real.sqrt (tailAverage M L p omega (translatedCube d (p : ℕ) z)) *
          (Real.sqrt (tailAverage M L (top + 4) omega
            (translatedCube d ((top : ℤ) + 4) z)))⁻¹) *
          (Real.sqrt (tailAverage M L (top + 4) omega
            (translatedCube d ((top : ℤ) + 4) z)) * X) := by
    field_simp
  rw [hsplit]
  have hmul := mul_le_mul hpair hbound
    (mul_nonneg (Real.sqrt_nonneg _) hX0) (rowTwoRatioBound_nonneg d C1 alpha m n)
  simpa only [hXdef, mul_assoc, Nat.cast_add, Nat.cast_ofNat] using! hmul

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
