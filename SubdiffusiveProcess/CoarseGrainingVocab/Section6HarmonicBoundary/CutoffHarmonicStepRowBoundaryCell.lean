/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowBoundaryCellPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowBoundarySum

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The normalized boundary-class cell row at a free cover scale.**

The competitor-centred ASD row of `StepRowCompetitorASD`, with its residual mean
paid by the boundary tile family of `StepRowResidualMeanPrice` at the
`s`-adapted tile depth of `StepRowTileDepth`.  The feedback constant is exactly
the one `StepRowBoundarySum` consumes; the oscillation leg carries the loss
`3^{4s(n+2-k)}` and the three datum legs `3^{12s(n+2-k)}`. -/
theorem exists_stepRowBoundaryNormalizedCellRow_atScale (d : ℕ) [NeZero d] :
    ∃ CA CH : ℝ, 0 ≤ CA ∧ 0 ≤ CH ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ k : ℤ, k ≤ (n : ℤ) - 4 →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ cube d (m : ℤ) →
        q ∈ supWindow x (4 * (3 : ℝ) ^ n / 9) →
        translatedCube d k (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) ⊆
          truncatedCube d (m : ℤ) (n : ℤ) x →
        ¬ (openCubeAtScale q (k - 1) ⊆ cube d (m : ℤ)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d) (c0 : ℝ),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        let D := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤
          (1 / (16 * (28 : ℝ) ^ d)) *
              volumeAverage (translatedCube d k c)
                (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
                  vecNormSq (u.grad p)) +
            CA * Real.rpow (3 : ℝ) (4 * sOrder.1 * D) *
              (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (fun y ↦ u.toFun (y + c) - c0)) +
            CH * Real.rpow (3 : ℝ) (12 * sOrder.1 * D) *
              (sigma * (vecNormSq (cubeAverageVec Q (fun y ↦ h.grad (y + c))) +
                  Real.rpow (sOrder.1 / 2) (-3 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
                      (fun y ↦ h.grad (y + c)) ^ 2) +
                sigma⁻¹ * (Real.rpow (sOrder.1 / 2) (-3 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
                      (fun y ↦ -(g (y + c))) ^ 2)) := by
  obtain ⟨K, Cv, Cosc, hK, hCv, hCosc, hASD⟩ := exists_stepRowCompetitorASD_atScale d
  obtain ⟨Cf, hCf, hprice⟩ := exists_stepRowResidualMeanPrice_atScale d
  set theta : ℝ := 1 / (16 * (28 : ℝ) ^ d) with hthetadef
  have htheta : 0 < theta := by rw [hthetadef]; positivity
  set Cj : ℝ := stepRowTileDepthConst (2 * K * Cf) theta with hCjdef
  have hCj : 0 < Cj := by rw [hCjdef]; exact stepRowTileDepthConst_pos _ _
  refine ⟨K + 4 * K * (2 : ℝ) ^ d * Cj,
    (theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * Cv, by positivity,
    by positivity, ?_⟩
  intro M sOrder hs L m n hnm k hk z x q omega hx hq hqwin hparent hnot hgood
    u h g c0 hdir hg hh
  dsimp only
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hs4 : sOrder.1 ≤ 1 / 4 := hs.2
  have hkm : k ≤ (m : ℤ) := by omega
  have hkn : k ≤ (n : ℤ) - 2 := by omega
  have hD0 : (0 : ℝ) ≤ ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) := by positivity
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hsD0 : (0 : ℝ) ≤ sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) :=
    mul_nonneg hs0.le hD0
  -- the tile depth
  obtain ⟨j, hjfeed, hjcount⟩ := exists_stepRowTileDepth_ofExponent
    (Cface := 2 * K * Cf) (theta := theta) (by positivity) htheta hs4
    (E := 2 * sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) (by positivity)
  -- the competitor-centred ASD row
  obtain ⟨g0, u0, h0, r, Hv, hg0, hu0, hu0g, hh0, hh0g, hHv0, hHveq, hHvprice,
      hoscB, hcell⟩ :=
    hASD M sOrder hs L m n hnm k hkn z x q omega hx hq hparent hgood
      u h g c0 hdir hg hh
  -- the residual-mean price
  have hnot' : ¬ translatedCube d (k - 1) q ⊆ cube d (m : ℤ) := by
    rw [← openCubeAtScale_eq_translatedCube]
    exact hnot
  have hres := hprice M sOrder.1 hs L n m k hkm hkn q x z
    (4 * (3 : ℝ) ^ n / 9) omega hx ⟨hqwin, hq⟩ le_rfl hnot' hgood
    u h u0 h0 r c0 j hdir.1 hu0 hu0g hh0 hh0g
  dsimp only at hres
  rw [← hHveq] at hres
  have hh0geq : h0.grad = fun y ↦ h.grad (y + Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) :=
    funext hh0g
  have hg0eq : (fun y ↦ -g0 y) =
      fun y ↦ -(g (y + Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) := by
    funext y
    rw [hg0 y]
  rw [hh0geq, hg0eq] at hHvprice
  have hrp3 : ∀ a : ℝ, (3 : ℝ) ^ a = Real.rpow (3 : ℝ) a := fun a ↦ rfl
  simp only [hrp3] at hres hcell hoscB hHvprice hjfeed hjcount ⊢
  -- physical readouts
  have hEuEq : localizedCoeffEnergyValue
      (openCubeSet (originCube d k))
      ((aCutoffFamily M L (translatePotentialSample
        (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)).coeffOn
        (originCube d k)) u0 =
      volumeAverage (translatedCube d k
          (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k))
        (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (u.grad p)) := by
    rw [localizedCoeffEnergyValue_aCutoffFamily_eq_translate M L omega
      (originCube d k) (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)
      (openCubeSet (originCube d k)) u0 u.grad hu0g,
      ← translatedCube_eq_translateSet]
  have hN0Eq : normalizedL2SqOnSet (openCubeSet (originCube d k))
      (fun y ↦ u0.toFun y - c0) =
      normalizedL2SqOnSet (openCubeSet (originCube d k))
        (fun y ↦ u.toFun (y + Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) - c0) := by
    congr 1
    funext y
    rw [hu0 y]
  rw [hEuEq, hN0Eq] at hres
  rw [hN0Eq] at hcell
  -- abbreviations
  set c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k with hcdef
  set sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set D : ℝ := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) with hDdef
  set Eu : ℝ := volumeAverage (translatedCube d k c)
    (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p))
    with hEudef
  set N0 : ℝ := normalizedL2SqOnSet (openCubeSet (originCube d k))
    (fun y ↦ u.toFun (y + c) - c0) with hN0def
  set Oscv : ℝ := normalizedL2SqOnSet (openCubeSet (originCube d k))
    (fun y ↦ (h0 + r.toH1Function).toFun y -
      volumeAverage (openCubeSet (originCube d k)) (h0 + r.toH1Function).toFun)
    with hOscdef
  set Res : ℝ := volumeAverage (openCubeSet (originCube d k))
    (fun y ↦ u0.toFun y - (h0 + r.toH1Function).toFun y) with hResdef
  set Z : ℝ := Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) with hZdef
  set Mj : ℝ := (windowSummationTileCount j : ℝ) with hMjdef
  have hZ0 : (0 : ℝ) ≤ Z := by rw [hZdef]; exact rpow_three_nonneg _
  have hEu0 : 0 ≤ Eu := by
    rw [← hEuEq,
      localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
        (Q := originCube d k)
        (a := aCutoffFamily M L (translatePotentialSample c omega))
        Set.Subset.rfl u0, volumeAverage_openCubeSet_eq_cubeAverage]
    refine cubeAverage_nonneg_of_nonneg_on ?_
    intro y hy
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet (originCube d k)
        (aCutoffFamily M L (translatePotentialSample c omega))) u0.grad y hy
  have hN00 : 0 ≤ N0 := by
    rw [hN0def]
    exact normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet _)
  have hOsc0 : 0 ≤ Oscv := by
    rw [hOscdef]
    exact normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet _)
  have hMj0 : (0 : ℝ) < Mj := by
    rw [hMjdef, windowSummationTileCount]
    positivity
  set R7 : ℝ := Real.rpow (3 : ℝ) (7 / 4 * sOrder.1 * D) with hR7def
  set R2 : ℝ := Real.rpow (3 : ℝ) (2 * sOrder.1 * D) with hR2def
  set R4 : ℝ := Real.rpow (3 : ℝ) (4 * sOrder.1 * D) with hR4def
  set R5 : ℝ := Real.rpow (3 : ℝ) (5 * sOrder.1 * D) with hR5def
  set R12 : ℝ := Real.rpow (3 : ℝ) (12 * sOrder.1 * D) with hR12def
  set Rq : ℝ := Real.rpow (3 : ℝ) (sOrder.1 / 4 * D) with hRqdef
  set DjR : ℝ := ((((n : ℤ) + 2 - windowSummationTileScale k j).toNat : ℕ) : ℝ)
    with hDjRdef
  set Kap2 : ℝ := ((3 : ℝ) ^ windowSummationTileScale k j) ^ 2 with hKap2def
  have hSZN0 : 0 ≤ sigma * Z * N0 := mul_nonneg (mul_nonneg hsigma.le hZ0) hN00
  -- the tile-scale identity
  have hidTile : Z * Kap2 * Mj = Real.rpow (3 : ℝ) (-(j : ℝ)) := by
    rw [hZdef, hKap2def, hMjdef]
    exact rpow_three_scale_tile_identity k j
  have hDjR : DjR = D + (j : ℝ) := by
    rw [hDjRdef, hDdef]
    exact toNat_depth_tileScale (by omega)
  have hexpid : R7 * Real.rpow (3 : ℝ) (sOrder.1 / 4 * DjR) *
      Real.rpow (3 : ℝ) (-(j : ℝ)) =
      Real.rpow (3 : ℝ) (2 * sOrder.1 * D) *
        Real.rpow (3 : ℝ) ((sOrder.1 / 4 - 1) * (j : ℝ)) := by
    rw [hR7def, hDjR, rpow_three_add3, rpow_three_add2]
    congr 1
    ring
  have hfeedcoef : (2 * K * Cf) *
      (R7 * Real.rpow (3 : ℝ) (sOrder.1 / 4 * DjR) *
        Real.rpow (3 : ℝ) (-(j : ℝ))) ≤ theta := by
    rw [hexpid]
    calc (2 * K * Cf) * (Real.rpow (3 : ℝ) (2 * sOrder.1 * D) *
          Real.rpow (3 : ℝ) ((sOrder.1 / 4 - 1) * (j : ℝ)))
        = (2 * K * Cf) * Real.rpow (3 : ℝ) (2 * sOrder.1 * D) *
            Real.rpow (3 : ℝ) ((sOrder.1 / 4 - 1) * (j : ℝ)) := by ring
      _ ≤ theta := hjfeed
  -- (1) the feedback leg
  have hEH0 : 0 ≤ Eu + Hv := by linarith only [hEu0, hHv0]
  have hfeed : K * R7 * (sigma * Z *
      (Cf * Real.rpow (3 : ℝ) (sOrder.1 / 4 * DjR) * sigma⁻¹ * Kap2 * Mj *
        (2 * Eu + 2 * Hv))) ≤ theta * (Eu + Hv) := by
    have hrw : K * R7 * (sigma * Z *
        (Cf * Real.rpow (3 : ℝ) (sOrder.1 / 4 * DjR) * sigma⁻¹ * Kap2 * Mj *
          (2 * Eu + 2 * Hv))) =
        ((2 * K * Cf) * (R7 * Real.rpow (3 : ℝ) (sOrder.1 / 4 * DjR) *
          (Z * Kap2 * Mj))) * ((sigma * sigma⁻¹) * (Eu + Hv)) := by ring
    rw [hrw, hidTile, mul_inv_cancel₀ hsigma.ne', one_mul]
    exact mul_le_mul_of_nonneg_right hfeedcoef hEH0
  -- (2) the oscillation leg of the tile price
  have hZSF : Z * cubeScaleFactor (originCube d k) ^ 2 = 1 := by
    rw [hZdef]
    exact rpow_three_neg_two_mul_cubeScaleFactor_sq k
  have hoscZ : sigma * Z * Oscv ≤ Cosc * Rq * Hv := by
    have h1 : sigma * Z * Oscv ≤
        sigma * Z * (Cosc * Rq * sigma⁻¹ * cubeScaleFactor (originCube d k) ^ 2 * Hv) :=
      mul_le_mul_of_nonneg_left hoscB (mul_nonneg hsigma.le hZ0)
    refine h1.trans (le_of_eq ?_)
    have heq : sigma * Z * (Cosc * Rq * sigma⁻¹ * cubeScaleFactor (originCube d k) ^ 2 * Hv) =
        (Cosc * Rq * Hv) * ((sigma * sigma⁻¹) * (Z * cubeScaleFactor (originCube d k) ^ 2)) := by
      ring
    rw [heq, hZSF, mul_inv_cancel₀ hsigma.ne']
    ring
  have hoscTerm : K * R7 * (sigma * Z *
      (2 * ((2 : ℝ) ^ d * Mj) * (2 * N0 + 2 * Oscv))) ≤
      4 * K * (2 : ℝ) ^ d * (R7 * Mj) * (sigma * Z * N0) +
        4 * K * (2 : ℝ) ^ d * Cosc * (R7 * Mj * Rq) * Hv := by
    have hexp : K * R7 * (sigma * Z *
        (2 * ((2 : ℝ) ^ d * Mj) * (2 * N0 + 2 * Oscv))) =
        4 * K * (2 : ℝ) ^ d * (R7 * Mj) * (sigma * Z * N0) +
          (4 * K * (2 : ℝ) ^ d * (R7 * Mj)) * (sigma * Z * Oscv) := by ring
    rw [hexp]
    have hc : (0 : ℝ) ≤ 4 * K * (2 : ℝ) ^ d * (R7 * Mj) := by
      have : (0 : ℝ) ≤ R7 := by rw [hR7def]; exact rpow_three_nonneg _
      positivity
    have hstep := mul_le_mul_of_nonneg_left hoscZ hc
    nlinarith only [hstep]
  -- the tile-count bounds
  have hMjle : Mj ≤ Cj * Real.rpow (3 : ℝ) ((16 / 15 : ℝ) * (2 * sOrder.1 * D)) := by
    rw [hMjdef, windowSummationTileCount_eq_rpow]
    exact hjcount
  have hR70 : (0 : ℝ) ≤ R7 := by rw [hR7def]; exact rpow_three_nonneg _
  have hR7Mj : R7 * Mj ≤ Cj * R4 := by
    have h1 : R7 * Mj ≤
        R7 * (Cj * Real.rpow (3 : ℝ) ((16 / 15 : ℝ) * (2 * sOrder.1 * D))) :=
      mul_le_mul_of_nonneg_left hMjle hR70
    refine h1.trans ?_
    have heq : R7 * (Cj * Real.rpow (3 : ℝ) ((16 / 15 : ℝ) * (2 * sOrder.1 * D))) =
        Cj * Real.rpow (3 : ℝ)
          (7 / 4 * sOrder.1 * D + (16 / 15 : ℝ) * (2 * sOrder.1 * D)) := by
      rw [hR7def, ← rpow_three_add2]; ring
    rw [heq, hR4def]
    refine mul_le_mul_of_nonneg_left (rpow_three_le_rpow_three ?_) hCj.le
    nlinarith only [hsD0]
  have hR7MjRq : R7 * Mj * Rq ≤ Cj * R5 := by
    have h1 : R7 * Mj * Rq ≤
        R7 * (Cj * Real.rpow (3 : ℝ) ((16 / 15 : ℝ) * (2 * sOrder.1 * D))) * Rq := by
      have := mul_le_mul_of_nonneg_left hMjle hR70
      exact mul_le_mul_of_nonneg_right this (by rw [hRqdef]; exact rpow_three_nonneg _)
    refine h1.trans ?_
    have heq : R7 * (Cj * Real.rpow (3 : ℝ) ((16 / 15 : ℝ) * (2 * sOrder.1 * D))) * Rq =
        Cj * Real.rpow (3 : ℝ)
          (7 / 4 * sOrder.1 * D + (16 / 15 : ℝ) * (2 * sOrder.1 * D) +
            sOrder.1 / 4 * D) := by
      rw [hR7def, hRqdef, ← rpow_three_add3]; ring
    rw [heq, hR5def]
    refine mul_le_mul_of_nonneg_left (rpow_three_le_rpow_three ?_) hCj.le
    nlinarith only [hsD0]
  set Dat : ℝ := sigma *
      (vecNormSq (cubeAverageVec (originCube d k) fun y ↦ h.grad (y + c)) +
        Real.rpow (sOrder.1 / 2) (-3 : ℝ) *
          (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) sOrder.1
            fun y ↦ h.grad (y + c)) ^ 2) +
    sigma⁻¹ * (Real.rpow (sOrder.1 / 2) (-3 : ℝ) *
      (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) sOrder.1
        fun y ↦ -g (y + c)) ^ 2) with hDatdef
  have hP30 : (0 : ℝ) ≤ Real.rpow (sOrder.1 / 2) (-3 : ℝ) :=
    Real.rpow_nonneg (by linarith only [hs0]) _
  have hDat0 : 0 ≤ Dat := by
    rw [hDatdef]
    exact add_nonneg
      (mul_nonneg hsigma.le
        (add_nonneg (vecNormSq_nonneg _) (mul_nonneg hP30 (sq_nonneg _))))
      (mul_nonneg (inv_nonneg.mpr hsigma.le) (mul_nonneg hP30 (sq_nonneg _)))
  have hR20 : (0 : ℝ) ≤ R2 := by rw [hR2def]; exact rpow_three_nonneg _
  have hR40 : (0 : ℝ) ≤ R4 := by rw [hR4def]; exact rpow_three_nonneg _
  have hR50 : (0 : ℝ) ≤ R5 := by rw [hR5def]; exact rpow_three_nonneg _
  have hRq0 : (0 : ℝ) ≤ Rq := by rw [hRqdef]; exact rpow_three_nonneg _
  have hR51 : (1 : ℝ) ≤ R5 := by
    rw [hR5def]
    exact Real.one_le_rpow (by norm_num) (by nlinarith only [hsD0])
  -- the residual-mean leg, fully priced
  have hResBound : K * R7 * (sigma * Z * Res ^ 2) ≤
      theta * (Eu + Hv) +
        (4 * K * (2 : ℝ) ^ d * (R7 * Mj) * (sigma * Z * N0) +
          4 * K * (2 : ℝ) ^ d * Cosc * (R7 * Mj * Rq) * Hv) := by
    have hc : (0 : ℝ) ≤ K * R7 * (sigma * Z) :=
      mul_nonneg (mul_nonneg hK.le hR70) (mul_nonneg hsigma.le hZ0)
    calc K * R7 * (sigma * Z * Res ^ 2)
        = (K * R7 * (sigma * Z)) * Res ^ 2 := by ring
      _ ≤ (K * R7 * (sigma * Z)) *
            (Cf * Real.rpow (3 : ℝ) (sOrder.1 / 4 * DjR) * sigma⁻¹ * Kap2 * Mj *
                (2 * Eu + 2 * Hv) +
              2 * ((2 : ℝ) ^ d * Mj) * (2 * N0 + 2 * Oscv)) :=
          mul_le_mul_of_nonneg_left hres hc
      _ = K * R7 * (sigma * Z *
              (Cf * Real.rpow (3 : ℝ) (sOrder.1 / 4 * DjR) * sigma⁻¹ * Kap2 * Mj *
                (2 * Eu + 2 * Hv))) +
            K * R7 * (sigma * Z *
              (2 * ((2 : ℝ) ^ d * Mj) * (2 * N0 + 2 * Oscv))) := by ring
      _ ≤ theta * (Eu + Hv) +
            (4 * K * (2 : ℝ) ^ d * (R7 * Mj) * (sigma * Z * N0) +
              4 * K * (2 : ℝ) ^ d * Cosc * (R7 * Mj * Rq) * Hv) :=
          add_le_add hfeed hoscTerm
  -- the exponent comparisons
  have e1 : K * R7 * (sigma * Z * N0) ≤ K * R4 * (sigma * Z * N0) := by
    have hle : R7 ≤ R4 := by
      rw [hR7def, hR4def]
      exact rpow_three_le_rpow_three (by nlinarith only [hsD0])
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hle hK.le) hSZN0
  have e2 : 4 * K * (2 : ℝ) ^ d * (R7 * Mj) * (sigma * Z * N0) ≤
      4 * K * (2 : ℝ) ^ d * Cj * R4 * (sigma * Z * N0) := by
    have hc : (0 : ℝ) ≤ 4 * K * (2 : ℝ) ^ d := by positivity
    calc 4 * K * (2 : ℝ) ^ d * (R7 * Mj) * (sigma * Z * N0)
        ≤ 4 * K * (2 : ℝ) ^ d * (Cj * R4) * (sigma * Z * N0) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hR7Mj hc) hSZN0
      _ = 4 * K * (2 : ℝ) ^ d * Cj * R4 * (sigma * Z * N0) := by ring
  have e3 : 4 * K * (2 : ℝ) ^ d * Cosc * (R7 * Mj * Rq) * Hv ≤
      4 * K * (2 : ℝ) ^ d * Cosc * Cj * R5 * Hv := by
    have hc : (0 : ℝ) ≤ 4 * K * (2 : ℝ) ^ d * Cosc := by positivity
    calc 4 * K * (2 : ℝ) ^ d * Cosc * (R7 * Mj * Rq) * Hv
        ≤ 4 * K * (2 : ℝ) ^ d * Cosc * (Cj * R5) * Hv :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hR7MjRq hc) hHv0
      _ = 4 * K * (2 : ℝ) ^ d * Cosc * Cj * R5 * Hv := by ring
  have e4 : K * R2 * Hv ≤ K * R5 * Hv := by
    have hle : R2 ≤ R5 := by
      rw [hR2def, hR5def]
      exact rpow_three_le_rpow_three (by nlinarith only [hsD0])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hK.le) hHv0
  have e5 : theta * Hv ≤ theta * R5 * Hv := by
    have hstep : theta * Hv ≤ theta * (R5 * Hv) :=
      mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left hHv0 hR51) htheta.le
    calc theta * Hv ≤ theta * (R5 * Hv) := hstep
      _ = theta * R5 * Hv := by ring
  have e6 : theta * (Eu + Hv) = theta * Eu + theta * Hv := by ring
  have e7 : (K + 4 * K * (2 : ℝ) ^ d * Cj) * R4 * (sigma * Z * N0) =
      K * R4 * (sigma * Z * N0) +
        4 * K * (2 : ℝ) ^ d * Cj * R4 * (sigma * Z * N0) := by ring
  have e8 : (theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * R5 * Hv =
      theta * R5 * Hv + 4 * K * (2 : ℝ) ^ d * Cosc * Cj * R5 * Hv +
        K * R5 * Hv := by ring
  have hsplit : K * (R7 * (sigma * Z * (N0 + Res ^ 2)) + R2 * Hv) =
      K * R7 * (sigma * Z * N0) + K * R7 * (sigma * Z * Res ^ 2) + K * R2 * Hv := by
    ring
  have hMain : (normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
        fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (u.grad p)) ≤
      theta * Eu + (K + 4 * K * (2 : ℝ) ^ d * Cj) * R4 * (sigma * Z * N0) +
        (theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * R5 * Hv := by
    rw [hsplit] at hcell
    linarith only [hcell, hResBound, e1, e2, e3, e4, e5,
      e6.le, e6.ge, e7.le, e7.ge, e8.le, e8.ge]
  -- the datum price
  have hlast : (theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * R5 * Hv ≤
      (theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * Cv * R12 * Dat := by
    have hcoef : (0 : ℝ) ≤ (theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * R5 := by
      have h0 : (0 : ℝ) ≤ theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K := by positivity
      exact mul_nonneg h0 hR50
    have hRR : R5 * Rq ≤ R12 := by
      rw [hR5def, hRqdef, rpow_three_add2, hR12def]
      exact rpow_three_le_rpow_three (by nlinarith only [hsD0])
    calc (theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * R5 * Hv
        ≤ (theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * R5 * (Cv * Rq * Dat) :=
          mul_le_mul_of_nonneg_left hHvprice hcoef
      _ = ((theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * Cv) * (R5 * Rq) * Dat := by
          ring
      _ ≤ ((theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * Cv) * R12 * Dat := by
          have hc2 : (0 : ℝ) ≤ (theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * Cv := by
            positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hRR hc2) hDat0
      _ = (theta + 4 * K * (2 : ℝ) ^ d * Cosc * Cj + K) * Cv * R12 * Dat := by ring
  linarith only [hMain, hlast]

omit [NeZero d] in

/-- **The boundary-class cell row at a free cover scale.**

`StepRowBoundarySum.BoundaryStepCellParentRow` is produced: the normalized cell
row of `exists_stepRowBoundaryNormalizedCellRow_atScale`, unnormalized by the
cell volume exactly as `StepRowInteriorPrice` does for the interior class. -/
theorem exists_boundaryStepCellParentRow (d : ℕ) [NeZero d] :
    ∃ Cbd : ℝ, 0 ≤ Cbd ∧ BoundaryStepCellParentRow d Cbd := by
  obtain ⟨CA, CH, hCA, hCH, hnorm⟩ :=
    exists_stepRowBoundaryNormalizedCellRow_atScale d
  refine ⟨CA + CH * (8 * caccioppoliExactDatumConstant d ^ 2 + 1) + 1,
    by positivity, ?_⟩
  intro M sOrder hs L m n hnm k hk z x q omega hz hx hq hqwin hparent hnot
    hgood u h g c0 hdir hg hh
  dsimp only
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hs4 : sOrder.1 ≤ 1 / 4 := hs.2
  have hkm : k ≤ (m : ℤ) := by omega
  have hkn : k ≤ (n : ℤ) - 2 := by omega
  have hhFull : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad := by
    apply memCubeEuclideanFullWsp_grad_of_memFractionalOn
    simpa [cube] using hh
  have hnormcell := hnorm M sOrder hs L m n hnm k hk z x q omega hx hq hqwin
    hparent hnot hgood u h g c0 hdir hg hhFull
  dsimp only at hnormcell
  obtain ⟨g0, u0, h0, hg0, hu0, hgLocal, hu0grad, _heq, hh0, hh0grad,
      hhLocal, hgRegRaw, _htrace⟩ :=
    exists_projectedBoundaryDirectDatum M L omega m k q sOrder u h g
      hdir hg hhFull hkm
  set c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k with hcdef
  set P : Set (Vec d) := translatedCube d k c with hPdef
  set sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set cell : Set (Vec d) := truncatedCube d (m : ℤ) (k - 2) q with hcelldef
  set D : ℝ := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) with hDdef
  set Z : ℝ := Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) with hZdef
  set R4 : ℝ := Real.rpow (3 : ℝ) (4 * sOrder.1 * D) with hR4def
  set E8 : ℝ := Real.rpow (3 : ℝ) (8 * sOrder.1 * D) with hE8def
  set R12 : ℝ := Real.rpow (3 : ℝ) (12 * sOrder.1 * D) with hR12def
  have hR4E8 : R4 * E8 = R12 := by
    rw [hR4def, hE8def, rpow_three_add2, hR12def]
    congr 1
    ring
  have hR40 : (0 : ℝ) ≤ R4 := by rw [hR4def]; exact rpow_three_nonneg _
  have hE81 : (1 : ℝ) ≤ E8 := by
    rw [hE8def]
    refine Real.one_le_rpow (by norm_num) ?_
    have : (0 : ℝ) ≤ D := by rw [hDdef]; positivity
    positivity
  have hZ0 : (0 : ℝ) ≤ Z := by rw [hZdef]; exact rpow_three_nonneg _
  have hsigma : 0 < sigma := by
    rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  -- volumes
  have hcellpos : 0 < (volume cell).toReal := by
    rw [hcelldef]
    exact Section6ExcessDecay.volume_toReal_truncatedCube_pos q hq (by omega)
  have hcellub : (volume cell).toReal ≤ ((3 : ℝ) ^ (k - 2)) ^ d := by
    rw [hcelldef]
    exact (Section6ExcessDecay.volume_toReal_truncatedCube_bounds q hq (by omega)).2
  have hPvol : (volume P).toReal = ((3 : ℝ) ^ k) ^ d := by
    rw [hPdef]
    exact Section6BoundedMultiplier.volume_translatedCube_toReal k c
  have hPpos : 0 < (volume P).toReal := by rw [hPvol]; positivity
  have hcellleP : (volume cell).toReal ≤ (volume P).toReal := by
    refine hcellub.trans ?_
    rw [hPvol]
    exact pow_le_pow_left₀ (by positivity)
      (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
  have hP0 : volume P ≠ 0 := (ENNReal.toReal_ne_zero.mp hPpos.ne').1
  have hPtop : volume P ≠ ⊤ := (ENNReal.toReal_ne_zero.mp hPpos.ne').2
  have hPtranslate : P = translateSet c (openCubeSet (originCube d k)) := by
    rw [hPdef, translatedCube_eq_translateSet]
  have hPdom : P ⊆ cube d (m : ℤ) := by
    rw [hPdef, hcdef]
    exact Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hkm
  set Ipar : ℝ := ∫ p in P, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
    vecNormSq (u.grad p) with hIpardef
  set Iosc : ℝ := ∫ p in P, (u.toFun p - c0) ^ 2 with hIoscdef
  set Idat : ℝ := ∫ p in P, vecNormSq (h.grad p) with hIdatdef
  set Gg : ℝ := (fractionalSeminormOn P sOrder.1 g).toReal with hGgdef
  set Gh : ℝ := (fractionalSeminormOn P sOrder.1 h.grad).toReal with hGhdef
  have hIpar0 : 0 ≤ Ipar := by
    rw [hIpardef]
    exact integral_nonneg fun p ↦ cutoffEnergyDensity_nonneg M L omega u p
  have hIosc0 : 0 ≤ Iosc := by
    rw [hIoscdef]; exact integral_nonneg fun p ↦ sq_nonneg _
  have hIdat0 : 0 ≤ Idat := by
    rw [hIdatdef]; exact integral_nonneg fun p ↦ vecNormSq_nonneg _
  have hratio : (volume cell).toReal * ((volume P).toReal)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hPpos, one_mul]
    exact hcellleP
  -- (a) the feedback leg
  have hVcEu : (volume cell).toReal *
      volumeAverage P (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
        vecNormSq (u.grad p)) ≤ Ipar := by
    have hEq : volumeAverage P (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
        vecNormSq (u.grad p)) = ((volume P).toReal)⁻¹ * Ipar := rfl
    rw [hEq, ← mul_assoc]
    exact mul_le_of_le_one_left hIpar0 hratio
  -- (b) the parent oscillation leg
  have hN0eq : normalizedL2SqOnSet (openCubeSet (originCube d k))
      (fun y ↦ u.toFun (y + c) - c0) = ((volume P).toReal)⁻¹ * Iosc := by
    have htr : volumeAverage P (fun p ↦ (u.toFun p - c0) ^ 2) =
        volumeAverage (openCubeSet (originCube d k))
          (fun y ↦ (u.toFun (y + c) - c0) ^ 2) := by
      rw [hPdef]
      refine volumeAverage_translatedCube_eq_of_eq_on k c ?_
      intro p _
      rw [show p - c + c = p by abel]
    show volumeAverage (openCubeSet (originCube d k))
        (fun y ↦ (u.toFun (y + c) - c0) ^ 2) = _
    rw [← htr]
    rfl
  have hVcN0 : (volume cell).toReal *
      normalizedL2SqOnSet (openCubeSet (originCube d k))
        (fun y ↦ u.toFun (y + c) - c0) ≤ Iosc := by
    rw [hN0eq, ← mul_assoc]
    exact mul_le_of_le_one_left hIosc0 hratio
  -- (c) the datum-mean leg, by Jensen
  have hPsubm : P ⊆ openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    simpa [cube] using hPdom hp
  have hhL2 : MemVectorL2 P h.grad :=
    h.grad_memVectorL2.mono_measure (Measure.restrict_mono_set volume hPsubm)
  have hhHil : MemLp (fun p ↦ HilbertVec.ofVec (h.grad p)) 2 (volume.restrict P) :=
    memHilbertVectorL2_hilbertifyVecField hhL2
  have hJensen : (volume P).toReal * vecNormSq (averageVecOn P h.grad) ≤ Idat := by
    have hmean := euclideanNorm_averageVecOn_le_vectorNormalizedL2On hPpos hhHil
    have hsq : vecNormSq (averageVecOn P h.grad) ≤ vectorNormalizedL2On P h.grad ^ 2 := by
      rw [← euclideanNorm_sq]
      exact pow_le_pow_left₀ (euclideanNorm_nonneg _) hmean 2
    calc (volume P).toReal * vecNormSq (averageVecOn P h.grad)
        ≤ (volume P).toReal * vectorNormalizedL2On P h.grad ^ 2 :=
          mul_le_mul_of_nonneg_left hsq ENNReal.toReal_nonneg
      _ = Idat := by
          unfold vectorNormalizedL2On
          rw [hIdatdef]
          calc (volume P).toReal *
                normalizedL2On P (fun p ↦ euclideanNorm (h.grad p)) ^ 2 =
              ∫ p in P, euclideanNorm (h.grad p) ^ 2 :=
            (Section6HolderInterior.setIntegral_sq_eq_volume_mul_normalizedL2On_sq
              hPtop).symm
            _ = ∫ p in P, vecNormSq (h.grad p) :=
              integral_congr_ae (Filter.Eventually.of_forall fun p ↦
                euclideanNorm_sq (h.grad p))
  have hmeanEq : cubeAverageVec (originCube d k) (fun y ↦ h.grad (y + c)) =
      averageVecOn P h.grad := by
    rw [hPtranslate]
    exact cubeAverageVec_comp_add_eq_averageVecOn_translateSet (originCube d k) c h.grad
  have hVcMn : (volume cell).toReal *
      vecNormSq (cubeAverageVec (originCube d k) (fun y ↦ h.grad (y + c))) ≤ Idat := by
    rw [hmeanEq]
    refine le_trans (mul_le_mul_of_nonneg_right hcellleP (vecNormSq_nonneg _)) hJensen
  -- (d) the two Besov legs
  have hA0m : volume (cube d (m : ℤ)) ≠ 0 := by
    rw [cube]
    have hreal : 0 < (volume (openCubeSet (originCube d (m : ℤ)))).toReal := by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos (originCube d (m : ℤ))
    exact (ENNReal.toReal_ne_zero.mp hreal.ne').1
  have hAtopm : volume (cube d (m : ℤ)) ≠ ∞ := by
    rw [cube]
    exact (volume_openCubeSet_lt_top (originCube d (m : ℤ))).ne
  have hfracG : MemFractionalOn (cube d (m : ℤ)) sOrder.1 g := by
    change fractionalSeminormOn (openCubeSet (originCube d (m : ℤ))) sOrder.1 g ≠ ⊤
    rw [fractionalSeminormOn_openCubeSet_eq_guarded_of_measurable _ _ _ hg.2.aestronglyMeasurable]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hg.2.eSeminorm_lt_top.ne
  have hgfin : fractionalSeminormOn P sOrder.1 g ≠ ⊤ :=
    memFractionalOn_mono_set hPdom hA0m hAtopm hP0 hfracG
  have hhfin : fractionalSeminormOn P sOrder.1 h.grad ≠ ⊤ :=
    memFractionalOn_mono_set hPdom hA0m hAtopm hP0 hh
  have hhReg : ForceBesovRegularity (originCube d k) sOrder.1
      (fun y ↦ h.grad (y + c)) :=
    forceBesovRegularity_of_memCubeEuclideanFullWsp_of_exponent_le hhLocal le_rfl
  have hgReg' : ForceBesovRegularity (originCube d k) sOrder.1
      (fun y ↦ -(g (y + c))) := by
    have heq : (fun x ↦ -g0 x) = fun y ↦ -(g (y + c)) := by
      funext y
      rw [hg0 y]
    rw [heq] at hgRegRaw
    exact hgRegRaw
  have hBhle := scaleNormalizedPositiveBesovVectorSeminormTwo_translate_le_window
    (originCube d k) c P sOrder h.grad hhLocal (by rw [← hPtranslate])
    (by rw [← hPtranslate]; exact hP0) (by rw [← hPtranslate]; exact hPtop)
    hP0 hPtop hhfin
  rw [← hPtranslate, div_self hPpos.ne', cubeBesovScaleWeight_neg_originCube,
    ← hGhdef] at hBhle
  have hBgle := projectedForceSeminorm_le_window
    (originCube d k) c P sOrder g (fun x ↦ g (x + c)) hgLocal (fun x ↦ rfl)
    (by rw [← hPtranslate]) (by rw [← hPtranslate]; exact hP0)
    (by rw [← hPtranslate]; exact hPtop) hP0 hPtop hgfin
  rw [← hPtranslate, div_self hPpos.ne', cubeBesovScaleWeight_neg_originCube,
    ← hGgdef] at hBgle
  set P3 : ℝ := Real.rpow (sOrder.1 / 2) (-3 : ℝ) with hP3def
  have hP30 : (0 : ℝ) ≤ P3 := by
    rw [hP3def]; exact Real.rpow_nonneg (by linarith only [hs0]) _
  set Cd2 : ℝ := 8 * caccioppoliExactDatumConstant d ^ 2 with hCd2def
  have hCd20 : (0 : ℝ) ≤ Cd2 := by rw [hCd2def]; positivity
  have hBhsq : P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d k) sOrder.1 (fun y ↦ h.grad (y + c))) ^ 2 ≤
      Cd2 * (Real.rpow sOrder.1 (-4 : ℝ) *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) * Gh ^ 2) := by
    have hb0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
        (originCube d k) sOrder.1 (fun y ↦ h.grad (y + c)) :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        hhReg
    have hsq := pow_le_pow_left₀ hb0 hBhle 2
    have hstep := mul_le_mul_of_nonneg_left hsq hP30
    refine hstep.trans (le_of_eq ?_)
    rw [hP3def, hCd2def]
    exact projected_datum_factor_atScale k hs0
  have hBgsq : P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d k) sOrder.1 (fun y ↦ -g (y + c))) ^ 2 ≤
      Cd2 * (Real.rpow sOrder.1 (-4 : ℝ) *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) * Gg ^ 2) := by
    have hb0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
        (originCube d k) sOrder.1 (fun y ↦ -g (y + c)) :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        hgReg'
    have hsq := pow_le_pow_left₀ hb0 hBgle 2
    have hstep := mul_le_mul_of_nonneg_left hsq hP30
    refine hstep.trans (le_of_eq ?_)
    rw [hP3def, hCd2def]
    exact projected_datum_factor_atScale k hs0
  -- (e) the assembly
  set Aw : ℝ := Real.rpow sOrder.1 (-4 : ℝ) *
    Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) with hAwdef
  have hAw0 : (0 : ℝ) ≤ Aw := by
    rw [hAwdef]
    exact mul_nonneg (Real.rpow_nonneg hs0.le _) (rpow_three_nonneg _)
  have hVcBh : (volume cell).toReal *
      (P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k)
        sOrder.1 (fun y ↦ h.grad (y + c))) ^ 2) ≤
      Cd2 * Aw * ((volume P).toReal * Gh ^ 2) := by
    calc (volume cell).toReal *
          (P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k)
            sOrder.1 (fun y ↦ h.grad (y + c))) ^ 2)
        ≤ (volume cell).toReal * (Cd2 * (Aw * Gh ^ 2)) :=
          mul_le_mul_of_nonneg_left hBhsq hcellpos.le
      _ = Cd2 * Aw * ((volume cell).toReal * Gh ^ 2) := by ring
      _ ≤ Cd2 * Aw * ((volume P).toReal * Gh ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcellleP (sq_nonneg _))
            (mul_nonneg hCd20 hAw0)
  have hVcBg : (volume cell).toReal *
      (P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k)
        sOrder.1 (fun y ↦ -g (y + c))) ^ 2) ≤
      Cd2 * Aw * ((volume P).toReal * Gg ^ 2) := by
    calc (volume cell).toReal *
          (P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k)
            sOrder.1 (fun y ↦ -g (y + c))) ^ 2)
        ≤ (volume cell).toReal * (Cd2 * (Aw * Gg ^ 2)) :=
          mul_le_mul_of_nonneg_left hBgsq hcellpos.le
      _ = Cd2 * Aw * ((volume cell).toReal * Gg ^ 2) := by ring
      _ ≤ Cd2 * Aw * ((volume P).toReal * Gg ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcellleP (sq_nonneg _))
            (mul_nonneg hCd20 hAw0)
  have hVcDat : (volume cell).toReal *
      (sigma * (vecNormSq (cubeAverageVec (originCube d k)
            (fun y ↦ h.grad (y + c))) +
          P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k)
            sOrder.1 (fun y ↦ h.grad (y + c))) ^ 2) +
        sigma⁻¹ * (P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo
          (originCube d k) sOrder.1 (fun y ↦ -g (y + c))) ^ 2)) ≤
      sigma * Idat + sigma * (Cd2 * Aw * ((volume P).toReal * Gh ^ 2)) +
        sigma⁻¹ * (Cd2 * Aw * ((volume P).toReal * Gg ^ 2)) := by
    have hsinv : (0 : ℝ) ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
    have hexp : (volume cell).toReal *
        (sigma * (vecNormSq (cubeAverageVec (originCube d k)
              (fun y ↦ h.grad (y + c))) +
            P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k)
              sOrder.1 (fun y ↦ h.grad (y + c))) ^ 2) +
          sigma⁻¹ * (P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo
            (originCube d k) sOrder.1 (fun y ↦ -g (y + c))) ^ 2)) =
        sigma * ((volume cell).toReal *
            vecNormSq (cubeAverageVec (originCube d k)
              (fun y ↦ h.grad (y + c)))) +
          sigma * ((volume cell).toReal *
            (P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k)
              sOrder.1 (fun y ↦ h.grad (y + c))) ^ 2)) +
          sigma⁻¹ * ((volume cell).toReal *
            (P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k)
              sOrder.1 (fun y ↦ -g (y + c))) ^ 2)) := by ring
    rw [hexp]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact mul_le_mul_of_nonneg_left hVcMn hsigma.le
    · exact mul_le_mul_of_nonneg_left hVcBh hsigma.le
    · exact mul_le_mul_of_nonneg_left hVcBg hsinv
  -- unnormalize
  have hintcell : (∫ p in cell, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
      vecNormSq (u.grad p)) =
      (volume cell).toReal * normalizedSetAverage cell
        (fun y ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
          vecNormSq (u.grad y)) := by
    rw [normalizedSetAverage, Homogenization.volumeAverage, ← mul_assoc,
      mul_inv_cancel₀ hcellpos.ne', one_mul]
  have hmul := mul_le_mul_of_nonneg_left hnormcell hcellpos.le
  rw [← hintcell] at hmul
  refine hmul.trans ?_
  have hR120 : (0 : ℝ) ≤ R12 := by rw [hR12def]; exact rpow_three_nonneg _
  have hsinv : (0 : ℝ) ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
  have hCbd0 : (0 : ℝ) ≤ CA + CH * (Cd2 + 1) + 1 := by positivity
  have hCAle : CA ≤ CA + CH * (Cd2 + 1) + 1 := by nlinarith only [hCH, hCd20]
  have hCHle : CH ≤ CA + CH * (Cd2 + 1) + 1 := by nlinarith only [hCA, hCH, hCd20]
  have hCHCd2le : CH * Cd2 ≤ CA + CH * (Cd2 + 1) + 1 := by
    nlinarith only [hCA, hCH, hCd20]
  have hs412 : Real.rpow sOrder.1 (-4 : ℝ) ≤ Real.rpow sOrder.1 (-12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hs0 (by linarith only [hs4]) (by norm_num)
  have hVp0 : (0 : ℝ) ≤ (volume P).toReal := hPpos.le
  -- the feedback leg
  have hA : (volume cell).toReal * (1 / (16 * (28 : ℝ) ^ d) *
      volumeAverage P (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
        vecNormSq (u.grad p))) ≤ 1 / (16 * (28 : ℝ) ^ d) * Ipar := by
    have hstep := mul_le_mul_of_nonneg_left hVcEu
      (by positivity : (0 : ℝ) ≤ 1 / (16 * (28 : ℝ) ^ d))
    calc (volume cell).toReal * (1 / (16 * (28 : ℝ) ^ d) *
          volumeAverage P (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
            vecNormSq (u.grad p)))
        = 1 / (16 * (28 : ℝ) ^ d) * ((volume cell).toReal *
            volumeAverage P (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p))) := by ring
      _ ≤ 1 / (16 * (28 : ℝ) ^ d) * Ipar := hstep
  -- the oscillation leg
  have hSZ0 : (0 : ℝ) ≤ CA * R4 * (sigma * Z) := by positivity
  have hOscInt0 : (0 : ℝ) ≤ R4 * (sigma * Z * Iosc) := by positivity
  have hB : (volume cell).toReal * (CA * R4 * (sigma * Z *
      normalizedL2SqOnSet (openCubeSet (originCube d k))
        (fun y ↦ u.toFun (y + c) - c0))) ≤
      (CA + CH * (Cd2 + 1) + 1) * R4 * (sigma * Z * Iosc) := by
    calc (volume cell).toReal * (CA * R4 * (sigma * Z *
          normalizedL2SqOnSet (openCubeSet (originCube d k))
            (fun y ↦ u.toFun (y + c) - c0)))
        = CA * R4 * (sigma * Z) * ((volume cell).toReal *
            normalizedL2SqOnSet (openCubeSet (originCube d k))
              (fun y ↦ u.toFun (y + c) - c0)) := by ring
      _ ≤ CA * R4 * (sigma * Z) * Iosc :=
          mul_le_mul_of_nonneg_left hVcN0 hSZ0
      _ = CA * (R4 * (sigma * Z * Iosc)) := by ring
      _ ≤ (CA + CH * (Cd2 + 1) + 1) * (R4 * (sigma * Z * Iosc)) :=
          mul_le_mul_of_nonneg_right hCAle hOscInt0
      _ = (CA + CH * (Cd2 + 1) + 1) * R4 * (sigma * Z * Iosc) := by ring
  -- the three datum legs
  have hC : (volume cell).toReal * (CH * R12 *
      (sigma * (vecNormSq (cubeAverageVec (originCube d k)
            (fun y ↦ h.grad (y + c))) +
          P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k)
            sOrder.1 (fun y ↦ h.grad (y + c))) ^ 2) +
        sigma⁻¹ * (P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo
          (originCube d k) sOrder.1 (fun y ↦ -g (y + c))) ^ 2))) ≤
      (CA + CH * (Cd2 + 1) + 1) * R4 *
          (E8 * (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
            ((volume P).toReal * Gg ^ 2)) +
        (CA + CH * (Cd2 + 1) + 1) * R4 *
          (E8 * (sigma * Real.rpow sOrder.1 (-4 : ℝ) *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
            ((volume P).toReal * Gh ^ 2)) +
        (CA + CH * (Cd2 + 1) + 1) * R4 * (E8 * sigma * Idat) := by
    have hCH0 : (0 : ℝ) ≤ CH * R12 := mul_nonneg hCH hR120
    have step1 : (volume cell).toReal * (CH * R12 *
        (sigma * (vecNormSq (cubeAverageVec (originCube d k)
              (fun y ↦ h.grad (y + c))) +
            P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k)
              sOrder.1 (fun y ↦ h.grad (y + c))) ^ 2) +
          sigma⁻¹ * (P3 * (scaleNormalizedPositiveBesovVectorSeminormTwo
            (originCube d k) sOrder.1 (fun y ↦ -g (y + c))) ^ 2))) ≤
        CH * R12 * (sigma * Idat +
          sigma * (Cd2 * Aw * ((volume P).toReal * Gh ^ 2)) +
          sigma⁻¹ * (Cd2 * Aw * ((volume P).toReal * Gg ^ 2))) := by
      calc (volume cell).toReal * (CH * R12 * _)
          = (CH * R12) * ((volume cell).toReal * _) := by ring
        _ ≤ (CH * R12) * (sigma * Idat +
              sigma * (Cd2 * Aw * ((volume P).toReal * Gh ^ 2)) +
              sigma⁻¹ * (Cd2 * Aw * ((volume P).toReal * Gg ^ 2))) :=
            mul_le_mul_of_nonneg_left hVcDat hCH0
    refine step1.trans ?_
    have e1 : CH * R12 * (sigma * Idat) ≤
        (CA + CH * (Cd2 + 1) + 1) * R4 * (E8 * sigma * Idat) := by
      have hnn : (0 : ℝ) ≤ R12 * (sigma * Idat) :=
        mul_nonneg hR120 (mul_nonneg hsigma.le hIdat0)
      calc CH * R12 * (sigma * Idat) = CH * (R12 * (sigma * Idat)) := by ring
        _ ≤ (CA + CH * (Cd2 + 1) + 1) * (R12 * (sigma * Idat)) :=
            mul_le_mul_of_nonneg_right hCHle hnn
        _ = (CA + CH * (Cd2 + 1) + 1) * R4 * (E8 * sigma * Idat) := by
            rw [← hR4E8]; ring
    have e2 : CH * R12 * (sigma * (Cd2 * Aw * ((volume P).toReal * Gh ^ 2))) ≤
        (CA + CH * (Cd2 + 1) + 1) * R4 *
          (E8 * (sigma * Real.rpow sOrder.1 (-4 : ℝ) *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
            ((volume P).toReal * Gh ^ 2)) := by
      have hnn : (0 : ℝ) ≤ R12 * (sigma * Aw * ((volume P).toReal * Gh ^ 2)) := by
        refine mul_nonneg hR120 (mul_nonneg (mul_nonneg hsigma.le hAw0) ?_)
        exact mul_nonneg hVp0 (sq_nonneg _)
      calc CH * R12 * (sigma * (Cd2 * Aw * ((volume P).toReal * Gh ^ 2)))
          = (CH * Cd2) * (R12 * (sigma * Aw * ((volume P).toReal * Gh ^ 2))) := by
            ring
        _ ≤ (CA + CH * (Cd2 + 1) + 1) *
              (R12 * (sigma * Aw * ((volume P).toReal * Gh ^ 2))) :=
            mul_le_mul_of_nonneg_right hCHCd2le hnn
        _ = (CA + CH * (Cd2 + 1) + 1) * R4 *
              (E8 * (sigma * Real.rpow sOrder.1 (-4 : ℝ) *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
                ((volume P).toReal * Gh ^ 2)) := by
            rw [← hR4E8, hAwdef]; ring
    have e3 : CH * R12 * (sigma⁻¹ * (Cd2 * Aw * ((volume P).toReal * Gg ^ 2))) ≤
        (CA + CH * (Cd2 + 1) + 1) * R4 *
          (E8 * (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
            ((volume P).toReal * Gg ^ 2)) := by
      have hVG : (0 : ℝ) ≤ (volume P).toReal * Gg ^ 2 :=
        mul_nonneg hVp0 (sq_nonneg _)
      have hnn : (0 : ℝ) ≤ R12 * (sigma⁻¹ * Aw * ((volume P).toReal * Gg ^ 2)) :=
        mul_nonneg hR120 (mul_nonneg (mul_nonneg hsinv hAw0) hVG)
      have hAwle : Aw ≤ Real.rpow sOrder.1 (-12 : ℝ) *
          Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) := by
        rw [hAwdef]
        exact mul_le_mul_of_nonneg_right hs412 (rpow_three_nonneg _)
      calc CH * R12 * (sigma⁻¹ * (Cd2 * Aw * ((volume P).toReal * Gg ^ 2)))
          = (CH * Cd2) * (R12 * (sigma⁻¹ * Aw * ((volume P).toReal * Gg ^ 2))) := by
            ring
        _ ≤ (CA + CH * (Cd2 + 1) + 1) *
              (R12 * (sigma⁻¹ * Aw * ((volume P).toReal * Gg ^ 2))) :=
            mul_le_mul_of_nonneg_right hCHCd2le hnn
        _ ≤ (CA + CH * (Cd2 + 1) + 1) *
              (R12 * (sigma⁻¹ * (Real.rpow sOrder.1 (-12 : ℝ) *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
                ((volume P).toReal * Gg ^ 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCbd0
            refine mul_le_mul_of_nonneg_left ?_ hR120
            refine mul_le_mul_of_nonneg_right ?_ hVG
            exact mul_le_mul_of_nonneg_left hAwle hsinv
        _ = (CA + CH * (Cd2 + 1) + 1) * R4 *
              (E8 * (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
                ((volume P).toReal * Gg ^ 2)) := by
            rw [← hR4E8]; ring
    have hsplit2 : CH * R12 * (sigma * Idat +
        sigma * (Cd2 * Aw * ((volume P).toReal * Gh ^ 2)) +
        sigma⁻¹ * (Cd2 * Aw * ((volume P).toReal * Gg ^ 2))) =
        CH * R12 * (sigma * Idat) +
          CH * R12 * (sigma * (Cd2 * Aw * ((volume P).toReal * Gh ^ 2))) +
          CH * R12 * (sigma⁻¹ * (Cd2 * Aw * ((volume P).toReal * Gg ^ 2))) := by
      ring
    rw [hsplit2]
    linarith only [e1, e2, e3]
  have hBudnn : (0 : ℝ) ≤ (CA + CH * (Cd2 + 1) + 1) * ((3 : ℝ) ^ (k - 2)) ^ d *
      ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 *
      harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g := by
    have hb := harmonicPhysicalFourBudgets_nonneg M L m n z x omega hs0
      (Section6ExcessDecay.tailAverage_nonneg M L (n + 2) omega _) u h g
    have h1 : (0 : ℝ) ≤ (CA + CH * (Cd2 + 1) + 1) * ((3 : ℝ) ^ (k - 2)) ^ d *
        ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 := by positivity
    exact mul_nonneg h1 hb
  have hVcsplit : ∀ X Y W : ℝ, (volume cell).toReal * (X + Y + W) =
      (volume cell).toReal * X + (volume cell).toReal * Y +
        (volume cell).toReal * W := by
    intro X Y W; ring
  rw [hVcsplit]
  have hexpand : (CA + CH * (Cd2 + 1) + 1) * R4 *
      ((sigma * Z * Iosc) +
        E8 * (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
          Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
          ((volume P).toReal * Gg ^ 2) +
        E8 * (sigma * Real.rpow sOrder.1 (-4 : ℝ) *
          Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
          ((volume P).toReal * Gh ^ 2) +
        E8 * sigma * Idat) =
      (CA + CH * (Cd2 + 1) + 1) * R4 * (sigma * Z * Iosc) +
        ((CA + CH * (Cd2 + 1) + 1) * R4 *
            (E8 * (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
              ((volume P).toReal * Gg ^ 2)) +
          (CA + CH * (Cd2 + 1) + 1) * R4 *
            (E8 * (sigma * Real.rpow sOrder.1 (-4 : ℝ) *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
              ((volume P).toReal * Gh ^ 2)) +
          (CA + CH * (Cd2 + 1) + 1) * R4 * (E8 * sigma * Idat)) := by ring
  linarith only [hA, hB, hC, hBudnn, hexpand.le, hexpand.ge]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
