
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.InteriorCellAtScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicTileEllipticity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffCellEnergy

@[expose] public section

/-!
# The interior cell at a free tile scale, at a finite cutoff

Cutoff companions of
`Section6HarmonicBoundary.exists_localTileEllipticityCaps_atScale` and
`Section6HarmonicBoundary.exists_interiorCellEnergy_le_parentPrices_atScale`:
the binders `n + 2 ≤ L` and `m ≤ L` are deleted and the good event is
`𝒢^{(L)}_{n+2,z}`.

The changed leaves are the cutoff error cap
`Section6HolderBelowCutoff.exists_section6HomogenizationError_le_of_cutoffGoodEvent`
and the scale-generic transport
`Section6CutoffHarmonic.localHomogenizationError_two_le_anchor_atScale`.  The
projected-cell readout `exists_projectedInteriorCellEnergy_readout` is
good-event free, and all the arithmetic legs of the original module are
deterministic; both are quoted unchanged.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The whole coarse ellipticity package on a tile of arbitrary scale.**

`exists_localTileEllipticityCap`  exposes only the `s/3` lower cap of
`localBoundaryEllipticityCaps_of_errorCap`; the interior cell price also needs
the upper cap `Ch02.LambdaS Q (1/2) A ≤ B σ` and the `s/6` lower ratio cap, so
this reads off all six.  It is `exists_localBoundaryEllipticityCaps_nextWindow`
with the inner cube scale left free and the loss `3^{(s/4)(n+2−k)}` made
explicit inside `tileEllipticityConst`. -/
theorem exists_localTileEllipticityCaps_atScale (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
        let Q := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        let B := tileEllipticityConst d C s ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B ∧
          sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B ∧
          Ch02.LambdaS Q (1 / 2) A ≤ B * sigma ∧
          (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * sigma⁻¹ ∧
          Ch02.lambdaS Q (s / 3) A ≤ B * sigma ∧
          Ch02.ThetaRatio Q (1 / 2) (s / 3) A ≤ B ^ (2 : ℕ) := by
  obtain ⟨C, hC, hgoodCap⟩ := exists_section6HomogenizationError_le_of_cutoffGoodEvent (d := d)
  refine ⟨3 * C, by positivity, ?_⟩
  intro M s hs L n k omega y z hcontain hgood
  dsimp only
  set Q : TriadicCube d := originCube d k with hQ
  set A := aCutoffFamily M L (translatePotentialSample y omega) with hAdef
  set sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z) with hsig
  set jj : ℝ := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) with hjj
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    rw [hsig]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using! h
  have hsection := hgoodCap M s hs L (n + 2) omega z hgood
  have hlocal := localHomogenizationError_two_le_anchor_atScale M hs L n k
    omega y z hcontain hgood
  have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
    ENNReal.toReal_nonneg
  have hE₀ : Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
      (scalarMatrix (d := d) sigma) ≤
        Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 8 * jj) * (3 * C)) := by
    refine hlocal.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    exact hsection.trans (by linarith only [hC])
  have hcaps := localBoundaryEllipticityCaps_of_errorCap Q A hs0 hs.2 hsigma hE₀
  simpa [tileEllipticityConst] using hcaps



theorem exists_interiorCellEnergy_le_parentPrices_atScale (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ k : ℤ, k ≤ (n : ℤ) - 2 →
      ∀ (z x q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ cube d (m : ℤ) →
        translatedCube d k (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) ⊆
          truncatedCube d (m : ℤ) (n : ℤ) x →
        openCubeAtScale q (k - 1) ⊆ cube d (m : ℤ) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d) (c0 : ℝ),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        let P := translatedCube d k
          (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun y => _root_.SubdiffusiveProcess.Model.aCutoff M L omega y *
              vecNormSq (u.grad y)) ≤
          K * Real.rpow (3 : ℝ)
              (2 * sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
            (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
                normalizedL2On P (fun y => u.toFun y - c0) ^ 2 +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) *
                (fractionalSeminormOn P sOrder.1 g).toReal ^ 2) := by
  obtain ⟨C, hC, hinterior⟩ := exists_projectedInteriorCellEnergy_readout d
  obtain ⟨Ct, hCt, hcaps⟩ := exists_localTileEllipticityCaps_atScale d
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set K0 : ℝ := 2 * (d : ℝ) * (192 * (d : ℝ) * Ct ^ 2 + 1) with hK0
  set Pref : ℝ := (4 * max 1 C) ^ (8 : ℕ) * 8 with hPref
  set Tdat : ℝ := (2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 with hTdat
  have hK0pos : 0 < K0 := by rw [hK0]; positivity
  have hPrefpos : 0 < Pref := by rw [hPref]; positivity
  have hmaxpos : (0 : ℝ) < max 1 Tdat := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h81 : (0 : ℝ) < (81 : ℝ) ^ d := by positivity
  refine ⟨(81 : ℝ) ^ d * Pref * K0 ^ (7 : ℕ) * max 1 Tdat,
    mul_pos (mul_pos (mul_pos h81 hPrefpos) (pow_pos hK0pos 7)) hmaxpos, ?_⟩
  intro M sOrder hs L m n hnm k hk z x q omega hz hx hq hparent hpatchPhysical hgood
    u h g c0 hdir hg hh
  dsimp only
  set c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k with hcdef
  set Q : TriadicCube d := originCube d k with hQdef
  set A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega) with hAdef
  set P : Set (Vec d) := translatedCube d k c with hPdef
  set sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set jj : ℝ := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) with hjjdef
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hjj0 : (0 : ℝ) ≤ jj := by rw [hjjdef]; positivity
  have hkm : k ≤ (m : ℤ) := by omega
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 3) z hx
  have hsigma : 0 < sigma := by
    rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z omega)
  -- geometry of the projected parent at the free cover scale
  have hPwin : P ⊆ truncatedCube d (m : ℤ) (n : ℤ) x := by
    rw [hPdef, hcdef]
    exact hparent
  have hcmem : c ∈ P := by
    rw [hPdef, Section6ExcessDecay.mem_translatedCube_iff]
    simpa using Section6ExcessDecay.zero_mem_cube d k
  have hcU : c ∈ truncatedCube d (m : ℤ) (n : ℤ) x := hPwin hcmem
  have hPdom : P ⊆ cube d (m : ℤ) := fun p hp => (hPwin hp).2
  have hPpos : 0 < (volume P).toReal := by
    rw [hPdef, translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d k)
  have hP0 : volume P ≠ 0 := (ENNReal.toReal_ne_zero.mp hPpos.ne').1
  have hPtop : volume P ≠ ⊤ := (ENNReal.toReal_ne_zero.mp hPpos.ne').2
  have hPtranslate : P = translateSet c (openCubeSet Q) := by
    rw [hPdef, hQdef, translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  have hpatch : openCubeAtScale (q - c) (k - 1) ⊆ openCubeSet Q := by
    rw [hQdef, hcdef]
    exact openCubeAtScale_wellPlaced_pullback_subset_originCube hkm hpatchPhysical
  -- the good-event cap package at the cover scale
  have hcontain := translateSet_cubeSet_originCube_subset_anchor_of_mem_nextWindow
    (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (k := k) (x := x) (y := c) (z := z)
    hk hx hcU
  obtain ⟨_hupper6, hlower6, hLam, _h4, _h5, _h6⟩ :=
    hcaps M sOrder.1 hs L n k omega c z hcontain hgood
  set Bv : ℝ := tileEllipticityConst d Ct sOrder.1 jj with hBvdef
  have hBpos : 0 < Bv := by rw [hBvdef]; exact tileEllipticityConst_pos d Ct sOrder.1 jj
  have hhalf := interiorHalfEllipticityCaps_of_sixth Q A hs0 hsigma hLam hlower6
  have hpref := caccioppoliWithRHSPrefactor_interiorHalf_le
    (Q := Q) (A := A) hC hs0 hs.2 hhalf.2.2
  -- the projected interior Caccioppoli readout, at the cover scale
  obtain ⟨g0, u0, hg0, hgLocal, hu0, _heq, hgReg, hcell⟩ :=
    hinterior M L omega m k q sOrder u h g c0 hdir hg hh hs.2 hkm hq hpatch
  -- the parent leg: no window transport, hence no volume ratio
  have hparent := normalizedL2SqOnSet_projected_le_window (m := (m : ℤ)) (k := k)
    (q := q) (U := P) u u0 c0 hu0 (by rw [hPdef, hcdef]) hPdom hPpos hPpos
  rw [div_self hPpos.ne', one_mul] at hparent
  -- the datum leg, on the parent
  have hA0 : volume (cube d (m : ℤ)) ≠ 0 := by
    rw [cube]
    have hreal : 0 < (volume (openCubeSet (originCube d (m : ℤ)))).toReal := by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos (originCube d (m : ℤ))
    exact (ENNReal.toReal_ne_zero.mp hreal.ne').1
  have hAtop : volume (cube d (m : ℤ)) ≠ ∞ := by
    rw [cube]
    exact (volume_openCubeSet_lt_top (originCube d (m : ℤ))).ne
  have hfrac : MemFractionalOn (cube d (m : ℤ)) sOrder.1 g := by
    change fractionalSeminormOn (openCubeSet (originCube d (m : ℤ))) sOrder.1 g ≠ ⊤
    rw [fractionalSeminormOn_openCubeSet_eq_guarded_of_measurable _ _ _ hg.2.aestronglyMeasurable]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hg.2.eSeminorm_lt_top.ne
  have hgfin : fractionalSeminormOn P sOrder.1 g ≠ ⊤ :=
    memFractionalOn_mono_set hPdom hA0 hAtop hP0 hfrac
  have hsource := projectedForceSeminorm_le_window Q c P sOrder g g0
    (by simpa [hQdef, hcdef] using hgLocal) hg0
    (by rw [← hPtranslate]) (by rw [← hPtranslate]; exact hP0)
    (by rw [← hPtranslate]; exact hPtop) hP0 hPtop hgfin
  rw [← hPtranslate, div_self hPpos.ne'] at hsource
  rw [cubeBesovScaleWeight_neg_originCube, Real.sqrt_one, one_mul] at hsource
  -- abbreviations for the two manuscript legs, measured on the parent
  set Gv : ℝ := (fractionalSeminormOn P sOrder.1 g).toReal with hGvdef
  set N2 : ℝ := (normalizedL2On P fun y => u.toFun y - c0) ^ 2 with hN2def
  set Leg1 : ℝ := sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) * N2 with hLeg1def
  set Leg2 : ℝ := Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
    Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) * Gv ^ 2 with hLeg2def
  have hGv0 : 0 ≤ Gv := ENNReal.toReal_nonneg
  have hN20 : 0 ≤ N2 := by rw [hN2def]; exact sq_nonneg _
  have hLeg10 : 0 ≤ Leg1 := by
    rw [hLeg1def]
    exact mul_nonneg (mul_nonneg hsigma.le (Real.rpow_nonneg (by norm_num) _)) hN20
  have hLeg20 : 0 ≤ Leg2 := by
    rw [hLeg2def]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (Real.rpow_nonneg hs0.le _) (inv_nonneg.mpr hsigma.le))
      (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg _)
  have hscaleQ : ((Q.scale : ℤ) : ℝ) = ((k : ℤ) : ℝ) := rfl
  -- the parent leg
  have hlamS : Ch02.lambdaS Q (sOrder.1 / 2) A ≤ Bv * sigma := hhalf.2.1
  have hlamInv : Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤ Bv * sigma⁻¹ := by
    rw [show Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) =
      (Ch02.lambdaS Q (sOrder.1 / 2) A)⁻¹ from Real.rpow_neg_one _]
    exact hhalf.1
  have hpar0 : 0 ≤ normalizedL2SqOnSet (openCubeSet Q) fun y => u0.toFun y - c0 :=
    normalizedL2SqOnSet_nonneg (openCubeSet Q) _ (measurableSet_openCubeSet Q)
  have hleg1 :
      Ch02.lambdaS Q (sOrder.1 / 2) A * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
          (normalizedL2SqOnSet (openCubeSet Q) fun y => u0.toFun y - c0) ≤
        Bv * Leg1 := by
    rw [hscaleQ, hLeg1def]
    have hcoef : Ch02.lambdaS Q (sOrder.1 / 2) A *
        Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) ≤
        Bv * sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hlamS (Real.rpow_nonneg (by norm_num) _)
    have hnn : 0 ≤ Bv * sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) :=
      mul_nonneg (mul_nonneg hBpos.le hsigma.le) (Real.rpow_nonneg (by norm_num) _)
    calc Ch02.lambdaS Q (sOrder.1 / 2) A * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
          (normalizedL2SqOnSet (openCubeSet Q) fun y => u0.toFun y - c0)
        ≤ Bv * sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) * N2 :=
          mul_le_mul hcoef hparent hpar0 hnn
      _ = Bv * (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) * N2) := by ring
  -- the datum leg
  have hbes0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
      (fun x => -g0 x) :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (by simpa [hQdef] using hgReg)
  have hsq := pow_le_pow_left₀ hbes0 hsource 2
  have hcoef2 : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
      Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤
      Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (Bv * sigma⁻¹) :=
    mul_le_mul_of_nonneg_left hlamInv
      (Real.rpow_nonneg (by linarith only [hs0] : (0 : ℝ) ≤ sOrder.1 / 2) _)
  have hcoef20 : 0 ≤ Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (Bv * sigma⁻¹) :=
    mul_nonneg (Real.rpow_nonneg (by linarith only [hs0]) _)
      (mul_nonneg hBpos.le (inv_nonneg.mpr hsigma.le))
  have hid := projected_source_factor_atScale
    (K := caccioppoliExactDatumConstant d) (G := Gv) k hs0
  rw [Real.sqrt_one, one_mul] at hid
  have hleg2 :
      Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
          Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1 (fun x => -g0 x) ^ 2 ≤
        Bv * (Tdat * Leg2) := by
    calc Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1 (fun x => -g0 x) ^ 2
        ≤ Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (Bv * sigma⁻¹) *
            (caccioppoliExactDatumConstant d * Real.rpow (3 : ℝ) (sOrder.1 * ((k : ℤ) : ℝ)) *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) * Gv)) ^ 2 :=
          mul_le_mul hcoef2 hsq (sq_nonneg _) hcoef20
      _ = (Bv * sigma⁻¹) * (Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            (caccioppoliExactDatumConstant d * Real.rpow (3 : ℝ) (sOrder.1 * ((k : ℤ) : ℝ)) *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) * Gv)) ^ 2) := by ring
      _ = (Bv * sigma⁻¹) * (Tdat * (Real.rpow sOrder.1 (-12 : ℝ) *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) * Gv ^ 2)) := by
          rw [hid, hTdat]
      _ = Bv * (Tdat * Leg2) := by rw [hLeg2def]; ring
  -- the two legs, absorbed into one dimension-only constant
  have hinner :
      Ch02.lambdaS Q (sOrder.1 / 2) A * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            (normalizedL2SqOnSet (openCubeSet Q) fun y => u0.toFun y - c0) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1 (fun x => -g0 x) ^ 2 ≤
        Bv * (max 1 Tdat * (Leg1 + Leg2)) := by
    have ha : Leg1 ≤ max 1 Tdat * Leg1 :=
      le_mul_of_one_le_left hLeg10 (le_max_left 1 Tdat)
    have hb : Tdat * Leg2 ≤ max 1 Tdat * Leg2 :=
      mul_le_mul_of_nonneg_right (le_max_right 1 Tdat) hLeg20
    calc _ ≤ Bv * Leg1 + Bv * (Tdat * Leg2) := add_le_add hleg1 hleg2
      _ ≤ Bv * (max 1 Tdat * Leg1) + Bv * (max 1 Tdat * Leg2) :=
          add_le_add (mul_le_mul_of_nonneg_left ha hBpos.le)
            (mul_le_mul_of_nonneg_left hb hBpos.le)
      _ = Bv * (max 1 Tdat * (Leg1 + Leg2)) := by ring
  have hinner0 :
      0 ≤ Ch02.lambdaS Q (sOrder.1 / 2) A * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            (normalizedL2SqOnSet (openCubeSet Q) fun y => u0.toFun y - c0) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1 (fun x => -g0 x) ^ 2 := by
    have hlam0 : 0 ≤ Ch02.lambdaS Q (sOrder.1 / 2) A := by
      rw [Ch02.lambdaS]
      exact Ch02.lambdaSq_finite_nonneg Q A (by linarith only [hs0]) (by norm_num)
    exact add_nonneg
      (mul_nonneg (mul_nonneg hlam0 (Real.rpow_nonneg (by norm_num) _)) hpar0)
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith only [hs0]) _)
        (Real.rpow_nonneg hlam0 _)) (sq_nonneg _))
  have hprefB : caccioppoliWithRHSPrefactor C Q A (1 / 2) (sOrder.1 / 2) ≤
      Pref * (Bv ^ (2 : ℕ)) ^ (3 : ℕ) := by
    rw [hPref]
    exact hpref
  have hprefB0 : 0 ≤ Pref * (Bv ^ (2 : ℕ)) ^ (3 : ℕ) :=
    mul_nonneg hPrefpos.le (by positivity)
  have hcombined := hcell.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hprefB hinner hinner0 hprefB0) h81.le)
  refine hcombined.trans ?_
  -- the seven powers of the tile ellipticity constant
  have hBle : Bv ≤ K0 * (3 : ℝ) ^ (sOrder.1 / 4 * jj) := by
    rw [hBvdef, hK0]
    exact tileEllipticityConst_le d hs0 hjj0
  have hpow7 : Bv ^ (7 : ℕ) ≤ K0 ^ (7 : ℕ) * Real.rpow (3 : ℝ) (2 * sOrder.1 * jj) :=
    pow_seven_le_rpow_three hBpos.le hK0pos.le hs0 hjj0 hBle
  have hsum0 : 0 ≤ (81 : ℝ) ^ d * Pref * max 1 Tdat * (Leg1 + Leg2) :=
    mul_nonneg (mul_nonneg (mul_nonneg h81.le hPrefpos.le) hmaxpos.le)
      (by linarith only [hLeg10, hLeg20])
  calc (81 : ℝ) ^ d * (Pref * (Bv ^ (2 : ℕ)) ^ (3 : ℕ) *
        (Bv * (max 1 Tdat * (Leg1 + Leg2))))
      = ((81 : ℝ) ^ d * Pref * max 1 Tdat * (Leg1 + Leg2)) * Bv ^ (7 : ℕ) := by ring
    _ ≤ ((81 : ℝ) ^ d * Pref * max 1 Tdat * (Leg1 + Leg2)) *
          (K0 ^ (7 : ℕ) * Real.rpow (3 : ℝ) (2 * sOrder.1 * jj)) :=
        mul_le_mul_of_nonneg_left hpow7 hsum0
    _ = (81 : ℝ) ^ d * Pref * K0 ^ (7 : ℕ) * max 1 Tdat *
          Real.rpow (3 : ℝ) (2 * sOrder.1 * jj) * (Leg1 + Leg2) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
