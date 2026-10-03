module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.WindowSummationProjectedParentTiles

@[expose] public section

/-!
# Boundary price on one projected window cell

This is the signed composition of the flush-face choice, the projected-parent
tile constructor, and the two physical tile-family estimates.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

/-- **Per-cell boundary price.**  At any chosen tile depth `j`, the residual
mean on a projected boundary parent is bounded by its coefficient energy on
that parent.  Both the energy feedback and the parent oscillation carry the
single volume loss `3^j`; the tile scale retains its gain `3^(2(kp-j))`. -/
theorem exists_windowSummation_projectedBoundaryCellPrice
    (d : ℕ) [NeZero d] :
    ∃ Cface : ℝ, 0 < Cface ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, n + 2 ≤ L →
      ∀ (m kp : ℤ) (q x z : Vec d) (r : ℝ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        kp ≤ m → kp ≤ (n : ℤ) - 2 →
        x ∈ truncatedCube d m ((n : ℤ) - 3) z →
        q ∈ boundaryWindow d m x r →
        r ≤ 4 * (3 : ℝ) ^ n / 9 →
        ¬ translatedCube d (kp - 1) q ⊆ cube d m →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
      ∀ (rho : H10Function (openCubeSet (originCube d m))) (j : ℕ),
        let c := Section6ExcessDecay.wellPlacedCentre q m kp
        let P := translatedCube d kp c
        let f := zeroExtend (openCubeSet (originCube d m)) rho.toH1Function.toFun
        let energy := fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (rho.grad p)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        averageOn P f ^ 2 ≤
          Cface * (3 : ℝ) ^
              (s / 4 * (((((n : ℤ) + 2 -
                windowSummationTileScale kp j).toNat : ℕ)) : ℝ)) *
              sigma⁻¹ * ((3 : ℝ) ^ windowSummationTileScale kp j) ^ 2 *
              windowSummationTileCount j * averageOn P energy +
            2 * ((2 : ℝ) ^ d * windowSummationTileCount j) *
              normalizedL2On P (fun p ↦ f p - averageOn P f) ^ 2 := by
  obtain ⟨Cup, hCup, hcapUp⟩ :=
    sq_averageOn_le_tileFamily_of_boundaryTileResidualMeanCap d
  obtain ⟨Clow, hClow, hcapLow⟩ :=
    windowSummation_sq_averageOn_le_lowerFaceTileFamily_of_boundaryTileResidualMeanCap d
  refine ⟨Cup + Clow, by positivity, ?_⟩
  intro M s hs L n hnL m kp q x z r omega hkp_m hkp_n hx hq hr hnot hgood rho j
  dsimp only
  set c : Vec d := Section6ExcessDecay.wellPlacedCentre q m kp with hc
  set P : Set (Vec d) := translatedCube d kp c with hP
  let V : Set (Vec d) := openCubeSet (originCube d m)
  set f : Vec d → ℝ := zeroExtend V rho.toH1Function.toFun with hf
  set e : Vec d → ℝ := fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
    vecNormSq (rho.grad p) with he
  set kappa : ℤ := windowSummationTileScale kp j with hkappa
  set Mt : ℕ := windowSummationTileCount j with hMt
  set b : Vec d := windowSummationParentLowerCorner c kp with hb
  have hVmeas : MeasurableSet V := by
    dsimp only [V]
    exact measurableSet_openCubeSet _
  have hPsubV : P ⊆ V := by
    rw [hP, hc]
    dsimp only [V]
    exact Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hkp_m
  have hPtop : volume P ≠ ⊤ := by
    rw [hP]
    exact volume_translatedCube_ne_top kp c
  have hPpos : 0 < (volume P).toReal := by
    rw [hP]
    exact volume_translatedCube_toReal_pos kp c
  have hPmeas : MeasurableSet P := by
    rw [hP]
    exact (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube d kp c).isOpen.measurableSet
  have heP : IntegrableOn e P := by
    rw [he]
    exact (integrableOn_aCutoff_energy M L omega (originCube d m)
      rho.toH1Function).mono_set hPsubV
  have hfP : IntegrableOn f P := by
    rw [hf]
    exact (windowSummation_zeroExtend_integrableOn m rho hPmeas).1
  have hf2P : IntegrableOn (fun p ↦ f p ^ 2) P := by
    rw [hf]
    exact (windowSummation_zeroExtend_integrableOn m rho hPmeas).2
  obtain ⟨j0, sig, hsig, hanchor, hside⟩ :=
    exists_windowSummation_projectedBoundaryParentTileFamily
      hkp_m hkp_n hx hq hr hnot j
  rcases hside with hupper | hlower
  · rcases hupper with ⟨hsig1, hface, houtside, hslab, hratio⟩
    subst sig
    simp only [ite_true] at hanchor
    set a : ℝ := c j0 + (3 : ℝ) ^ kp / 2 with ha
    set W : Set (Vec d) := faceDoubledSlab j0 a b ((3 : ℝ) ^ kappa) Mt with hW
    have hWmeas : MeasurableSet W := by
      rw [hW]
      exact MeasurableSet.iUnion fun idx ↦ measurableSet_axisCube _ _
    have hfW : IntegrableOn f W := by
      rw [hf]
      exact (windowSummation_zeroExtend_integrableOn m rho hWmeas).1
    have henergy := windowSummation_faceDoubledSlab_zeroExtendEnergy_le_parent
      c kp j j0 a hVmeas
      (fun p ↦ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega p).le)
      (windowSummation_upperFaceDoubledSlab_inter_cube_subset_parent
        c m kp j j0 (by simpa only [c] using hface)) heP
    dsimp only at henergy
    have heW : IntegrableOn (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
        vecNormSq (zeroExtendGrad V rho.grad p)) W := by
      simpa only [W, b, kappa, Mt] using henergy.1
    have heAvg : averageOn W (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
        vecNormSq (zeroExtendGrad V rho.grad p)) ≤ Mt * averageOn P e := by
      simpa only [W, b, kappa, Mt, P, e] using henergy.2
    have hraw := hcapUp M s hs L n hnL kappa omega z j0 a b Mt
      (by simpa only [Mt] using windowSummation_faceIndex_card_pos j0 j)
      (by simpa only [a, b, kappa, Mt, c] using hanchor) hgood V hVmeas rho
      (by simpa only [a, c, V, cube] using houtside) P
      (by simpa only [a, b, kappa, Mt, c, P] using hslab)
      hPtop hPpos hfP hf2P hfW heW
    dsimp only at hraw
    have hratio' : (volume P).toReal /
        (volume (upperFaceInnerSlab j0 a b ((3 : ℝ) ^ kappa) Mt)).toReal ≤
          (2 : ℝ) ^ d * Mt := by
      simpa only [a, b, kappa, Mt, c, P] using hratio
    set K : ℝ := (3 : ℝ) ^
        (s / 4 * (((((n : ℤ) + 2 - kappa).toNat : ℕ)) : ℝ)) *
        (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))⁻¹ *
        ((3 : ℝ) ^ kappa) ^ 2 with hK
    set E : ℝ := averageOn P e with hE
    set O : ℝ := normalizedL2On P (fun p ↦ f p - averageOn P f) ^ 2 with hO
    have hsigma0 : 0 ≤ tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z) :=
      Section6ExcessDecay.tailAverage_nonneg M L (n + 2) omega _
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have hE0 : 0 ≤ E := by
      rw [hE, averageOn, volumeAverage]
      refine mul_nonneg (by positivity) (setIntegral_nonneg hPmeas ?_)
      intro p _
      change 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (rho.grad p)
      exact mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega p).le
        (vecNormSq_nonneg _)
    have hO0 : 0 ≤ O := by rw [hO]; positivity
    have henergyBound : Cup * K *
        averageOn W (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (zeroExtendGrad V rho.grad p)) ≤
        (Cup + Clow) * K * (Mt * E) := by
      calc
        Cup * K * averageOn W (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
            vecNormSq (zeroExtendGrad V rho.grad p)) ≤
            Cup * K * (Mt * E) :=
          mul_le_mul_of_nonneg_left (by simpa only [hE, hMt] using heAvg)
            (mul_nonneg hCup.le hK0)
        _ ≤ (Cup + Clow) * K * (Mt * E) := by
          have hc : Cup ≤ Cup + Clow := by linarith
          have hfactor : 0 ≤ K * (Mt * E) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hc hfactor]
    have hoscBound : 2 * ((volume P).toReal /
        (volume (upperFaceInnerSlab j0 a b ((3 : ℝ) ^ kappa) Mt)).toReal) * O ≤
        2 * ((2 : ℝ) ^ d * Mt) * O := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio' (by norm_num)) hO0
    have hraw' : averageOn P f ^ 2 ≤ Cup * K *
        averageOn W (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (zeroExtendGrad V rho.grad p)) +
        2 * ((volume P).toReal /
          (volume (upperFaceInnerSlab j0 a b ((3 : ℝ) ^ kappa) Mt)).toReal) * O := by
      simpa only [hf, hK, hW, hO, mul_assoc] using hraw
    have hlocal := hraw'.trans (add_le_add henergyBound hoscBound)
    convert hlocal using 1
    all_goals dsimp only [f, e, K, E, O, kappa, Mt, V]
    all_goals ring
  · rcases hlower with ⟨hsigm, hface, houtside, hslab, hratio⟩
    subst sig
    simp only [if_neg (by norm_num : (-1 : ℝ) ≠ 1)] at hanchor
    set a : ℝ := c j0 - (3 : ℝ) ^ kp / 2 with ha
    set W : Set (Vec d) := faceDoubledSlab j0 a b ((3 : ℝ) ^ kappa) Mt with hW
    have hWmeas : MeasurableSet W := by
      rw [hW]
      exact MeasurableSet.iUnion fun idx ↦ measurableSet_axisCube _ _
    have hfW : IntegrableOn f W := by
      rw [hf]
      exact (windowSummation_zeroExtend_integrableOn m rho hWmeas).1
    have henergy := windowSummation_faceDoubledSlab_zeroExtendEnergy_le_parent
      c kp j j0 a hVmeas
      (fun p ↦ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega p).le)
      (windowSummation_lowerFaceDoubledSlab_inter_cube_subset_parent
        c m kp j j0 (by simpa only [c] using hface)) heP
    dsimp only at henergy
    have heW : IntegrableOn (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
        vecNormSq (zeroExtendGrad V rho.grad p)) W := by
      simpa only [W, b, kappa, Mt] using henergy.1
    have heAvg : averageOn W (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
        vecNormSq (zeroExtendGrad V rho.grad p)) ≤ Mt * averageOn P e := by
      simpa only [W, b, kappa, Mt, P, e] using henergy.2
    have hraw := hcapLow M s hs L n hnL kappa omega z j0 a b Mt
      (by simpa only [Mt] using windowSummation_faceIndex_card_pos j0 j)
      (by simpa only [a, b, kappa, Mt, c] using hanchor) hgood V hVmeas rho
      (by simpa only [a, c, V, cube] using houtside) P
      (by simpa only [a, b, kappa, Mt, c, P] using hslab)
      hPtop hPpos hfP hf2P hfW heW
    dsimp only at hraw
    have hratio' : (volume P).toReal /
        (volume (faceInnerSlab j0 a b ((3 : ℝ) ^ kappa) Mt)).toReal ≤
          (2 : ℝ) ^ d * Mt := by
      simpa only [a, b, kappa, Mt, c, P] using hratio
    set K : ℝ := (3 : ℝ) ^
        (s / 4 * (((((n : ℤ) + 2 - kappa).toNat : ℕ)) : ℝ)) *
        (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))⁻¹ *
        ((3 : ℝ) ^ kappa) ^ 2 with hK
    set E : ℝ := averageOn P e with hE
    set O : ℝ := normalizedL2On P (fun p ↦ f p - averageOn P f) ^ 2 with hO
    have hsigma0 : 0 ≤ tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z) :=
      Section6ExcessDecay.tailAverage_nonneg M L (n + 2) omega _
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have hE0 : 0 ≤ E := by
      rw [hE, averageOn, volumeAverage]
      refine mul_nonneg (by positivity) (setIntegral_nonneg hPmeas ?_)
      intro p _
      change 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (rho.grad p)
      exact mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega p).le
        (vecNormSq_nonneg _)
    have hO0 : 0 ≤ O := by rw [hO]; positivity
    have henergyBound : Clow * K *
        averageOn W (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (zeroExtendGrad V rho.grad p)) ≤
        (Cup + Clow) * K * (Mt * E) := by
      calc
        Clow * K * averageOn W (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
            vecNormSq (zeroExtendGrad V rho.grad p)) ≤
            Clow * K * (Mt * E) :=
          mul_le_mul_of_nonneg_left (by simpa only [hE, hMt] using heAvg)
            (mul_nonneg hClow.le hK0)
        _ ≤ (Cup + Clow) * K * (Mt * E) := by
          have hc : Clow ≤ Cup + Clow := by linarith
          have hfactor : 0 ≤ K * (Mt * E) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hc hfactor]
    have hoscBound : 2 * ((volume P).toReal /
        (volume (faceInnerSlab j0 a b ((3 : ℝ) ^ kappa) Mt)).toReal) * O ≤
        2 * ((2 : ℝ) ^ d * Mt) * O := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio' (by norm_num)) hO0
    have hraw' : averageOn P f ^ 2 ≤ Clow * K *
        averageOn W (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (zeroExtendGrad V rho.grad p)) +
        2 * ((volume P).toReal /
          (volume (faceInnerSlab j0 a b ((3 : ℝ) ^ kappa) Mt)).toReal) * O := by
      simpa only [hf, hK, hW, hO, mul_assoc] using hraw
    have hlocal := hraw'.trans (add_le_add henergyBound hoscBound)
    convert hlocal using 1
    all_goals dsimp only [f, e, K, E, O, kappa, Mt, V]
    all_goals ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
