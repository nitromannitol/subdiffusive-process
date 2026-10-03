module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowResidualCorrector
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowCompetitorASD
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryGoodEventWeightedCutoff

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The projected parent is the translate of the origin cube of its scale. -/
theorem translatedCube_eq_translateSet (d : ℕ) (k : ℤ) (c : Vec d) :
    translatedCube d k c = translateSet c (openCubeSet (originCube d k)) := by
  rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]


/-- Parent-level coefficient-energy triangle inequality. -/
theorem localizedCoeffEnergyValue_parent_sub_le_two_mul_add
    {Q : TriadicCube d} {a : CoeffFamily d}
    (u v : H1Function (openCubeSet Q)) :
    localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) (u - v) ≤
      2 * localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) u +
        2 * localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v := by
  have h := cubeAverage_coefficientEnergyDensity_h1Sub_le_two_mul_add Q a u v
  rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      Set.Subset.rfl (u - v),
    localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      Set.Subset.rfl u,
    localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      Set.Subset.rfl v,
    volumeAverage_openCubeSet_eq_cubeAverage, volumeAverage_openCubeSet_eq_cubeAverage,
    volumeAverage_openCubeSet_eq_cubeAverage]
  exact h


omit [NeZero d] in
/-- Averages on a projected parent are averages of the translated integrand on
the origin cube of the same scale. -/
theorem volumeAverage_translatedCube_eq_of_eq_on (k : ℤ) (c : Vec d)
    {F G : Vec d → ℝ}
    (hFG : ∀ p ∈ translatedCube d k c, F p = G (p - c)) :
    volumeAverage (translatedCube d k c) F =
      volumeAverage (openCubeSet (originCube d k)) G := by
  rw [translatedCube_eq_translateSet, Ch01.volumeAverage_translateSet_eq_comp_addRight]
  refine volumeAverage_eq_of_ae_eq ?_
  filter_upwards [self_mem_ae_restrict
    (measurableSet_openCubeSet (originCube d k))] with y hy
  have hmem : y + c ∈ translatedCube d k c := by
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    have : y + c - c = y := by abel
    rw [this]
    simpa [cube] using hy
  have := hFG (y + c) hmem
  have hyc : y + c - c = y := by abel
  rw [hyc] at this
  exact this

omit [NeZero d] in
/-- Averages agree when the integrands agree on the (measurable) window. -/
theorem volumeAverage_congr_on {W : Set (Vec d)} (hW : MeasurableSet W)
    {F G : Vec d → ℝ} (hFG : ∀ p ∈ W, F p = G p) :
    volumeAverage W F = volumeAverage W G := by
  refine volumeAverage_eq_of_ae_eq ?_
  filter_upwards [self_mem_ae_restrict hW] with y hy
  exact hFG y hy


/-- **The competitor-centred residual mean, priced by the boundary tile family.**

The physical residual `u - v` is glued into a genuine `H¹₀(𝔠_m)` function by
`StepRowResidualCorrector.exists_stepRowResidualCorrector` and handed to
`WindowSummationBoundaryCellPrice.exists_windowSummation_projectedBoundaryCellPrice`.
Its energy input splits into the solution's own parent energy and the
*competitor's* parent energy — never the datum's — and its oscillation input
splits into the solution's parent oscillation and the competitor's.

Everything is stated in the translated frame of the projected parent. -/
theorem exists_stepRowResidualMeanPrice_atScale (d : ℕ) [NeZero d] :
    ∃ Cface : ℝ, 0 < Cface ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ),
        s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L n m : ℕ), n + 2 ≤ L →
      ∀ k : ℤ, k ≤ (m : ℤ) → k ≤ (n : ℤ) - 2 →
      ∀ (q x z : Vec d) (rad : ℝ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ boundaryWindow d (m : ℤ) x rad →
        rad ≤ 4 * (3 : ℝ) ^ n / 9 →
        ¬ translatedCube d (k - 1) q ⊆ cube d (m : ℤ) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (u0 h0 : H1Function (openCubeSet (originCube d k)))
        (r : H10Function (openCubeSet (originCube d k))) (c0 : ℝ) (j : ℕ),
        HasZeroTraceDifferenceOn (openCubeSet (originCube d (m : ℤ))) u h →
        (∀ y, u0.toFun y =
          u.toFun (y + Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) →
        (∀ y, u0.grad y =
          u.grad (y + Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) →
        (∀ y, h0.toFun y =
          h.toFun (y + Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) →
        (∀ y, h0.grad y =
          h.grad (y + Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) →
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample c omega)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        let kappa := windowSummationTileScale k j
        volumeAverage (openCubeSet Q)
            (fun y ↦ u0.toFun y - (h0 + r.toH1Function).toFun y) ^ 2 ≤
          Cface * (3 : ℝ) ^
                (s / 4 * (((((n : ℤ) + 2 - kappa).toNat : ℕ)) : ℝ)) *
              sigma⁻¹ * ((3 : ℝ) ^ kappa) ^ 2 *
              (windowSummationTileCount j : ℝ) *
              (2 * localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q) u0 +
                2 * localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q)
                    (h0 + r.toH1Function)) +
            2 * ((2 : ℝ) ^ d * (windowSummationTileCount j : ℝ)) *
              (2 * normalizedL2SqOnSet (openCubeSet Q)
                    (fun y ↦ u0.toFun y - c0) +
                2 * normalizedL2SqOnSet (openCubeSet Q)
                    (fun y ↦ (h0 + r.toH1Function).toFun y -
                      volumeAverage (openCubeSet Q)
                        (h0 + r.toH1Function).toFun)) := by
  obtain ⟨Cface, hCface, hprice⟩ :=
    exists_windowSummation_projectedBoundaryCellPrice d
  refine ⟨Cface, hCface, ?_⟩
  intro M s hs L n m hnL k hkm hkn q x z rad omega hx hq hrad hnot hgood
    u h u0 h0 r c0 j hzt hu0 hu0g hh0 hh0g
  dsimp only
  set c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k with hcdef
  set A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
    with hAdef
  set sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set v : H1Function (openCubeSet (originCube d k)) := h0 + r.toH1Function with hvdef
  set cv : ℝ := volumeAverage (openCubeSet (originCube d k)) v.toFun with hcvdef
  have hPsub : translatedCube d k c ⊆ cube d (m : ℤ) :=
    Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hkm
  obtain ⟨rho, hval, hgrad, _ho1, _ho2⟩ :=
    exists_stepRowResidualCorrector hPsub hzt r
  have hraw := hprice M s hs L n hnL (m : ℤ) k q x z rad omega hkm hkn hx hq
    hrad hnot hgood rho j
  dsimp only at hraw
  rw [← hcdef] at hraw
  set f : Vec d → ℝ :=
    zeroExtend (openCubeSet (originCube d (m : ℤ))) rho.toH1Function.toFun
    with hfdef
  set en : Vec d → ℝ := fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
    vecNormSq (rho.grad p) with hendef
  have hPmeas : MeasurableSet (translatedCube d k c) :=
    (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube d k
      c).isOpen.measurableSet
  have hPpos : 0 < (volume (translatedCube d k c)).toReal :=
    volume_translatedCube_toReal_pos k c
  have hPtop : volume (translatedCube d k c) ≠ ⊤ := volume_translatedCube_ne_top k c
  have hPV : translatedCube d k c ⊆ openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    simpa [cube] using hPsub hp
  -- (a) the mean of the glued residual is the competitor-centred residual mean
  have hmeanEq : averageOn (translatedCube d k c) f =
      volumeAverage (openCubeSet (originCube d k)) (fun y ↦ u0.toFun y - v.toFun y) := by
    show volumeAverage (translatedCube d k c) f = _
    refine volumeAverage_translatedCube_eq_of_eq_on k c ?_
    intro p hp
    have hfp : f p = rho.toH1Function.toFun p := by
      rw [hfdef]
      exact Set.indicator_of_mem (hPV hp) _
    rw [hfp, hval p hp, hvdef]
    show _ = u0.toFun (p - c) - (h0.toFun (p - c) + r.toH1Function.toFun (p - c))
    rw [hu0 (p - c), hh0 (p - c), show p - c + c = p by abel]
    ring
  -- (b) the energy of the glued residual is the parent energy of `u0 - v`
  have hEnEq : averageOn (translatedCube d k c) en =
      localizedCoeffEnergyValue (openCubeSet (originCube d k)) (A.coeffOn (originCube d k)) (u0 - v) := by
    have htr := localizedCoeffEnergyValue_aCutoffFamily_eq_translate
      M L omega (originCube d k) c (openCubeSet (originCube d k)) (u0 - v)
      (fun p ↦ (u0 - v).grad (p - c)) (by intro y; simp)
    show volumeAverage (translatedCube d k c) en = _
    rw [htr, ← translatedCube_eq_translateSet]
    refine volumeAverage_congr_on hPmeas ?_
    intro p hp
    rw [hendef]
    have hg : rho.toH1Function.grad p = (u0 - v).grad (p - c) := by
      rw [hgrad p hp]
      rw [H1Function.sub_grad, hvdef, H1Function.add_grad]
      simp only []
      rw [hu0g (p - c), hh0g (p - c), show p - c + c = p by abel]
      funext i
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    show SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
        vecNormSq (rho.toH1Function.grad p) = _
    rw [hg]
  -- (c) the oscillation of the glued residual
  have hfint := windowSummation_zeroExtend_integrableOn (m : ℤ) rho hPmeas
  have hminim := Section6TheoremC.normalizedL2On_sub_averageOn_le
    (W := translatedCube d k c) (f := f) (c0 - cv) hPpos hPtop hfint.1 hfint.2
  have hosc0 : 0 ≤ normalizedL2On (translatedCube d k c)
      (fun p ↦ f p - averageOn (translatedCube d k c) f) :=
    Section6Iteration.normalizedL2On_nonneg _ _
  have hoscSq := pow_le_pow_left₀ hosc0 hminim 2
  have hshift : normalizedL2On (translatedCube d k c)
      (fun p ↦ f p - (c0 - cv)) ^ 2 ≤
      2 * normalizedL2SqOnSet (openCubeSet (originCube d k)) (fun y ↦ u0.toFun y - c0) +
        2 * normalizedL2SqOnSet (openCubeSet (originCube d k)) (fun y ↦ v.toFun y - cv) := by
    have hid : normalizedL2On (translatedCube d k c)
        (fun p ↦ f p - (c0 - cv)) ^ 2 =
        volumeAverage (translatedCube d k c) (fun p ↦ (f p - (c0 - cv)) ^ 2) :=
      Section6Iteration.normalizedL2On_sq _ _
    have htrans : volumeAverage (translatedCube d k c)
        (fun p ↦ (f p - (c0 - cv)) ^ 2) =
        normalizedL2SqOnSet (openCubeSet (originCube d k))
          (fun y ↦ (u0.toFun y - c0) - (v.toFun y - cv)) := by
      refine volumeAverage_translatedCube_eq_of_eq_on k c ?_
      intro p hp
      have hfp : f p = rho.toH1Function.toFun p := by
        rw [hfdef]
        exact Set.indicator_of_mem (hPV hp) _
      have hres : rho.toH1Function.toFun p = u0.toFun (p - c) - v.toFun (p - c) := by
        rw [hval p hp, hvdef]
        show _ = u0.toFun (p - c) - (h0.toFun (p - c) + r.toH1Function.toFun (p - c))
        rw [hu0 (p - c), hh0 (p - c), show p - c + c = p by abel]
        ring
      rw [hfp, hres]
      show _ = ((u0.toFun (p - c) - c0) - (v.toFun (p - c) - cv)) ^ 2
      ring
    rw [hid, htrans]
    have hmu : MemLp (fun y ↦ u0.toFun y - c0) 2
        (volume.restrict (openCubeSet (originCube d k))) := u0.memL2.sub (memLp_const c0)
    have hmv : MemLp (fun y ↦ v.toFun y - cv) 2
        (volume.restrict (openCubeSet (originCube d k))) := v.memL2.sub (memLp_const cv)
    exact normalizedL2SqOnSet_sub_le_two_mul_add hmu hmv
  -- assembly
  have hsplitE : localizedCoeffEnergyValue (openCubeSet (originCube d k)) (A.coeffOn (originCube d k)) (u0 - v) ≤
      2 * localizedCoeffEnergyValue (openCubeSet (originCube d k)) (A.coeffOn (originCube d k)) u0 +
        2 * localizedCoeffEnergyValue (openCubeSet (originCube d k)) (A.coeffOn (originCube d k)) v :=
    localizedCoeffEnergyValue_parent_sub_le_two_mul_add u0 v
  have hcoefE : (0 : ℝ) ≤ Cface * (3 : ℝ) ^
        (s / 4 * (((((n : ℤ) + 2 - windowSummationTileScale k j).toNat : ℕ)) : ℝ)) *
      sigma⁻¹ * ((3 : ℝ) ^ windowSummationTileScale k j) ^ 2 *
      (windowSummationTileCount j : ℝ) := by
    have hsigma : 0 < sigma := by
      rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
        ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
      exact tailCoefficientCubeAverage_pos M L (n + 2)
        (translatePotentialSample z omega)
    have h1 : (0 : ℝ) ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
    positivity
  have hcoefO : (0 : ℝ) ≤ 2 * ((2 : ℝ) ^ d * (windowSummationTileCount j : ℝ)) := by
    positivity
  nth_rewrite 1 [hmeanEq] at hraw
  refine hraw.trans (add_le_add ?_ ?_)
  · refine mul_le_mul_of_nonneg_left ?_ hcoefE
    rw [hEnEq]
    exact hsplitE
  · exact mul_le_mul_of_nonneg_left (hoscSq.trans hshift) hcoefO

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
