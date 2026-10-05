module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.SharpLoopApplication
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffCellEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffSharpLoop

@[expose] public section

/-!
# The interior harmonic comparison at a finite cutoff

This is the chain (`Section6HarmonicInterior/`: cover energy, weighted
energy slot, sharp loop application) re-run with the cutoff good event
`𝒢^{(L)}_{n+2,z}` and with the binder `m ≤ L` deleted.

Only two of the four inputs of `exists_interiorHarmonicComparison_le_sharpLoopBound`
mention the good event or the cutoff relation at all:

* the depth-two cell energy, replaced by
  `Section6HolderBelowCutoff.exists_interiorCellEnergy_le_manuscriptPrices_cutoff`;
* the sharp comparator loop, replaced by
  `Section6HolderBelowCutoff.exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_sharp_neZero`.

The retained PDE datum (`Section6HarmonicInterior.exists_localSourceComparisonDatum_weak_retained`)
and the force overlap slot (`exists_interiorForceOverlap_le_windowSeminorm`) are
already good-event free and are quoted unchanged, as is the frame change
`cubeAverage_coefficientEnergyDensity_aCutoffFamily_eq_translatedCube`.

**Residual `s`-power .**  The right-hand side is the same loop carrier
`flatComparatorSharpGoodEventLoopBound` as in the uncut chain, whose real
readout carries `s^{-2}` on the `𝓔` term rather than the printed `s^{-3/2}`.
Nothing in the cutoff re-run changes that: the question is inherited from the uncut comparison.

This is the harmonic-approximation clause of `l.cutoff.regularity.good.scale.estimates`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **Datum-free interior cover energy display at a finite cutoff.**  Companion
of `Section6HarmonicInterior.exists_interiorCoverEnergy_le_manuscriptPrices_weak`
on the cutoff good event, with the binder `m ≤ L` deleted. -/
theorem exists_interiorCoverEnergy_le_manuscriptPrices_cutoff (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let D := translatedCube d ((n : ℤ) - 2) y
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage D (fun q ↦
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega q * vecNormSq (u.grad q)) ≤
          K * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                normalizedL2On U
                  (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal ^ 2) := by
  obtain ⟨K, hK, hcell⟩ := exists_interiorCellEnergy_le_manuscriptPrices_cutoff d
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hnm z x y omega hz hx hD hnot hgood u g
    hweak hg
  let k : ℤ := (n : ℤ) - 2
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let B : ℝ := K *
    (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
      Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2)
  have htranslated : translateSet y (openCubeSet (originCube d k)) =
      translatedCube d k y := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  have hparent : translatedCube d k y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    have hp' : p ∈ translatedCube d ((n : ℤ) - 2) y := by
      simpa only [k] using hp
    exact (hD hp').2
  apply normalizedCutoffEnergy_translatedCube_le_of_depthTwo_cell_bounds
    M L omega u hparent B
  intro R hR
  let qR : Vec d := y + triadicCubeShift R
  have hDtranslate : translateSet y (openCubeSet (originCube d k)) ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x := by
    rw [htranslated]
    simpa only [k] using hD
  have hqR : qR ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x :=
    translated_descendantCentre_mem_of_parent_subset hR hDtranslate
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hpatch : openCubeAtScale qR ((n : ℤ) - 3) ⊆ cube d (m : ℤ) :=
    openCubeAtScale_predTwo_subset_domain_of_not_boundaryTouches
      hxDomain hqR hnot
  have hbound := hcell M sOrder hs L m n hnm z x qR omega hz hx hqR
    hpatch hgood u g hweak hg
  have hset : translateSet y (openCubeSet R) =
      truncatedCube d (m : ℤ) (k - 2) qR := by
    apply translate_descendant_openCubeSet_eq_truncatedCube hR
    rw [htranslated]
    simpa only [cube] using hparent
  rw [hset]
  simpa only [k, U, sigma, B] using hbound

/-- **The weighted-energy slot at a finite cutoff.** -/
theorem exists_interiorWeightedEnergy_le_manuscriptPrices_cutoff (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
      ∀ (u0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2)))),
        (∀ p, u0.grad p = u.grad (p + y)) →
      ∀ (s1 smid : FractionalOrder), s1.1 < smid.1 →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        Ch03.ABK26.weightedLocalSymmetricEnergyLp (originCube d ((n : ℤ) - 2))
            ((originCube d ((n : ℤ) - 2)).scale - 1) (by omega)
            ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
              (originCube d ((n : ℤ) - 2))) u0 s1 smid FiniteLpExponent.two ≤
          ENNReal.ofReal
            (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
              Real.sqrt (K *
                (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                    normalizedL2On U
                      (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
                  Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                    Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                    (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))) := by
  obtain ⟨K, hK, hcover⟩ := exists_interiorCoverEnergy_le_manuscriptPrices_cutoff d
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hnm z x y omega hz hx hD hnot hgood u g hweak hg
    u0 hu0 s1 smid hgap
  dsimp only
  have henergy := hcover M sOrder hs L m n hnm z x y omega hz hx hD hnot
    hgood u g hweak hg
  simp only at henergy
  have hframe := cubeAverage_coefficientEnergyDensity_aCutoffFamily_eq_translatedCube
    M L omega ((n : ℤ) - 2) y u0 u.grad hu0
  have hroot := weightedLocalSymmetricEnergyLp_two_le_rootEnergyReadout
    (originCube d ((n : ℤ) - 2))
    ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
      (originCube d ((n : ℤ) - 2))) u0 s1 smid (by linarith)
  refine hroot.trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_
    (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
  rw [hframe]
  exact Real.sqrt_le_sqrt henergy

/-- **The interior harmonic comparison at a finite cutoff, in the sharp loop
carrier.**  Word-for-word
`Section6HarmonicInterior.exists_interiorHarmonicComparison_le_sharpLoopBound`
with the binder `m ≤ L` deleted and `goodEvent M none (n+2) z 1 (s/8)` replaced
by `goodEvent M (some L) (n+2) z 1 (s/8)`. -/
theorem exists_interiorCutoffHarmonicComparison_le_sharpLoopBound (d : ℕ) [NeZero d] :
    ∃ (C : ℝ≥0∞) (K Cd : ℝ), C < ∞ ∧ 0 < K ∧ 0 < Cd ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
      let Q := originCube d ((n : ℤ) - 2)
      let U := truncatedCube d (m : ℤ) (n : ℤ) x
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      let E := Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z)
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (cube d (m : ℤ)) u g →
        MemCubeEuclideanFullWsp (originCube d (m : ℤ)) s2
          FiniteLpExponent.two g →
      ∀ (v : H1Function (translatedCube d ((n : ℤ) - 2) y)),
        IsWeaklyHarmonicOn (fun _ => (1 : ℝ))
          (translatedCube d ((n : ℤ) - 2) y) v →
        MemH10 (translatedCube d ((n : ℤ) - 2) y)
          (fun p ↦ v.toFun p - u.toFun p) →
        normalizedL2On (translatedCube d ((n : ℤ) - 2) y)
            (fun p ↦ u.toFun p - v.toFun p) ≤
          flatComparatorSharpGoodEventLoopBound C d n sigma smid s1 s2 E
            (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
              Real.sqrt (K *
                (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                    normalizedL2On U
                      (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2 +
                  Real.rpow s (-12 : ℝ) * sigma⁻¹ *
                    Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
                    (fractionalSeminormOn U s g).toReal ^ 2)))
            (Cd * Real.rpow s (-(1 / 2 : ℝ)) *
              (fractionalSeminormOn U s g).toReal)
            Q (fun p ↦ g (p + y)) := by
  obtain ⟨C, hCtop, hloop⟩ :=
    exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_sharp_neZero d
  obtain ⟨K, hK, henergy⟩ :=
    exists_interiorWeightedEnergy_le_manuscriptPrices_cutoff d
  obtain ⟨Cd, hCd, hforce⟩ := exists_interiorForceOverlap_le_windowSeminorm d
  refine ⟨C, K, Cd, hCtop, hK, hCd, ?_⟩
  intro M s hs L m n hnm z x y omega hz hx hD hnot hgood
  dsimp only
  intro u g hweak hg
  have hDset : translatedCube d ((n : ℤ) - 2) y =
      translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))) := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  rw [hDset]
  intro v hharm htrace
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hsubOpen : translatedCube d ((n : ℤ) - 2) y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    exact (hD hp).2
  obtain ⟨g0, hg0, hg0eq, u0, v0, hu0forced, _hv0, _huv0, hu0val, hu0grad⟩ :=
    exists_localSourceComparisonDatum_weak_retained M L omega m ((n : ℤ) - 2) y
      ⟨s, (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
        by linarith [hs.2]⟩
      u g hweak hg hsubOpen
      (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z)) hsigma
  have hS := henergy M
    ⟨s, (mul_pos (by norm_num)
          (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
      by linarith [hs.2]⟩
    hs L m n hnm z x y omega hz hx hD hnot hgood u g hweak hg u0 hu0grad
    ⟨s / 3, by
      have hs0 : 0 < s :=
        (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
      positivity, by linarith [hs.2]⟩
    ⟨s / 2, by
      have hs0 : 0 < s :=
        (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
      positivity, by linarith [hs.2]⟩
    (by
      have hs0 : 0 < s :=
        (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
      dsimp only
      linarith)
  have hDforce := hforce
    ⟨s, (mul_pos (by norm_num)
          (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
      by linarith [hs.2]⟩
    m n hnm z x y hx hD g g0 hg hg0 hg0eq
  have hcontain : translateSet (y - z)
      (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
        cubeSet (originCube d ((n : ℤ) + 2)) :=
    closedOffGridCube_subset_originAnchorParent hx hD
  have hharm' : IsUnitWeaklyHarmonicOn
      (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2)))) v :=
    isUnitWeaklyHarmonicOn_iff.mpr hharm
  have hg0fun : (fun p ↦ g (p + y)) = g0 := (funext hg0eq).symm
  rw [hg0fun]
  exact hloop M s hs L n omega y z hcontain hgood g0 hg0 u0 hu0forced
    u.toFun v hharm' htrace hu0val _ _ hS hDforce

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
