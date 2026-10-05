module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.WeightedEnergySlot
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.ForceOverlapSlot
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.RetainedDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorSharpErrorLoop
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalEllipticityControl

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The literal-centre sharp comparator loop at the `[NeZero d]` signature of
the Section 6 anchors.  Companion of
`exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop_of_forced_sharp_neZero`
for the un-projected loop. -/
theorem exists_normalizedL2On_sub_flatComparator_le_goodEventLoop_of_forced_sharp_neZero
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
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
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet y (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet y (openCubeSet Q)) ubar →
        MemH10 (translateSet y (openCubeSet Q))
          (fun p ↦ ubar.toFun p - uPhysical p) →
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translateSet y (openCubeSet Q))
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSharpGoodEventLoopBound C d n sigma smid s1 s2
            E S D Q g := by
  classical
  by_cases hmodel : Nonempty (_root_.SubdiffusiveProcess.Model.GMCModel d)
  · let M0 : _root_.SubdiffusiveProcess.Model.GMCModel d := Classical.choice hmodel
    exact exists_normalizedL2On_sub_flatComparator_le_goodEventLoop_of_forced_sharp
      d M0.shellPrefix.dimension
  · refine ⟨0, ENNReal.zero_lt_top, ?_⟩
    intro M
    exact (hmodel ⟨M⟩).elim

/-- **The interior harmonic comparison, in the sharp loop carrier.**  Every
slot of the committed sharp comparator loop is discharged from the interior
anchor's own hypotheses; the right-hand side is written in the
manuscript quantities. -/
theorem exists_interiorHarmonicComparison_le_sharpLoopBound (d : ℕ) [NeZero d] :
    ∃ (C : ℝ≥0∞) (K Cd : ℝ), C < ∞ ∧ 0 < K ∧ 0 < Cd ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        ¬ BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
          (cube d (m : ℤ)) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
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
    exists_normalizedL2On_sub_flatComparator_le_goodEventLoop_of_forced_sharp_neZero d
  obtain ⟨K, hK, henergy⟩ :=
    exists_interiorWeightedEnergy_le_manuscriptPrices_weak d
  obtain ⟨Cd, hCd, hforce⟩ := exists_interiorForceOverlap_le_windowSeminorm d
  refine ⟨C, K, Cd, hCtop, hK, hCd, ?_⟩
  intro M s hs L m n hmL hnm z x y omega hz hx hD hnot hgood
  dsimp only
  intro u g hweak hg
  have hDset : translatedCube d ((n : ℤ) - 2) y =
      translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))) := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  rw [hDset]
  intro v hharm htrace
  -- the sigma of the loop
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  -- the recentred PDE datum
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
  -- the two slots
  have hS := henergy M
    ⟨s, (mul_pos (by norm_num)
          (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
      by linarith [hs.2]⟩
    hs L m n hmL hnm z x y omega hz hx hD hnot hgood u g hweak hg u0 hu0grad
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
  -- the loop premises
  have hcontain : translateSet (y - z)
      (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
        cubeSet (originCube d ((n : ℤ) + 2)) :=
    closedOffGridCube_subset_originAnchorParent hx hD
  have hnL : n + 2 ≤ L := by omega
  have hharm' : IsUnitWeaklyHarmonicOn
      (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2)))) v :=
    isUnitWeaklyHarmonicOn_iff.mpr hharm
  have hg0fun : (fun p ↦ g (p + y)) = g0 := (funext hg0eq).symm
  rw [hg0fun]
  exact hloop M s hs L n hnL omega y z hcontain hgood g0 hg0 u0 hu0forced
    u.toFun v hharm' htrace hu0val _ _ hS hDforce

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
