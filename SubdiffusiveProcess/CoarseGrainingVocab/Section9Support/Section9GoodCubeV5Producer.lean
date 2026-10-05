module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceCatalogueEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionReducedReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSelectedParameters
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCatalogueTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeBoundedScaleClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryCatalogTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5Oscillation

@[expose] public section

/-!
# A selected good-cube package with a **small** exported oscillation constant

This is the version-4 selected package of `Section9GoodCubeSelectedProducer`
with the following tolerance order: the requested tolerance
`eps0` is fixed **first**, the inner depth `j2` of the exported reference
template is the depth that the strict harmonic contraction needs for that
`eps0`, and the layer-zero bad
predicate absorbs the corresponding coefficient-local harmonic event.

Nothing else changes: the finite Sobolev, torsion and mass catalogue, the
auxiliary interior geometry, the clock budget and the tail calibration are the
version-4 ones, read on the enlarged layer-zero event.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Enlarging the reference-box predicate enlarges the site event by exactly the
corresponding union. -/
theorem coefficientLocalBadEvent_union {d : ℕ} (M : GMCModel d) (n : ℕ) (C : ℝ)
    (s t : Set (nativeBox n C (0 : Lattice d) → ℝ)) (z : Lattice d) :
    coefficientLocalBadEvent M n C (s ∪ t) z
      = coefficientLocalBadEvent M n C s z ∪ coefficientLocalBadEvent M n C t z := by
  simp only [coefficientLocalBadEvent, Set.preimage_union]

/-- The version-4 selected package together with the **strict** oscillation
contraction on the exported reference pairs, at the tolerance `eps0` chosen
before the depth. -/
def GoodCubeSelectedReducedPackageV5 (d : ℕ) (eta p0 CE eps0 : ℝ) : Prop :=
  ∃ (c C A0 eps1 : ℝ) (Cdep j1 j2 : ℕ) (r : ℤ),
    0 < c ∧ 0 < C ∧ 1 ≤ A0 ∧ A0 ≤ C ∧ CE * A0 ^ CE ≤ C ∧ 0 < eps1 ∧
    1 < (3 : ℝ) ^ r ∧ ((shellCoverShifts d r).card : ℝ) ≤ C ∧ 1 ≤ C ∧
    1 + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ) ∧
    c ≤ 1 / 3 ∧ c ≤ Real.sqrt layerTailConstant * eps1 ∧
    2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * c) ≤ eps1 ∧
    C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 ∧
    ∃ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
      (Qfam0 Afam0 : Set (Cube d))
      (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n 1 (0 : Lattice d) → ℝ)),
      (∀ (n : ℕ) (z : Lattice d),
        IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
          (goodCubeReferencePairs Pfam0 n z) (goodCubeReferenceFamily Qfam0 n z)
          (goodCubeReferenceFamily Afam0 n z)) ∧
      (∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))) ∧
      (∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
        M.P.toMeasure (coefficientLocalBadEvent M n 1 (bad M n) z) ≤ ENNReal.ofReal
          (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)))))) ∧
      GoodCubeReducedDisplaysV4 d c A0 p0 eps1 Pfam0 Qfam0 Afam0 bad ∧
      (∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d)
        (omega : PotentialSample d),
        omega ∉ coefficientLocalBadEvent M n 1 (bad M n) z →
        LocalHarmonicOscillation (aCutoff M n omega) eps0
          (goodCubeReferencePairs Pfam0 n z))

theorem exists_goodCube_selected_reduced_package_v5
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p : ℝ, 2 < p ∧ ∀ (CE eta eps0 : ℝ), 0 < eta → 0 < eps0 →
      GoodCubeSelectedReducedPackageV5 d eta p CE eps0 := by
  classical
  obtain ⟨p, A, hp, hA, hevent⟩ := exists_goodCube_reference_catalogue_event_family d hd
  refine ⟨p, hp, ?_⟩
  intro CE eta eps0 heta heps0
  obtain ⟨jH, hjH, hoscN⟩ := exists_goodCube_reference_oscillation_local_event d eps0 heps0
  obtain ⟨C, cShell, Cdep, j1, r, hC, hcShell, hAC, hCEC, hBr, hNC, h1C,
    hCdep, hcShell3, hcShellK, hcShellDelta, hj1, hsmall⟩ :=
    exists_goodCube_selected_scalar_parameters d eta heta A CE hA
  obtain ⟨grid0, Pfam0, Qfam0, Afam0, hgeom0, hinside, hgeom⟩ :=
    exists_goodCubeReferenceTemplate d hj1 (le_trans (by norm_num) hjH)
  have hunit : ((0 : Vec d), (1 : ℝ)) ∈ Qfam0 := by
    simpa only [pow_zero] using hgeom0.self_mem
  have hinside1 : ∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ)) := by
    simpa only [pow_zero] using hinside
  -- the exported pair template as a finite set, and its harmonic event
  set PF : Finset (Cube d × Cube d) := hgeom0.finite_P.toFinset with hPFdef
  have hPFcoe : (PF : Set (Cube d × Cube d)) = Pfam0 := by
    rw [hPFdef, Set.Finite.coe_toFinset]
  obtain ⟨cH, hcH, _hcHb, _hcH12, hoscFam⟩ := hoscN PF.card 1 one_pos
  obtain ⟨badH, hbadH⟩ := hoscFam j1 grid0 PF Qfam0 Afam0 (le_refl _)
    (by rw [hPFcoe]; exact hgeom)
  obtain ⟨K, hK, hlowerTheta⟩ :=
    exists_goodCube_reference_torsion_lower_readout_parameters d hd p A hp hA
  obtain ⟨theta, W, htheta0, htheta1, _hW, hcoverChoices⟩ :=
    exists_goodCube_complete_auxiliary_geometry Qfam0 hgeom0.finite_Q hgeom0.side_pos
      hunit hinside1
  obtain ⟨k0, etaCap, epsH, hk0, hetaCap, hepsH, hlowerV⟩ :=
    hlowerTheta theta htheta0 htheta1
  obtain ⟨j, hj, heventJ⟩ := hevent epsH hepsH
  obtain ⟨k, _N0, v0, centers, hv0, _hv0eq, hauxAll⟩ :=
    hcoverChoices etaCap K hetaCap hK j hj
  obtain ⟨_J0, depth, hdepthAll, _hnative, _hvolume⟩ :=
    exists_goodCube_reference_scale_catalog grid0 Qfam0 hgeom0.finite_Q hgeom0.side_pos
      hgeom0.gridded hinside1
  have hdepth : ∀ Q : Qfam0, Q.val.2 = (3 : ℝ)^(-(depth Q : ℤ)) :=
    fun Q => (hdepthAll Q).2.1
  have htarget := goodCube_auxiliary_target_geometry Qfam0 hgeom0.finite_Q
    hgeom0.side_pos hunit hinside1
  let : Finite (Option (GoodCubeCompactPair Qfam0)) := htarget.1
  have hauxInside : ∀ i, ∀ x ∈ centers i,
      cubeSet (x, (3 : ℝ)^(-(k : ℤ))) ⊆ cubeSet ((0 : Vec d), (1 : ℝ)) := by
    intro i x hx
    have hout := ((hauxAll i).2.2.2.2 x hx).2.1
    exact (subset_closure.trans hout).trans
      (hinside1 _ (htarget.2 i).2.2.1)
  obtain ⟨G, P, J, N, hGcard, hPcard, _hkJ, hG, hGorig, hGquarter, hGaux, hP, _hPgeom⟩ :=
    exists_goodCube_unified_test_catalog Qfam0 hgeom0.finite_Q depth hdepth hinside1
      centers j k (by omega) hauxInside
  obtain ⟨epsL2, hepsL2, hlower⟩ := hlowerV v0 hv0
  obtain ⟨cEvt, hcEvt, _hcEvtHalf, heventG⟩ := heventJ J N epsL2 hepsL2
  let X := goodCubeAuxiliaryCenterUnion centers
  have hX : ∀ x ∈ X, cubeSet (x, (3 : ℝ)^(-(k : ℤ))) ⊆
      cubeSet ((0 : Vec d), (1 : ℝ)) := by
    intro x hx
    obtain ⟨i, hi⟩ := (mem_goodCube_auxiliary_center_union centers x).mp hx
    exact hauxInside i x hi
  have hPcard' : (goodCubeAuxiliaryPairs X j (-(k : ℤ))).card ≤ N := by
    simpa only [hP] using hPcard
  obtain ⟨bad, hbad⟩ := heventG G hGcard (fun q hq => (hG q hq).1)
    (fun q hq => (hG q hq).2) k X hX hPcard'
  obtain ⟨cClock, hcClock, _hcClockHalf, hclock⟩ := exists_goodCube_depth_clock_threshold J
  -- the two layer-zero tails are absorbed into one
  have hminpos : 0 < min cEvt cH := lt_min hcEvt hcH
  obtain ⟨cAbs, hcAbs, hcAbsMin, _hcAbsHalf, habsorb⟩ :=
    goodCube_exists_finite_tail_absorption 2 ((min cEvt cH) ^ 2) (min cEvt cH)
      (by norm_num) (by positivity) hminpos
  let massFraction : ℝ := (((3 : ℝ)^(-(J : ℤ)))^d) / 3
  have hmass : 0 < massFraction := by dsimp [massFraction]; positivity
  let c : ℝ := min cAbs (min cShell (min cEvt (min cClock (min (k0 / 2) massFraction))))
  have hc : 0 < c := lt_min hcAbs (lt_min hcShell (lt_min hcEvt (lt_min hcClock
    (lt_min (div_pos hk0 (by norm_num)) hmass))))
  have hccAbs : c ≤ cAbs := min_le_left _ _
  have hcTail : c ≤ min cShell (min cEvt (min cClock (min (k0 / 2) massFraction))) :=
    min_le_right _ _
  have hccShell : c ≤ cShell := hcTail.trans (min_le_left _ _)
  have hcRest : c ≤ min cEvt (min cClock (min (k0 / 2) massFraction)) :=
    hcTail.trans (min_le_right _ _)
  have hccEvt : c ≤ cEvt := hcRest.trans (min_le_left _ _)
  have hcRest2 : c ≤ min cClock (min (k0 / 2) massFraction) := hcRest.trans (min_le_right _ _)
  have hccClock : c ≤ cClock := hcRest2.trans (min_le_left _ _)
  have hcRest3 : c ≤ min (k0 / 2) massFraction := hcRest2.trans (min_le_right _ _)
  have hccLower : c ≤ k0 / 2 := hcRest3.trans (min_le_left _ _)
  have hccMass : c ≤ massFraction := hcRest3.trans (min_le_right _ _)
  have hccH : c ≤ cH := (hccAbs.trans hcAbsMin).trans (min_le_right _ _)
  have hbudget : ∀ M : GMCModel d, M.delta ≤ c →
      2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2 :=
    fun M hdelta => hclock M.delta M.shellPrefix.delta_pos (hdelta.trans hccClock)
  -- the enlarged layer-zero predicate
  set badV5 : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n 1 (0 : Lattice d) → ℝ) :=
    fun M n => bad M n ∪ badH M n with hbadV5
  have hsubBad : ∀ (M : GMCModel d) (n : ℕ) (z : Lattice d)
      (omega : PotentialSample d),
      omega ∉ coefficientLocalBadEvent M n 1 (badV5 M n) z →
      omega ∉ coefficientLocalBadEvent M n 1 (bad M n) z := by
    intro M n z omega hom hmem
    exact hom (by rw [hbadV5, coefficientLocalBadEvent_union]; exact Or.inl hmem)
  have hsubBadH : ∀ (M : GMCModel d) (n : ℕ) (z : Lattice d)
      (omega : PotentialSample d),
      omega ∉ coefficientLocalBadEvent M n 1 (badV5 M n) z →
      omega ∉ coefficientLocalBadEvent M n 1 (badH M n) z := by
    intro M n z omega hom hmem
    exact hom (by rw [hbadV5, coefficientLocalBadEvent_union]; exact Or.inr hmem)
  have hdisp : GoodCubeReducedDisplaysV4 d c A p 1 Pfam0 Qfam0 Afam0 badV5 := by
    refine goodCube_reducedDisplaysV4_of_finiteLocalTests
      p A c 1 K theta k0 etaCap epsH v0 epsL2 massFraction
      Pfam0 Qfam0 Afam0 hgeom0.finite_Q hgeom0.side_pos hunit hinside1 depth hdepth
      j k J G (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d)) centers
      hGorig hGquarter hGaux ?_ ?_ ?_ ?_ hlower hccLower hccMass badV5 hbudget ?_
    · intro i x hx
      exact goodCube_auxiliary_pair_catalog_mem centers j k i x hx
    · intro i
      exact (hauxAll i).2.2.1
    · intro i
      exact (hauxAll i).2.2.2.1
    · intro i x hx
      obtain ⟨_hW, hparent, htheta, hhalf, hvol⟩ := (hauxAll i).2.2.2.2 x hx
      exact ⟨hparent, htheta, hhalf, fun y s hs => (hvol y s hs).2⟩
    · intro M hdelta n z omega hout
      exact (hbad M (hdelta.trans hccEvt) n).2 z omega (hsubBad M n z omega hout)
  have hdeltaShell : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * c) ≤ 1 := by
    have hnonneg : 0 ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ := by positivity
    have hle := mul_le_mul_of_nonneg_left hccShell hnonneg
    linarith only [hle, hcShellDelta]
  refine ⟨c, C, A, 1, Cdep, j1, jH, r, hc, hC, hA, hAC, hCEC, one_pos,
    hBr, hNC, h1C, hCdep, hccShell.trans hcShell3, ?_, hdeltaShell, hsmall,
    grid0, Pfam0, Qfam0, Afam0, badV5, hgeom, hinside, ?_, hdisp, ?_⟩
  · simpa only [mul_one] using hccShell.trans hcShellK
  · -- the combined layer-zero tail
    intro M hdelta n z
    have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
    have h1 := (hbad M (hdelta.trans hccEvt) n).1 z
    have h2 := (hbadH M (hdelta.trans hccH) n).1 z
    have hDnn : (0 : ℝ) ≤ M.delta ^ 2 * Real.log M.delta ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hmono : ∀ e : ℝ, min cEvt cH ≤ e →
        ENNReal.ofReal (Real.exp (-(e ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) ≤
          ENNReal.ofReal (Real.exp
            (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) := by
      intro e he
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg ?_))
      refine div_le_div_of_nonneg_right ?_ hDnn
      nlinarith [hminpos.le, hminpos.le.trans he]
    have hsum : M.P.toMeasure (coefficientLocalBadEvent M n 1 (badV5 M n) z) ≤
        ENNReal.ofReal (Real.exp
          (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) +
        ENNReal.ofReal (Real.exp
          (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) := by
      rw [hbadV5, coefficientLocalBadEvent_union]
      exact (measure_union_le _ _).trans
        (add_le_add (h1.trans (hmono cEvt (min_le_left _ _)))
          (h2.trans (hmono cH (min_le_right _ _))))
    refine hsum.trans ?_
    have hdouble : ENNReal.ofReal (Real.exp
          (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) +
        ENNReal.ofReal (Real.exp
          (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) =
        ENNReal.ofReal (2 * Real.exp
          (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring
    rw [hdouble]
    have habs := habsorb M.delta hdpos (hdelta.trans hccAbs)
    have habs' : 2 * Real.exp
          (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))) ≤
        Real.exp (-(cAbs ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))) := by
      simpa only [neg_div] using habs
    exact (ENNReal.ofReal_le_ofReal habs').trans
      (goodCube_catalogue_tail_mono M c cAbs C hc.le hccAbs h1C)
  · -- the strict oscillation contraction on the exported pairs
    intro M hdelta n z omega hom
    have h := (hbadH M (hdelta.trans hccH) n).2 z omega (hsubBadH M n z omega hom)
    rwa [hPFcoe] at h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
