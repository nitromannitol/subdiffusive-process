module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceCatalogueEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionReducedReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSelectedParameters
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCatalogueTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeBoundedScaleClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryCatalogTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryScales
@[expose] public section

/-!
# A selected good-cube package at every requested tolerance

One dimension-only Sobolev exponent and constant are chosen first. The shell
and exit constant C precedes the fixed original template. Its auxiliary
interior fraction determines the lower and contraction tolerances; the
strict harmonic separation precedes the finite covers and their positive
volume floor. The torsion comparison tolerance and event threshold are
chosen last, still before the model. A common smaller c pays the event,
clock, pointwise lower, mass, and shell constraints simultaneously.

Every premise of the reduced-display constructor is supplied by the proved
geometry, actual coefficient tests, and native torsion readouts below.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem exists_goodCube_selected_reduced_package
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p : ℝ, 2 < p ∧ ∀ (CE eta : ℝ), 0 < eta →
      GoodCubeSelectedReducedPackage d eta p CE := by
  classical
  obtain ⟨p, A, hp, hA, hevent⟩ := exists_goodCube_reference_catalogue_event_family d hd
  refine ⟨p, hp, ?_⟩
  intro CE eta heta
  obtain ⟨C, cShell, Cdep, j1, r, hC, hcShell, hAC, hCEC, hBr, hNC, h1C,
    hCdep, hcShell3, hcShellK, hcShellDelta, hj1, hsmall⟩ :=
    exists_goodCube_selected_scalar_parameters d eta heta A CE hA
  obtain ⟨grid0, Pfam0, Qfam0, Afam0, hgeom0, hinside, hgeom⟩ :=
    exists_goodCubeReferenceTemplate d hj1 (le_refl 1)
  have hunit : ((0 : Vec d), (1 : ℝ)) ∈ Qfam0 := by
    simpa only [pow_zero] using hgeom0.self_mem
  have hinside1 : ∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ)) := by
    simpa only [pow_zero] using hinside
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
  letI : Finite (Option (GoodCubeCompactPair Qfam0)) := htarget.1
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
  let massFraction : ℝ := (((3 : ℝ)^(-(J : ℤ)))^d) / 3
  have hmass : 0 < massFraction := by dsimp [massFraction]; positivity
  let c : ℝ := min cShell (min cEvt (min cClock (min (k0 / 2) massFraction)))
  have hc : 0 < c := lt_min hcShell (lt_min hcEvt (lt_min hcClock
    (lt_min (div_pos hk0 (by norm_num)) hmass)))
  have hccShell : c ≤ cShell := min_le_left _ _
  have hcRest : c ≤ min cEvt (min cClock (min (k0 / 2) massFraction)) := min_le_right _ _
  have hccEvt : c ≤ cEvt := hcRest.trans (min_le_left _ _)
  have hcRest2 : c ≤ min cClock (min (k0 / 2) massFraction) := hcRest.trans (min_le_right _ _)
  have hccClock : c ≤ cClock := hcRest2.trans (min_le_left _ _)
  have hcRest3 : c ≤ min (k0 / 2) massFraction := hcRest2.trans (min_le_right _ _)
  have hccLower : c ≤ k0 / 2 := hcRest3.trans (min_le_left _ _)
  have hccMass : c ≤ massFraction := hcRest3.trans (min_le_right _ _)
  have hbudget : ∀ M : GMCModel d, M.delta ≤ c →
      2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2 :=
    fun M hdelta => hclock M.delta M.shellPrefix.delta_pos (hdelta.trans hccClock)
  have hdisp : GoodCubeReducedDisplaysV4 d c A p 1 Pfam0 Qfam0 Afam0 bad := by
    refine goodCube_reducedDisplaysV4_of_finiteLocalTests
      p A c 1 K theta k0 etaCap epsH v0 epsL2 massFraction
      Pfam0 Qfam0 Afam0 hgeom0.finite_Q hgeom0.side_pos hunit hinside1 depth hdepth
      j k J G (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d)) centers
      hGorig hGquarter hGaux ?_ ?_ ?_ ?_ hlower hccLower hccMass bad hbudget ?_
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
      exact (hbad M (hdelta.trans hccEvt) n).2 z omega hout
  have hdeltaShell : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * c) ≤ 1 := by
    have hnonneg : 0 ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ := by positivity
    have hle := mul_le_mul_of_nonneg_left hccShell hnonneg
    linarith only [hle, hcShellDelta]
  refine ⟨c, C, A, 1, Cdep, j1, 1, r, hc, hC, hA, hAC, hCEC, one_pos,
    hBr, hNC, h1C, hCdep, hccShell.trans hcShell3, ?_, hdeltaShell, hsmall,
    grid0, Pfam0, Qfam0, Afam0, bad, hgeom, hinside, ?_, hdisp⟩
  · simpa only [mul_one] using hccShell.trans hcShellK
  · intro M hdelta n z
    exact ((hbad M (hdelta.trans hccEvt) n).1 z).trans
      (goodCube_catalogue_tail_mono M c cEvt C hc.le hccEvt h1C)
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
