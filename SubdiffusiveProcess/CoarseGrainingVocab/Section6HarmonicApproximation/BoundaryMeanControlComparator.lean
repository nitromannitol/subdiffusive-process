module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanControlFlush
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryFlatComparatorPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.AnchorCompetitor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector

@[expose] public section

/-!
# Flat comparator mean control on a projected boundary cell

The construction is the GMC specialization of
`Algsuperdiff/Section4/Provider/ExcessDecay/SealComparator.lean` and
`SealOddGlue.lean`: solve the two identity-coefficient Dirichlet problems,
subtract them, use the ambient zero trace to reflect the difference oddly,
and apply the dimension-only flush-face mean theorem.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory InnerProductSpace
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
open MeanControlGeometry MeanControlSchauder

noncomputable section

variable {d : ℕ}

private theorem h10Transport_toFun {U V : Set (Vec d)} (hUV : U = V)
    (rho : H10Function U) :
    (hUV ▸ rho).toH1Function.toFun = rho.toH1Function.toFun := by
  subst V
  rfl

theorem truncatedWindow_wellPlacedCentre_eq_translatedCube
    {m k : ℤ} (hkm : k ≤ m) (q : Vec d) :
    truncatedWindow (wellPlacedCentre q m k) m k =
      translatedCube d k (wellPlacedCentre q m k) := by
  unfold truncatedWindow translatedCube cube
  exact Set.inter_eq_left.2
    (translatedCube_wellPlacedCentre_subset_cube q hkm)

private theorem translatedCube_wellPlacedCentre_nonempty
    {m k : ℤ} (q : Vec d) :
    (translatedCube d k (wellPlacedCentre q m k)).Nonempty := by
  refine ⟨wellPlacedCentre q m k, ?_⟩
  rw [Section6ExcessDecay.mem_translatedCube_iff]
  simpa using zero_mem_cube d k

/-- The two flat harmonic replacements have a difference whose mean is
controlled by its mean-zero oscillation on the physical clamped cell. -/
theorem exists_flatComparatorDifference_mean_le_oscillation
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m k : ℤ) (q : Vec d) (i : Fin d) (sg : ℝ)
        (u h : H1Function (openCubeSet (originCube d m))),
        k < m → (sg = 1 ∨ sg = -1) →
        wellPlacedHalfGap m k < sg * q i →
        MemH10 (openCubeSet (originCube d m))
          (fun y => u.toFun y - h.toFun y) →
        let c := wellPlacedCentre q m k
        let P := translatedCube d k c
        ∃ ubar hbar : H1Function (truncatedWindow c m k),
          IsUnitWeaklyHarmonicOn (truncatedWindow c m k) ubar ∧
          IsUnitWeaklyHarmonicOn (truncatedWindow c m k) hbar ∧
          MemH10 (truncatedWindow c m k)
            (fun y => ubar.toFun y - u.toFun y) ∧
          MemH10 (truncatedWindow c m k)
            (fun y => hbar.toFun y - h.toFun y) ∧
          normalizedL2On P (fun y => u.toFun y - ubar.toFun y) ≤
            flatComparatorPriceConst d * (3 : ℝ) ^ k *
              ∑ j : Fin d, normalizedL2On P (fun y => u.grad y j) ∧
          normalizedL2On P (fun y => h.toFun y - hbar.toFun y) ≤
            flatComparatorPriceConst d * (3 : ℝ) ^ k *
              ∑ j : Fin d, normalizedL2On P (fun y => h.grad y j) ∧
          |volumeAverage P (fun y => ubar.toFun y - hbar.toFun y)| ≤
            C * normalizedL2On P
              (fun y => (ubar.toFun y - hbar.toFun y) -
                volumeAverage P
                  (fun z => ubar.toFun z - hbar.toFun z)) := by
  classical
  obtain ⟨C, hC0, hmean⟩ :=
    exists_abs_volumeAverage_le_normalizedL2On_wellPlacedFaceOdd d
  refine ⟨C, hC0, ?_⟩
  intro m k q i sg u h hkm hsg hover hdat
  let c : Vec d := wellPlacedCentre q m k
  let P : Set (Vec d) := translatedCube d k c
  let W : Set (Vec d) := truncatedWindow c m k
  let T : Set (Vec d) := translateSet c (openCubeSet (originCube d k))
  have hWP : W = P := by
    simpa only [W, P, c] using
      truncatedWindow_wellPlacedCentre_eq_translatedCube hkm.le q
  have hWopen : IsOpen W := by
    dsimp only [W]
    exact isOpen_truncatedWindow c m k
  have hWdom : W ⊆ openCubeSet (originCube d m) := by
    dsimp only [W]
    exact truncatedWindow_subset_domain c m k
  have hWne : W.Nonempty := by
    rw [hWP]
    exact translatedCube_wellPlacedCentre_nonempty q
  have hWconv : IsOpenBoundedConvexDomain W := by
    dsimp only [W]
    exact isOpenBoundedConvexDomain_truncatedWindow c m k
  have hPT : P = T := by
    dsimp only [P, T]
    rw [translatedCube, cube,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet]
  have hTW : T = W := hPT.symm.trans hWP.symm
  have hTdom : T ⊆ openCubeSet (originCube d m) := by
    rw [hTW]
    exact hWdom
  obtain ⟨ubarT, rhouT, hubarTHarm, hubarTval, _hubarTgrad, hubarTPrice⟩ :=
    exists_flatComparator_translatedCube_le hTdom u
  obtain ⟨hbarT, rhohT, hhbarTHarm, hhbarTval, _hhbarTgrad, hhbarTPrice⟩ :=
    exists_flatComparator_translatedCube_le hTdom h
  let ubar : H1Function W := h1FunctionOfSetEq hTW ubarT
  let hbar : H1Function W := h1FunctionOfSetEq hTW hbarT
  let rhou : H10Function W := hTW ▸ rhouT
  let rhoh : H10Function W := hTW ▸ rhohT
  have hubarHarm : IsUnitWeaklyHarmonicOn W ubar := by
    exact isUnitWeaklyHarmonicOn_h1FunctionOfSetEq hTW hubarTHarm
  have hhbarHarm : IsUnitWeaklyHarmonicOn W hbar := by
    exact isUnitWeaklyHarmonicOn_h1FunctionOfSetEq hTW hhbarTHarm
  have hubarTrace' : MemH10 W
      (fun y => ubar.toFun y - u.toFun y) := by
    refine ⟨rhou, ?_⟩
    funext y
    rw [show rhou.toH1Function.toFun y = rhouT.toH1Function.toFun y by
      exact congrFun (h10Transport_toFun hTW rhouT) y]
    rw [show ubar.toFun y = ubarT.toFun y by
      dsimp only [ubar]; rw [h1FunctionOfSetEq_toFun]]
    rw [hubarTval y]
    ring
  have hhbarTrace' : MemH10 W
      (fun y => hbar.toFun y - h.toFun y) := by
    refine ⟨rhoh, ?_⟩
    funext y
    rw [show rhoh.toH1Function.toFun y = rhohT.toH1Function.toFun y by
      exact congrFun (h10Transport_toFun hTW rhohT) y]
    rw [show hbar.toFun y = hbarT.toFun y by
      dsimp only [hbar]; rw [h1FunctionOfSetEq_toFun]]
    rw [hhbarTval y]
    ring
  have hubarPrice : normalizedL2On P (fun y => u.toFun y - ubar.toFun y) ≤
      flatComparatorPriceConst d * (3 : ℝ) ^ k *
        ∑ j : Fin d, normalizedL2On P (fun y => u.grad y j) := by
    rw [hPT]
    simpa only [ubar, h1FunctionOfSetEq_toFun] using hubarTPrice
  have hhbarPrice : normalizedL2On P (fun y => h.toFun y - hbar.toFun y) ≤
      flatComparatorPriceConst d * (3 : ℝ) ^ k *
        ∑ j : Fin d, normalizedL2On P (fun y => h.grad y j) := by
    rw [hPT]
    simpa only [hbar, h1FunctionOfSetEq_toFun] using hhbarTPrice
  let hW : H1Function W := h.restrict hWopen hWdom
  have hPsi : ∀ y ∈ W,
      hW.toFun y = h.toFun y - Section6ExcessDecay.affineLift c 0 0 y := by
    intro y _
    change h.toFun y = h.toFun y -
      (0 + vecDot (0 : Vec d) (y - c))
    simp only [vecDot_zero_left, zero_add, sub_zero]
  obtain ⟨V, hoddUpper, hoddLower, hharmV, hVmem, hVae⟩ :=
    Section6BoundaryL2.exists_classicalCompetitor_datumSplit_anchor
      (x := c) (m := m) (k := k) hkm
      hWopen (Set.Subset.rfl) hWdom hdat hubarHarm hubarTrace'
      hhbarHarm hPsi hhbarTrace'
  have hodd : ∀ y ∈ reflectedWindow c m k,
      V (coordFaceReflection
        (sg * ((1 / 2 : ℝ) * (3 : ℝ) ^ m)) i y) = -V y := by
    rcases hsg with rfl | rfl
    · intro y hy
      have hface : MeetsUpperFace c m k i := by
        rw [MeetsUpperFace]
        have hlevel := MeanControlGeometry.wellPlacedCentre_faceLevel
          hkm.le (Or.inl rfl) hover
        dsimp only [c]
        linarith only [hlevel]
      simpa only [one_mul] using hoddUpper i hface y hy
    · intro y hy
      have hface : MeetsLowerFace c m k i := by
        rw [MeetsLowerFace]
        have hlevel := MeanControlGeometry.wellPlacedCentre_faceLevel
          hkm.le (Or.inr rfl) hover
        dsimp only [c]
        linarith only [hlevel]
      simpa only [neg_mul, one_mul] using hoddLower i hface y hy
  have hVbound := hmean m k q i sg V hkm hsg hover
    (by simpa only [c] using hodd) hVmem (by simpa only [c] using hharmV)
  let F : Vec d → ℝ := fun y => ubar.toFun y - hbar.toFun y
  have hVaeP : V =ᵐ[volume.restrict P] F := by
    rw [← hWP]
    filter_upwards [hVae] with y hy
    dsimp only [F]
    simpa only [Section6ExcessDecay.affineLift, vecDot_zero_left, add_zero,
      sub_zero] using hy
  have hmeanEq : volumeAverage P V = volumeAverage P F := by
    unfold volumeAverage
    rw [integral_congr_ae hVaeP]
  have hnormEq :
      normalizedL2On P (fun y => V y - volumeAverage P V) =
        normalizedL2On P (fun y => F y - volumeAverage P F) := by
    apply Section6OddClass.normalizedL2On_congr_ae
    filter_upwards [hVaeP] with y hy
    rw [hy, hmeanEq]
  refine ⟨ubar, hbar, hubarHarm, hhbarHarm, hubarTrace', hhbarTrace',
    hubarPrice, hhbarPrice, ?_⟩
  rw [hnormEq] at hVbound
  rw [hmeanEq] at hVbound
  simpa only [c, P, F] using hVbound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
