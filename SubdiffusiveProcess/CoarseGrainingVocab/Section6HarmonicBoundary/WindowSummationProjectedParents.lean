module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.WindowCellCover

@[expose] public section

/-!
# Summation of projected boundary parents over a window

This is the bounded-overlap part of the variable-scale cover used in
`l.harmonic.approximation.good.scales.GMC`.  We retain only lattice cell centres which lie in
the truncated inner window.  Their projected parents stay in the truncated
outer window by
`translatedCube_wellPlacedCentre_subset_boundaryWindow`, and at most `28^d`
such parents contain any point.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Scale-`k` lattice cells whose centres lie in the truncated window. -/
def windowSummationBoundaryIndices (k m : ℤ) (x : Vec d) (rho : ℝ) :
    Finset (Fin d → ℤ) :=
  (windowBox k x rho).filter fun idx ↦
    cellCentre k idx ∈ boundaryWindow d m x rho

theorem mem_windowSummationBoundaryIndices_iff
    {k m : ℤ} {x : Vec d} {rho : ℝ} {idx : Fin d → ℤ} :
    idx ∈ windowSummationBoundaryIndices k m x rho ↔
      idx ∈ windowBox k x rho ∧
        cellCentre k idx ∈ boundaryWindow d m x rho := by
  simp only [windowSummationBoundaryIndices, Finset.mem_filter]

/-- The projected parent associated with a scale-`k` lattice cell. -/
def windowSummationProjectedParent (k m : ℤ) (idx : Fin d → ℤ) :
    Set (Vec d) :=
  translatedCube d (k + 2)
    (Section6ExcessDecay.wellPlacedCentre (cellCentre k idx) m (k + 2))

theorem measurableSet_windowSummationProjectedParent
    (k m : ℤ) (idx : Fin d → ℤ) :
    MeasurableSet (windowSummationProjectedParent (d := d) k m idx) :=
  (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube d (k + 2)
    (Section6ExcessDecay.wellPlacedCentre (cellCentre k idx) m (k + 2))).isOpen.measurableSet

/-- Every selected projected parent stays in the prescribed outer window. -/
theorem windowSummationProjectedParent_subset_boundaryWindow
    {k m : ℤ} {x : Vec d} {rho R : ℝ} (hkm : k + 2 ≤ m)
    (hgap : rho + (3 : ℝ) ^ (k + 3) / 2 ≤ R)
    {idx : Fin d → ℤ} (hidx : idx ∈ windowSummationBoundaryIndices k m x rho) :
    windowSummationProjectedParent (d := d) k m idx ⊆ boundaryWindow d m x R := by
  have hq := (mem_windowSummationBoundaryIndices_iff.mp hidx).2
  have hsub := translatedCube_wellPlacedCentre_subset_boundaryWindow
    (d := d) (m := m) (k := k + 2) hkm hq
  refine hsub.trans (boundaryWindow_mono m x ?_)
  simpa only [add_assoc] using! hgap

/-- A selected projected parent is contained in the parent ball used by the
dimension-only packing estimate. -/
theorem windowSummationProjectedParent_subset_parentWindow
    {k m : ℤ} {x : Vec d} {rho : ℝ} (hkm : k + 2 ≤ m)
    {idx : Fin d → ℤ} (hidx : idx ∈ windowSummationBoundaryIndices k m x rho) :
    windowSummationProjectedParent (d := d) k m idx ⊆
      supWindow (cellCentre k idx) ((3 : ℝ) ^ (k + 3) / 2) := by
  have hq := (mem_windowSummationBoundaryIndices_iff.mp hidx).2
  simpa only [add_assoc, windowSummationProjectedParent] using!
    (translatedCube_wellPlacedCentre_subset_supWindow hq.2 hkm)

/-- **Bounded overlap of the projected parents.**  A point lies in at most
`28^d` parents belonging to the selected window cells. -/
theorem windowSummationProjectedParent_overlap_le
    (k m : ℤ) (x : Vec d) (rho : ℝ) (hkm : k + 2 ≤ m) (p : Vec d) :
    ((windowSummationBoundaryIndices k m x rho).filter fun idx ↦
      p ∈ windowSummationProjectedParent (d := d) k m idx).card ≤ 28 ^ d := by
  let t := windowSummationBoundaryIndices (d := d) k m x rho
  have hsub : (t.filter fun idx ↦
      p ∈ windowSummationProjectedParent (d := d) k m idx) ⊆
      (t.filter fun idx ↦
        p ∈ supWindow (cellCentre k idx) ((3 : ℝ) ^ (k + 3) / 2)) := by
    intro idx hidx
    rw [Finset.mem_filter] at hidx ⊢
    exact ⟨hidx.1,
      windowSummationProjectedParent_subset_parentWindow hkm hidx.1 hidx.2⟩
  exact (Finset.card_le_card hsub).trans (card_filter_parentWindow_le k p t)

/-- **Window summation of projected-parent energies.**

For every nonnegative integrable density, the sum over the projected parents
of the selected scale-`k` boundary cells is at most `28^d` times its integral
over the outer truncated window.  This is the bounded-overlap input required
by `BoundaryWindowEnergyStepRow`. -/
theorem windowSummation_sum_setIntegral_projectedParents_le
    (k m : ℤ) (x : Vec d) (rho R : ℝ) (hkm : k + 2 ≤ m)
    (hgap : rho + (3 : ℝ) ^ (k + 3) / 2 ≤ R)
    {F : Vec d → ℝ} (hF0 : ∀ p, 0 ≤ F p)
    (hint : IntegrableOn F (boundaryWindow d m x R)) :
    ∑ idx ∈ windowSummationBoundaryIndices k m x rho,
        ∫ p in windowSummationProjectedParent (d := d) k m idx, F p ≤
      (28 : ℝ) ^ d * ∫ p in boundaryWindow d m x R, F p := by
  let t := windowSummationBoundaryIndices (d := d) k m x rho
  let P : (Fin d → ℤ) → Set (Vec d) :=
    fun idx ↦ windowSummationProjectedParent (d := d) k m idx
  let W := boundaryWindow d m x R
  have hPmeas : ∀ idx, MeasurableSet (P idx) :=
    fun idx ↦ measurableSet_windowSummationProjectedParent k m idx
  have hPW : ∀ idx ∈ t, P idx ⊆ W :=
    fun idx hidx ↦ windowSummationProjectedParent_subset_boundaryWindow hkm hgap hidx
  have hPint : ∀ idx ∈ t, IntegrableOn F (P idx) :=
    fun idx hidx ↦ hint.mono_set (hPW idx hidx)
  have hind : ∀ idx ∈ t, Integrable ((P idx).indicator F) :=
    fun idx hidx ↦ (hPint idx hidx).integrable_indicator (hPmeas idx)
  have hsumIntegral :
      ∑ idx ∈ t, ∫ p in P idx, F p =
        ∫ p, ∑ idx ∈ t, (P idx).indicator F p := by
    rw [integral_finsetSum _ hind]
    exact Finset.sum_congr rfl fun idx _ ↦ (integral_indicator (hPmeas idx)).symm
  have hWmeas : MeasurableSet W := by
    simpa only [W, boundaryWindow, supWindow, cube] using!
      (measurableSet_supWindow x R).inter
        (measurableSet_openCubeSet (originCube d m))
  have hleft : Integrable (fun p ↦ ∑ idx ∈ t, (P idx).indicator F p) :=
    integrable_finsetSum _ hind
  have hright : Integrable (fun p ↦ (28 : ℝ) ^ d * W.indicator F p) :=
    (hint.integrable_indicator hWmeas).const_mul _
  have hpoint : ∀ p, ∑ idx ∈ t, (P idx).indicator F p ≤
      (28 : ℝ) ^ d * W.indicator F p := by
    intro p
    have hsum : ∑ idx ∈ t, (P idx).indicator F p =
        (t.filter fun idx ↦ p ∈ P idx).card • F p := by
      rw [Finset.card_filter]
      simp only [Set.indicator_apply]
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun idx _ ↦ by
        by_cases hp : p ∈ P idx <;> simp [hp]
    rw [hsum, nsmul_eq_mul]
    by_cases hpW : p ∈ W
    · rw [Set.indicator_of_mem hpW]
      have hcard : ((t.filter fun idx ↦ p ∈ P idx).card : ℝ) ≤
          (28 : ℝ) ^ d := by
        exact_mod_cast windowSummationProjectedParent_overlap_le k m x rho hkm p
      exact mul_le_mul_of_nonneg_right hcard (hF0 p)
    · have hempty : (t.filter fun idx ↦ p ∈ P idx) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun idx hidx hp ↦ ?_
        exact hpW (hPW idx hidx hp)
      rw [hempty, Set.indicator_of_notMem hpW]
      simp
  have hmono := integral_mono hleft hright hpoint
  rw [hsumIntegral]
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_indicator hWmeas]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
