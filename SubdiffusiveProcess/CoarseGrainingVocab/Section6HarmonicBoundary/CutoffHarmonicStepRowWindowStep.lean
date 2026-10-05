
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowWindowStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowInteriorSum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowBoundaryCell
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicWindowStepAbsorption

@[expose] public section

/-!
# The window-step row from the boundary step-cell parent row, at a finite cutoff

Cutoff companions of
`Section6HarmonicBoundary.exists_boundaryWindowEnergyStepRow_of_boundaryStepCellParentRow`
and
`Section6HarmonicBoundary.exists_boundaryCellManuscriptRow_of_boundaryStepCellParentRow`:
the binder `m ≤ L` is deleted and the good event is `𝒢^{(L)}_{n+2,z}`.  The
changed leaves are the cutoff interior and boundary cover sums; the cover-scale
matching is deterministic and is quoted unchanged.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **`BoundaryWindowEnergyStepRow` from the boundary-class cell row.**

With the interior class, the empty cells, the cover-scale choice, the
bounded-overlap summation and the exponent bookkeeping all discharged, the step
row — the single open input of the frozen v6 anchor — follows from
`BoundaryStepCellParentRow` alone. -/
theorem exists_boundaryWindowEnergyStepRow_of_boundaryStepCellParentRow
    (d : ℕ) [NeZero d]
    {Cbd : ℝ} (hCbd : 0 ≤ Cbd) (hbrow : BoundaryStepCellParentRow d Cbd) :
    ∃ Cstep : ℝ, 0 ≤ Cstep ∧ BoundaryWindowEnergyStepRow d Cstep := by
  classical
  obtain ⟨Kint, hKint, hint⟩ := exists_interiorCellSum_le_budgets_atScale d
  obtain ⟨Kbd, hKbd, hbd⟩ :=
    exists_boundaryCellSum_le_parentFeedback_add_budgets_atScale d hCbd hbrow
  refine ⟨Kint + Kbd, by positivity, ?_⟩
  intro M sOrder hs L m n hnm z x omega hz hx hgood u h g hdir hg hh
    rho R hrho hlt hR
  -- notation
  set E : Vec d → ℝ := fun p =>
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p) with hEdef
  have hE0 : ∀ p, 0 ≤ E p := fun p => cutoffEnergyDensity_nonneg M L omega u p
  have hEint : IntegrableOn E (cube d (m : ℤ)) :=
    integrableOn_aCutoff_energy M L omega (originCube d (m : ℤ)) u
  set Bud : ℝ := harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g
    with hBuddef
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < sOrder.1 :=
    (mul_pos (by norm_num : (0 : ℝ) < 512) (pow_pos hdelta 2)).trans_le hs.1
  have hBud0 : 0 ≤ Bud :=
    harmonicPhysicalFourBudgets_nonneg M L m n z x omega hs0
      (Section6ExcessDecay.tailAverage_nonneg M L (n + 2) omega _) u h g
  have hNpos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hgapPos : 0 < R - rho := by linarith
  have hgapSmall : R - rho ≤ (3 : ℝ) ^ n / 9 := by linarith
  have hrho0 : (0 : ℝ) ≤ rho := le_trans (by positivity) hrho
  -- the cover scale
  obtain ⟨k, hk27, hk9⟩ := exists_coverScale_matched hgapPos
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hkn4 : k ≤ (n : ℤ) - 4 := by
    have hle : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ ((n : ℤ) - 4) := by
      have h4 : (3 : ℝ) ^ ((n : ℤ) - 4) = (3 : ℝ) ^ n / 81 := by
        rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
        norm_num
      rw [h4]
      linarith
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hle
  have hkm : k ≤ (m : ℤ) := by omega
  have h3j : (0 : ℝ) < (3 : ℝ) ^ (k - 2) := zpow_pos (by norm_num) _
  have hjval : (3 : ℝ) ^ (k - 2) = (3 : ℝ) ^ k / 9 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hgapCover : rho + 14 * (3 : ℝ) ^ (k - 2) ≤ R := by
    rw [hjval]
    linarith
  -- the cover of the inner window by the cells of its index box
  set E' : Vec d → ℝ := (cube d (m : ℤ)).indicator E with hE'def
  have hE'0 : ∀ p, 0 ≤ E' p := fun p =>
    Set.indicator_nonneg (fun q _ => hE0 q) p
  have hE'int : Integrable E' :=
    hEint.integrable_indicator (measurableSet_cube d (m : ℤ))
  have hcover : windowCutoffEnergy M L omega m x u rho ≤
      ∑ idx ∈ windowBox (k - 2) x rho,
        ∫ p in truncatedCube d (m : ℤ) (k - 2) (cellCentre (k - 2) idx), E p := by
    have hstep := setIntegral_supWindow_le_sum_cells (k - 2) x rho hE'0
      hE'int.integrableOn
    rw [hE'def, setIntegral_supWindow_indicator_cube] at hstep
    refine le_trans (le_of_eq ?_) (hstep.trans (le_of_eq ?_))
    · rw [windowCutoffEnergy, hEdef]
    · exact Finset.sum_congr rfl fun idx _ => by
        rw [setIntegral_cellCube_indicator_cube]
  refine hcover.trans ?_
  -- the interior / boundary split
  set T : Finset (Fin d → ℤ) := (windowBox (k - 2) x rho).filter
    (fun idx => openCubeAtScale (cellCentre (k - 2) idx) (k - 1) ⊆ cube d (m : ℤ))
    with hTdef
  have hsplit := Finset.sum_filter_add_sum_filter_not (windowBox (k - 2) x rho)
    (fun idx => openCubeAtScale (cellCentre (k - 2) idx) (k - 1) ⊆ cube d (m : ℤ))
    (fun idx => ∫ p in truncatedCube d (m : ℤ) (k - 2) (cellCentre (k - 2) idx), E p)
  rw [← hsplit]
  -- the interior half
  have hinterior := hint M sOrder hs L m n hnm k hkn4 z x omega hz hx hgood
    u h g hdir hg hh rho R hrho0 hlt hR hgapCover hk27
  -- the boundary half, by the summed parent-local boundary row
  set Tc : Finset (Fin d → ℤ) := (windowBox (k - 2) x rho).filter
    (fun idx => ¬ (openCubeAtScale (cellCentre (k - 2) idx) (k - 1) ⊆
      cube d (m : ℤ))) with hTcdef
  have hPsub : ∀ idx ∈ windowBox (k - 2) x rho,
      stepRowParent (d := d) (k - 2) (m : ℤ) idx ⊆ cube d (m : ℤ) :=
    fun idx _ => stepRowParent_subset_cube (by omega) idx
  -- the bounded-overlap summation of the parents
  have hoverlap : ∑ idx ∈ windowBox (k - 2) x rho,
      (∫ p in stepRowParent (d := d) (k - 2) (m : ℤ) idx, E p) ≤
      (28 : ℝ) ^ d * windowCutoffEnergy M L omega m x u R := by
    have hrewrite : ∀ idx ∈ windowBox (k - 2) x rho,
        (∫ p in stepRowParent (d := d) (k - 2) (m : ℤ) idx, E p) =
          ∫ p in stepRowParent (d := d) (k - 2) (m : ℤ) idx, E' p := by
      intro idx hidx
      rw [hE'def, setIntegral_indicator_cube_of_subset (hPsub idx hidx)]
    rw [Finset.sum_congr rfl hrewrite]
    refine (sum_setIntegral_parents_le (k - 2) x rho hE'0 _
      (measurableSet_stepRowParent (k - 2) (m : ℤ))
      (fun idx _ => stepRowParent_subset_supWindow (by omega) idx)
      hE'int.integrableOn).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hE'def, setIntegral_supWindow_indicator_cube]
    have : windowCutoffEnergy M L omega m x u (rho + 14 * (3 : ℝ) ^ (k - 2)) ≤
        windowCutoffEnergy M L omega m x u R :=
      windowCutoffEnergy_mono M L omega m x u hgapCover
    exact this
  have hbdfinal : ∑ idx ∈ Tc,
      (∫ p in truncatedCube d (m : ℤ) (k - 2) (cellCentre (k - 2) idx), E p) ≤
      (1 / 16 : ℝ) * windowCutoffEnergy M L omega m x u R +
        Kbd * ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3 := by
    have hraw := hbd M sOrder hs L m n hnm k hkn4 z x omega hz hx hgood
      u h g hdir hg hh rho R hrho0 hlt hR hgapCover hk27
    have hover' : ∑ idx ∈ windowBox (k - 2) x rho,
        (∫ p in stepRowParent (d := d) (k - 2) (m : ℤ) idx,
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
        (28 : ℝ) ^ d * windowCutoffEnergy M L omega m x u R := by
      simpa only [hEdef] using hoverlap
    simp only [hEdef, hBuddef, hTcdef]
    refine hraw.trans ?_
    refine add_le_add ?_ le_rfl
    have hstep := mul_le_mul_of_nonneg_left hover'
      (by positivity : (0 : ℝ) ≤ 1 / (16 * (28 : ℝ) ^ d))
    refine hstep.trans (le_of_eq ?_)
    have h28 : ((28 : ℝ) ^ d) ≠ 0 := by positivity
    field_simp

  have hintfinal : ∑ idx ∈ T,
      (∫ p in truncatedCube d (m : ℤ) (k - 2) (cellCentre (k - 2) idx), E p) ≤
      Kint * ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3 := by
    rw [hTdef, hEdef, hBuddef]
    exact hinterior
  have hcomb := add_le_add hintfinal hbdfinal
  refine hcomb.trans (le_of_eq ?_)
  rw [hBuddef]
  field_simp
  ring

/-- **The boundary-cell manuscript row from the boundary-class cell row.**

Composing the reduction above with
`WindowStepAbsorption.boundaryCellManuscriptRow_of_windowStepRow`: the whole
frozen v6 anchor is then the bare application
`FrozenAssembly.harmonic_approximation_good_scales_of_cellRow d hCb hrow`. -/
theorem exists_boundaryCellManuscriptRow_of_boundaryStepCellParentRow (d : ℕ) [NeZero d]
    {Cbd : ℝ} (hCbd : 0 ≤ Cbd) (hbrow : BoundaryStepCellParentRow d Cbd) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ BoundaryCellManuscriptRow d Cb := by
  obtain ⟨Cstep, hCstep, hrow⟩ :=
    exists_boundaryWindowEnergyStepRow_of_boundaryStepCellParentRow d hCbd hbrow
  exact boundaryCellManuscriptRow_of_windowStepRow d hCstep hrow

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
