module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseScore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ResponseDensity

@[expose] public section

/-!
# Literal cutoff response carrier

The accumulated-error definition uses the real unit-sphere supremum at
cutoff `min l L`, whereas the measurable cutoff score uses finite quarter-net
atoms.  This file supplies their almost-sure annular comparison on one common
event, uniformly over all scales and cells.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open Filter MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

theorem cutoffLocalResponseScaleAtom_ne_top {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L j n : ℕ)
    (omega : Sample d) : cutoffLocalResponseScaleAtom M L j n omega ≠ ∞ := by
  unfold cutoffLocalResponseScaleAtom
  split_ifs
  · dsimp only [cutoffLocalResponseAnnulusMax]
    apply ne_of_lt
    rw [Finset.sup'_lt_iff]
    intro R _
    by_cases hann : triadicCubeShift R ∉ cube d ((j : ℤ) - 1)
    · rw [ite_eq_left hann]
      exact (localNormalizedResponseQuarterNetMax_ne_top
        M (min n L) R omega).lt_top
    · rw [ite_eq_right hann]
      simp
  · simp

theorem cutoffLocalResponseScore_ne_top {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (s epsilon K : ℝ) (j : ℕ) (omega : Sample d) :
    cutoffLocalResponseScore M L s epsilon K j omega ≠ ∞ := by
  unfold cutoffLocalResponseScore
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  rw [ENNReal.sum_ne_top]
  intro n _hn
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (cutoffLocalResponseScaleAtom_ne_top M L j n omega)

/-- The cutoff response score inherits the deterministic annular coloring
range of the uncutoff score. -/
theorem columnsIndep_cutoffResponseScoreArray {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (s epsilon K : ℝ) :
    SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (cutoffResponseScoreArray M L s epsilon K) (responseScoreRange d) :=
  columnsIndep_cutoffResponseScoreArray_of_separated M L s epsilon K
    (responseScoreRange d) responseScoreArray_annulus_separation

/-- One common full-measure set controls every unit direction at every
response scale with the deterministic cutoff `L`. -/
theorem ae_forall_section6Response_cutoff_le_two_mul_localNet
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ n : ℕ, ∀ R : TriadicCube d,
      R.scale = (n : ℤ) → ∀ e : Vec d, vecNormSq e = 1 →
        ENNReal.ofReal
            (section6Response M n (min n L) omega (triadicCubeShift R) e) ≤
          2 * localNormalizedResponseQuarterNetMax M (min n L) R omega := by
  rw [ae_all_iff]
  intro n
  rw [ae_all_iff]
  intro R
  filter_upwards
    [normalizedResponseQuarterNetMax_ae_eq_local M (min n L) R]
      with omega heq
  intro hscale e he
  calc
    ENNReal.ofReal
        (section6Response M n (min n L) omega (triadicCubeShift R) e) ≤
        normalizedDefect M (min n L) (Ch02.cubeDomain R) omega := by
      rw [section6Response_shift_eq_cutoffResponseOnCube
        M n (min n L) R hscale e omega]
      unfold cutoffResponseOnCube SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect
        paperScalarProbeMaxOn
      exact le_iSup_of_le ⟨e, he⟩ (le_refl _)
    _ ≤ 2 * normalizedResponseQuarterNetMax M (min n L)
          (Ch02.cubeDomain R) omega :=
      normalizedDefect_le_two_mul_quarterNetMax
        M (min n L) (Ch02.cubeDomain R) omega
    _ = 2 * localNormalizedResponseQuarterNetMax M (min n L) R omega := by
      rw [heq]

/-- Pointwise annular carrier comparison, conditional on the common
quarter-net event. -/
theorem sSup_section6Response_cutoff_le_two_mul_localResponseScaleAtom_toReal_of_localNet
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : Sample d)
    (hall : ∀ n : ℕ, ∀ R : TriadicCube d,
      R.scale = (n : ℤ) → ∀ e : Vec d, vecNormSq e = 1 →
        ENNReal.ofReal
            (section6Response M n (min n L) omega (triadicCubeShift R) e) ≤
          2 * localNormalizedResponseQuarterNetMax M (min n L) R omega)
    (j l : ℕ) (hlj : l + 2 ≤ j) (z : Vec d)
    (hzgrid : OnTriadicGrid l z)
    (hzann : z ∈ cube d j \ cube d (j - 1)) :
    sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M l (min l L) omega z e} ≤
      2 * (cutoffLocalResponseScaleAtom M L j l omega).toReal := by
  have hzparent : z ∈ cubeSet (originCube d (j : ℤ)) :=
    openCubeSet_subset_cubeSet _ hzann.1
  have hcover := cubeSet_subset_iUnion_descendantsAtScale
    (originCube d (j : ℤ))
    (show (l : ℤ) ≤ (originCube d (j : ℤ)).scale by
      change (l : ℤ) ≤ (j : ℤ)
      exact_mod_cast (show l ≤ j by omega)) hzparent
  obtain ⟨R, hR, hzR⟩ := Set.mem_iUnion₂.1 hcover
  have hscale : R.scale = (l : ℤ) := scale_eq_of_mem_descendantsAtScale hR
  have hshift : triadicCubeShift R = z :=
    triadicCubeShift_eq_of_onTriadicGrid_of_mem_cubeSet hscale hzgrid hzR
  have hannR : triadicCubeShift R ∉ cube d ((j : ℤ) - 1) := by
    rw [hshift]
    exact hzann.2
  have hnetAtom : localNormalizedResponseQuarterNetMax M (min l L) R omega ≤
      cutoffLocalResponseScaleAtom M L j l omega := by
    unfold cutoffLocalResponseScaleAtom
    rw [dite_eq_left hlj]
    dsimp only [cutoffLocalResponseAnnulusMax]
    calc
      localNormalizedResponseQuarterNetMax M (min l L) R omega =
          (if triadicCubeShift R ∉ cube d ((j : ℤ) - 1) then
            localNormalizedResponseQuarterNetMax M (min l L) R omega else 0) := by
        rw [ite_eq_left hannR]
      _ ≤ _ := Finset.le_sup' (fun Q =>
        if triadicCubeShift Q ∉ cube d ((j : ℤ) - 1) then
          localNormalizedResponseQuarterNetMax M (min l L) Q omega else 0) hR
  let values : Set ℝ := {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    t = section6Response M l (min l L) omega z e}
  have hnonempty : values.Nonempty := by
    let e : ScalarProbeUnitSphere d := Classical.arbitrary _
    exact ⟨section6Response M l (min l L) omega z e.1, e.1, e.2, rfl⟩
  have htop : 2 * cutoffLocalResponseScaleAtom M L j l omega ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num)
      (cutoffLocalResponseScaleAtom_ne_top M L j l omega)
  have hupper : ∀ t ∈ values,
      t ≤ 2 * (cutoffLocalResponseScaleAtom M L j l omega).toReal := by
    rintro t ⟨e, he, rfl⟩
    have hENN := (hall l R hscale e he).trans
      (mul_le_mul_of_nonneg_left hnetAtom (by norm_num))
    have hreal := (ENNReal.ofReal_le_iff_le_toReal htop).mp hENN
    rw [hshift] at hreal
    simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_mul] using hreal
  exact csSup_le hnonempty hupper

/-- The literal cutoff response supremum is dominated almost surely by the
measurable cutoff score atom, simultaneously over annular cells. -/
theorem ae_forall_sSup_section6Response_cutoff_le_two_mul_localResponseScaleAtom_toReal
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ j l : ℕ, l + 2 ≤ j →
      ∀ z : Vec d, OnTriadicGrid l z →
        z ∈ cube d j \ cube d (j - 1) →
          sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
              t = section6Response M l (min l L) omega z e} ≤
            2 * (cutoffLocalResponseScaleAtom M L j l omega).toReal := by
  filter_upwards
    [ae_forall_section6Response_cutoff_le_two_mul_localNet M L]
      with omega hall
  intro j l hlj z hzgrid hzann
  exact
    sSup_section6Response_cutoff_le_two_mul_localResponseScaleAtom_toReal_of_localNet
      M L omega hall j l hlj z hzgrid hzann

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
