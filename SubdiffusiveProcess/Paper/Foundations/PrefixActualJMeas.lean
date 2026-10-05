module

public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorResponse

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model
open Homogenization hiding Vec
open scoped ENNReal

namespace SubdiffusiveProcess.Paper

private theorem J_eq_ofReal_realSup {d : ℕ} [NeZero d] (M : GMCModel d)
    (n : ℕ) (omega : PotentialSample d) (x : Vec d) :
    sSup {v : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
      v = ENNReal.ofReal (section6Response M n n omega x e)} =
      ENNReal.ofReal (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M n n omega x e}) := by
  let S : Set ℝ := {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M n n omega x e}
  have hb : BddAbove S := bddAbove_section6Response_unitSphere M n n omega x
  have hne : S.Nonempty := by
    obtain ⟨e, he⟩ := (Classical.arbitrary (ScalarProbeUnitSphere d))
    exact ⟨section6Response M n n omega x e, e, he, rfl⟩
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨e, he, rfl⟩
    exact ENNReal.ofReal_le_ofReal (le_csSup hb ⟨e, he, rfl⟩)
  · have hJtop : sSup {v : ENNReal | ∃ e : Vec d,
          vecNormSq e = 1 ∧ v = ENNReal.ofReal (section6Response M n n omega x e)} ≠ ∞ := by
      have hle : sSup {v : ENNReal | ∃ e : Vec d,
          vecNormSq e = 1 ∧ v = ENNReal.ofReal (section6Response M n n omega x e)} ≤
          ENNReal.ofReal (sSup S) := by
        apply sSup_le
        rintro v ⟨e, he, rfl⟩
        exact ENNReal.ofReal_le_ofReal (le_csSup hb ⟨e, he, rfl⟩)
      exact (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
    apply (ENNReal.ofReal_le_iff_le_toReal hJtop).mpr
    apply csSup_le hne
    have hsup : ∀ t ∈ S,
        ENNReal.ofReal t ≤ sSup {v : ENNReal | ∃ e : Vec d,
          vecNormSq e = 1 ∧ v = ENNReal.ofReal (section6Response M n n omega x e)} := by
      rintro t ⟨e, he, rfl⟩
      exact le_sSup ⟨e, he, rfl⟩
    intro t ht
    exact (ENNReal.ofReal_le_iff_le_toReal hJtop).mp (hsup t ht)

theorem aux_lem_prefix_limit_actual_J_meas {d : ℕ} [NeZero d] (M : GMCModel d)
    (n : ℕ) (x : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
        v = ENNReal.ofReal (section6Response M n n omega x e)}) := by
  have hm := SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.measurable_sSup_section6Response_unitSphere M n n x
  convert hm.ennreal_ofReal using 1
  funext omega
  exact J_eq_ofReal_realSup M n omega x

end SubdiffusiveProcess.Paper
