import SubdiffusiveProcess.Paper.Foundations.PrefixActualPrawMeas
import SubdiffusiveProcess.Paper.primitive_scores_finite
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.AccumulatedErrorMeasurability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

noncomputable section

open MeasureTheory Filter
open scoped Topology
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess

namespace Paper

private theorem spatial_sup_meas {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {W : Set (Vec d)} (hWopen : IsOpen W)
    (F : Ω → Vec d → ENNReal)
    (hcont : ∀ omega, Continuous (F omega))
    (hmeas : ∀ x, Measurable (fun omega => F omega x)) :
    Measurable (fun omega => sSup {v : ENNReal | ∃ x ∈ W, v = F omega x}) := by exact Paper.aux_dedup_d107_spatialSup_meas (d := d) (Ω := Ω) (W := W) (hWopen := hWopen) (F := F) (hcont := hcont) (hmeas := hmeas)

private def normOn {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) : ENNReal :=
  sSup {v : ENNReal | ∃ x : Vec d, x ∈ W ∧ v = ENNReal.ofReal |f x|}

theorem aux_dsc_block_meas {d : ℕ} (s : ℝ) (k : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          normOn (translatedCube d k z) (shellBlock k j omega)}) := by
  have hinner : ∀ j : ℕ, Measurable (fun omega : PotentialSample d =>
      normOn (translatedCube d k z) (shellBlock k j omega)) := by
    intro j
    change Measurable (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ x ∈ translatedCube d k z,
        v = ENNReal.ofReal |shellBlock k j omega x|})
    apply spatial_sup_meas
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.isOpen_translatedCube d k z)
    · intro omega
      exact ENNReal.continuous_ofReal.comp
        ((SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_shellBlock k j omega).abs)
    · intro x
      exact (continuous_abs.measurable.comp
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.measurable_shellBlock_eval k j x)).ennreal_ofReal
  have hterm : ∀ j : ℕ, Measurable (fun omega : PotentialSample d =>
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
        normOn (translatedCube d k z) (shellBlock k j omega)) := by
    intro j
    exact Measurable.const_mul (hinner j) _
  have heq : (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          normOn (translatedCube d k z) (shellBlock k j omega)}) =
      (fun omega => ⨆ j : {j : ℕ // j ≤ k},
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          normOn (translatedCube d k z) (shellBlock k j omega)) := by
    funext omega
    apply le_antisymm
    · refine sSup_le ?_
      rintro v ⟨j, hj, rfl⟩
      exact le_iSup_of_le ⟨j, hj⟩ le_rfl
    · refine iSup_le fun j => ?_
      exact le_sSup ⟨j.1, j.2, rfl⟩
  rw [heq]
  exact Measurable.iSup (fun j => hterm j)


end Paper
