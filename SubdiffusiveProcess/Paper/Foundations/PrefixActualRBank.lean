module

public import SubdiffusiveProcess.Paper.primitive_scores_finite

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section
namespace Paper
open SubdiffusiveProcess.Frozen.Assumptions

variable {d : ℕ}

/-- The literal response-score supremum is bounded by a finite grid bank at each depth. -/
theorem aux_prefix_Rsc_le_guarded_bank (M : GMCModel d) (s : ℝ)
    (m : ℕ) (z : Vec d) (omega : PotentialSample d) :
    sSup {v : ℝ≥0∞ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid n (x - z) ∧
      x - z ∈ cube d (j : ℤ) \ cube d ((j : ℤ) - 1) ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
        aux_psf_Jval M n omega x} ≤
    (Finset.Icc 0 m).sup (fun j =>
      (Finset.Icc 0 j).sup (fun n =>
        if n + 2 ≤ j then
          (aux_psf_Rindex d j).sup (fun k =>
            ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
              aux_psf_Jval M n omega (aux_psf_Rpoint n z k))
        else 0)) := by
  refine sSup_le ?_
  rintro v ⟨j, n, hjm, hnj, x, hgrid, hannulus, rfl⟩
  obtain ⟨k, hk, rfl⟩ := aux_psf_Rpoint_mem n j z x hgrid hannulus.1
  have hj : j ∈ Finset.Icc 0 m := Finset.mem_Icc.mpr ⟨Nat.zero_le j, hjm⟩
  have hn : n ∈ Finset.Icc 0 j := Finset.mem_Icc.mpr ⟨Nat.zero_le n, by omega⟩
  calc
    _ ≤ (aux_psf_Rindex d j).sup (fun k =>
          ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
            aux_psf_Jval M n omega (aux_psf_Rpoint n z k)) := Finset.le_sup hk
    _ ≤ (Finset.Icc 0 j).sup (fun n =>
          if n + 2 ≤ j then
            (aux_psf_Rindex d j).sup (fun k =>
              ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
                aux_psf_Jval M n omega (aux_psf_Rpoint n z k))
          else 0) := by
            simpa [hnj] using (Finset.le_sup (f := fun n =>
              if n + 2 ≤ j then
                (aux_psf_Rindex d j).sup (fun k =>
                  ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
                    aux_psf_Jval M n omega (aux_psf_Rpoint n z k))
              else 0) hn)
    _ ≤ _ := Finset.le_sup (f := fun j =>
      (Finset.Icc 0 j).sup (fun n =>
        if n + 2 ≤ j then
          (aux_psf_Rindex d j).sup (fun k =>
            ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
              aux_psf_Jval M n omega (aux_psf_Rpoint n z k))
        else 0)) hj

end Paper
