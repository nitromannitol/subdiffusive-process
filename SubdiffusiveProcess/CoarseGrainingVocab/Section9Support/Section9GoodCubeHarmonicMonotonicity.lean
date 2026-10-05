module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeProvider

@[expose] public section

/-!
# The exported oscillation display at constant one

The statement requires only `0 < eps0`. Its exported harmonic
oscillation display therefore follows from inclusion with `eps0 = 1`.
This does not supply the strict oscillation decay used internally in the
source's exit-time lower bound.
That analytic step remains a separate obligation.
-/

set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Oscillation increases when its observation set is enlarged. -/
theorem oscillation_mono_set {d : ℕ} {S T : Set (Vec d)}
    (hST : S ⊆ T) (h : Vec d → ℝ) : oscillation S h ≤ oscillation T h := by
  unfold Section9SupportInput.oscillation
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  exact le_iSup_of_le x (le_iSup_of_le (hST hx)
    (le_iSup_of_le y (le_iSup_of_le (hST hy) le_rfl)))

/-- Every admissible geometry gives the exported oscillation estimate with
constant one, for any coefficient and every function in the tested class. -/
theorem localHarmonicOscillation_one_of_isLocalCubeGeometry {d j1 j2 : ℕ}
    {grid : Finset (Vec d)} {U : Cube d}
    {Pfam : Set (Cube d × Cube d)} {Qfam Afam : Set (Cube d)}
    (hgeo : IsLocalCubeGeometry grid j1 j2 U Pfam Qfam Afam) (a : Vec d → ℝ) :
    LocalHarmonicOscillation a 1 Pfam := by
  constructor
  intro p hp h _
  rw [ENNReal.ofReal_one, one_mul]
  exact oscillation_mono_set (subset_closure.trans (hgeo.pair_nested p hp)) h

/-- The exact `hoscillation` input of the provider, with its free exported
constant chosen to be one. No exceptional event or analytic premise occurs. -/
theorem goodCubeDisplay_localHarmonicOscillation_one {d : ℕ}
    (c eps1 B : ℝ) (j1 j2 : ℕ)
    (E0 : GMCModel d → ℕ → Lattice d → Set (PotentialSample d)) :
    GoodCubeDisplay d c eps1 B j1 j2 E0
      (fun M n _ omega _ Pfam _ _ =>
        LocalHarmonicOscillation (aCutoff M n omega) 1 Pfam) := by
  intro M _ n grid z Pfam Qfam Afam hgeo omega _ law _
  exact localHarmonicOscillation_one_of_isLocalCubeGeometry hgeo (aCutoff M n omega)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
