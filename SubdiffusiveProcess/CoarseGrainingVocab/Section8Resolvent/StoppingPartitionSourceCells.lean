import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionGeometricHandoff
import Mathlib.Topology.Compactness.LocallyFinite




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ} {Cell : Type*}

/-- The indices whose enlarged cells meet a fixed closed ball form a finite
set. -/
theorem finite_stoppingEnlargements_meeting_closedBall
    (enlargement : Cell → Set (Vec d)) (hlocallyFinite : LocallyFinite enlargement)
    (x0 : Vec d) (R : ℝ) :
    {q | (enlargement q ∩ Metric.closedBall x0 R).Nonempty}.Finite :=
  hlocallyFinite.finite_nonempty_inter_compact (isCompact_closedBall x0 R)

/-- Source cells, represented as the finite set of enlargements meeting the
closed source ball. -/
def stoppingSourceCells (enlargement : Cell → Set (Vec d))
    (hlocallyFinite : LocallyFinite enlargement) (x0 : Vec d) (R : ℝ) :
    Finset Cell :=
  (finite_stoppingEnlargements_meeting_closedBall enlargement hlocallyFinite x0 R).toFinset

theorem mem_stoppingSourceCells_iff
    (enlargement : Cell → Set (Vec d))
    (hlocallyFinite : LocallyFinite enlargement) (x0 : Vec d) (R : ℝ)
    (q : Cell) :
    q ∈ stoppingSourceCells enlargement hlocallyFinite x0 R ↔
      (enlargement q ∩ Metric.closedBall x0 R).Nonempty := by
  simp [stoppingSourceCells]

/-- A locally finite enlargement family over a global cell cover has a
nonempty source family around every nonnegative-radius ball. -/
theorem stoppingSourceCells_nonempty
    (cell enlargement : Cell → Set (Vec d))
    (hlocallyFinite : LocallyFinite enlargement)
    (hcellSubset : ∀ q, cell q ⊆ enlargement q)
    (hcover : ∀ x, ∃ q, x ∈ cell q)
    (x0 : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    (stoppingSourceCells enlargement hlocallyFinite x0 R).Nonempty := by
  obtain ⟨q, hq⟩ := hcover x0
  refine ⟨q, (mem_stoppingSourceCells_iff enlargement hlocallyFinite x0 R q).mpr ?_⟩
  exact ⟨x0, hcellSubset q hq, Metric.mem_closedBall_self hR⟩

/-- Specialization to centred threefold enlargements of translated stopping
cells. -/
theorem stoppingSourceCells_translatedCube_nonempty
    (scale : Cell → ℤ) (centre : Cell → Vec d)
    (hlocallyFinite : LocallyFinite fun q ↦
      translatedCube d (scale q + 1) (centre q))
    (hcover : ∀ x, ∃ q, x ∈ translatedCube d (scale q) (centre q))
    (x0 : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    (stoppingSourceCells
      (fun q ↦ translatedCube d (scale q + 1) (centre q))
      hlocallyFinite x0 R).Nonempty := by
  apply stoppingSourceCells_nonempty
    (fun q ↦ translatedCube d (scale q) (centre q))
    (fun q ↦ translatedCube d (scale q + 1) (centre q))
    hlocallyFinite
  · intro q
    exact translatedCube_subset_translatedCube_sameCenter (by omega) (centre q)
  · exact hcover
  · exact hR

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
