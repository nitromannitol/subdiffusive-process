import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedSourceParentReadout

/-!
# Transporting a finite cell family onto a larger cell set

The two-radius Neumann family is indexed by an abstract finite type whose cell
map lands inside — but does not exhaust — the one-step source cells.  The
fourth conjunct of `DualCellMajorantInputs`, by contrast, needs an observable
defined on *every* source cell.

`nfExtendByZero` extends the family's scalar observable by zero off the image
of the cell map.  The two facts needed downstream are that this preserves
measurability and nonnegativity, and that the resulting normalized fourth
moment over the larger cell set is dominated by the family's own normalized
fourth moment whenever the family index is no larger than the cell set.

Nothing here is specific to the Neumann family or to triadic geometry beyond
the type of cells.
-/

open MeasureTheory Homogenization
open scoped ENNReal BigOperators Classical

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ} {ι Omega : Type*}

/-- Extend a family observable, indexed by cells through `cell`, to every
triadic cube, by zero off the image of `cell`. -/
def nfExtendByZero (cell : ι → TriadicCube d) (G : ι → Omega → ℝ)
    (R : TriadicCube d) (omega : Omega) : ℝ :=
  if h : ∃ i, cell i = R then G h.choose omega else 0

theorem nfExtendByZero_of_not_mem {cell : ι → TriadicCube d}
    {G : ι → Omega → ℝ} {R : TriadicCube d} (hR : ¬ ∃ i, cell i = R)
    (omega : Omega) : nfExtendByZero cell G R omega = 0 := by
  simp only [nfExtendByZero, dif_neg hR]

/-- On the image of the cell map the extension is the family observable at
*some* index over that cell. -/
theorem exists_nfExtendByZero_eq {cell : ι → TriadicCube d}
    {G : ι → Omega → ℝ} {R : TriadicCube d} (hR : ∃ i, cell i = R) :
    ∃ i, cell i = R ∧ ∀ omega, nfExtendByZero cell G R omega = G i omega :=
  ⟨hR.choose, hR.choose_spec, fun _ ↦ by simp only [nfExtendByZero, dif_pos hR]⟩

theorem nfExtendByZero_nonneg {cell : ι → TriadicCube d}
    {G : ι → Omega → ℝ} (hG : ∀ i omega, 0 ≤ G i omega)
    (R : TriadicCube d) (omega : Omega) :
    0 ≤ nfExtendByZero cell G R omega := by
  by_cases h : ∃ i, cell i = R
  · simp only [nfExtendByZero, dif_pos h]
    exact hG _ omega
  · simp only [nfExtendByZero, dif_neg h]
    exact le_rfl

theorem measurable_nfExtendByZero [MeasurableSpace Omega]
    {cell : ι → TriadicCube d} {G : ι → Omega → ℝ}
    (hG : ∀ i, Measurable (G i)) (R : TriadicCube d) :
    Measurable (nfExtendByZero cell G R) := by
  by_cases h : ∃ i, cell i = R
  · have heq : nfExtendByZero cell G R = G h.choose := by
      funext omega
      simp only [nfExtendByZero, dif_pos h]
    rw [heq]
    exact hG _
  · have heq : nfExtendByZero cell G R = fun _ : Omega ↦ (0 : ℝ) := by
      funext omega
      simp only [nfExtendByZero, dif_neg h]
    rw [heq]
    exact measurable_const

/-- The extension only redistributes mass: its fourth-power sum over any
finite cell set is at most the family's own fourth-power sum. -/
theorem sum_ofReal_nfExtendByZero_pow_four_le [Fintype ι] [DecidableEq ι]
    (cell : ι → TriadicCube d) (G : ι → Omega → ℝ)
    (s : Finset (TriadicCube d)) (omega : Omega) :
    ∑ R ∈ s, ENNReal.ofReal (nfExtendByZero cell G R omega ^ (4 : ℕ)) ≤
      ∑ i, ENNReal.ofReal (G i omega ^ (4 : ℕ)) := by
  set T : Finset (TriadicCube d) := s.filter (fun R ↦ ∃ i, cell i = R) with hT
  have hzero : ∀ R ∈ s, R ∉ T →
      ENNReal.ofReal (nfExtendByZero cell G R omega ^ (4 : ℕ)) = 0 := by
    intro R hRs hRT
    have hno : ¬ ∃ i, cell i = R := by
      intro hex
      exact hRT (Finset.mem_filter.mpr ⟨hRs, hex⟩)
    rw [nfExtendByZero_of_not_mem hno]
    simp
  have hsplit :
      ∑ R ∈ T, ENNReal.ofReal (nfExtendByZero cell G R omega ^ (4 : ℕ)) =
        ∑ R ∈ s, ENNReal.ofReal
          (nfExtendByZero cell G R omega ^ (4 : ℕ)) :=
    Finset.sum_subset (Finset.filter_subset _ _) hzero
  rw [← hsplit]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hTempty : T = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro R hR
      obtain ⟨_, hex⟩ := Finset.mem_filter.mp hR
      obtain ⟨i, _⟩ := hex
      exact hι.elim i
    rw [hTempty, Finset.sum_empty]
    exact zero_le _
  · obtain ⟨i0⟩ := hι
    obtain ⟨sec, hcellSec, hvalue⟩ :
        ∃ sec : TriadicCube d → ι, (∀ R ∈ T, cell (sec R) = R) ∧
          (∀ R ∈ T, ∀ w : Omega,
            nfExtendByZero cell G R w = G (sec R) w) := by
      refine ⟨fun R ↦ if h : ∃ i, cell i = R then h.choose else i0,
        ?_, ?_⟩
      · intro R hR
        obtain ⟨_, hex⟩ := Finset.mem_filter.mp hR
        simp only [dif_pos hex]
        exact hex.choose_spec
      · intro R hR w
        obtain ⟨_, hex⟩ := Finset.mem_filter.mp hR
        simp only [nfExtendByZero, dif_pos hex]
    have hinj : Set.InjOn sec (T : Set (TriadicCube d)) := by
      intro R hR R' hR' heq
      have hR1 : R ∈ T := hR
      have hR2 : R' ∈ T := hR'
      rw [← hcellSec R hR1, ← hcellSec R' hR2, heq]
    have hstep : ∑ R ∈ T, ENNReal.ofReal (G (sec R) omega ^ (4 : ℕ)) ≤
        ∑ i, ENNReal.ofReal (G i omega ^ (4 : ℕ)) := by
      rw [← Finset.sum_image
        (f := fun i ↦ ENNReal.ofReal (G i omega ^ (4 : ℕ))) hinj]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    refine le_trans (le_of_eq ?_) hstep
    exact Finset.sum_congr rfl fun R hR ↦ by rw [hvalue R hR omega]

/-! ## The subtype case: the extension is exact -/

/-- When the cell map is the coercion of a subtype of a finite cell set, the
extension recovers the family observable on the nose. -/
theorem nfExtendByZero_val_eq {s : Finset (TriadicCube d)}
    (G : {R : TriadicCube d // R ∈ s} → Omega → ℝ)
    (i : {R : TriadicCube d // R ∈ s}) (omega : Omega) :
    nfExtendByZero (fun j : {R : TriadicCube d // R ∈ s} ↦
        (j : TriadicCube d)) G (i : TriadicCube d) omega = G i omega := by
  have hex : ∃ j : {R : TriadicCube d // R ∈ s},
      (j : TriadicCube d) = (i : TriadicCube d) := ⟨i, rfl⟩
  have hchoose : hex.choose = i := Subtype.ext hex.choose_spec
  simp only [nfExtendByZero, dif_pos hex, hchoose]

/-- Exact transfer: over any finite cell set containing the family's own
cells, the extension's fourth-power sum **equals** the family's. -/
theorem sum_ofReal_nfExtendByZero_val_eq
    {s t : Finset (TriadicCube d)} (hst : s ⊆ t)
    (G : {R : TriadicCube d // R ∈ s} → Omega → ℝ) (omega : Omega) :
    ∑ R ∈ t, ENNReal.ofReal
        (nfExtendByZero (fun j : {R : TriadicCube d // R ∈ s} ↦
          (j : TriadicCube d)) G R omega ^ (4 : ℕ)) =
      ∑ i : {R : TriadicCube d // R ∈ s},
        ENNReal.ofReal (G i omega ^ (4 : ℕ)) := by
  have hzero : ∀ R ∈ t, R ∉ s → ENNReal.ofReal
      (nfExtendByZero (fun j : {R : TriadicCube d // R ∈ s} ↦
        (j : TriadicCube d)) G R omega ^ (4 : ℕ)) = 0 := by
    intro R _hRt hRs
    have hno : ¬ ∃ j : {R : TriadicCube d // R ∈ s},
        (j : TriadicCube d) = R := by
      rintro ⟨j, hj⟩
      exact hRs (hj ▸ j.2)
    rw [nfExtendByZero_of_not_mem hno]
    simp
  rw [← Finset.sum_subset hst hzero,
    ← Finset.sum_coe_sort s (fun R ↦ ENNReal.ofReal
      (nfExtendByZero (fun j : {R : TriadicCube d // R ∈ s} ↦
        (j : TriadicCube d)) G R omega ^ (4 : ℕ)))]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [nfExtendByZero_val_eq]

/-- Normalized form: if the family index is no larger than the cell set, the
extension's normalized `ENNReal` fourth moment over the cell set is dominated
by the family's. -/
theorem lintegral_normalized_ofReal_nfExtendByZero_pow_four_le
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Omega] {mu : Measure Omega}
    (cell : ι → TriadicCube d) (G : ι → Omega → ℝ)
    (s : Finset (TriadicCube d))
    (hcard : (Finset.univ : Finset ι).card ≤ s.card) :
    ∫⁻ omega, (((s.card : ℝ≥0∞))⁻¹ *
        ∑ R ∈ s, ENNReal.ofReal
          (nfExtendByZero cell G R omega ^ (4 : ℕ))) ∂mu ≤
      ∫⁻ omega, ((((Finset.univ : Finset ι).card : ℝ≥0∞))⁻¹ *
        ∑ i, ENNReal.ofReal (G i omega ^ (4 : ℕ))) ∂mu := by
  apply lintegral_mono
  intro omega
  have hcard' : (((s.card : ℝ≥0∞))⁻¹) ≤
      ((((Finset.univ : Finset ι).card : ℝ≥0∞))⁻¹) := by
    apply ENNReal.inv_le_inv.mpr
    exact_mod_cast hcard
  exact mul_le_mul' hcard'
    (sum_ofReal_nfExtendByZero_pow_four_le cell G s omega)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
