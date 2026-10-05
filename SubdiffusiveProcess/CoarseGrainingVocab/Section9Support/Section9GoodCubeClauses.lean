module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeLayerEvents
public import SubdiffusiveProcess.CoarseGrainingVocab.RestrictedCoefficientSigma

@[expose] public section

/-!
# The probabilistic clauses 7d and 7e of the good-cube anchor

`SubdiffusiveProcess.Section9.weighted_good_cube_events` asks for a multiscale event field
`E` with

* clause 7d `IndependentEventScales`: the whole spatial field at scale `j` is
  independent of the whole spatial field at scale `j' ≠ j`;
* clause 7e `MultiscaleFiniteRangeIndependentEvents … (fun j => Cdep * 3 ^ j)`:
  at a fixed `j`, subfamilies whose dependence boxes are far apart are
  independent.

`mfd:in-deterministic` and `s.tightness` gets both
from the locality of the events: `G(U)` sees only `a_n` on `CU` (hence only the
shells `0, …, n`), and `B_j(U)` sees only `g_{n+j}` on a box of side `C3^{n+j}`.
This file turns those two locality statements into the two clauses, for the
*whole* field — `j = 0` included — and with the exact constant relation
`C + √d ≤ Cdep`.

The two locality hypotheses are clauses 7a and 7b of the anchor: 7b is
discharged by `Section9GoodCubeLayerEvents.measurableSet_layerEvent`
(obligation O3); 7a is the remaining measurability debt, reduced in
`Section9GoodCubeRestrictedBad.lean` (gap G1) and by obligations O1/O2.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Homogenization Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open _root_.SubdiffusiveProcess.Model

variable {d : ℕ}

/-! ## The prefix σ-field of the cutoff -/

/-- The window-restricted σ-field is below any σ-field for which every window
evaluation is measurable.  (The established `restrictedCoefficientSigma_le` is the
special case of the ambient σ-field.) -/
theorem restrictedCoefficientSigma_le_of_measurable {Omega : Type*}
    {m : MeasurableSpace Omega} {a : Omega → Vec d → ℝ} {B : Set (Vec d)}
    (h : ∀ x ∈ B, @Measurable Omega ℝ m _ fun omega => a omega x) :
    restrictedCoefficientSigma a B ≤ m := by
  refine iSup_le fun x => ?_
  have hx := (h (x : Vec d) x.2).comap_le
  rwa [(BorelSpace.measurable_eq : (Real.measurableSpace : MeasurableSpace ℝ) = borel ℝ)] at hx

/-- **The locality of `a_n` in the shells.**  The finite cutoff `a_n` is a
function of the shells `0, …, n` only, so any window-restricted σ-field of `a_n`
is below the σ-field of that prefix of shells
(`mfd:in-deterministic` and `s.tightness`, `mfd:in-deterministic` and `s.tightness`). -/
theorem restrictedCoefficientSigma_aCutoff_le_prefix (M : GMCModel d) (n : ℕ)
    (B : Set (Vec d)) :
    restrictedCoefficientSigma
        (fun omega : PotentialSample d => aCutoff M n omega) B ≤
      ⨆ k ∈ Set.Iic n, MeasurableSpace.comap
        (fun omega : PotentialSample d => omega k) inferInstance := by
  refine restrictedCoefficientSigma_le_of_measurable ?_
  intro x _
  let : MeasurableSpace (PotentialSample d) :=
    ⨆ k ∈ Set.Iic n, MeasurableSpace.comap
      (fun omega : PotentialSample d => omega k) inferInstance
  have hcoord : ∀ k ∈ Finset.range (n + 1),
      Measurable (fun omega : PotentialSample d => omega k) := by
    intro k hk
    refine Measurable.of_comap_le ?_
    exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iic n) =>
      MeasurableSpace.comap (fun omega : PotentialSample d => omega i) inferInstance)
      k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  show Measurable (fun omega : PotentialSample d => aCutoff M n omega x)
  unfold _root_.SubdiffusiveProcess.Model.aCutoff
  refine Measurable.exp ?_
  refine Finset.measurable_sum _ fun k hk => ?_
  exact ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp (hcoord k hk)).sub_const _

/-- The cutoff's window-restricted σ-field is below its shell-local source
σ-field on an open window.  (Re-derivation of the private
`SubdiffusiveProcess.CoarseGrainingVocab.measurable_aCutoff_eval_local` at the level this file
needs; the private lemma cannot be named from outside its module.) -/
theorem restrictedCoefficientSigma_aCutoff_le_localSource [NeZero d]
    (M : GMCModel d) (L : ℕ) {U : Set (Vec d)} (hU : IsOpen U) :
    restrictedCoefficientSigma
        (fun omega : PotentialSample d => aCutoff M L omega) U ≤
      SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma L U := by
  refine restrictedCoefficientSigma_le_of_measurable ?_
  intro x hx
  have hcoord : ∀ k : Fin (L + 1),
      @Measurable (PotentialSample d) (PotentialField d)
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma L U)
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U)
        (fun omega => omega k) := by
    intro k
    refine Measurable.of_comap_le (le_iSup
      (fun q : Fin (L + 1) => (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U).comap
        (fun omega : PotentialSample d => omega q)) k)
  have heval : ∀ k : Fin (L + 1),
      @Measurable (PotentialSample d) ℝ
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma L U) _
        (fun omega => omega k x) := fun k =>
    (SubdiffusiveProcess.CoarseGrainingVocab.measurable_eval_potentialFieldLocalSigma_of_mem_isOpen
      hU hx).comp (hcoord k)
  show @Measurable (PotentialSample d) ℝ
    (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma L U) _
    (fun omega => aCutoff M L omega x)
  unfold _root_.SubdiffusiveProcess.Model.aCutoff
  apply Measurable.exp
  refine Finset.measurable_sum (Finset.range (L + 1)) fun k hk => ?_
  exact (heval ⟨k, Finset.mem_range.mp hk⟩).sub_const _

/-! ## Clause 7d -/

/-- **Clause 7d.**  The layer-zero event sees the shells `0, …, n`, every later
layer sees a single shell, and the shells are independent
(`SubdiffusiveProcess.Model.ShellLawPrefix.independent`), so the whole spatial
fields at different scales are independent. -/
theorem independentEventScales_goodCube (M : GMCModel d) (n : ℕ) {C : ℝ}
    {E : ℕ → Lattice d → Set (PotentialSample d)}
    (hE0 : ∀ z : Lattice d,
      MeasurableSet[restrictedCoefficientSigma
        (fun omega : PotentialSample d => aCutoff M n omega) (nativeBox n C z)] (E 0 z))
    (hEj : ∀ j, 1 ≤ j → ∀ z : Lattice d,
      MeasurableSet[shellLocalSigma (n + j) (layerBox n j C z)] (E j z)) :
    IndependentEventScales M.P.toMeasure E := by
  refine independentEventScales_of_blocks M.shellPrefix.independent
    (goodCubeBlock n) (pairwise_disjoint_goodCubeBlock n) ?_
  intro j
  refine MeasurableSpace.generateFrom_le ?_
  rintro A ⟨z, -, rfl⟩
  match j with
  | 0 =>
      have h := (restrictedCoefficientSigma_aCutoff_le_prefix M n (nativeBox n C z)) _ (hE0 z)
      exact h
  | (i + 1) =>
      have hle : shellLocalSigma (n + (i + 1)) (layerBox n (i + 1) C z) ≤
          ⨆ k ∈ goodCubeBlock n (i + 1), MeasurableSpace.comap
            (fun omega : PotentialSample d => omega k) inferInstance := by
        refine le_trans (MeasurableSpace.comap_mono
          (potentialFieldLocalSigma_le_borel (layerBox n (i + 1) C z))) ?_
        exact le_iSup₂ (f := fun k (_ : k ∈ goodCubeBlock n (i + 1)) =>
          MeasurableSpace.comap (fun omega : PotentialSample d => omega k) inferInstance)
          (n + (i + 1)) rfl
      exact hle _ (hEj (i + 1) (Nat.le_add_left 1 i) z)

/-! ## Clause 7e -/

/-- **Clause 7e at scale zero.**  The layer-zero events, being `a_n`-local on the
boxes `CU`, are independent across site sets separated by more than `Cdep`
lattice steps, by the finite-range independence of the cutoff source σ-fields
(`SubdiffusiveProcess.CoarseGrainingVocab.indep_aCutoffPotentialLocalSigma_of_separation`). -/
theorem finiteRangeIndependentEvents_layerZero [NeZero d] (M : GMCModel d)
    {C : ℝ} {Cdep : ℕ} (hCdep : C + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ)) (n : ℕ)
    (E : Lattice d → Set (PotentialSample d))
    (hE : ∀ z : Lattice d,
      MeasurableSet[restrictedCoefficientSigma
        (fun omega : PotentialSample d => aCutoff M n omega) (nativeBox n C z)] (E z)) :
    FiniteRangeIndependentEvents M.P.toMeasure (Cdep * 3 ^ 0) E := by
  intro S T hsep
  have hmeasU : MeasurableSet (⋃ z ∈ S, nativeBox n C z) :=
    MeasurableSet.biUnion S.to_countable fun z _ =>
      (isOpen_centeredAxisCube _ _).measurableSet
  have hmeasV : MeasurableSet (⋃ z ∈ T, nativeBox n C z) :=
    MeasurableSet.biUnion T.to_countable fun z _ =>
      (isOpen_centeredAxisCube _ _).measurableSet
  have hsepbox : ∀ ⦃p q : Vec d⦄, p ∈ (⋃ z ∈ S, nativeBox n C z) →
      q ∈ (⋃ z ∈ T, nativeBox n C z) →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ n ≤ Homogenization.Book.Ch02.vecNorm (p - q) := by
    intro p q hp hq
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨z', hz', hqz⟩ := Set.mem_iUnion₂.mp hq
    have := euclidean_separation_of_latticeDist (n := n) (j := 0) hCdep
      (hsep z hz z' hz') hpz hqz
    simpa only [euclideanNorm_eq_vecNorm, Nat.add_zero] using this
  have hindep := SubdiffusiveProcess.CoarseGrainingVocab.indep_aCutoffPotentialLocalSigma_of_separation
    M n (⋃ z ∈ S, nativeBox n C z) (⋃ z ∈ T, nativeBox n C z) hmeasU hmeasV hsepbox
  have hdom : ∀ (R : Set (Lattice d)),
      eventFieldSigma E R ≤ SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma n
        (⋃ z ∈ R, nativeBox n C z) := by
    intro R
    refine MeasurableSpace.generateFrom_le ?_
    rintro A ⟨z, hz, rfl⟩
    have h1 : restrictedCoefficientSigma
        (fun omega : PotentialSample d => aCutoff M n omega) (nativeBox n C z) ≤
        restrictedCoefficientSigma
          (fun omega : PotentialSample d => aCutoff M n omega)
          (⋃ z ∈ R, nativeBox n C z) :=
      SubdiffusiveProcess.CoarseGrainingVocab.restrictedCoefficientSigma_mono _
        (Set.subset_biUnion_of_mem hz)
    have h2 : restrictedCoefficientSigma
        (fun omega : PotentialSample d => aCutoff M n omega)
        (⋃ z ∈ R, nativeBox n C z) ≤
        SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma n
          (⋃ z ∈ R, nativeBox n C z) := by
      refine restrictedCoefficientSigma_aCutoff_le_localSource M n ?_
      exact isOpen_biUnion fun z _ => isOpen_centeredAxisCube _ _
    exact (h1.trans h2) _ (hE z)
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hindep (hdom S)) (hdom T)

/-! ## The concrete event field and the clauses it closes -/

/-- The event field of the anchor: layer zero is the complement of the good
event `G(U)`, and every later layer is the printed `B_j(U)`
(`mfd:in-deterministic` and `s.tightness`). -/
def goodCubeEventField (n : ℕ) (C eps1 : ℝ)
    (E0 : Lattice d → Set (PotentialSample d)) :
    ℕ → Lattice d → Set (PotentialSample d)
  | 0 => E0
  | (j + 1) => layerEvent n (j + 1) C eps1

/-- **Clauses 7b, 7d and 7e of `SubdiffusiveProcess.Section9.weighted_good_cube_events`,
for the concrete event field, from clause 7a alone.**

Given only the layer-zero locality (clause 7a — the remaining measurability
debt, obligations O1/O2 and gap G1), the layer events supply the rest of the
structural package: their own locality (clause 7b, obligation O3), the scale
independence (clause 7d) and the finite-range independence at every scale
(clause 7e), with the constant relation `C + √d ≤ Cdep` of
`euclidean_separation_of_latticeDist`.

Not produced here: clause 7c at the finitely many `j ≥ 1` with `3^j ≤ C`
(`measure_layerEvent_le` covers `3^j > C`), clause 7c at `j = 0`
(obligation O5) and clause 7f (obligation O7). -/
theorem goodCubeEventField_clauses [NeZero d] (M : GMCModel d) (n : ℕ)
    {C eps1 : ℝ} {Cdep : ℕ} (hC : 0 ≤ C)
    (hCdep : C + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ))
    (E0 : Lattice d → Set (PotentialSample d))
    (hE0 : ∀ z : Lattice d,
      MeasurableSet[restrictedCoefficientSigma
        (fun omega : PotentialSample d => aCutoff M n omega) (nativeBox n C z)] (E0 z)) :
    (∀ j, 1 ≤ j → ∀ z : Lattice d,
        MeasurableSet[shellLocalSigma (n + j) (layerBox n j C z)]
          (goodCubeEventField n C eps1 E0 j z)) ∧
      IndependentEventScales M.P.toMeasure (goodCubeEventField n C eps1 E0) ∧
      MultiscaleFiniteRangeIndependentEvents M.P.toMeasure (fun j => Cdep * 3 ^ j)
        (goodCubeEventField n C eps1 E0) := by
  have hlayer : ∀ j, 1 ≤ j → ∀ z : Lattice d,
      MeasurableSet[shellLocalSigma (n + j) (layerBox n j C z)]
        (goodCubeEventField n C eps1 E0 j z) := by
    intro j hj z
    match j with
    | 0 => exact absurd hj (by omega)
    | (i + 1) => exact measurableSet_layerEvent hC n (i + 1) eps1 z
  refine ⟨hlayer, independentEventScales_goodCube M n hE0 hlayer, ?_⟩
  intro j
  match j with
  | 0 => exact finiteRangeIndependentEvents_layerZero M hCdep n E0 hE0
  | (i + 1) =>
      exact finiteRangeIndependentEvents_layer M hCdep n (i + 1) _
        (hlayer (i + 1) (by omega))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
