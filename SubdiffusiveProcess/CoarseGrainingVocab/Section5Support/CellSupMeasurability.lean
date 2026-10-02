import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteSlopeSeparability




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Set TopologicalSpace

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-! ## The cellwise supremum on a countable dense subset -/

/-- A closed Kuhn cell has a countable dense subset of itself. -/
theorem exists_countable_dense_closedCarrier (T : KuhnCell d) :
    ∃ x : ℕ → Vec d, (∀ m, x m ∈ T.closedCarrier) ∧
      T.closedCarrier ⊆ closure (Set.range x) := by
  obtain ⟨t, htsub, htc, htd⟩ :=
    (IsSeparable.of_separableSpace T.closedCarrier).exists_countable_dense_subset
  have htne : t.Nonempty := by
    obtain ⟨y, hy⟩ := T.closedCarrier_nonempty
    have hmem : y ∈ closure t := htd hy
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, closure_empty] at hmem
    exact hmem
  obtain ⟨x, hx⟩ := htc.exists_eq_range htne
  exact ⟨x, fun m => htsub (by rw [hx]; exact ⟨m, rfl⟩), by rwa [← hx]⟩

/-- **The cellwise supremum is a countable supremum.**  For a continuous field
the supremum over the compact closed cell is the supremum over any dense
sequence in it. -/
theorem cellSup_eq_iSup_of_dense {B : Vec d → ℝ} (hB : Continuous B)
    {T : KuhnCell d} {x : ℕ → Vec d} (hx : ∀ m, x m ∈ T.closedCarrier)
    (hdense : T.closedCarrier ⊆ closure (Set.range x)) :
    cellSup B T = ⨆ m, B (x m) := by
  have hbddImage : BddAbove (B '' T.closedCarrier) :=
    ((isCompact_closedCarrier T).image_of_continuousOn hB.continuousOn).bddAbove
  have hbdd : BddAbove (Set.range fun m => B (x m)) := by
    refine hbddImage.mono ?_
    rintro y ⟨m, rfl⟩
    exact ⟨x m, hx m, rfl⟩
  refine le_antisymm ?_ ?_
  · refine csSup_le ((T.closedCarrier_nonempty).image B) ?_
    rintro y ⟨z, hz, rfl⟩
    by_contra hcon
    push_neg at hcon
    have hOopen : IsOpen (B ⁻¹' Set.Ioi (⨆ m, B (x m))) :=
      hB.isOpen_preimage _ isOpen_Ioi
    obtain ⟨y, hyO, hyr⟩ :=
      mem_closure_iff.mp (hdense hz) _ hOopen hcon
    obtain ⟨m, rfl⟩ := hyr
    exact absurd (le_ciSup hbdd m) (not_le.mpr hyO)
  · exact ciSup_le fun m => le_cellSup T hB.continuousOn (hx m)

/-- **(M1).**  The cellwise supremum of a sample-dependent continuous field is
measurable in the sample. -/
theorem measurable_cellSup {B : Ω → Vec d → ℝ} (T : KuhnCell d)
    (hB : ∀ ω, Continuous (B ω)) (hmeas : ∀ y : Vec d, Measurable fun ω => B ω y) :
    Measurable fun ω => cellSup (B ω) T := by
  obtain ⟨x, hx, hdense⟩ := exists_countable_dense_closedCarrier T
  have hfun : (fun ω => cellSup (B ω) T) = fun ω => ⨆ m, B ω (x m) :=
    funext fun ω => cellSup_eq_iSup_of_dense (hB ω) hx hdense
  rw [hfun]
  exact Measurable.iSup fun m => hmeas (x m)

/-! ## The measurability obligation, discharged -/

/-- **`omega |-> dirichletInfOn (B omega) U p` is measurable.**  This is the one
genuinely new probabilistic obligation created by building the continuum
Dirichlet minimum, and it is now unconditional given the two hypotheses a GMC
sample supplies: continuity of the field sample by sample, and measurability of
the field in the sample at each fixed point.

The route is the one (S2c) opened: the continuum minimum is a countable infimum
of discrete minima (`dirichletInfOn_eq_iInf_kuhnDirichletInf`), each discrete
minimum is an infimum over a countable sample-free family of slope assignments
(`exists_countable_eps_optimal_kuhnSlopes`), and each discrete energy is a finite
sum in the cellwise suprema (`measurable_cellSup`). -/
theorem measurable_dirichletInfOn_of_measurable_apply {n : ℕ}
    {Q : TriadicCube (n + 1)} {U : Set (Vec (n + 1))} {B : Ω → Vec (n + 1) → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hUQ : U ⊆ openCubeSet Q)
    (hB : ∀ ω, Continuous (B ω)) (hB0 : ∀ ω x, 0 ≤ B ω x)
    (hmeas : ∀ y : Vec (n + 1), Measurable fun ω => B ω y) (p : Vec (n + 1)) :
    Measurable fun ω => dirichletInfOn (B ω) U p :=
  measurable_dirichletInfOn hU hUQ hB hB0 p fun T => measurable_cellSup T hB hmeas

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
