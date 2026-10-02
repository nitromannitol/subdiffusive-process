import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteSlopeSeparability




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Set

noncomputable section

variable {d : ℕ}

variable {Ω : Type*} [MeasurableSpace Ω]



theorem exists_measurable_eps_optimal_kuhnSlopes {B : Ω → Vec d → ℝ}
    {S : Finset (KuhnCell d)} {U : Set (Vec d)} (p : Vec d)
    (hB : ∀ ω, Continuous (B ω)) (hB0 : ∀ ω x, 0 ≤ B ω x)
    (hcell : ∀ T ∈ S, Measurable fun ω => cellSup (B ω) T) {eps : ℝ} (heps : 0 < eps) :
    ∃ (D : ℕ → KuhnCell d → Vec d) (n : Ω → ℕ),
      (∀ m, D m ∈ kuhnSlopeSet U S) ∧ Measurable n ∧
        ∀ ω, kuhnDiscreteEnergy (B ω) S U p (D (n ω)) <
          kuhnDirichletInf (B ω) S U p + eps := by
  classical
  obtain ⟨D, hD, hopt⟩ := exists_countable_eps_optimal_kuhnSlopes U S
  set P : Ω → ℕ → Prop := fun ω m =>
    kuhnDiscreteEnergy (B ω) S U p (D m) < kuhnDirichletInf (B ω) S U p + eps with hP
  have hex : ∀ ω, ∃ m, P ω m := fun ω => hopt (B ω) p eps heps
  have hmeas : ∀ m, MeasurableSet {ω | P ω m} := by
    intro m
    exact measurableSet_lt (measurable_kuhnDiscreteEnergy hcell)
      ((measurable_kuhnDirichletInf hB hB0 hcell).add_const eps)
  exact ⟨D, fun ω => Nat.find (hex ω), hD, measurable_find hex hmeas,
    fun ω => Nat.find_spec (hex ω)⟩

/-- The selected slope field is measurable, cell by cell: it is a countably
valued function of the sample. -/
theorem measurable_selected_slope {D : ℕ → KuhnCell d → Vec d} {n : Ω → ℕ}
    (hn : Measurable n) (T : KuhnCell d) :
    Measurable fun ω => D (n ω) T :=
  (measurable_from_top (f := fun m => D m T)).comp hn

/-- The pieces of the induced countable partition of the sample space are
measurable, and on each of them the selected slope assignment is one
*deterministic* member of the slope set.  This is the exact form in which Step 3
freezes the slopes before using the independence of `A_{N-1}^{(R)}` from
`B_{NR}`. -/
theorem measurableSet_selection_fiber {n : Ω → ℕ} (hn : Measurable n) (m : ℕ) :
    MeasurableSet {ω | n ω = m} :=
  hn (measurableSet_singleton m)

omit [MeasurableSpace Ω] in
theorem selected_slope_eq_on_fiber {D : ℕ → KuhnCell d → Vec d} {n : Ω → ℕ} {m : ℕ}
    {ω : Ω} (hω : ω ∈ {ω | n ω = m}) : D (n ω) = D m := by
  rw [show n ω = m from hω]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
