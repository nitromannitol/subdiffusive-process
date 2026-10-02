import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteDirichletConvergence




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The discrete infimum over a countable family -/

/-- The defining bound, stated on the slope set rather than on a competitor. -/
theorem kuhnDirichletInf_le_of_mem_kuhnSlopeSet {B : Vec d → ℝ}
    {S : Finset (KuhnCell d)} {U : Set (Vec d)} (hB : Continuous B)
    (hB0 : ∀ x, 0 ≤ B x) (p : Vec d) {q : KuhnCell d → Vec d}
    (hq : q ∈ kuhnSlopeSet U S) :
    kuhnDirichletInf B S U p ≤ kuhnDiscreteEnergy B S U p q :=
  csInf_le (bddBelow_kuhnDiscreteEnergy_image hB hB0 p) ⟨q, hq, rfl⟩

/-- **The discrete infimum as a countable infimum.**  A countable family of
admissible slope assignments which is `eps`-optimal realizes `Q_{R,pi}(p)`. -/
theorem kuhnDirichletInf_eq_iInf {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec d)
    (D : ℕ → KuhnCell d → Vec d) (hD : ∀ m, D m ∈ kuhnSlopeSet U S)
    (hopt : ∀ eps > 0, ∃ m,
      kuhnDiscreteEnergy B S U p (D m) < kuhnDirichletInf B S U p + eps) :
    kuhnDirichletInf B S U p = ⨅ m, kuhnDiscreteEnergy B S U p (D m) := by
  have hbdd : BddBelow (Set.range fun m => kuhnDiscreteEnergy B S U p (D m)) := by
    refine ⟨0, ?_⟩
    rintro E ⟨m, rfl⟩
    exact kuhnDiscreteEnergy_nonneg hB hB0 p (D m)
  refine le_antisymm
    (le_ciInf fun m => kuhnDirichletInf_le_of_mem_kuhnSlopeSet hB hB0 p (hD m)) ?_
  refine le_of_forall_pos_le_add fun eps heps => ?_
  obtain ⟨m, hm⟩ := hopt eps heps
  exact le_trans (ciInf_le hbdd m) hm.le

/-! ## The measurability chain -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The last reduction.**  For a *fixed* slope assignment the discrete energy is
measurable in the sample as soon as each cellwise supremum is: the slope set and
the cell volumes carry no sample dependence. -/
theorem measurable_kuhnDiscreteEnergy {B : Ω → Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} {p : Vec d} {q : KuhnCell d → Vec d}
    (h : ∀ T ∈ S, Measurable fun ω => cellSup (B ω) T) :
    Measurable fun ω => kuhnDiscreteEnergy (B ω) S U p q := by
  refine Finset.measurable_sum S fun T hT => ?_
  exact ((h T hT).mul_const (vecNormSq (p + q T))).const_mul
    (volume.real (U ∩ T.openCarrier))

/-- **Measurability of `Q_{R,pi}(p)`** from a sample-independent countable family
of `eps`-optimal slope assignments. -/
theorem measurable_kuhnDirichletInf_of_iInf {B : Ω → Vec d → ℝ}
    {S : Finset (KuhnCell d)} {U : Set (Vec d)} {p : Vec d}
    (D : ℕ → KuhnCell d → Vec d)
    (hmeas : ∀ m, Measurable fun ω => kuhnDiscreteEnergy (B ω) S U p (D m))
    (heq : ∀ ω, kuhnDirichletInf (B ω) S U p =
      ⨅ m, kuhnDiscreteEnergy (B ω) S U p (D m)) :
    Measurable fun ω => kuhnDirichletInf (B ω) S U p := by
  have hfun : (fun ω => kuhnDirichletInf (B ω) S U p) =
      fun ω => ⨅ m, kuhnDiscreteEnergy (B ω) S U p (D m) := funext heq
  rw [hfun]
  exact Measurable.iInf hmeas



theorem measurable_dirichletInfOn_of_measurable_kuhnDirichletInf {n : ℕ}
    {Q : TriadicCube (n + 1)} {U : Set (Vec (n + 1))} {B : Ω → Vec (n + 1) → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hUQ : U ⊆ openCubeSet Q)
    (hB : ∀ ω, Continuous (B ω)) (hB0 : ∀ ω x, 0 ≤ B ω x) (p : Vec (n + 1))
    (hmeas : ∀ j : ℤ, Measurable fun ω =>
      kuhnDirichletInf (B ω) (triadicSimplexPartition Q (min j Q.scale)) U p) :
    Measurable fun ω => dirichletInfOn (B ω) U p := by
  have hfun : (fun ω => dirichletInfOn (B ω) U p) =
      fun ω => ⨅ j : ℤ,
        kuhnDirichletInf (B ω) (triadicSimplexPartition Q (min j Q.scale)) U p :=
    funext fun ω =>
      dirichletInfOn_eq_iInf_kuhnDirichletInf hU hUQ (hB ω) (hB0 ω) p
  rw [hfun]
  exact Measurable.iInf hmeas

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
