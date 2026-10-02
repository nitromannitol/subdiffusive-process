import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeshGluing
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteSlopeSeparability
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteDirichletConvergence




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- **A countable, sample-free family of conforming competitors that realizes
the continuum Dirichlet minimum for every continuous nonnegative
coefficient.**  The selection quantity is the discrete energy, so the induced
measurable selection only needs the measurability of the cellwise suprema. -/
theorem exists_countable_optimal_kuhnCompetitors {n : ℕ} {Q : TriadicCube (n + 1)}
    {U : Set (Vec (n + 1))} (hU : IsOpenBoundedConvexDomain U)
    (hUQ : U ⊆ openCubeSet Q) (p : Vec (n + 1)) :
    ∃ (S : ℕ → Finset (KuhnCell (n + 1))) (q : ℕ → KuhnCell (n + 1) → Vec (n + 1))
      (w : ℕ → H10Function U),
      (∀ (i : ℕ) (B : Vec (n + 1) → ℝ), Continuous B →
        dirichletEnergyOn' B U p (w i).toH1Function.grad ≤
          kuhnDiscreteEnergy B (S i) U p (q i)) ∧
      (∀ (B : Vec (n + 1) → ℝ), Continuous B → (∀ x, 0 ≤ B x) →
        ∀ eps > 0, ∃ i, kuhnDiscreteEnergy B (S i) U p (q i) <
          dirichletInfOn B U p + eps) := by
  classical
  have hUopen : IsOpen U := hU.isOpen
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hUb : Bornology.IsBounded U := hU.isBoundedDomain.isBounded
  have hUfin : volume U ≠ ⊤ := ne_of_lt hU.isBoundedDomain.volume_lt_top
  haveI : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hU.isBoundedDomain.volume_lt_top⟩
  set mesh : ℤ → Finset (KuhnCell (n + 1)) :=
    fun j => triadicSimplexPartition Q (min j Q.scale) with hmesh
  have hscale : ∀ j : ℤ, ∀ T ∈ mesh j, T.supportCube.scale = min j Q.scale :=
    fun j T hT => supportCube_scale_eq_of_mem_triadicSimplexPartition
      (min_le_right j Q.scale) hT
  have hcover : ∀ j : ℤ, U ⊆ ⋃ T ∈ (mesh j : Set (KuhnCell (n + 1))), T.carrier := by
    intro j x hx
    have hxc : x ∈ cubeSet Q := openCubeSet_subset_cubeSet Q (hUQ hx)
    rw [cubeSet_eq_iUnion_triadicSimplexPartition Q (min_le_right j Q.scale)] at hxc
    exact hxc
  have hfam : ∀ j : ℤ, ∃ D : ℕ → KuhnCell (n + 1) → Vec (n + 1),
      (∀ m, D m ∈ kuhnSlopeSet U (mesh j)) ∧
      ∀ (B : Vec (n + 1) → ℝ) (r : Vec (n + 1)), ∀ eps > 0, ∃ m,
        kuhnDiscreteEnergy B (mesh j) U r (D m) <
          kuhnDirichletInf B (mesh j) U r + eps :=
    fun j => exists_countable_eps_optimal_kuhnSlopes U (mesh j)
  choose D hD hDopt using hfam
  have hcomp : ∀ (j : ℤ) (m : ℕ), ∃ c : KuhnCompetitor U (mesh j), c.slope = D j m :=
    fun j m => hD j m
  choose comp hcompslope using hcomp
  set e : ℕ ≃ ℤ × ℕ := (Denumerable.eqv (ℤ × ℕ)).symm with he
  refine ⟨fun i => mesh (e i).1, fun i => D (e i).1 (e i).2,
    fun i => (comp (e i).1 (e i).2).toH10Function, ?_, ?_⟩
  · intro i B hB
    obtain ⟨C, hC⟩ := exists_bound_of_continuous_of_isBounded hB hUb
    have hnorm : IntegrableOn
        (fun x => vecNormSq (p + (comp (e i).1 (e i).2).grad x)) U volume :=
      integrableOn_vecNormSq_add_grad
        (comp (e i).1 (e i).2).toH10Function.toH1Function p
    have hint : IntegrableOn
        (fun x => B x * vecNormSq (p + (comp (e i).1 (e i).2).grad x)) U volume :=
      integrableOn_mul_of_integrableOn_vecNormSq hUmeas hB.measurable hC hnorm
    have h := dirichletEnergyOn'_le_kuhnDiscreteEnergy (B := B) (S := mesh (e i).1)
      (U := U) (p := p) (s := min (e i).1 Q.scale) hUmeas hUfin (hscale (e i).1)
      (hcover (e i).1) hB (comp (e i).1 (e i).2) hint
    rw [hcompslope] at h
    exact h
  · intro B hB hB0 eps heps
    have hiInf := dirichletInfOn_eq_iInf_kuhnDirichletInf hU hUQ hB hB0 p
    have hlt : (⨅ j : ℤ, kuhnDirichletInf B (mesh j) U p) <
        dirichletInfOn B U p + eps / 2 := by
      rw [← hiInf]
      linarith [half_pos heps]
    obtain ⟨j, hj⟩ := exists_lt_of_ciInf_lt hlt
    obtain ⟨m, hm⟩ := hDopt j B p (eps / 2) (half_pos heps)
    refine ⟨e.symm (j, m), ?_⟩
    simp only [Equiv.apply_symm_apply]
    linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
