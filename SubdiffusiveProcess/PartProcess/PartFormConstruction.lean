module

public import SubdiffusiveProcess.PartProcess.CoreClosure

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- The closed part form follows from density of the restricted core. -/
theorem exists_partForm_of_dense (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m)
    (U : Set X) (hU : MeasurableSet U)
    (hdense : Dense {v : Lp ℝ 2 (m.restrict U) |
      ∃ u, E.MemCoreOn U u ∧ restrictLp U u = v}) :
    ∃ F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (m.restrict U), IsPartFormOn E U F := by
  let D := E.killedCoreClosure U
  let r : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 (m.restrict U) := restriction U
  let e : Lp ℝ 2 (m.restrict U) →L[ℝ] Lp ℝ 2 m := extension U hU
  have her : ∀ u ∈ D, e (r u) = u := by
    intro u hu
    exact extend_restrict U hU u (zeroOutside_coreLimit E U u
      ((coreLimit_iff_mem_killedCoreClosure E U u).2 hu))
  have hre : ∀ u, r (e u) = u := restrict_extend U hU
  have henorm : ∀ u, ‖e u‖ = ‖u‖ := norm_extendLp U hU
  have he_mem : ∀ u ∈ D.map r.toLinearMap, e u ∈ D := by
    intro u hu
    obtain ⟨v, hv, hvu⟩ := Submodule.mem_map.1 hu
    rw [← hvu]
    change e (r v) ∈ D
    rw [her v hv]
    exact hv
  have he_domain : ∀ u ∈ D.map r.toLinearMap, e u ∈ E.domain :=
    fun u hu => (he_mem u hu).1
  let F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (m.restrict U) :=
    { domain := D.map r.toLinearMap
      form := fun u v => E.form (e u) (e v)
      denseDomain := hdense.mono (by
        rintro v ⟨u, hu, huv⟩
        exact Submodule.mem_map.2 ⟨u,
          (E.isKilledDomain_killedCoreClosure U).memCoreOn_mem u hu, huv⟩)
      form_symm := fun u hu v hv => E.form_symm _ (he_domain u hu) _ (he_domain v hv)
      form_add_left := by
        intro u hu v hv w hw
        rw [map_add]
        exact E.form_add_left _ (he_domain u hu) _ (he_domain v hv) _ (he_domain w hw)
      form_smul_left := by
        intro a u hu v hv
        rw [map_smul]
        exact E.form_smul_left a _ (he_domain u hu) _ (he_domain v hv)
      form_nonneg := fun u hu => E.form_nonneg _ (he_domain u hu)
      complete := by
        intro u hu hc
        obtain ⟨w, hw, hlim⟩ := E.complete (fun n => e (u n))
          (fun n => he_domain _ (hu n)) (by
            intro ε hε
            obtain ⟨N, hN⟩ := hc ε hε
            refine ⟨N, fun p hp q hq => ?_⟩
            simpa only [← map_sub, henorm] using hN p hp q hq)
        have hwD : w ∈ D := (graphClosed_killedCoreClosure E U).2
          (fun n => e (u n)) w (fun n => he_mem _ (hu n)) hw hlim
        refine ⟨r w, Submodule.mem_map.2 ⟨w, hwD, rfl⟩, ?_⟩
        refine hlim.congr fun n => ?_
        change E.energyNormSq (e (u n) - w) =
          E.form (e (u n - r w)) (e (u n - r w)) + ‖u n - r w‖ ^ 2
        rw [map_sub, her w hwD]
        rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq]
        congr 1
        have hn := henorm (u n - r w)
        rw [map_sub, her w hwD] at hn
        rw [hn] }
  refine ⟨F, ?_⟩
  constructor
  · intro v
    change v ∈ D.map r.toLinearMap ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨u, hu, huv⟩
      exact ⟨u, (coreLimit_iff_mem_killedCoreClosure E U u).2 hu, huv⟩
    · rintro ⟨u, hu, huv⟩
      exact ⟨u, (coreLimit_iff_mem_killedCoreClosure E U u).1 hu, huv⟩
  · intro u v hu hv
    change E.form (e (r u)) (e (r v)) = E.form u v
    rw [her u ((coreLimit_iff_mem_killedCoreClosure E U u).1 hu),
      her v ((coreLimit_iff_mem_killedCoreClosure E U v).1 hv)]

end SubdiffusiveProcess.PartProcess
