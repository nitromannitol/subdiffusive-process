module

public import SubdiffusiveProcess.PartProcess.GraphClosure
public import SubdiffusiveProcess.PartProcess.Penalization
public import SubdiffusiveProcess.PartProcess.CoreLattice
public import SubdiffusiveProcess.DirichletForm.FOTLocalityApproximation

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess.PartProcess
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

/-- Compactly supported domain elements localize within the regular carrier. -/
theorem compact_supported_mem_coreClosure
    (E : _root_.SubdiffusiveProcess.DirichletForm m) (V : Set (Fin d → ℝ))
    (C : Set (Lp ℝ 2 m)) (hC : _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm V C)
    (A U : Set (Fin d → ℝ)) (hA : IsCompact A) (hU : IsOpen U)
    (hAU : A ⊆ U) (hUV : U ⊆ V) :
    supportedDomain E.toClosedForm A ≤ E.toClosedForm.killedCoreClosure U := by
  intro u hu
  have hbounded : ∀ (v : Lp ℝ 2 m), v ∈ E.domain → ZeroOutside A v →
      ∀ R : ℝ≥0, (∀ᵐ x ∂m, |v x| ≤ R) → v ∈ E.toClosedForm.killedCoreClosure U := by
    intro v hv hz R hvR
    obtain ⟨w, f, W, hw, hf, hfK, hfU, hwf, hf01, _, hAW, hfW⟩ :=
      hC.exists_cutoff E hA hU hAU hUV
    obtain ⟨a, haR⟩ := hC.exists_bounded_coreApproximation E hv hvR
    have hfv : ∀ᵐ x ∂m, v x * f x = v x := by
      filter_upwards [hz] with x hx
      by_cases hxA : x ∈ A
      · rw [hfW x (hAW hxA), mul_one]
      · rw [hx hxA, zero_mul]
    obtain ⟨b, hb⟩ := a.exists_supported haR hw.1 hf hfK
      (hfU.trans hUV) hwf hf01 hfv
    apply mem_graphClosed_of_tendsto_of_form_le E.toClosedForm
      (E.toClosedForm.killedCoreClosure U) (graphClosed_killedCoreClosure _ U)
      (fun n => (E.toClosedForm.isKilledDomain_killedCoreClosure U).memCoreOn_mem _
        ⟨b.mem_domain n, b.rep n, b.continuous n, b.compact n,
          (hb n).trans hfU, b.ae_rep n⟩) b.tendsto b.energy_le
  apply mem_graphClosed_of_tendsto_of_form_le E.toClosedForm
    (E.toClosedForm.killedCoreClosure U) (graphClosed_killedCoreClosure _ U)
    (fun n => hbounded (_root_.SubdiffusiveProcess.DirichletForm.clipLp (n + 1) u)
      (_root_.SubdiffusiveProcess.DirichletForm.clipLp_mem E (n + 1) hu.1).1 (by
        filter_upwards [_root_.SubdiffusiveProcess.DirichletForm.coeFn_clipLp (n + 1) u, hu.2] with x hx hz hxA
        rw [hx, hz hxA]
        exact _root_.SubdiffusiveProcess.DirichletForm.clip_zero (by positivity)) (n + 1) (by
        filter_upwards [_root_.SubdiffusiveProcess.DirichletForm.coeFn_clipLp (n + 1) u] with x hx
        rw [hx]
        exact _root_.SubdiffusiveProcess.DirichletForm.abs_clip_le (by positivity) _))
    (_root_.SubdiffusiveProcess.DirichletForm.tendsto_clipLp u)
    (fun n => (_root_.SubdiffusiveProcess.DirichletForm.clipLp_mem E (n + 1) hu.1).2)

/-- Intersecting with the regular carrier does not change the ambient core closure. -/
theorem coreClosure_inter_carrier
    (E : _root_.SubdiffusiveProcess.DirichletForm m) (V : Set (Fin d → ℝ))
    (C : Set (Lp ℝ 2 m)) (hC : _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm V C)
    (U : Set (Fin d → ℝ)) :
    E.toClosedForm.killedCoreClosure (U ∩ V) = E.toClosedForm.killedCoreClosure U := by
  apply le_antisymm
  · rintro u ⟨hu, happ⟩
    exact ⟨hu, fun ε hε => by
      obtain ⟨w, hw, he⟩ := happ ε hε
      exact ⟨w, hw.mono inter_subset_left, he⟩⟩
  · intro u hu
    have hcore : ∀ b, E.toClosedForm.MemCoreOn U b →
        b ∈ E.toClosedForm.killedCoreClosure (U ∩ V) := by
      intro b hb
      obtain ⟨w, hw, hlim, hbound⟩ := hC.exists_approx E hb.1
      have heq : variableClipLp b b = b :=
        variableClipLp_eq_of_abs_le b b (Eventually.of_forall fun _ => le_rfl)
      have ht : Tendsto (fun n => variableClipLp b (w n)) atTop (𝓝 b) := by
        simpa only [Function.comp_def, heq] using! (variableClipLp_continuous b).tendsto b |>.comp hlim
      apply mem_graphClosed_of_tendsto_of_form_le E.toClosedForm
        (E.toClosedForm.killedCoreClosure (U ∩ V)) (graphClosed_killedCoreClosure _ _)
        (fun n => (E.toClosedForm.isKilledDomain_killedCoreClosure _).memCoreOn_mem _
          (variableClipLp_memCore_inter E U V b (w n) hb (hw n))) ht
        (B := 4 * (2 * E.form b b + 2) + 6 * E.form b b)
      intro n
      exact (variableClipLp_mem_form_le E b (w n) hb.1 (hw n).1).2.trans
        (by gcongr; exact hbound n)
    obtain ⟨w, hw, hlim⟩ := (E.toClosedForm.isKilledDomain_killedCoreClosure U).exists_seq hu
    exact (graphClosed_killedCoreClosure E.toClosedForm (U ∩ V)).2 w u
      (fun n => hcore _ (hw n)) hu.1
      (hlim.congr fun n => E.toClosedForm.energyNormSq_sub_comm hu.1 (hw n).1)

end SubdiffusiveProcess.PartProcess
