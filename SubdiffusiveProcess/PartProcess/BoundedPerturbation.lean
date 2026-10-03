module

public import SubdiffusiveProcess.PartProcess.BoundedPotential
public import SubdiffusiveProcess.PartProcess.CoreClosure

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
variable {X : Type*} [MeasurableSpace X] {m : Measure X}

theorem exists_boundedPerturbation (E : DirichletForm.ClosedForm m)
    (q : X → ℝ) (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (B : ℝ) (hB : ∀ x, q x ≤ B) :
    ∃ F : DirichletForm.ClosedForm m, F.domain = E.domain ∧
      ∀ u v, F.form u v = E.form u v + ∫ x, q x * u x * v x ∂m := by
  let B0 : ℝ := max B 0
  have hB0 : 0 ≤ B0 := le_max_right _ _
  have hqb : ∀ x, |q x| ≤ B0 := fun x => by
    rw [abs_of_nonneg (hq0 x)]
    exact (hB x).trans (le_max_left _ _)
  let Q : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m := multiplication q hq B0 hB0 hqb
  have hQpos : ∀ u, 0 ≤ inner ℝ (Q u) u :=
    inner_multiplication_nonneg q hq B0 hB0 hqb hq0
  have hQbound : ∀ u, inner ℝ (Q u) u ≤ B0 * ‖u‖ ^ 2 :=
    inner_multiplication_le q hq B0 hB0 hqb
  let F : DirichletForm.ClosedForm m :=
    { domain := E.domain
      form := fun u v => E.form u v + inner ℝ (Q u) v
      denseDomain := E.denseDomain
      form_symm := by
        intro u hu v hv
        rw [E.form_symm u hu v hv, inner_multiplication_symm]
      form_add_left := by
        intro u hu v hv w hw
        rw [E.form_add_left u hu v hv w hw, map_add, inner_add_left]
        ring
      form_smul_left := by
        intro a u hu v hv
        rw [E.form_smul_left a u hu v hv, map_smul, real_inner_smul_left]
        ring
      form_nonneg := fun u hu => add_nonneg (E.form_nonneg u hu) (hQpos u)
      complete := by
        intro u hu hc
        obtain ⟨w, hw, hlim⟩ := E.complete u hu (by
          intro ε hε
          obtain ⟨N, hN⟩ := hc ε hε
          refine ⟨N, fun p hp r hr => ?_⟩
          have hn := hN p hp r hr
          have hpos := hQpos (u p - u r)
          linarith)
        refine ⟨w, hw, ?_⟩
        have hbound : ∀ n,
            E.form (u n - w) (u n - w) + inner ℝ (Q (u n - w)) (u n - w) +
              ‖u n - w‖ ^ 2 ≤ (B0 + 1) * E.energyNormSq (u n - w) := by
          intro n
          have hq := hQbound (u n - w)
          have he := E.form_nonneg _ (E.domain.sub_mem (hu n) hw)
          rw [DirichletForm.ClosedForm.energyNormSq]
          nlinarith [sq_nonneg ‖u n - w‖]
        apply squeeze_zero (fun n => ?_) hbound
          (by simpa only [DirichletForm.ClosedForm.energyNormSq, mul_zero] using! hlim.const_mul (B0 + 1))
        exact add_nonneg (add_nonneg
          (E.form_nonneg _ (E.domain.sub_mem (hu n) hw)) (hQpos _)) (sq_nonneg _) }
  refine ⟨F, rfl, fun u v => ?_⟩
  change E.form u v + inner ℝ (Q u) v = _
  rw [inner_multiplication]

end SubdiffusiveProcess.PartProcess
