import SubdiffusiveProcess.Meyers.Defs

/-! Transport between `Vec 1 = Fin 1 → ℝ` and `ℝ` (the evaluation `x ↦ x 0` is a measure-preserving
measurable equivalence). -/

open MeasureTheory Set Filter Topology
open SubdiffusiveProcess Homogenization

noncomputable section

namespace SubdiffusiveProcess.Meyers

/-- evaluation at `0`, as a measurable equivalence `Vec 1 ≃ᵐ ℝ` -/
def evalEquiv : Vec 1 ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ

theorem evalEquiv_apply (x : Vec 1) : evalEquiv x = x 0 := rfl

theorem mp_eval : MeasurePreserving evalEquiv (volume : Measure (Vec 1)) volume :=
  volume_preserving_funUnique (Fin 1) ℝ

theorem vec1_eq_const (x : Vec 1) : x = fun _ => x 0 := by
  funext i
  fin_cases i
  rfl

theorem ball_eq_preimage (x0 : Vec 1) {r : ℝ} (hr : 0 < r) :
    Metric.ball x0 r = evalEquiv ⁻¹' Ioo (x0 0 - r) (x0 0 + r) := by
  ext x
  rw [Metric.mem_ball, dist_pi_lt_iff hr, mem_preimage, evalEquiv_apply, mem_Ioo]
  constructor
  · intro h
    have := h 0
    rw [Real.dist_eq, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi, Real.dist_eq, abs_lt]
    constructor <;> linarith [h.1, h.2]

theorem integral_transport {J : Set ℝ} (f : ℝ → ℝ) :
    ∫ x in evalEquiv ⁻¹' J, f (x 0) = ∫ t in J, f t :=
  mp_eval.setIntegral_preimage_emb evalEquiv.measurableEmbedding f J

theorem integrableOn_transport {J : Set ℝ} (f : ℝ → ℝ) :
    IntegrableOn (fun x : Vec 1 => f (x 0)) (evalEquiv ⁻¹' J) ↔ IntegrableOn f J :=
  mp_eval.integrableOn_comp_preimage evalEquiv.measurableEmbedding

theorem ae_transport {J : Set ℝ} (p : ℝ → Prop) :
    (∀ᵐ t ∂volume.restrict J, p t) ↔
      ∀ᵐ x ∂(volume : Measure (Vec 1)).restrict (evalEquiv ⁻¹' J), p (x 0) := by
  have hrp := mp_eval.restrict_preimage_emb evalEquiv.measurableEmbedding J
  rw [← hrp.map_eq]
  exact evalEquiv.measurableEmbedding.ae_map_iff

end SubdiffusiveProcess.Meyers
