import SubdiffusiveProcess.Paper.density_chain_prefix
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Function.AEMeasurableOrder
open Filter MeasureTheory Set
open scoped Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- A dummy prefix starts the universal indexed-tree count at any absolute base
level. No geometric identification with a translated unit-root tree is needed. -/
theorem density_shifted_chain_counts
    {A Cells Roots Field Ω : Type} [Nonempty A] [Countable Roots]
    [MeasurableSpace Field] [MeasurableSpace Ω]
    (mu : Measure Field) (P : Measure Ω) (field : Ω → Field)
    (hfield : MeasurePreserving field P mu)
    (Good : Cells → Set Field) (level : Cells → ℕ) (H1 : ℕ)
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hChain : ∀ (active : List A → Prop) (index : List A → Cells),
      (∀ w, active w → level (index w) = H1 * w.length) →
      ∃ B : Field → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
        ∀ᵐ omega ∂mu, ∀ (J : ℕ) (pi : Fin J → A), 1 ≤ J →
          (Set.ncard {i : Fin J | ¬ (active ((List.ofFn pi).take (i.val + 1)) →
            omega ∈ Good (index ((List.ofFn pi).take (i.val + 1))))} : ℝ) ≤
              theta * (J : ℝ) + B omega)
    (base : Roots → ℕ) (active : Roots → List A → Prop) (index : Roots → List A → Cells)
    (hlevel : ∀ root w, active root w → level (index root w) = H1 * (base root + w.length)) :
    ∃ B : Roots → Ω → ℝ,
      (∀ root, Measurable (B root) ∧ ∀ omega, 0 ≤ B root omega) ∧
      ∀ᵐ omega ∂P, ∀ (root : Roots) (J : ℕ) (w : Fin J → A),
        (Set.ncard {i : Fin J | ¬ (active root ((List.ofFn w).take (i.val + 1)) →
          field omega ∈ Good (index root ((List.ofFn w).take (i.val + 1))))} : ℝ) ≤
            theta * (J : ℝ) + B root omega := by
  classical
  let liftActive := fun root (w : List A) =>
    base root ≤ w.length ∧ active root (w.drop (base root))
  let liftIndex := fun root (w : List A) => index root (w.drop (base root))
  have hLift : ∀ root w, liftActive root w → level (liftIndex root w) = H1 * w.length := by
    intro root w hw
    have h := hlevel root (w.drop (base root)) hw.2
    have hlen : base root + (w.drop (base root)).length = w.length := by
      rw [List.length_drop]
      omega
    exact h.trans (congrArg (fun n => H1 * n) hlen)
  choose B hBm hB0 hCount using fun root => hChain (liftActive root) (liftIndex root) (hLift root)
  refine ⟨(fun root omega => B root (field omega) + theta * (base root : ℝ)),
    (fun root => ⟨((hBm root).comp hfield.measurable).add_const _,
      fun omega => add_nonneg (hB0 root (field omega)) (mul_nonneg htheta (Nat.cast_nonneg _))⟩), ?_⟩
  filter_upwards [hfield.quasiMeasurePreserving.ae (ae_all_iff.mpr hCount)] with omega h
  intro root J w
  let w0 : Fin (base root) → A := fun _ => Classical.choice inferInstance
  have hc := density_chain_prefix
    (fun v => liftActive root v → field omega ∈ Good (liftIndex root v))
    theta (B root (field omega)) htheta (hB0 root (field omega)) (h root)
    (base root) w0 J w
  have heq : ∀ v : List A,
      (liftActive root (List.ofFn w0 ++ v) → field omega ∈ Good (liftIndex root (List.ofFn w0 ++ v))) ↔
      (active root v → field omega ∈ Good (index root v)) := by
    intro v
    have hdrop : (List.ofFn w0 ++ v).drop (base root) = v := by
      simpa only [List.length_ofFn] using (show (List.ofFn w0 ++ v).drop (List.ofFn w0).length = v from List.drop_left)
    have hlen : base root ≤ (List.ofFn w0 ++ v).length := by
      simp only [List.length_append, List.length_ofFn]
      omega
    simp only [liftActive, liftIndex, hdrop, hlen, true_and]
  simpa only [heq] using hc
end Paper
