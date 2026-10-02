import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

/-!
# Weak-to-strong measurability on a separable real Hilbert space

The finite-volume one-step correctors are characterized by their scalar weak
equations.  This module records the separable-Hilbert fact that makes those
scalar probes sufficient for measurability of the whole solution vector.

The proof expands in a Hilbert basis.  Second countability makes the
orthonormal index set countable (disjoint radius-`1/3` balls), so the finite
partial sums form a strongly measurable net converging pointwise to the
original vector.
-/

open Filter MeasureTheory Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A map into a second-countable real Hilbert space is measurable once all
of its scalar inner-product probes are measurable. -/
theorem measurable_of_forall_real_inner_right {f : Omega → E}
    (hf : ∀ y : E, Measurable fun omega => inner ℝ (f omega) y) :
    Measurable f := by
  obtain ⟨w, b, _hb⟩ := exists_hilbertBasis ℝ E
  have hwCountable : Countable w := by
    let balls : w → Set E := fun i => Metric.ball (b i) (1 / 3 : ℝ)
    have hpair : Pairwise fun i j => Disjoint (balls i) (balls j) := by
      intro i j hij
      apply Metric.ball_disjoint_ball
      have horth : inner ℝ (b i) (b j) = 0 :=
        b.orthonormal.inner_eq_zero hij
      have hsq : ‖b i - b j‖ * ‖b i - b j‖ = 2 := by
        rw [norm_sub_sq_eq_norm_sq_add_norm_sq_real horth]
        norm_num [b.orthonormal.norm_eq_one]
      have hnorm : 1 ≤ ‖b i - b j‖ := by
        have hn := norm_nonneg (b i - b j)
        nlinarith
      simpa [balls, dist_eq_norm] using
        (show (1 / 3 : ℝ) + 1 / 3 ≤ ‖b i - b j‖ by linarith)
    exact hpair.countable_of_isOpen_disjoint
      (fun i => by simp [balls])
      (fun i => by exact ⟨b i, Metric.mem_ball_self (by norm_num)⟩)
  letI : Countable w := hwCountable
  let approximant : Finset w → Omega → E := fun s omega =>
    ∑ i ∈ s, b.repr (f omega) i • b i
  have hpartial : ∀ s : Finset w, StronglyMeasurable (approximant s) := by
    intro s
    dsimp only [approximant]
    have hs := Finset.stronglyMeasurable_sum s fun i _ => by
      have hi : Measurable fun omega => b.repr (f omega) i := by
        simpa only [b.repr_apply_apply, real_inner_comm] using hf (b i)
      exact hi.stronglyMeasurable.smul_const (b i)
    have heq : (∑ i ∈ s, fun omega => b.repr (f omega) i • b i) =
        fun omega => ∑ i ∈ s, b.repr (f omega) i • b i := by
      funext omega
      simp
    rw [← heq]
    exact hs
  have hlim : Tendsto approximant atTop (𝓝 f) := by
    rw [tendsto_pi_nhds]
    intro omega
    simpa only [approximant] using b.hasSum_repr (f omega)
  exact (stronglyMeasurable_of_tendsto atTop hpartial hlim).measurable

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
