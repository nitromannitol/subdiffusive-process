import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossingDiscount
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

/-!
# Iterating the temporal crossing estimate

Each discounted endpoint contracts by the same factor. The ordering of stopping
times lets the estimate iterate, and the event inclusion supplies the final tail bound.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing

/-- The temporal crossing estimate, with constants depending only on `c0`. -/
theorem crossing_bound {d : ℕ} (c0 : ℝ) (hc0 : 0 < c0)
    (mu : Measure (Path d)) [IsProbabilityMeasure mu]
    (t F : ℝ) (ht : 0 < t) (hF : 0 < F) (n : ℕ)
    (event : Set (Path d)) (hcross : Crossing mu c0 F t n event) :
    mu event ≤ ENNReal.ofReal (Real.exp (t/F - (min c0 1*(1-Real.exp (-c0)))*n)) := by
  cases n with
  | zero =>
    simpa using probability_zero mu event (t/F) (div_pos ht hF).le
  | succ k =>
    rcases hcross with ⟨T, S, hstop, hTS, hST, hE, hcond⟩
    let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(min c0 1*(1-Real.exp (-c0)))))
    let a : ℕ → ℝ≥0∞ := fun i => ∫⁻ x, discount F (S i x) ∂mu
    have hstep (i : ℕ) (hi : i < k+1) :
        a i ≤ q * (∫⁻ x, discount F (T i x) ∂mu) := by
      exact discount_contraction mu (hstop i hi).1.measurableSpace_le F c0 hF hc0
        (S i) (T i) (hstop i hi).2.measurable' (hstop i hi).1.measurable
        (hTS i hi) (hcond i hi (hstop i hi).1)
    have hseed : a 0 ≤ q := by
      apply (hstep 0 (by omega)).trans
      simpa using mul_le_mul_right
        (bounded_lintegral mu (fun x => discount F (T 0 x))
          (fun x => discount_le_one F hF (T 0 x))) q
    have hrec (i : ℕ) (hi : i+1 < k+1) : a (i+1) ≤ q * a i := by
      exact (hstep (i+1) hi).trans (mul_le_mul_right
        (discount_monotone_integral mu F hF (S i) (T (i+1)) (hST i hi)) q)
    have hlast : a k ≤ q^(k+1) := pow_bounded a q (k+1) hseed hrec k (by omega)
    have hE' : event ⊆ {x | S k x ≤ ENNReal.ofReal t} := by simpa using hE
    have htail := discount_tail mu F t hF (S k)
      (hstop k (by omega)).2.measurable' event hE'
    calc mu event ≤ ENNReal.ofReal (Real.exp (t/F)) * q^(k+1) :=
          tail_assembly _ _ _ _ (discount_inverse F t ht.le) (htail.trans hlast)
      _ = _ := exp_ENN_product _ t F (k+1)

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing
