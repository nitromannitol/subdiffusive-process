module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveAlgebra

@[expose] public section

/-!
# Integrating and absorbing the boundary coercive inequality

The direct boundary test first gives an equality between the integral of the
main energy and an expanded right-hand side.  The pointwise Young estimate in
`BoundaryCoerciveAlgebra` leaves three eighths of the main energy.  This module
performs the measure-theoretic integration and absorption once and for all.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Generic integral absorption in the exact constants produced by
`scalar_boundary_coercive_rhs_le`. -/
theorem setIntegral_boundary_coercive_absorb
    {V : Set (Homogenization.Vec d)}
    {main rhs datum cutoff force : Homogenization.Vec d → ℝ}
    (hmain : IntegrableOn main V) (hrhs : IntegrableOn rhs V)
    (hdatum : IntegrableOn datum V) (hcutoff : IntegrableOn cutoff V)
    (hforce : IntegrableOn force V)
    (hcutoff0 : 0 ≤ ∫ x in V, cutoff x ∂volume)
    (hforce0 : 0 ≤ ∫ x in V, force x ∂volume)
    (hid : ∫ x in V, main x ∂volume = ∫ x in V, rhs x ∂volume)
    (hpoint : rhs ≤ᵐ[volume.restrict V]
      fun x => (3 / 8 : ℝ) * main x + (5 / 2 : ℝ) * datum x +
        (17 / 2 : ℝ) * cutoff x + (9 / 2 : ℝ) * force x) :
    ∫ x in V, main x ∂volume ≤
      4 * ∫ x in V, datum x ∂volume +
        14 * ∫ x in V, cutoff x ∂volume +
        8 * ∫ x in V, force x ∂volume := by
  have hmainC : IntegrableOn (fun x => (3 / 8 : ℝ) * main x) V :=
    hmain.const_mul _
  have hdatumC : IntegrableOn (fun x => (5 / 2 : ℝ) * datum x) V :=
    hdatum.const_mul _
  have hcutoffC : IntegrableOn (fun x => (17 / 2 : ℝ) * cutoff x) V :=
    hcutoff.const_mul _
  have hforceC : IntegrableOn (fun x => (9 / 2 : ℝ) * force x) V :=
    hforce.const_mul _
  have hbound : IntegrableOn
      (fun x => (3 / 8 : ℝ) * main x + (5 / 2 : ℝ) * datum x +
        (17 / 2 : ℝ) * cutoff x + (9 / 2 : ℝ) * force x) V :=
    ((hmainC.add hdatumC).add hcutoffC).add hforceC
  have hmono := integral_mono_ae hrhs hbound hpoint
  have hsplit :
      ∫ x in V, ((3 / 8 : ℝ) * main x + (5 / 2 : ℝ) * datum x +
          (17 / 2 : ℝ) * cutoff x + (9 / 2 : ℝ) * force x) ∂volume =
        (3 / 8 : ℝ) * ∫ x in V, main x ∂volume +
          (5 / 2 : ℝ) * ∫ x in V, datum x ∂volume +
          (17 / 2 : ℝ) * ∫ x in V, cutoff x ∂volume +
          (9 / 2 : ℝ) * ∫ x in V, force x ∂volume := by
    calc
      ∫ x in V, ((3 / 8 : ℝ) * main x + (5 / 2 : ℝ) * datum x +
            (17 / 2 : ℝ) * cutoff x + (9 / 2 : ℝ) * force x) ∂volume =
          (∫ x in V, ((3 / 8 : ℝ) * main x + (5 / 2 : ℝ) * datum x +
              (17 / 2 : ℝ) * cutoff x) ∂volume) +
            ∫ x in V, (9 / 2 : ℝ) * force x ∂volume :=
        integral_add ((hmainC.add hdatumC).add hcutoffC) hforceC
      _ = ((∫ x in V, ((3 / 8 : ℝ) * main x +
                (5 / 2 : ℝ) * datum x) ∂volume) +
              ∫ x in V, (17 / 2 : ℝ) * cutoff x ∂volume) +
            ∫ x in V, (9 / 2 : ℝ) * force x ∂volume := by
        congr 1
        simpa only [Pi.add_apply] using
          (integral_add (hmainC.add hdatumC) hcutoffC)
      _ = (((∫ x in V, (3 / 8 : ℝ) * main x ∂volume) +
                ∫ x in V, (5 / 2 : ℝ) * datum x ∂volume) +
              ∫ x in V, (17 / 2 : ℝ) * cutoff x ∂volume) +
            ∫ x in V, (9 / 2 : ℝ) * force x ∂volume := by
        congr 2
        simpa only [Pi.add_apply] using (integral_add hmainC hdatumC)
      _ = _ := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          integral_const_mul]
  rw [hsplit] at hmono
  rw [← hid] at hmono
  nlinarith only [hmono, hcutoff0, hforce0]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
