module

public import SubdiffusiveProcess.Paper.lane4_reference_point_moments

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open SubdiffusiveProcess
open scoped ENNReal

namespace SubdiffusiveProcess.Paper

/-- A real moment bound gives the numerical Lp bound once membership is known. -/
theorem aux_shallow_eLpNorm_le_of_integral_rpow_norm_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Ω → ℝ) (p L : ℝ) (hp : 0 < p)
    (hs : MemLp s (ENNReal.ofReal p) P)
    (hbound : (∫ ω, ‖s ω‖ ^ p ∂P) ≤ L) :
    eLpNorm s (ENNReal.ofReal p) P ≤ ENNReal.ofReal (L ^ p⁻¹) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  rw [hs.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hbound
    (inv_nonneg.mpr hp.le))

/-- The paired positive and inverse moment in the point estimate controls the
numerical Lp norm of the positive response factor. -/
theorem aux_shallow_eLpNorm_le_of_paired_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Ω → ℝ) (p L : ℝ) (hp : 0 < p)
    (hspos : ∀ ω, 0 < s ω)
    (hs : MemLp s (ENNReal.ofReal p) P)
    (hsum : Integrable (fun ω => (s ω) ^ p + (s ω) ^ (-p)) P)
    (hbound : (∫ ω, (s ω) ^ p + (s ω) ^ (-p) ∂P) ≤ L) :
    eLpNorm s (ENNReal.ofReal p) P ≤ ENNReal.ofReal (L ^ p⁻¹) := by
  apply aux_shallow_eLpNorm_le_of_integral_rpow_norm_le P s p L hp hs
  apply (integral_mono_of_nonneg (ae_of_all _ fun ω => Real.rpow_nonneg
      (norm_nonneg (s ω)) p) hsum (ae_of_all _ fun ω => ?_)).trans hbound
  change ‖s ω‖ ^ p ≤ (s ω) ^ p + (s ω) ^ (-p)
  rw [Real.norm_eq_abs, abs_of_pos (hspos ω)]
  exact le_add_of_nonneg_right (Real.rpow_nonneg (hspos ω).le _)

/-- Positivity for the precise point factor in `lane4_reference_point_moments`. -/
theorem aux_shallow_reference_point_factor_pos
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N k : ℕ) (ω : BilateralField d) (y : SpatialCoordinates d) :
    0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp (H ω y + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) y -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
  exact mul_pos
    (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k))
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
    (Real.exp_pos _)

/-- Numeric Lp rate for the exact point factor, deduced from the proved paired
moment bound at the shallow proof's exponent `2*q`. -/
theorem lem_as_coarse_shallow_grid_point_rate
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cmom Crate : ℝ,
      0 < Cmom ∧ 0 < Crate ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (N k : ℕ), k ≤ N →
        ∀ y : SpatialCoordinates d,
          (∀ i, 0 ≤ y i ∧ y i ≤ 1) →
          eLpNorm
            (fun ω : BilateralField d =>
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
                  Real.exp (H ω y + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) y -
                    (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
            (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal
            ((Cmom * Real.exp (Crate * ((2 * q) + (2 * q)^2) *
              M.delta^2 * (k : ℝ))) ^ (2 * q)⁻¹) := by
  obtain ⟨Cmom, Crate, hCmom, hCrate, hpoint⟩ :=
    lane4_reference_point_moments d hd q hq
  refine ⟨Cmom, Crate, hCmom, hCrate, ?_⟩
  intro delta0 hdelta0 hdelta01 M Rm H hH hMd N k hkn y hy
  have hq2 : (2 * q : ℝ) ∈ Set.Icc 1 (2 * q) :=
    ⟨by linarith, le_rfl⟩
  obtain ⟨hInt, hbound, hs, _⟩ :=
    hpoint delta0 hdelta0 hdelta01 M Rm H hH hMd
      (2 * q) hq2 N k hkn y hy
  exact aux_shallow_eLpNorm_le_of_paired_moment
    (chaosSampleLaw M).toMeasure
    (fun ω : BilateralField d =>
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (H ω y + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) y -
            (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
    (2 * q)
    (Cmom * Real.exp (Crate * ((2 * q) + (2 * q)^2) * M.delta^2 * (k : ℝ)))
    (by linarith)
    (fun ω => aux_shallow_reference_point_factor_pos M H N k ω y)
    hs hInt hbound

end SubdiffusiveProcess.Paper




