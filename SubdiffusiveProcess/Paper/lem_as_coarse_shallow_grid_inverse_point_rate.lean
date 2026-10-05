module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_point_rate

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open SubdiffusiveProcess
open scoped ENNReal

namespace SubdiffusiveProcess.Paper

/-- The inverse half of a paired positive and inverse moment controls its Lp norm. -/
theorem aux_shallow_inverse_eLpNorm_le_of_paired_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Ω → ℝ) (p L : ℝ) (hp : 0 < p)
    (hspos : ∀ ω, 0 < s ω)
    (hsinv : MemLp (fun ω => (s ω)⁻¹) (ENNReal.ofReal p) P)
    (hsum : Integrable (fun ω => (s ω) ^ p + (s ω) ^ (-p)) P)
    (hbound : (∫ ω, (s ω) ^ p + (s ω) ^ (-p) ∂P) ≤ L) :
    eLpNorm (fun ω => (s ω)⁻¹) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (L ^ p⁻¹) := by
  apply aux_shallow_eLpNorm_le_of_integral_rpow_norm_le P
    (fun ω => (s ω)⁻¹) p L hp hsinv
  apply (integral_mono_of_nonneg (ae_of_all _ fun ω => Real.rpow_nonneg
      (norm_nonneg ((s ω)⁻¹)) p) hsum (ae_of_all _ fun ω => ?_)).trans hbound
  change ‖(s ω)⁻¹‖ ^ p ≤ (s ω) ^ p + (s ω) ^ (-p)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hspos ω)),
    ← Real.rpow_neg_eq_inv_rpow]
  exact le_add_of_nonneg_left (Real.rpow_nonneg (hspos ω).le _)

/-- The inverse response factor obeys the same numerical bound as the positive
factor, by the inverse half of the paired moment theorem. -/
theorem lem_as_coarse_shallow_grid_inverse_point_rate
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
              (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
                  Real.exp (H ω y + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) y -
                    (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))⁻¹)
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
  obtain ⟨hInt, hbound, _, hsinv⟩ :=
    hpoint delta0 hdelta0 hdelta01 M Rm H hH hMd
      (2 * q) hq2 N k hkn y hy
  exact aux_shallow_inverse_eLpNorm_le_of_paired_moment
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
    hsinv hInt hbound

end SubdiffusiveProcess.Paper


