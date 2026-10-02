import SubdiffusiveProcess.Paper.lfgc_root_band
import SubdiffusiveProcess.Paper.lfgc_base_moments
import SubdiffusiveProcess.Lfgc.Cover
import SubdiffusiveProcess.Paper.chart_coords_measurable

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Zero-disorder smallness of the root statistic

At small disorder, uniformly in the cutoff, the root level and the centre,
`P(t < aux_lfgc_root_impl_rootX H) ≤ #coords · (C δ^c / (t/K)^2)^p` for the infrared field `H`.
Each selected coordinate of a root chart equals, almost surely, the same coordinate of the
unit-root chart of the shifted field (`aux_lem_band_U2_T4_chart_identity`); the shift
preserves the law, so the base moments of `BaseMoments` and lem_band's `invlam_core`,
`cellE` apply.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The four selected coordinates of a root chart agree a.e. with those of the shifted unit chart. -/
theorem aux_lfgc_root_base_root_coords_transport [NeZero d] (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (sigma : ℝ) (N : ℕ) (m : ℤ) (hm : m ≤ (N : ℤ)) (w : SpatialCoordinates d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      let F := aux_lfgc_root_stat_rootChart I M H omega N m w
      let ref := Paper.aux_lem_band_U2_reference M H N m w omega
      let G := Paper.aux_lem_band_U2_unitChart I M H (Paper.aux_lem_band_U2_shift m w omega)
        ((N : ℤ) - m).toNat
      ref / Paper.aux_lem_band_U2_lamF sigma F = (Paper.aux_lem_band_U2_lamF sigma G)⁻¹ ∧
      Paper.aux_lem_band_U2_LamF sigma F / ref = Paper.aux_lem_band_U2_LamF sigma G ∧
      Paper.aux_lem_band_U2_errF sigma F ref = Paper.aux_lem_band_U2_errF sigma G 1 ∧
      ∀ a b : Fin d, Paper.aux_lem_band_U2_sigF a b F / ref = Paper.aux_lem_band_U2_sigF a b G := by
  have hT4 := Paper.aux_lem_band_U2_T4_chart_identity I M H hH N m hm w (by positivity)
  filter_upwards [hT4] with omega homega
  intro F ref G
  have hpos := Paper.aux_lem_band_U2_reference_pos M H N m w omega
  have e1 : Paper.aux_lem_band_U2_lamF sigma F = ref * Paper.aux_lem_band_U2_lamF sigma G :=
    Paper.aux_lem_band_U2_lamF_scaled sigma _ hpos _ _ homega
  have e2 : Paper.aux_lem_band_U2_LamF sigma F = ref * Paper.aux_lem_band_U2_LamF sigma G :=
    Paper.aux_lem_band_U2_LamF_scaled sigma _ hpos _ _ homega
  have e3 : Paper.aux_lem_band_U2_errF sigma F ref = Paper.aux_lem_band_U2_errF sigma G 1 :=
    Paper.aux_lem_band_U2_errF_scaled sigma _ hpos _ _ homega
  have e4 : ∀ a b : Fin d, Paper.aux_lem_band_U2_sigF a b F =
      ref * Paper.aux_lem_band_U2_sigF a b G :=
    fun a b => Paper.aux_lem_band_U2_sigF_scaled _ hpos _ _ homega a b
  have hpos' : 0 < ref := hpos
  refine ⟨?_, ?_, e3, fun a b => ?_⟩
  · rw [e1, div_mul_eq_div_div, div_self hpos'.ne', one_div]
  · rw [e2]; field_simp
  · rw [e4 a b]; field_simp

/-- Chebyshev from a transported moment bound. -/
theorem lfgc_root_base (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ)
    (w : SpatialCoordinates d) (f : BilateralField d → ℝ) (g : BilateralField d → ℝ)
    (hf : AEStronglyMeasurable f (chaosSampleLaw M).toMeasure)
    (hfg : f =ᵐ[(chaosSampleLaw M).toMeasure] fun omega => g (Paper.aux_lem_band_U2_shift m w omega))
    {p B : ℝ} (hp : 0 < p) (hB : eLpNorm g (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal B) {s : ℝ} (hs : 0 < s) :
    (chaosSampleLaw M).toMeasure {omega | s < |f omega|} ≤ (ENNReal.ofReal B / ENNReal.ofReal s) ^ p := by
  refine (meas_lt_abs_le_eLpNorm _ hf hp hs).trans ?_
  gcongr
  rw [eLpNorm_congr_ae hfg, Paper.aux_lem_band_U2_eLpNorm_comp_shift]
  exact hB

end Paper
