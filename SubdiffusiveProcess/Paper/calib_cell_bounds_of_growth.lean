import Mathlib
import SubdiffusiveProcess.Paper.prop_growth_large_root
import SubdiffusiveProcess.Paper.prop_conc_countable_native_growth_with_moment
import SubdiffusiveProcess.Paper.prop_conc_native_cell_bounds_with_moment
import SubdiffusiveProcess.Paper.prop_conc_form_cutoff_continuity
import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family
import SubdiffusiveProcess.Sobolev.NativeGrowthOnLargeCubes

/-! Harmonic-cell bounds for a cell of ANY side from the `prop_growth` conclusion on the cell (Stage 3 adapter).
Deterministic: energy, energy-measure growth and Hölder bound of the continuous harmonic functions with smooth datum on a cube
`Q(c, r)` (side `r` arbitrary) from a uniform bound `K_n ≤ B` in `GrowthAtCoef` for the coefficients `A_n`.  The proof is that of
`prop_conc_countable_native_growth_with_moment` and `prop_conc_native_cell_bounds_with_moment` (cells of side `≤ 1`), with the
unit-ball step replaced by `native_energy_and_measure_growth_all_cubes`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- **Cell bounds from `prop_growth` on a cell of any side.** -/
theorem calib_cell_bounds_of_growth {d : ℕ} (hd : 2 ≤ d) (c : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (A : ℕ → PositiveCoefficient (centeredCube c r hr)) (a : ℕ → SpatialCoordinates d → ℝ)
    (hAa : ∀ n, (fun x => (A n).val x) =ᵐ[volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))] a n)
    (t alpha : ℝ) (ht : 0 ≤ t) (ha : 0 < alpha) (K : ℕ → ℝ) (B : ℝ) (hK : ∀ n, K n ≤ B)
    (hG : aux_prop_growth_large_root_GrowthAtCoef c r hr t alpha A K)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi)
    (beta : H1Function (centeredCube c r hr : Set (SpatialCoordinates d))) (hbeta : beta.toFun = phi) :
    ∃ E Gr Ho : ℝ, 0 ≤ E ∧ 0 ≤ Gr ∧ 0 ≤ Ho ∧
      ∀ (n : ℕ) (v : H1Function (centeredCube c r hr : Set (SpatialCoordinates d))),
        IsWeaklyHarmonicOn (a n) (centeredCube c r hr : Set (SpatialCoordinates d)) v →
        HasZeroTraceDifferenceOn (centeredCube c r hr : Set (SpatialCoordinates d)) v beta →
        ContinuousOn v.toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))) →
        energy (a n) (centeredCube c r hr : Set (SpatialCoordinates d)) v ≤ E ∧
        (∀ x ∈ closure (centeredCube c r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
          ((volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a n y * ∑ j : Fin d, (v.grad y j) ^ 2))) (Metric.ball x rad) ≤
              ENNReal.ofReal (Gr * rad ^ t)) ∧
        (∀ x ∈ closure (centeredCube c r hr : Set (SpatialCoordinates d)),
          ∀ y ∈ closure (centeredCube c r hr : Set (SpatialCoordinates d)),
          |v.toFun x - v.toFun y| ≤ Ho * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) := by
  haveI dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨Ag, hAg1, hAg⟩ := native_energy_and_measure_growth_all_cubes c hr
  let Cphi := c2Norm (closedCube c r hr : Set (SpatialCoordinates d)) phi
  have hC : 0 ≤ Cphi := aux_prop_growth_c2Norm_nonneg _ _
  let Bp := max B 0
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  have hE : 0 ≤ Bp * Cphi ^ 2 := mul_nonneg hBp0 (sq_nonneg _)
  refine ⟨Ag * (Bp * Cphi ^ 2), 2 ^ t * (Ag * (Bp * Cphi ^ 2)), Bp * Cphi,
    mul_nonneg (zero_le_one.trans hAg1) hE,
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (mul_nonneg (zero_le_one.trans hAg1) hE),
    mul_nonneg hBp0 hC, ?_⟩
  intro n v hharm htrace hvcont
  have hP := centeredCube_killedPoincare c hr
  have hmin := native_harmonic_energy_eq_infimum (A n) (a n) (hAa n) beta v htrace hharm
  have hsolve := solvesDirichlet_zero_of_native_minimum hP (A n) (a n) (hAa n) beta v htrace hmin.le
  obtain ⟨henergy, U, hUcont, hUae, hUholder, hUnorm⟩ := hG n (fun _ => 0) 0 le_rfl
    aemeasurable_const (Filter.Eventually.of_forall fun _ => by norm_num)
    phi Cphi hphi le_rfl _ _
    ((sobolevDataOfH1_fst_coeFn beta).trans (Filter.Eventually.of_forall fun x => congrFun hbeta x)) hsolve
  have hKn : K n * Cphi ^ 2 ≤ Bp * Cphi ^ 2 :=
    mul_le_mul_of_nonneg_right ((hK n).trans (le_max_left _ _)) (sq_nonneg _)
  have hg : ∀ x ∈ centeredCube c r hr, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
      localGradientEnergy (A n)
        (s := Metric.ball x rad ∩ (centeredCube c r hr : Set (SpatialCoordinates d)))
        (Metric.isOpen_ball.measurableSet.inter (centeredCube c r hr).isOpen.measurableSet)
        (sobolevGradient (sobolevDataOfH1 v)) ≤ (Bp * Cphi ^ 2) * rad ^ t := by
    intro x hx rad hrad hrad1
    have h1 := henergy x rad hx hrad hrad1
    have hrt : 0 ≤ rad ^ t := Real.rpow_nonneg hrad.le _
    calc _ ≤ K n * (0 + Cphi) ^ 2 * rad ^ t := h1
      _ ≤ (Bp * Cphi ^ 2) * rad ^ t := by
        rw [zero_add]; exact mul_le_mul_of_nonneg_right hKn hrt
  obtain ⟨hen, hgrow⟩ := hAg (A n) (a n) (hAa n) v (Bp * Cphi ^ 2) t hE ht hg
  have heq := eqOn_closure_of_ae_eq_restrict (centeredCube c r hr).isOpen
    hvcont hUcont.continuousOn ((sobolevDataOfH1_fst_coeFn v).symm.trans hUae)
  rw [aux_prop_conc_form_cutoff_continuity_closure_cube] at heq
  have hholder := (isHolderOn_congr heq).mpr hUholder
  have hnorm : cAlphaNorm alpha (closedCube c r hr : Set (SpatialCoordinates d)) v.toFun ≤ Bp * Cphi := by
    rw [cAlphaNorm_congr heq]
    have h2 := hUnorm
    rw [zero_add] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right ((hK n).trans (le_max_left _ _)) hC)
  refine ⟨hen, fun x _ rad hrad hrad1 => hgrow x rad hrad hrad1, ?_⟩
  rw [aux_prop_conc_form_cutoff_continuity_closure_cube]
  exact aux_lem_cutoffs_pair_bound_of_holder ha hholder hnorm

end
end Paper
