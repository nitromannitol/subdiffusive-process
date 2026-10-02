import SubdiffusiveProcess.Paper.prop_conc_native_cell_bounds_with_moment

/-! Deterministic conversion of smooth Dirichlet estimates into native harmonic cell controls.
The coefficient sequence and its bound are supplied; there is no random extraction here. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- A smooth homogeneous Dirichlet estimate records both local energy growth and Holder control. -/
def aux_prop_conc_native_cell_control_Estimate
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (t alpha K : ℝ) : Prop :=
  ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ 2 phi →
    ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
      (b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet a (fun _ => 0) b u →
      (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
        0 < rad → rad ≤ 1 →
        localGradientEnergy a
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient u.val) ≤
            K * (c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi) ^ 2 * rad ^ t) ∧
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        (u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
        cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
          K * c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi

/-- Smooth homogeneous Dirichlet estimates bound every native harmonic representative with the same trace. -/
theorem prop_conc_native_cell_control
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hAC : ∀ n, (aC n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] a n)
    (t alpha K : ℝ) (ht : 0 ≤ t) (ha : 0 < alpha) (hK : 0 ≤ K)
    (hest : ∀ n, aux_prop_conc_native_cell_control_Estimate z r hr (aC n) t alpha K)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi)
    (beta : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))) (hbeta : beta.toFun = phi) :
    ∃ E Gr Ho : ℝ, 0 ≤ E ∧ 0 ≤ Gr ∧ 0 ≤ Ho ∧
      ∀ (n : ℕ) (v : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))),
        IsWeaklyHarmonicOn (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d)) v beta →
        ContinuousOn v.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        energy (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) v ≤ E ∧
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
          ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a n y * ∑ j : Fin d, (v.grad y j) ^ 2)))
              (Metric.ball x rad) ≤ ENNReal.ofReal (Gr * rad ^ t)) ∧
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          |v.toFun x - v.toFun y| ≤ Ho * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) := by
  haveI dimensionNonzero : NeZero d := ⟨by omega⟩
  let Cphi := c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi
  have hC : 0 ≤ Cphi := aux_prop_growth_c2Norm_nonneg _ _
  have hE : 0 ≤ K * Cphi ^ 2 := mul_nonneg hK (sq_nonneg _)
  refine ⟨K * Cphi ^ 2, 2 ^ t * (K * Cphi ^ 2), K * Cphi, hE,
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE, mul_nonneg hK hC, ?_⟩
  intro n v hharm htrace hvcont
  have hmin := native_harmonic_energy_eq_infimum (aC n) (a n) (hAC n) beta v htrace hharm
  have hsolve := solvesDirichlet_zero_of_native_minimum (centeredCube_killedPoincare z hr)
    (aC n) (a n) (hAC n) beta v htrace hmin.le
  obtain ⟨hg, U, hUcont, hUae, hUholder, hUnorm⟩ := hest n phi hphi
    _ _
    ((sobolevDataOfH1_fst_coeFn beta).trans (Eventually.of_forall fun x => congrFun hbeta x)) hsolve
  have heq := eqOn_closure_of_ae_eq_restrict (centeredCube z r hr).isOpen
    hvcont hUcont.continuousOn ((sobolevDataOfH1_fst_coeFn v).symm.trans hUae)
  rw [aux_prop_conc_form_cutoff_continuity_closure_cube] at heq
  have hholder := (isHolderOn_congr heq).mpr hUholder
  have hnorm : cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) v.toFun ≤ K * Cphi := by
    rw [cAlphaNorm_congr heq]
    exact hUnorm
  refine ⟨?_, ?_, ?_⟩
  · apply native_energy_le_of_unit_growth z hr hr1 (aC n) (a n) (hAC n) v
    simpa only [Real.one_rpow, mul_one] using hg z 1 (Metric.mem_ball_self (half_pos hr)) one_pos le_rfl
  · intro x _ rad hrad hrad1
    exact native_energyMeasure_growth_of_localGradient z hr hr1 (aC n) (a n) (hAC n) v
      (K * Cphi ^ 2) t hE ht (fun y hy s hs hs1 => hg y s hy hs hs1) x rad hrad hrad1
  · rw [aux_prop_conc_form_cutoff_continuity_closure_cube]
    exact aux_lem_cutoffs_pair_bound_of_holder ha hholder hnorm

end
end Paper
