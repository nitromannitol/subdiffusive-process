module

public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasure

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology BigOperators

namespace Paper
noncomputable section

/-- The finite energy measure of the canonical affine minimizer. -/
def aux_prop_conc_affine_cutoff_growth_measure
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) u‖)
    (a : PositiveCoefficient Q) (pvec : Fin d → ℝ) : Measure (SpatialCoordinates d) :=
  let u := dirichletMinimizer (killedResponseSpace hP) a (affineSobolev hQ pvec 0)
  (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
    (fun x => ENNReal.ofReal (∑ j : Fin d, a.val x *
      ((sobolevGradient (u : SobolevData Q)) j x) ^ 2))

/-- The measure is finite, and its cell mass is the actual affine response. -/
theorem aux_prop_conc_affine_cutoff_growth_finite_mass
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) u‖)
    (a : PositiveCoefficient Q) (pvec : Fin d → ℝ) :
    IsFiniteMeasure (aux_prop_conc_affine_cutoff_growth_measure hQ hP a pvec) ∧
      (aux_prop_conc_affine_cutoff_growth_measure hQ hP a pvec).real Q =
        affineDirichletResponse hQ hP a pvec := by
  let u := dirichletMinimizer (killedResponseSpace hP) a (affineSobolev hQ pvec 0)
  obtain ⟨hfin, hreal⟩ := gradientEnergy_withDensity_finite_and_real a
    (sobolevGradient (u : SobolevData Q))
  refine ⟨hfin, ?_⟩
  exact (hreal Q Q.isOpen.measurableSet).trans
    (localGradientEnergy_domain_eq_sobolevCoefficientForm a (u : SobolevData Q))

/-- The canonical affine minimizer solves the source-free Dirichlet problem. -/
theorem aux_prop_conc_affine_cutoff_growth_solves
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) u‖)
    (a : PositiveCoefficient Q) (pvec : Fin d → ℝ) :
    SolvesDirichlet a (fun _ => 0) (affineSobolev hQ pvec 0)
      (dirichletMinimizer (killedResponseSpace hP) a (affineSobolev hQ pvec 0)) := by
  refine ⟨dirichletMinimizer_mem_affine (killedResponseSpace hP) a
    (affineSobolev hQ pvec 0), ?_⟩
  intro psi
  simpa only [zero_mul, integral_zero] using
    dirichletMinimizer_euler (killedResponseSpace hP) a (affineSobolev hQ pvec 0) psi

/-- The actual affine minimizers have one finite-cutoff growth bank, chosen
before the slope or Poincare witness. All cutoffs and slopes share the event.
The moment constant retains the model and cell dependence of `prop_growth`.
-/
theorem prop_conc_affine_cutoff_growth
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t p : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (hp : 1 ≤ p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : ℝ≥0),
        (∀ n, Measurable (K n)) ∧
        (∀ n, eLpNorm (K n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ Cbound) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ n, 1 ≤ K n om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (hP : ∃ C : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            C * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
          (n : ℕ) (pvec : Fin d → ℝ),
        let mu := aux_prop_conc_affine_cutoff_growth_measure
          (centeredCube_isBounded z hr) hP (cutoffPositiveCoefficient M H om n z hr) pvec
        IsFiniteMeasure mu ∧
          mu.real (centeredCube z r hr) =
            affineDirichletResponse (centeredCube_isBounded z hr) hP
              (cutoffPositiveCoefficient M H om n z hr) pvec ∧
          ∀ (x : SpatialCoordinates d) (rho : ℝ), x ∈ centeredCube z r hr →
            0 < rho → rho ≤ 1 →
            mu (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
              ENNReal.ofReal (K n om *
                (c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
                  (fun y => affineSlope pvec y + 0)) ^ 2 * rho ^ t) := by
  obtain ⟨delta0, hdelta0, hsupplier⟩ :=
    prop_growth d hd I Pin X W Cp Sob t (1 / 2) 1 (fun _ => p)
      ht htd (by norm_num) (by norm_num) (fun _ => hp)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hr1
  obtain ⟨K0, C0, hmem, hnorm, hge, hgrowth⟩ :=
    hsupplier M Rm Sreg It H hIR hdelta z r hr hr1
  let K : ℕ → BilateralField d → ℝ := fun n =>
    (hmem 0 n).aestronglyMeasurable.mk (K0 n)
  have hKm (n : ℕ) : Measurable (K n) :=
    (hmem 0 n).aestronglyMeasurable.measurable_mk
  have heq (n : ℕ) : K0 n =ᵐ[(chaosSampleLaw M).toMeasure] K n :=
    (hmem 0 n).aestronglyMeasurable.ae_eq_mk
  have heqAll : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ n, K0 n om = K n om :=
    ae_all_iff.mpr heq
  refine ⟨K, (C0 0).toNNReal, hKm, ?_, ?_, ?_⟩
  · intro n
    rw [← eLpNorm_congr_ae (heq n)]
    exact hnorm 0 n
  · filter_upwards [hge, heqAll] with om hom he n
    rw [← he n]
    exact hom n
  · filter_upwards [hgrowth, heqAll] with om hom he hP n pvec
    dsimp only
    obtain ⟨hfin, hmass⟩ := aux_prop_conc_affine_cutoff_growth_finite_mass
      (centeredCube_isBounded z hr) hP (cutoffPositiveCoefficient M H om n z hr) pvec
    refine ⟨hfin, hmass, ?_⟩
    let phi : SpatialCoordinates d → ℝ := fun y => affineSlope pvec y + 0
    let Cphi : ℝ := c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi
    let a := cutoffPositiveCoefficient M H om n z hr
    let u := dirichletMinimizer (killedResponseSpace hP) a
      (affineSobolev (centeredCube_isBounded z hr) pvec 0)
    have hphi : ContDiff ℝ 2 phi := (affineSlope pvec).contDiff.add contDiff_const
    have hbound := (hom n (fun _ => 0) 0 le_rfl aemeasurable_const
      (by filter_upwards [] with x; simp)
      phi Cphi hphi le_rfl (affineSobolev (centeredCube_isBounded z hr) pvec 0) u
      (affineL2_coeFn (centeredCube_isBounded z hr) pvec 0)
      (aux_prop_conc_affine_cutoff_growth_solves
        (centeredCube_isBounded z hr) hP a pvec)).1
    intro x rho hx hrho hrho1
    let mu := aux_prop_conc_affine_cutoff_growth_measure
      (centeredCube_isBounded z hr) hP a pvec
    letI : IsFiniteMeasure mu := hfin
    have hreal := (gradientEnergy_withDensity_finite_and_real a
      (sobolevGradient (u : SobolevData (centeredCube z r hr)))).2
      (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
    have hb := hbound x rho hx hrho hrho1
    rw [he n, zero_add] at hb
    have hm : mu.real (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        K n om * Cphi ^ 2 * rho ^ t := hreal.trans_le hb
    exact (ENNReal.ofReal_toReal (measure_ne_top mu _)).symm.trans_le
      (ENNReal.ofReal_le_ofReal hm)

end
end Paper

