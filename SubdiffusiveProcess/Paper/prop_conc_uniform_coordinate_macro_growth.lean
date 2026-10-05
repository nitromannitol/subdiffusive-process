module

public import SubdiffusiveProcess.Paper.prop_conc_uniform_affine_macro_growth
public import SubdiffusiveProcess.Paper.prop_conc_coordinate_limit_growth

@[expose] public section

/-! # Uniform coordinate energy growth

The finitely many coordinate minimizers share one disorder threshold and one
moment bound, both fixed before the model. Growth is asserted at resolved radii.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Coordinate energy measures share a uniform moment growth bound above the cutoff scale. -/
theorem prop_conc_uniform_coordinate_macro_growth
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t p : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) (hp : 1 ≤ p) :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 ≤ B ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Sreg : in_6_16 d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ K : ℕ → BilateralField d → ℝ,
        (∀ N, Measurable (K N)) ∧ (∀ N om, 0 ≤ K N om) ∧
        (∀ N, eLpNorm (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
          ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
            C * ‖subspaceGradient (killedSobolevGraph
              (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖)
          (N : ℕ) (x : SpatialCoordinates d) (rho : ℝ),
          x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos → 0 < rho → rho ≤ 1 →
          (3 : ℝ) ^ (-(N : ℤ)) ≤ rho →
          (aux_prop_conc_coordinate_limit_growth_measure
            (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP
            (cutoffPositiveCoefficient M H om N 0 one_pos) : Measure (SpatialCoordinates d))
            (Metric.ball x rho ∩ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) ≤
              ENNReal.ofReal (K N om * rho ^ t) := by
  classical
  let hdim : NeZero d := ⟨by omega⟩
  choose delta B hdelta hB hbank using fun i : Fin d =>
    prop_conc_uniform_affine_macro_growth d hd t p ht htd hp (Pi.single i 1)
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
  let delta0 := Finset.univ.inf' hne delta
  have hdelta0 : 0 < delta0 := (Finset.lt_inf'_iff hne).mpr (fun i _ => hdelta i)
  refine ⟨delta0, ∑ i, B i, hdelta0, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  intro M Sreg H hIR hsmall
  choose K hKm hK0 hKn hKg using fun i : Fin d =>
    hbank i M Sreg H hIR (hsmall.trans (Finset.inf'_le _ (Finset.mem_univ i)))
  let KS : ℕ → BilateralField d → ℝ := fun N om => ∑ i, K i N om
  refine ⟨KS, (fun N => Finset.measurable_sum _ (fun i _ => hKm i N)),
    (fun N om => Finset.sum_nonneg (fun i _ => hK0 i N om)), ?_, ?_⟩
  · intro N
    have hpn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
    calc
      eLpNorm (KS N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ∑ i, eLpNorm (K i N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure := by
        simpa only [KS, Finset.sum_fn] using
          (eLpNorm_sum_le (f := fun i => K i N) (s := Finset.univ)
            hpn)
      _ ≤ ∑ i, ENNReal.ofReal (B i) := Finset.sum_le_sum (fun i _ => hKn i N)
      _ = ENNReal.ofReal (∑ i, B i) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i _ => hB i)).symm
  · have hall : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ i : Fin d,
        ∀ (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
          ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
            C * ‖subspaceGradient (killedSobolevGraph
              (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖)
          (N : ℕ) (x : SpatialCoordinates d) (rho : ℝ),
          x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos → 0 < rho → rho ≤ 1 →
          (3 : ℝ) ^ (-(N : ℤ)) ≤ rho →
          localGradientEnergy (cutoffPositiveCoefficient M H om N 0 one_pos)
            (s := Metric.ball x rho ∩ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
            (Metric.isOpen_ball.measurableSet.inter (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet)
            (sobolevGradient (dirichletMinimizer (killedResponseSpace hP)
              (cutoffPositiveCoefficient M H om N 0 one_pos)
              (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) (Pi.single i 1) 0)).val) ≤
            K i N om * rho ^ t := ae_all_iff.mpr hKg
    filter_upwards [hall] with om hom
    intro hP N x rho hx hrho hrho1 hcutoff
    let a := cutoffPositiveCoefficient M H om N 0 one_pos
    let mu := fun i : Fin d => aux_prop_conc_affine_cutoff_growth_measure
      (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP a (Pi.single i 1)
    have hsingle (i : Fin d) : mu i
        (Metric.ball x rho ∩ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) ≤
          ENNReal.ofReal (K i N om * rho ^ t) := by
      let hfin : IsFiniteMeasure (mu i) :=
        (aux_prop_conc_affine_cutoff_growth_finite_mass _ hP a (Pi.single i 1)).1
      have hreal := (gradientEnergy_withDensity_finite_and_real a
        (sobolevGradient (dirichletMinimizer (killedResponseSpace hP) a
          (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) (Pi.single i 1) 0)).val)).2
          (Metric.ball x rho ∩ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet)
      exact (ENNReal.ofReal_toReal (measure_ne_top (mu i) _)).symm.trans_le
        (ENNReal.ofReal_le_ofReal (hreal.trans_le (hom i hP N x rho hx hrho hrho1 hcutoff)))
    change (∑ i, mu i) _ ≤ _
    rw [Measure.finsetSum_apply]
    calc
      _ ≤ ∑ i, ENNReal.ofReal (K i N om * rho ^ t) := Finset.sum_le_sum (fun i _ => hsingle i)
      _ = ENNReal.ofReal (KS N om * rho ^ t) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
          mul_nonneg (hK0 i N om) (Real.rpow_nonneg hrho.le _))]
        congr 1
        exact (Finset.sum_mul _ _ _).symm

end
end SubdiffusiveProcess.Paper
