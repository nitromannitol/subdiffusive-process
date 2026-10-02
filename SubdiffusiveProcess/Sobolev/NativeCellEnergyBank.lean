import SubdiffusiveProcess.Sobolev.NativeEnergyMeasureRestriction
import SubdiffusiveProcess.Sobolev.GradientEnergyPartition
import SubdiffusiveProcess.Sobolev.GradientEnergyMass

/-! Cell bounds control the actual energy measure of their native Sobolev glue.
Local bounds are preserved separately from the sum used for global compactness.
-/
open MeasureTheory Set TopologicalSpace Homogenization
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- Exact cell data give local energy-measure bounds and their global sum. -/
theorem native_cell_energy_bank
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} {I : Type*} [Fintype I]
    (cell : I → Opens (SpatialCoordinates d)) (hle : ∀ i, cell i ≤ Q)
    (hdisj : Pairwise (Function.onFun Disjoint (fun i => (cell i : Set (SpatialCoordinates d)))))
    (hcover : (⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume] (Q : Set (SpatialCoordinates d)))
    (a : PositiveCoefficient Q) (b : ∀ i, PositiveCoefficient (cell i))
    (hab : ∀ i, (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (cell i : Set (SpatialCoordinates d))] (b i).val)
    (w : H1Function (Q : Set (SpatialCoordinates d))) (u : ∀ i, weakSobolevGraph (cell i))
    (hdata : ∀ i, sobolevDataOfH1 (w.restrict (cell i).isOpen (hle i)) = (u i).val)
    (E : I → ℝ) (hE : ∀ i, 0 ≤ E i)
    (hbound : ∀ i, sobolevCoefficientForm (b i) (u i).val (u i).val ≤ E i) :
    let mu := gradientEnergyMeasure a (sobolevGradient (sobolevDataOfH1 w))
    (∀ i, mu (cell i : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (E i)) ∧
      mu Set.univ ≤ ENNReal.ofReal (∑ i, E i) ∧
      mu (closure (Q : Set (SpatialCoordinates d)))ᶜ = 0 ∧
      sobolevCoefficientForm a (sobolevDataOfH1 w) (sobolevDataOfH1 w) ≤ ∑ i, E i := by
  let mu := gradientEnergyMeasure a (sobolevGradient (sobolevDataOfH1 w))
  have hlocal : ∀ i, mu (cell i : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (E i) := by
    intro i
    have hrestrict := gradientEnergyMeasure_restrict_of_native_data (hle i) a (b i)
      (hab i) w (u i) (hdata i)
    have hm := congrArg (fun nu : Measure (SpatialCoordinates d) => nu Set.univ) hrestrict
    dsimp only at hm
    rw [Measure.restrict_apply_univ] at hm
    change mu (cell i : Set (SpatialCoordinates d)) = _ at hm
    rw [hm]
    exact gradientEnergyMeasure_univ_le (b i) (u i).val (E i) (hbound i)
  have hmass : mu Set.univ ≤ ENNReal.ofReal (∑ i, E i) :=
    withDensity_mass_le_sum_of_partition volume (Q : Set (SpatialCoordinates d))
      (fun i => (cell i : Set (SpatialCoordinates d))) hle
      (fun i => (cell i).isOpen.measurableSet) hdisj hcover _ E hE hlocal
  refine ⟨hlocal, hmass, gradientEnergyMeasure_support _ _, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hE i))] at hreal
  exact (gradientEnergyMeasure_univ_toReal a (sobolevDataOfH1 w)).symm.trans_le hreal

end SubdiffusiveProcess
