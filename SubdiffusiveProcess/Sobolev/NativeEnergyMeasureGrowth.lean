module

public import SubdiffusiveProcess.Sobolev.NativeCellGrowth
public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasure
public import SubdiffusiveProcess.Analysis.MeasureBallGrowth

@[expose] public section

/-! Transfer native local gradient bounds to coefficient-weighted energy measures.
This is a deterministic conversion on a cell of side at most one. -/
open MeasureTheory Set TopologicalSpace Homogenization
open scoped ENNReal NNReal BigOperators
namespace SubdiffusiveProcess
noncomputable section

/-- Local native gradient bounds control energy-measure balls with arbitrary centers. -/
theorem native_energyMeasure_growth_of_localGradient
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : PositiveCoefficient (centeredCube z r hr)) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c)
    (v : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (B t : ℝ) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hg : ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
      localGradientEnergy a
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (sobolevDataOfH1 v)) ≤ B * rad ^ t) :
    ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
      ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (c y * ∑ i : Fin d, (v.grad y i) ^ 2)))
        (Metric.ball x rad) ≤ ENNReal.ofReal ((2 ^ t * B) * rad ^ t) := by
  let Q := centeredCube z r hr
  let g : SpatialCoordinates d → ENNReal := fun y =>
    ENNReal.ofReal (c y * ∑ i : Fin d, (v.grad y i) ^ 2)
  let mu := volume.withDensity g
  let nu := (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
    (fun y => ENNReal.ofReal (∑ i : Fin d, a.val y * ((sobolevGradient (sobolevDataOfH1 v)) i y) ^ 2))
  obtain ⟨hfinite, hreal⟩ := gradientEnergy_withDensity_finite_and_real a
    (sobolevGradient (sobolevDataOfH1 v))
  haveI finiteEnergy : IsFiniteMeasure nu := hfinite
  have heq : mu.restrict (Q : Set (SpatialCoordinates d)) = nu := by
    rw [restrict_withDensity Q.isOpen.measurableSet]
    apply withDensity_congr_ae
    filter_upwards [hc, ae_all_iff.mpr (fun i => sobolevDataOfH1_snd_coeFn v i)] with y hy hgrad
    dsimp only [g]
    rw [← hy, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [show (sobolevGradient (sobolevDataOfH1 v)) i y = v.grad y i from hgrad i])
  have hopen : ∀ x ∈ Q, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
      mu (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) ≤ ENNReal.ofReal (B * rad ^ t) := by
    intro x hx rad hrad hrad1
    have hs : MeasurableSet (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) :=
      Metric.isOpen_ball.measurableSet.inter Q.isOpen.measurableSet
    have hset : mu (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) =
        nu (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) := by
      rw [← heq, Measure.restrict_apply hs, inter_assoc, inter_self]
    rw [hset]
    apply (ENNReal.toReal_le_toReal (measure_ne_top nu _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (mul_nonneg hB (Real.rpow_nonneg hrad.le _))]
    exact (hreal _ hs).le.trans (hg x hx rad hrad hrad1)
  have hq : (Q : Set (SpatialCoordinates d)) ⊆ Metric.ball z 1 :=
    inter_eq_right.mp (centeredCube_unit_ball_inter z hr hr1)
  have hall := measure_ball_inter_growth_of_centers_mem mu (Q : Set (SpatialCoordinates d)) z
    (Metric.mem_ball_self (half_pos hr)) hq B t hB ht hopen
  intro x rad hrad hrad1
  have heq' : (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity g =
      mu.restrict (Q : Set (SpatialCoordinates d)) :=
    (restrict_withDensity Q.isOpen.measurableSet g).symm
  change ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity g) _ ≤ _
  rw [heq', Measure.restrict_apply Metric.isOpen_ball.measurableSet]
  exact hall x rad hrad hrad1

end
end SubdiffusiveProcess
