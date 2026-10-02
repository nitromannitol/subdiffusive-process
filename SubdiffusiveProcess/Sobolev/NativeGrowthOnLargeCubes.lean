import SubdiffusiveProcess.Sobolev.NativeEnergyMeasureGrowth
import SubdiffusiveProcess.Analysis.BoundedSetBallGrowth

/-! Native local gradient bounds control full energy and energy-measure growth
on every positive cube. The geometric factor may depend on that cube. -/

open MeasureTheory Set TopologicalSpace Homogenization
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess
noncomputable section

/-- Every positive cube admits the native energy and ball-growth conversion with a fixed geometric factor. -/
theorem native_energy_and_measure_growth_all_cubes
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (c : SpatialCoordinates d → ℝ),
      (a.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c) →
      ∀ (v : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
        (B t : ℝ), 0 ≤ B → 0 ≤ t →
      (∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        localGradientEnergy a
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (sobolevDataOfH1 v)) ≤ B * rad ^ t) →
      energy c (centeredCube z r hr : Set (SpatialCoordinates d)) v ≤ A * B ∧
      ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal (c y * ∑ i : Fin d, (v.grad y i) ^ 2)))
          (Metric.ball x rad) ≤ ENNReal.ofReal ((2 ^ t * (A * B)) * rad ^ t) := by
  let Q := centeredCube z r hr
  have hcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) := by
    change IsCompact (closure (Metric.ball z (r / 2)))
    exact (isCompact_closedBall z (r / 2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  obtain ⟨A, hA, hgeom⟩ := boundedSet_measure_ball_growth (Q : Set (SpatialCoordinates d)) hcompact
  refine ⟨A, hA, ?_⟩
  intro a c hc v B t hB ht hg
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
    exact Finset.sum_congr rfl (fun i _ => by
      rw [show (sobolevGradient (sobolevDataOfH1 v)) i y = v.grad y i from hgrad i])
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
  obtain ⟨hmass, hall⟩ := hgeom mu B t hB ht hopen
  constructor
  · have hmass' : nu (Q : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (A * B) := by
      rw [← heq, Measure.restrict_apply Q.isOpen.measurableSet, inter_self]
      exact hmass
    have hmassReal := (ENNReal.toReal_le_toReal (measure_ne_top nu _)
      ENNReal.ofReal_ne_top).mpr hmass'
    have hrealQ : (nu (Q : Set (SpatialCoordinates d))).toReal =
        localGradientEnergy a Q.isOpen.measurableSet (sobolevGradient (sobolevDataOfH1 v)) :=
      hreal _ Q.isOpen.measurableSet
    rw [hrealQ,
      localGradientEnergy_domain_eq_sobolevCoefficientForm,
      ENNReal.toReal_ofReal (mul_nonneg (zero_le_one.trans hA) hB)] at hmassReal
    rwa [energy_eq_sobolevCoefficientForm a c hc]
  · intro x rad hrad hrad1
    change ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity g) _ ≤ _
    rw [← restrict_withDensity Q.isOpen.measurableSet g,
      Measure.restrict_apply Metric.isOpen_ball.measurableSet]
    exact hall x rad hrad hrad1

end
end SubdiffusiveProcess
