import SubdiffusiveProcess.Frozen.Section6.CutoffHolderBoundedMultiplier
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedCoefficientEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.EquationLocalization

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.BoundedMultiplier

/-- The bounded-multiplier conclusions depend only on the coefficient on the window. -/
theorem pathwise_estimate_congr {d : ℕ} (M : GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d) (j : ℕ) (B' : Set (Vec d)) (epsilon C c : ℝ)
    (w v : PotentialSample d)
    (heq : restrictedCoefficientObservation (aCutoff M L) (translatedCube d m z) w =
      restrictedCoefficientObservation (aCutoff M L) (translatedCube d m z) v) :
    BoundedMultiplierPathwiseEstimate M L m z j B' epsilon C c w ↔
      BoundedMultiplierPathwiseEstimate M L m z j B' epsilon C c v := by
  have hcoeff : ∀ x ∈ translatedCube d m z, aCutoff M L w x = aCutoff M L v x := by
    intro x hx
    exact congrFun heq ⟨x, hx⟩
  have htransfer : ∀ w v : PotentialSample d,
      (∀ x ∈ translatedCube d m z, aCutoff M L w x = aCutoff M L v x) →
      BoundedMultiplierPathwiseEstimate M L m z j B' epsilon C c w →
      BoundedMultiplierPathwiseEstimate M L m z j B' epsilon C c v := by
    intro w v hcoeff hp theta hcont hpos hnear h hharm
    apply hp theta hcont hpos hnear h
    exact (isWeaklyHarmonicOn_congr_coeff
      (by rw [translatedCube_eq_metricBall]; exact Metric.isOpen_ball.measurableSet)
      (fun x hx => congrArg (fun a : ℝ => a * theta x) (hcoeff x hx))).mpr hharm
  exact ⟨htransfer w v hcoeff, htransfer v w (fun x hx => (hcoeff x hx).symm)⟩

/-- Localize an ambient exceptional event without changing its probability bound. -/
theorem exists_restricted_estimate (d : ℕ) :
    ∃ epsilon c C : ℝ, 0 < epsilon ∧ 0 < c ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ (L : ℕ) (m : ℤ) (z : Vec d) (j : ℕ), 0 < j →
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
        ∃ bad : Set (PotentialSample d),
          MeasurableSet[restrictedCoefficientSigma (aCutoff M L) (translatedCube d m z)] bad ∧
          M.P.toMeasure bad ≤ ENNReal.ofReal
            (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
          ∀ w ∉ bad, BoundedMultiplierPathwiseEstimate M L m z j B' epsilon C c w := by
  obtain ⟨epsilon, c, C, hepsilon, hc, hC, hmain⟩ :=
    SubdiffusiveProcess.Frozen.Section6.cutoff_holder_bounded_multiplier d
  refine ⟨epsilon, c, C, hepsilon, hc, hC, ?_⟩
  intro M hdelta L m z j hj B' hB'
  obtain ⟨bad, hmeas, htail, hpath⟩ := hmain M hdelta L m z j hj B' hB'
  have hprinted : (⨆ i : ℕ, MeasurableSpace.comap
      (fun w : PotentialSample d => w i) inferInstance) =
        (inferInstance : MeasurableSpace (PotentialSample d)) := by
    simp only [MeasurableSpace.pi]
  have hmeas' : MeasurableSet bad := by simpa only [hprinted] using hmeas
  letI : Nonempty (translatedCube d m z) := by
    have h := (Homogenization.Book.Ch02.openCubeSet_nonempty (originCube d m)).image
      (fun x => z + x)
    exact h.to_subtype
  obtain ⟨bad', hmeas', htail', hpath'⟩ :=
    Section6Stopping.restricted_exists_coefficient_bad M.P.toMeasure (aCutoff M L)
      (translatedCube d m z) (continuous_aCutoff M L)
      (fun x _ => measurable_aCutoff M L x)
      (BoundedMultiplierPathwiseEstimate M L m z j B' epsilon C c)
      badᶜ hmeas'.compl hpath (pathwise_estimate_congr M L m z j B' epsilon C c)
  refine ⟨bad', hmeas', ?_, hpath'⟩
  exact htail'.trans (by simpa only [compl_compl] using htail)

end SubdiffusiveProcess.BoundedMultiplier
