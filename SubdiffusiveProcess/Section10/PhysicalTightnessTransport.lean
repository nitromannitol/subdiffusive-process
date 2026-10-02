import SubdiffusiveProcess.Section10.PhysicalTightnessNonexplosion
import SubdiffusiveProcess.Section10.PhysicalTightnessRandomLaws
import MarkovProcess.Lifetime.NonexplosiveTransport
import MarkovProcess.Lifetime.CountablySeparated
import MarkovProcess.Path.Polish
import SubdiffusiveProcess.Model.LifetimeProcess

/-!
# Exact lifetime-law conclusions from uniform path tightness

Measurable extension preserves probability at every environment and every start.
Its bad-path event is contained in the complement of the infinite-lifetime image
of the compact path set. Hence the lifetime formulation of (i) directly supplies
(ii), including the literal universal quantifier over probability measures used
by the approved consumer. Uniform lifetime tightness also implies simultaneous
all-start nonexplosion. The quantitative tightness supplier is kept explicit;
these reductions do not claim the paper root.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

local instance cemeteryVecStandardBorel (d : ℕ) : StandardBorelSpace (Cemetery (Vec d)) := by
  letI : BorelSpace (Cemetery (Vec d)) := SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  infer_instance

/-- The bad event of the canonical extension is contained in the lifetime bad
image event, even before nonexplosion is known. -/
theorem extension_bad_mass_le {d : ℕ} (ν : Measure (Path d))
    (default : ContinuousPath (Vec d)) (K : Set (ContinuousPath (Vec d)))
    (hK : MeasurableSet K) :
    ν.map (LifetimePath.continuousPathExtension default) Kᶜ ≤
      ν (LifetimePath.ofContinuousPath '' K)ᶜ := by
  rw [Measure.map_apply (LifetimePath.measurable_continuousPathExtension default) hK.compl]
  apply measure_mono
  rintro w hw ⟨p, hp, rfl⟩
  exact hw (by simpa using hp)

/-- The infinite-lifetime image version of (i) already implies nonexplosion,
on one full environment event for all cutoffs and all starting points. -/
theorem nonexplosion_of_lifetime_tightness {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (LN : ℕ → Kernel (Ω × Vec d) (Path d))
    (htight : ∀ B : Set (Vec d), IsCompact B → ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (ContinuousPath (Vec d)), IsCompact K ∧
        ∀ N : ℕ, ∃ G : Ω → ENNReal, Measurable G ∧
          (∀ ω, ∀ x ∈ B, LN N (ω, x) (LifetimePath.ofContinuousPath '' K)ᶜ ≤ G ω) ∧
          ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal ε) :
    ∀ᵐ ω ∂μ, ∀ N : ℕ, ∀ x : Vec d, ∀ᵐ w ∂LN N (ω, x), w.lifetime = ⊤ := by
  have hzero : ∀ N m : ℕ, ∀ᵐ ω ∂μ,
      ∀ x ∈ Metric.closedBall (0 : Vec d) (m : ℝ),
        LN N (ω, x) {w | w.lifetime ≠ ⊤} = 0 := by
    intro N m
    apply ae_forall_eq_zero_of_majorants μ (Metric.closedBall (0 : Vec d) (m : ℝ))
      (fun ω x => LN N (ω, x) {w | w.lifetime ≠ ⊤})
    intro ε hε
    obtain ⟨K, hK, hbound⟩ := htight _ (isCompact_closedBall _ _) ε hε
    obtain ⟨G, hG, hpoint, hmoment⟩ := hbound N
    refine ⟨G, hG, Eventually.of_forall (fun ω x hx => ?_), hmoment⟩
    refine (measure_mono ?_).trans (hpoint ω x hx)
    rintro w hw ⟨p, hp, rfl⟩
    exact hw (LifetimePath.lifetime_ofContinuousPath p)
  filter_upwards [ae_all_iff.mpr fun N => ae_all_iff.mpr (hzero N)] with ω hω
  intro N x
  obtain ⟨m, hm⟩ := exists_nat_gt (dist x (0 : Vec d))
  have hx : x ∈ Metric.closedBall (0 : Vec d) (m : ℝ) := Metric.mem_closedBall.mpr hm.le
  have h := measure_eq_zero_iff_ae_notMem.mp (hω N m x hx)
  filter_upwards [h] with w hw
  exact not_not.mp hw

/-- Literal random-law conclusion for the lifetime kernel, derived from the
measurable majorants in (i). No conservativity premise is needed for this step. -/
theorem lifetime_compact_random_laws {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (LN : ℕ → Kernel (Ω × Vec d) (Path d))
    (hLN : ∀ N, IsMarkovKernel (LN N)) (B : Set (Vec d))
    (htight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (ContinuousPath (Vec d)), IsCompact K ∧
        ∀ N : ℕ, ∃ G : Ω → ENNReal, Measurable G ∧
          (∀ ω, ∀ x ∈ B, LN N (ω, x) (LifetimePath.ofContinuousPath '' K)ᶜ ≤ G ω) ∧
          ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal ε)
    (default : ContinuousPath (Vec d)) :
    ∀ η : ℝ, 0 < η → ∃ Keta : Set (ProbabilityMeasure (ContinuousPath (Vec d))),
      IsCompact Keta ∧ ∀ N : ℕ, μ {ω | ∃ x ∈ B,
        ∀ ν : ProbabilityMeasure (ContinuousPath (Vec d)),
          (ν : Measure (ContinuousPath (Vec d))) =
            (LN N (ω, x)).map (LifetimePath.continuousPathExtension default) →
          ν ∉ Keta} ≤ ENNReal.ofReal η := by
  let P : ℕ → Ω → Vec d → ProbabilityMeasure (ContinuousPath (Vec d)) := fun N ω x => by
    letI := hLN N
    exact ⟨(LN N (ω, x)).map (LifetimePath.continuousPathExtension default),
      Measure.isProbabilityMeasure_map (LifetimePath.measurable_continuousPathExtension default).aemeasurable⟩
  have hpath : ∀ ε : ℝ, 0 < ε → ∃ K : Set (ContinuousPath (Vec d)), IsCompact K ∧
      ∀ N : ℕ, ∃ G : Ω → ENNReal, Measurable G ∧
        (∀ ω, ∀ x ∈ B, (P N ω x : Measure (ContinuousPath (Vec d))) Kᶜ ≤ G ω) ∧
        ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨K, hK, hbound⟩ := htight ε hε
    refine ⟨K, hK, ?_⟩
    intro N
    obtain ⟨G, hG, hpoint, hmoment⟩ := hbound N
    exact ⟨G, hG, fun ω x hx =>
      (extension_bad_mass_le (LN N (ω, x)) default K hK.isClosed.measurableSet).trans
        (hpoint ω x hx), hmoment⟩
  intro η hη
  obtain ⟨Keta, hKeta, hbad⟩ := exists_compact_random_laws μ P B hpath η hη
  refine ⟨Keta, hKeta, ?_⟩
  intro N
  refine (measure_mono ?_).trans (hbad N)
  rintro ω ⟨x, hx, hν⟩
  exact ⟨x, hx, hν (P N ω x) rfl⟩

end SubdiffusiveProcess.Section10.PhysicalTightness
