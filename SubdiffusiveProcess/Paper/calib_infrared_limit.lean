import SubdiffusiveProcess.Paper.calib_tendsto_continuousMap_of_equilipschitz_dense
import SubdiffusiveProcess.Paper.infrared_characterization_local_lipschitz_majorant
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization

/-! Joint coordinates for the infrared potential: point evaluations on a dense sequence and measurable
local Lipschitz majorants.  Their almost-sure convergence along a represented sequence gives a locally
uniform limit `hinf` of `H (env n ω)`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal
noncomputable section
namespace Paper

/-- A measurable real function is tight under a probability measure. -/
theorem aux_calib_infrared_limit_tight {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Measurable f) :
    ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, P {ω | Mb < |f ω|} ≤ ENNReal.ofReal rho := by
  intro rho hrho
  have hanti : Antitone (fun n : ℕ => {ω | (n : ℝ) < |f ω|}) := by
    intro a b hab ω (hω : (b : ℝ) < |f ω|)
    exact lt_of_le_of_lt (by exact_mod_cast hab) hω
  have hinter : ⋂ n : ℕ, {ω | (n : ℝ) < |f ω|} = ∅ := by
    ext ω
    simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_ge |f ω|
    exact ⟨n, hn⟩
  have hmeas : ∀ n : ℕ, NullMeasurableSet {ω | (n : ℝ) < |f ω|} P := fun n =>
    (measurableSet_lt measurable_const hf.abs).nullMeasurableSet
  have ht := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top P _⟩
  rw [hinter, measure_empty] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hrho))).exists
  exact ⟨n, hn.le⟩

/-- A measurable version of the local Lipschitz majorant of the infrared characterization on the ball of
radius `m`. -/
theorem aux_calib_infrared_limit_lipschitz_majorant (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (m : ℕ) :
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∃ G : BilateralField d → ℝ, Measurable G ∧ (∀ β, 0 ≤ G β) ∧
        (∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ x y : SpatialCoordinates d,
          x ∈ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ) →
          y ∈ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ) →
          |H β x - H β y| ≤ G β * dist x y) ∧
        Integrable G (chaosSampleLaw M).toMeasure := by
  intro M H hH
  have hr : (0 : ℝ) < 2 * (m : ℝ) + 2 := by positivity
  obtain ⟨C, _, hmaj⟩ := infrared_characterization_local_lipschitz_majorant d hd
    (0 : SpatialCoordinates d) (2 * (m : ℝ) + 2) hr 1 le_rfl
  obtain ⟨G, hG0, hGlip, hGmem, -⟩ := hmaj M H hH
  have hint : Integrable G (chaosSampleLaw M).toMeasure := by
    have := hGmem.integrable (by simp)
    exact this
  have hae := hint.aestronglyMeasurable.ae_eq_mk
  have hmaxae : ∀ᵐ β ∂(chaosSampleLaw M).toMeasure,
      G β = max (hint.aestronglyMeasurable.mk G β) 0 := by
    filter_upwards [hae] with β hβ
    rw [← hβ]
    exact (max_eq_left (hG0 β)).symm
  refine ⟨fun β => max (hint.aestronglyMeasurable.mk G β) 0, ?_, fun β => le_max_right _ _, ?_, ?_⟩
  · exact hint.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const
  · filter_upwards [hGlip, hmaxae] with β hβ hβe x y hx hy
    rw [← hβe]
    refine hβ x y ?_ ?_
    · exact Metric.closedBall_subset_closedBall (by linarith) hx
    · exact Metric.closedBall_subset_closedBall (by linarith) hy
  · exact hint.congr hmaxae

/-- **Locally uniform limit of the infrared potentials along a represented sequence.**  If the point
evaluations of `H (env n ω)` on a dense sequence and the local Lipschitz majorants `G m (env n ω)` converge
almost surely, then `H (env n ω)` converges almost surely in `C(ℝ^d, ℝ)` (compact-open topology). -/
theorem calib_infrared_limit (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (env : ℕ → Ω → BilateralField d)
    (hmp : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure)
    (G : ℕ → BilateralField d → ℝ)
    (hGlip : ∀ m : ℕ, ∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ x y : SpatialCoordinates d,
      x ∈ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ) →
      y ∈ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ) →
      |H β x - H β y| ≤ G m β * dist x y)
    (hGnn : ∀ m β, 0 ≤ G m β)
    (hGconv : ∀ᵐ ω ∂P, ∀ m : ℕ, CauchySeq (fun n => G m (env n ω)))
    (hHconv : ∀ᵐ ω ∂P, ∀ j : ℕ,
      CauchySeq (fun n => H (env n ω) (TopologicalSpace.denseSeq (SpatialCoordinates d) j))) :
    ∃ hinf : Ω → C(SpatialCoordinates d, ℝ),
      ∀ᵐ ω ∂P, Tendsto (fun n => H (env n ω)) atTop (𝓝 (hinf ω)) := by
  classical
  refine ⟨fun ω => if h : ∃ f : C(SpatialCoordinates d, ℝ),
    Tendsto (fun n => H (env n ω)) atTop (𝓝 f) then h.choose else 0, ?_⟩
  have hlip : ∀ᵐ ω ∂P, ∀ n m : ℕ, ∀ x y : SpatialCoordinates d,
      x ∈ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ) →
      y ∈ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ) →
      |H (env n ω) x - H (env n ω) y| ≤ G m (env n ω) * dist x y := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    exact (hmp n).quasiMeasurePreserving.ae (hGlip m)
  filter_upwards [hlip, hGconv, hHconv] with ω hl hgc hhc
  have hex : ∃ f : C(SpatialCoordinates d, ℝ), Tendsto (fun n => H (env n ω)) atTop (𝓝 f) := by
    refine calib_tendsto_continuousMap_of_equilipschitz_dense (fun n => H (env n ω))
      (TopologicalSpace.denseSeq (SpatialCoordinates d))
      (TopologicalSpace.denseRange_denseSeq _) 0 hhc ?_
    intro m
    obtain ⟨B, hB⟩ := (hgc m).isBounded_range.exists_norm_le
    refine ⟨max B 0, le_max_right _ _, fun n x hx y hy => ?_⟩
    have h1 : G m (env n ω) ≤ max B 0 := by
      have := hB (G m (env n ω)) ⟨n, rfl⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    exact (hl n m x y hx hy).trans (mul_le_mul_of_nonneg_right h1 dist_nonneg)
  simp only [dif_pos hex]
  exact hex.choose_spec

end Paper
