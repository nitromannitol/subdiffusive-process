module

public import SubdiffusiveProcess.Processes.E7.LocalWeakEquation

@[expose] public section

/-!
# Comparison of the weighted measures on bounded sets
-/
open MeasureTheory Filter Set Topology Homogenization
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

/-- `L²(vol|W)` is dominated by `L²(w dx)` for a positive continuous weight on a bounded set. -/
theorem eLpNorm_restrict_le_wm {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {W : Set (St d)} (hW : MeasurableSet W) (hWb : Bornology.IsBounded W) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : St d → ℝ,
      eLpNorm f 2 (volume.restrict W) ≤ C * eLpNorm f 2 (wm w) := by
  obtain ⟨C0, hC0, hle⟩ := restrict_le_smul_wm hw hpos hW hWb
  refine ⟨C0 ^ (1 / (2 : ℝ)), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC0, fun f => ?_⟩
  calc eLpNorm f 2 (volume.restrict W) ≤ eLpNorm f 2 (C0 • wm w) := eLpNorm_mono_measure _ hle
    _ = C0 ^ (1 / (2 : ℝ)) * eLpNorm f 2 (wm w) := by
        rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
        simp

/-- Two positive continuous weights are comparable in `L²` on functions supported in a bounded
measurable set. -/
theorem eLpNorm_wm_le_wm {w₁ w₂ : St d → ℝ} (h₁ : Continuous w₁) (h₂ : Continuous w₂)
    (hpos₂ : ∀ x, 0 < w₂ x) {W : Set (St d)} (hW : MeasurableSet W)
    (hWb : Bornology.IsBounded W) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : St d → ℝ, (∀ x, x ∉ W → f x = 0) →
      eLpNorm f 2 (wm w₁) ≤ C * eLpNorm f 2 (wm w₂) := by
  obtain ⟨C1, hC1, hle1⟩ := eLpNorm_wm_le h₁ hW hWb
  obtain ⟨C2, hC2, hle2⟩ := eLpNorm_restrict_le_wm h₂ hpos₂ hW hWb
  refine ⟨C1 * C2, ENNReal.mul_ne_top hC1 hC2, fun f hf => ?_⟩
  calc eLpNorm f 2 (wm w₁) ≤ C1 * eLpNorm f 2 (volume.restrict W) := hle1 f hf
    _ ≤ C1 * (C2 * eLpNorm f 2 (wm w₂)) := by gcongr; exact hle2 f
    _ = C1 * C2 * eLpNorm f 2 (wm w₂) := by ring

/-- Classes of `L²(w dx)` are locally integrable. -/
theorem locallyIntegrable_wm {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (g : Lp ℝ 2 (wm w)) : LocallyIntegrable (fun x => (g : St d → ℝ) x) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hmem : MemLp (fun x => (g : St d → ℝ) x) 2 (volume.restrict K) :=
    memLp_restrict_of_wm hw hpos hK.measurableSet hK.isBounded (by simpa using Lp.memLp g)
  haveI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact hmem.integrable (by norm_num)

/-- The weak gradient of a domain element vanishes almost everywhere on an open set where the
element itself vanishes. -/
theorem gradOf_ae_zero_of_ae_zero {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {z : Lp ℝ 2 (wm ρ)}
    (hz : z ∈ gradDomain hc hρ) {O : Set (St d)} (hO : IsOpen O)
    (hz0 : ∀ᵐ x ∂(volume : Measure (St d)), x ∈ O → z x = 0) (i : Fin d) :
    ∀ᵐ x ∂(volume : Measure (St d)), x ∈ O → (gradOf hc hρ z i) x = 0 := by
  obtain ⟨g, hg⟩ := (mem_gradDomain_iff hc hρ z).1 hz
  have hgo : gradOf hc hρ z = g := gradOf_spec hc hρ hcpos hρpos hg
  rw [hgo]
  refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((locallyIntegrable_wm hc hcpos (g i)).locallyIntegrableOn _) ?_
  intro ψ hψ hψc hψO
  have hp := gradGraph_pairing hc hρ hcpos hρpos (ψ := ψ) ⟨hψ, hψc⟩ i (z, g) hg
  dsimp only at hp
  have h1 : ∫ x, dpartial i ψ x * z x = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hz0] with x hx
    simp only [Pi.zero_apply]
    by_cases hxO : x ∈ O
    · rw [hx hxO, mul_zero]
    · have : fderiv ℝ ψ x = 0 :=
        Function.notMem_support.mp fun hs => hxO (hψO (support_fderiv_subset ℝ hs))
      simp [dpartial, this]
  rw [h1, zero_add] at hp
  simpa [smul_eq_mul] using hp

/-- `ρ dx` charges every nonempty open set. -/
theorem isOpenPosMeasure_wm {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x) :
    (wm w).IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  exact hU.measure_ne_zero volume hne ((wm_null_iff hw hpos U).1 h0)

end SubdiffusiveProcess.E7
