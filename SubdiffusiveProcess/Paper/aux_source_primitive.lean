module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.lem_primitive_newtonian_convolution
public import SubdiffusiveProcess.Paper.lem_primitive_holder_upgrade

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_source_primitive :
  ∀ (d : ℕ), 2 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∃ g : SpatialCoordinates d → Fin d → ℝ,
          (∀ φ : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ φ →
            HasCompactSupport φ →
            (∑ i : Fin d, ∫ x, g x i * fderiv ℝ φ x (Pi.single i 1)) =
              -∫ x, (Set.indicator
                (centeredCube z r hr : Set (SpatialCoordinates d)) F x) * φ x) ∧
          halfHolderSeminorm
              (closedCube z r hr : Set (SpatialCoordinates d)) g ≤
            C * Real.sqrt r * Kf := by
  intro d hd
  obtain ⟨C_log, C_holder, C_cube, hC_log, hC_holder, hC_cube, hprimitive⟩ :=
    lem_primitive d hd
  refine ⟨C_cube, hC_cube, ?_⟩
  intro z r hr F Kf hKf hF hFbound
  let S : Set (SpatialCoordinates d) := centeredCube z r hr
  have hS_meas : MeasurableSet S :=
    (centeredCube z r hr).isOpen.measurableSet
  let Fm : SpatialCoordinates d → ℝ := hF.mk F
  let B : SpatialCoordinates d → ℝ := fun x =>
    max (-Kf) (min Kf (Fm x))
  let f : SpatialCoordinates d → ℝ := S.indicator B
  have hFm : Measurable Fm := hF.measurable_mk
  have hB : Measurable B :=
    measurable_const.max (measurable_const.min hFm)
  have hf : Measurable f := hB.indicator hS_meas
  have hf_bound : ∀ x, |f x| ≤ Kf := by
    intro x
    by_cases hx : x ∈ S
    · simp only [f, Set.indicator_of_mem hx]
      apply (abs_le).2
      constructor
      · exact le_max_left _ _
      · exact max_le (by linarith) (min_le_left _ _)
    · simp only [f, Set.indicator_of_notMem hx, abs_zero]
      exact hKf
  have hf_support : ∀ x, x ∉ (closedCube z r hr : Set (SpatialCoordinates d)) → f x = 0 := by
    intro x hx
    by_cases hxs : x ∈ S
    · exact False.elim (hx (centeredCube_subset_closedCube z hr hxs))
    · simp only [f, Set.indicator_of_notMem hxs]
  have hf_memLp : MemLp f (⊤ : ENNReal) volume := by
    refine MeasureTheory.memLp_top_of_bound hf.aestronglyMeasurable Kf ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simpa [Real.norm_eq_abs] using hf_bound x
  have hf_ae_support : ∀ᵐ x ∂volume, x ∉ (closedCube z r hr : Set (SpatialCoordinates d)) → f x = 0 :=
    Filter.Eventually.of_forall hf_support
  set g : SpatialCoordinates d → Fin d → ℝ :=
    (fun x i =>
      ((d : ℝ) * (volume {w : SpatialCoordinates d |
        Real.sqrt (∑ j : Fin d, (w j) ^ 2) < 1}).toReal)⁻¹ *
        ∫ y, (if x = y then 0 else
          (x i - y i) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ d) * f y)
  with hg_def
  have h_result := hprimitive r hr z f hf_memLp hf_ae_support
  obtain ⟨hg_identity, _, _, _, _, hg_cube⟩ := h_result
  have h_bound_norm : ∀ᵐ x ∂volume, ‖f x‖ ≤ Kf :=
    Filter.Eventually.of_forall (fun x => by
      simpa [Real.norm_eq_abs] using hf_bound x)
  have hKf_esssup : (eLpNormEssSup f volume).toReal ≤ Kf := by
    have hle : eLpNormEssSup f volume ≤ ENNReal.ofReal Kf :=
      MeasureTheory.eLpNormEssSup_le_of_ae_bound h_bound_norm
    have hfin : eLpNormEssSup f volume ≠ (⊤ : ENNReal) := by
      intro htop
      have htop' : (⊤ : ENNReal) ≤ ENNReal.ofReal Kf := by simpa [htop] using hle
      have heq : ENNReal.ofReal Kf = (⊤ : ENNReal) := le_antisymm le_top htop'
      exact ENNReal.ofReal_ne_top heq
    have := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
    simpa [ENNReal.toReal_ofReal hKf] using this
  have hg_holder : halfHolderSeminorm (closedCube z r hr : Set (SpatialCoordinates d)) g ≤
      C_cube * Real.sqrt r * Kf := by
    refine le_trans hg_cube ?_
    have h_nonneg : 0 ≤ C_cube * Real.sqrt r :=
      mul_nonneg (hC_cube.le) (Real.sqrt_nonneg r)
    nlinarith
  refine ⟨g, ?_, hg_holder⟩
  intro φ hφ hφcompact
  rw [hg_identity φ hφ hφcompact]
  congr 1
  apply integral_congr_ae
  have hFae : ∀ᵐ x ∂volume, x ∈ S → F x = Fm x :=
    (ae_restrict_iff' hS_meas).mp hF.ae_eq_mk
  have hFbound_ae : ∀ᵐ x ∂volume, x ∈ S → |F x| ≤ Kf :=
    (ae_restrict_iff' hS_meas).mp hFbound
  filter_upwards [hFae, hFbound_ae] with x hxF hxFbound
  by_cases hxs : x ∈ S
  · have hFm_bound : |Fm x| ≤ Kf := by
      simpa [hxF hxs] using hxFbound hxs
    have hlow : -Kf ≤ Fm x := (abs_le.mp hFm_bound).1
    have hupp : Fm x ≤ Kf := (abs_le.mp hFm_bound).2
    have hclip : B x = Fm x := by
      dsimp [B]
      rw [min_eq_right hupp, max_eq_right hlow]
    have hxs' : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      simpa [S] using hxs
    simp only [Set.indicator_of_mem hxs, f, hclip,
      Set.indicator_of_mem hxs', hxF hxs]
  · have hxs' : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      simpa [S] using hxs
    simp only [Set.indicator_of_notMem hxs, f,
      Set.indicator_of_notMem hxs']

end Paper
