module

public import SubdiffusiveProcess.Paper.Support.UniformResolventLargeCoercivity

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_mfd_prop_uniform_resolvent_coercivity_modification
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (K : ℕ → α → ℝ) (C : ℝ) (q : ℝ≥0∞)
    (hmem : ∀ N, MemLp (K N) q μ) (hbound : ∀ N, eLpNorm (K N) q μ ≤ ENNReal.ofReal C) :
    ∃ Kc : ℕ → α → ℝ, (∀ N, Measurable (Kc N)) ∧ (∀ N β, 0 ≤ Kc N β) ∧
      (∀ N, ∀ᵐ β ∂μ, K N β ≤ Kc N β) ∧
      (∀ N, MemLp (Kc N) q μ ∧ eLpNorm (Kc N) q μ ≤ ENNReal.ofReal C) := by
  classical
  let Km : ℕ → α → ℝ := fun N => (hmem N).aestronglyMeasurable.mk (K N)
  have hKm : ∀ N, StronglyMeasurable (Km N) := fun N =>
    (hmem N).aestronglyMeasurable.stronglyMeasurable_mk
  have hKae : ∀ N, K N =ᵐ[μ] Km N := fun N => (hmem N).aestronglyMeasurable.ae_eq_mk
  let Kc : ℕ → α → ℝ := fun N β => max (Km N β) 0
  have hKcm : ∀ N, Measurable (Kc N) := fun N => (hKm N).measurable.max measurable_const
  have hdom : ∀ N, ∀ᵐ β ∂μ, ‖Kc N β‖ ≤ ‖K N β‖ := by
    intro N
    filter_upwards [hKae N] with β hβ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hβ]
    simp only [Kc]
    rcases le_total (Km N β) 0 with h | h
    · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left h]
  refine ⟨Kc, hKcm, fun N β => le_max_right _ _, ?_, ?_⟩
  · intro N
    filter_upwards [hKae N] with β hβ
    rw [hβ]
    exact le_max_left _ _
  · intro N
    refine ⟨(hmem N).of_le (hKcm N).aestronglyMeasurable (hdom N), ?_⟩
    exact (eLpNorm_mono_ae (hKcm N).aestronglyMeasurable (hdom N)).trans (hbound N)

theorem aux_mfd_prop_uniform_resolvent_coercivity_raw
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (r ≤ 1 ∨ ∃ k : ℕ, 0 < k ∧ r = (3 : ℝ) ^ k) →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cb : ℝ), 0 ≤ Cb ∧
        (∀ N β, ∀ v : killedSobolevGraph (centeredCube z r hr),
          cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
              (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) < ⊤ ∧
          cubeFractionalSqNorm hd z r hr threeQuarterOrder
              (v : SobolevData (centeredCube z r hr)).1 ≤
            K N β * sobolevCoefficientForm (cutoffPositiveCoefficient M H β N z hr)
              (v : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr))) ∧
        (∀ N, MemLp (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb) := by
  obtain ⟨δL, hδL, hlarge⟩ := aux_mfd_prop_uniform_resolvent_large_coercivity_moments d hd E Pc Sf q hq
  obtain ⟨δF, hδF, hsmall⟩ := aux_lem_coercivity_compat d hd E Pc Sf
  refine ⟨min δL (δF q), lt_min hδL (hδF q hq), ?_⟩
  intro M Rm H hH hδ z r hr hrad
  rcases hrad with hsm | ⟨k, hk, rfl⟩
  · obtain ⟨K, hK, hmom⟩ := hsmall M Rm H hH z r hr hsm
    obtain ⟨Cb, hmem, hbound⟩ := hmom q hq (hδ.trans (min_le_right _ _))
    refine ⟨K, max Cb 0, le_max_right _ _, fun N β v => (hK N β).1 v, fun N => ?_⟩
    exact ⟨hmem N, (hbound N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  · obtain ⟨Kc, Cb, hCb, -, hcoer, hmom⟩ :=
      hlarge M Rm H hH (hδ.trans (min_le_left _ _)) k hk hr z
    exact ⟨Kc, Cb, hCb, fun N β v => ⟨(hcoer N β v).1, (hcoer N β v).2.1⟩, hmom⟩

theorem aux_mfd_prop_uniform_resolvent_coercivity_moments
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
      ∀ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i),
        (∀ i, r i ≤ 1 ∨ ∃ k : ℕ, 0 < k ∧ r i = (3 : ℝ) ^ k) →
      ∃ (Kc : ℕ → ℕ → BilateralField d → ℝ) (Cb : ℕ → ℝ),
        (∀ i, 0 ≤ Cb i) ∧
        (∀ i N, Measurable (Kc i N)) ∧
        (∀ i N β, 0 ≤ Kc i N β) ∧
        (∀ i N, ∀ᵐ β ∂(chaosSampleLaw M).toMeasure,
          ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
            cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
                (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
            cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
                (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
              Kc i N β *
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N (z i) (hr i))
                  (v : SobolevData (centeredCube (z i) (r i) (hr i)))
                  (v : SobolevData (centeredCube (z i) (r i) (hr i)))) ∧
        (∀ i N, MemLp (Kc i N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (Kc i N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb i)) := by
  obtain ⟨δ0, hδ0, hraw⟩ := aux_mfd_prop_uniform_resolvent_coercivity_raw d hd E Pc Sf q hq
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm H hH hδ z r hr hrad
  have hK : ∀ i, ∃ (K : ℕ → BilateralField d → ℝ) (Cb : ℝ), 0 ≤ Cb ∧
      (∀ N β, ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
        cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
        cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
            (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
          K N β * sobolevCoefficientForm
            (cutoffPositiveCoefficient M H β N (z i) (hr i))
            (v : SobolevData (centeredCube (z i) (r i) (hr i)))
            (v : SobolevData (centeredCube (z i) (r i) (hr i)))) ∧
      (∀ N, MemLp (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb) :=
    fun i => hraw M Rm H hH hδ (z i) (r i) (hr i) (hrad i)
  choose K Cb hCb hcoerK hmomK using hK
  have hmod := fun i => aux_mfd_prop_uniform_resolvent_coercivity_modification
    (chaosSampleLaw M).toMeasure (K i) (Cb i) (ENNReal.ofReal q) (fun N => (hmomK i N).1)
    (fun N => (hmomK i N).2)
  choose Kc hKcmeas hKcnonneg hKcae hKcmom using hmod
  refine ⟨Kc, Cb, hCb, hKcmeas, hKcnonneg, ?_, hKcmom⟩
  intro i N
  filter_upwards [hKcae i N] with β hβ v
  obtain ⟨h1, h2⟩ := hcoerK i N β v
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hβ (sobolevCoefficientForm_nonneg _ _))⟩

end SubdiffusiveProcess.Paper
