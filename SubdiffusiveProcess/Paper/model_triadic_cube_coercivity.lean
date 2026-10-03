module

public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.large_cube_killed_coercivity

@[expose] public section




open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- A family of `L¹`-bounded random variables has a measurable nonnegative modification that
dominates it almost everywhere, with the same `L¹` bound. -/
theorem aux_model_triadic_cube_coercivity_modification
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (K : ℕ → α → ℝ) (C : ℝ)
    (hmem : ∀ N, MemLp (K N) 1 μ) (hbound : ∀ N, eLpNorm (K N) 1 μ ≤ ENNReal.ofReal C) :
    ∃ Kc : ℕ → α → ℝ, (∀ N, Measurable (Kc N)) ∧ (∀ N β, 0 ≤ Kc N β) ∧
      (∀ N, ∀ᵐ β ∂μ, K N β ≤ Kc N β) ∧
      (∀ N, MemLp (Kc N) 1 μ ∧ eLpNorm (Kc N) 1 μ ≤ ENNReal.ofReal C) := by
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

/-- Markov's inequality: uniform `L¹` bounds give uniform tightness of the laws. -/
theorem aux_model_triadic_cube_coercivity_tail
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (Y : ℕ → α → ℝ) (hY : ∀ N, Measurable (Y N)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N, eLpNorm (Y N) 1 μ ≤ ENNReal.ofReal C) :
    ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N, μ {β | Mb < Y N β} ≤ ENNReal.ofReal rho := by
  intro rho hrho
  set R : ℝ := C / rho + 1 with hR
  have hRpos : 0 < R := by positivity
  refine ⟨R, fun N => ?_⟩
  have hsub : {β | R < Y N β} ⊆ {β | ENNReal.ofReal R ≤ ‖Y N β‖ₑ} := by
    intro β hβ
    simp only [Set.mem_setOf_eq] at hβ ⊢
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (hβ.le.trans (le_abs_self _))
  have hmarkov : ENNReal.ofReal R * μ {β | ENNReal.ofReal R ≤ ‖Y N β‖ₑ} ≤
      ∫⁻ β, ‖Y N β‖ₑ ∂μ :=
    mul_meas_ge_le_lintegral₀ (hY N).enorm.aemeasurable _
  have hCR : C ≤ rho * R := by
    have : C / rho < R := by rw [hR]; linarith
    rw [div_lt_iff₀ hrho] at this
    linarith
  have hle : ENNReal.ofReal R * μ {β | ENNReal.ofReal R ≤ ‖Y N β‖ₑ} ≤
      ENNReal.ofReal R * ENNReal.ofReal rho := by
    calc ENNReal.ofReal R * μ {β | ENNReal.ofReal R ≤ ‖Y N β‖ₑ}
        ≤ ∫⁻ β, ‖Y N β‖ₑ ∂μ := hmarkov
      _ = eLpNorm (Y N) 1 μ := (eLpNorm_one_eq_lintegral_enorm (hY N).aestronglyMeasurable).symm
      _ ≤ ENNReal.ofReal C := hbound N
      _ ≤ ENNReal.ofReal (R * rho) := ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = ENNReal.ofReal R * ENNReal.ofReal rho := ENNReal.ofReal_mul hRpos.le
  have hcancel := (ENNReal.mul_le_mul_iff_right (a := ENNReal.ofReal R)
    (by simpa using hRpos) ENNReal.ofReal_ne_top).1 hle
  exact (measure_mono hsub).trans hcancel

/-- Raw pathwise coercivity constants on one cube of radius `≤ 1` or `3 ^ k` (`k > 0`), with the
disorder threshold fixed before the model and the cube: `lem_coercivity` for `r ≤ 1` (first moment,
`p = 1`), `large_cube_killed_coercivity` for `r = 3 ^ k`. -/
theorem aux_model_triadic_cube_coercivity_raw
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
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
        (∀ N, MemLp (K N) 1 (chaosSampleLaw M).toMeasure ∧
          eLpNorm (K N) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb) := by
  obtain ⟨δL, hδL, hlarge⟩ := large_cube_killed_coercivity d hd E Pc Sf
  obtain ⟨δF, hδF, hsmall⟩ := aux_lem_coercivity_compat d hd E Pc Sf
  refine ⟨min δL (δF 1), lt_min hδL (hδF 1 le_rfl), ?_⟩
  intro M Rm H hH hδ z r hr hrad
  rcases hrad with hsm | ⟨k, hk, rfl⟩
  · obtain ⟨K, hK, hmom⟩ := hsmall M Rm H hH z r hr hsm
    obtain ⟨Cb, hmem, hbound⟩ := hmom 1 le_rfl (hδ.trans (min_le_right _ _))
    refine ⟨K, max Cb 0, le_max_right _ _, fun N β v => (hK N β).1 v, fun N => ?_⟩
    rw [ENNReal.ofReal_one] at hmem hbound
    exact ⟨hmem N, (hbound N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  · obtain ⟨Kc, Cb, hCb, -, hcoer, hmom⟩ :=
      hlarge M Rm H hH (hδ.trans (min_le_left _ _)) k hk hr z
    exact ⟨Kc, Cb, hCb, fun N β v => ⟨(hcoer N β v).1, (hcoer N β v).2.1⟩, hmom⟩

/-- **Actual measurable coercivity constants on every triadic cube.**  For one disorder threshold
`δ0`, chosen before the model and the cubes, and every cube family with radii `≤ 1` or `3 ^ k`
(`k > 0`): measurable, nonnegative constants `Kc i N`, almost-sure killed fractional coercivity,
a uniform-in-`N` `L¹` bound per cube, and uniform tightness in `N`. -/
theorem model_triadic_cube_coercivity
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
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
                  (Lane4.cutoffPositiveCoefficient M H β N (z i) (hr i))
                  (v : SobolevData (centeredCube (z i) (r i) (hr i)))
                  (v : SobolevData (centeredCube (z i) (r i) (hr i)))) ∧
        (∀ i N, MemLp (Kc i N) 1 (chaosSampleLaw M).toMeasure ∧
          eLpNorm (Kc i N) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb i)) ∧
        (∀ i, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
          (chaosSampleLaw M).toMeasure {β | Mb < Kc i N β} ≤ ENNReal.ofReal rho) := by
  obtain ⟨δ0, hδ0, hraw⟩ := aux_model_triadic_cube_coercivity_raw d hd E Pc Sf
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
      (∀ N, MemLp (K N) 1 (chaosSampleLaw M).toMeasure ∧
        eLpNorm (K N) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb) :=
    fun i => hraw M Rm H hH hδ (z i) (r i) (hr i) (hrad i)
  choose K Cb hCb hcoerK hmomK using hK
  have hmod := fun i => aux_model_triadic_cube_coercivity_modification
    (chaosSampleLaw M).toMeasure (K i) (Cb i) (fun N => (hmomK i N).1)
    (fun N => (hmomK i N).2)
  choose Kc hKcmeas hKcnonneg hKcae hKcmom using hmod
  refine ⟨Kc, Cb, hCb, hKcmeas, hKcnonneg, ?_, hKcmom, ?_⟩
  · intro i N
    filter_upwards [hKcae i N] with β hβ v
    obtain ⟨h1, h2⟩ := hcoerK i N β v
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hβ (sobolevCoefficientForm_nonneg _ _))⟩
  · intro i rho hrho
    exact aux_model_triadic_cube_coercivity_tail (chaosSampleLaw M).toMeasure (Kc i)
      (hKcmeas i) (Cb i) (hCb i) (fun N => (hKcmom i N).2) rho hrho

end Paper
