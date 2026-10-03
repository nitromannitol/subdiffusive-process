module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib_coordinates_stage3
public import SubdiffusiveProcess.Paper.calib_coordinates_cells
public import SubdiffusiveProcess.Paper.calib_response_tight
public import SubdiffusiveProcess.Paper.calib_infrared_limit
public import SubdiffusiveProcess.Paper.calibResp_integrable
public import SubdiffusiveProcess.Paper.conv_represented_calibration_package

@[expose] public section

/-! The extra real coordinates of the calibration extraction and the decoding of their almost-sure convergence: the
calibration responses `Λ^0_{N,Q_{3^{K0+k}}}`, the point values and Lipschitz majorants of the infrared potential, and the Stage-3
cell constants.  Their almost-sure convergence along a represented sequence gives `conv_represented_calibration_package`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
namespace Paper
noncomputable section

/-- Almost-sure existence of a limit gives a limit function. -/
theorem aux_calib_coordinates_lim {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (h : ∀ᵐ omega ∂P, ∃ Z : ℝ, Tendsto (fun n => f n omega) atTop (𝓝 Z)) :
    ∃ L : Ω → ℝ, ∀ᵐ omega ∂P, Tendsto (fun n => f n omega) atTop (𝓝 (L omega)) := by
  classical
  refine ⟨fun omega => if hh : ∃ Z : ℝ, Tendsto (fun n => f n omega) atTop (𝓝 Z) then hh.choose else 0, ?_⟩
  filter_upwards [h] with omega hω
  simp only [dif_pos hω]
  exact hω.choose_spec

/-- **The calibration coordinates.** -/
theorem calib_coordinates (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : Paper.in_J d) (Pc : Paper.in_poincare d hd Jc) (Xc : Paper.in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : Paper.in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H), M.delta ≤ δ0 →
      ∃ (Y : Type) (_ : Countable Y) (Zx : Y → ℕ → BilateralField d → ℝ),
        (∀ y N, Measurable (Zx y N)) ∧
        (∀ y, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
          (chaosSampleLaw M).toMeasure {β | Mb < |Zx y N β|} ≤ ENNReal.ofReal rho) ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (env : ℕ → Ω → BilateralField d),
          (∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure) → ∀ (NE NF : ℕ → ℕ),
          (∀ᵐ omega ∂P, ∀ y, ∃ ZE ZF : ℝ,
            Tendsto (fun n => Zx y (NE n) (env n omega)) atTop (𝓝 ZE) ∧
            Tendsto (fun n => Zx y (NF n) (env n omega)) atTop (𝓝 ZF)) →
          conv_represented_calibration_package d hd M H Ω P env NE NF t alpha := by
  obtain ⟨δ1, hδ1, hT⟩ := calib_response_tight d hd Jc
  obtain ⟨δ2, hδ2, hS⟩ := calib_coordinates_stage3 d hd Jc Pc Xc W Cp Sf t alpha ht htd ha0 ha1
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro M Rm H hH hδ
  obtain ⟨K00, hK00⟩ := hT M (hδ.trans (min_le_left _ _))
  obtain ⟨Kc, hKm, hKt, hKae⟩ := hS M Rm (hδ.trans (min_le_right _ _)) (K00 + 1) (by omega)
  choose G hGm hGnn hGlip hGint using fun m => aux_calib_infrared_limit_lipschitz_majorant d hd m M H hH
  have hd0 : 0 ≤ t := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨ℕ ⊕ ℕ ⊕ ℕ ⊕ (ℕ × OddGridIndex d (triadicHalf 1)), inferInstance,
    Sum.elim (fun k N β => calibResp d hd M (K00 + 1 + k) N β)
      (Sum.elim (fun j _ β => H β (denseSeq (SpatialCoordinates d) j))
        (Sum.elim (fun m _ β => G m β) (fun p N β => Kc p N β))), ?_, ?_, ?_⟩
  · rintro (k | j | m | p) N
    · exact aux_calibResp_integrable_measurable d hd M (K00 + 1 + k) N
    · exact (continuous_eval_const (denseSeq (SpatialCoordinates d) j)).measurable.comp hH.1
    · exact hGm m
    · exact hKm p N
  · rintro (k | j | m | p) rho hrho
    · obtain ⟨Mb, hMb⟩ := hK00 (k + 1) rho hrho
      exact ⟨Mb, fun N => by
        have := hMb N
        simpa [show K00 + (k + 1) = K00 + 1 + k by omega] using this⟩
    · obtain ⟨Mb, hMb⟩ := aux_calib_infrared_limit_tight (chaosSampleLaw M).toMeasure
        (fun β => H β (denseSeq (SpatialCoordinates d) j))
        ((continuous_eval_const (denseSeq (SpatialCoordinates d) j)).measurable.comp hH.1) rho hrho
      exact ⟨Mb, fun N => hMb⟩
    · obtain ⟨Mb, hMb⟩ := aux_calib_infrared_limit_tight (chaosSampleLaw M).toMeasure (G m) (hGm m) rho hrho
      exact ⟨Mb, fun N => hMb⟩
    · exact hKt p rho hrho
  · intro Ω _ P _ env hmp NE NF hconv
    have hcE : ∀ k, ∀ᵐ omega ∂P, ∃ Z : ℝ,
        Tendsto (fun n => calibResp d hd M (K00 + 1 + k) (NE n) (env n omega)) atTop (𝓝 Z) := by
      intro k
      filter_upwards [hconv] with omega hω
      obtain ⟨ZE, ZF, hE, hF⟩ := hω (Sum.inl k)
      exact ⟨ZE, hE⟩
    have hcF : ∀ k, ∀ᵐ omega ∂P, ∃ Z : ℝ,
        Tendsto (fun n => calibResp d hd M (K00 + 1 + k) (NF n) (env n omega)) atTop (𝓝 Z) := by
      intro k
      filter_upwards [hconv] with omega hω
      obtain ⟨ZE, ZF, hE, hF⟩ := hω (Sum.inl k)
      exact ⟨ZF, hF⟩
    choose LE hLE using fun k => aux_calib_coordinates_lim P
      (fun n omega => calibResp d hd M (K00 + 1 + k) (NE n) (env n omega)) (hcE k)
    choose LF hLF using fun k => aux_calib_coordinates_lim P
      (fun n omega => calibResp d hd M (K00 + 1 + k) (NF n) (env n omega)) (hcF k)
    obtain ⟨hinf, hhinf⟩ := calib_infrared_limit d M H P env hmp G hGlip hGnn
      (by
        filter_upwards [hconv] with omega hω m
        obtain ⟨ZE, ZF, hE, hF⟩ := hω (Sum.inr (Sum.inr (Sum.inl m)))
        exact hE.cauchySeq)
      (by
        filter_upwards [hconv] with omega hω j
        obtain ⟨ZE, ZF, hE, hF⟩ := hω (Sum.inr (Sum.inl j))
        exact hE.cauchySeq)
    have hKE : ∀ᵐ omega ∂P, ∀ p : ℕ × OddGridIndex d (triadicHalf 1), ∃ Z : ℝ,
        Tendsto (fun n => Kc p (NE n) (env n omega)) atTop (𝓝 Z) := by
      filter_upwards [hconv] with omega hω p
      obtain ⟨ZE, ZF, hE, hF⟩ := hω (Sum.inr (Sum.inr (Sum.inr p)))
      exact ⟨ZE, hE⟩
    have hKF : ∀ᵐ omega ∂P, ∀ p : ℕ × OddGridIndex d (triadicHalf 1), ∃ Z : ℝ,
        Tendsto (fun n => Kc p (NF n) (env n omega)) atTop (𝓝 Z) := by
      filter_upwards [hconv] with omega hω p
      obtain ⟨ZE, ZF, hE, hF⟩ := hω (Sum.inr (Sum.inr (Sum.inr p)))
      exact ⟨ZF, hF⟩
    exact ⟨K00 + 1, LE, LF, hinf, hLE, hLF, hhinf,
      calib_coordinates_cells hd M (K00 + 1) t alpha hd0 ha0 Kc hKae P env hmp NE hKE,
      calib_coordinates_cells hd M (K00 + 1) t alpha hd0 ha0 Kc hKae P env hmp NF hKF⟩

end
end Paper
