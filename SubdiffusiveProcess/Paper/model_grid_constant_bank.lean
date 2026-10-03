module

public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.goodext_cutoff_ellipticity_locality
public import SubdiffusiveProcess.Paper.model_triadic_cube_coercivity

@[expose] public section




open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Measurable nonnegative modification of `L^p`-bounded variables, dominating them almost
everywhere, with the same `L^p` bound. -/
theorem aux_model_grid_constant_bank_modification
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : ℝ≥0∞)
    (K : ℕ → α → ℝ) (C : ℝ)
    (hmem : ∀ N, MemLp (K N) p μ) (hbound : ∀ N, eLpNorm (K N) p μ ≤ ENNReal.ofReal C) :
    ∃ Kc : ℕ → α → ℝ, (∀ N, Measurable (Kc N)) ∧ (∀ N β, 0 ≤ Kc N β) ∧
      (∀ N, ∀ᵐ β ∂μ, K N β ≤ Kc N β) ∧
      (∀ N, MemLp (Kc N) p μ ∧ eLpNorm (Kc N) p μ ≤ ENNReal.ofReal C) := by
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

/-- **Whole-grid constant bank** (`eq:mfd-3`, one random constant per whole grid). -/
theorem model_grid_constant_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Xc : in_extension d hd E)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (eta p beta : ℝ) (heta : 0 < eta) (hp : 1 ≤ p) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (Grid : Type) [Countable Grid] (z0 : Grid → SpatialCoordinates d) (R : Grid → ℝ)
        (hR : ∀ g, 0 < R g) (origin : Grid → SpatialCoordinates d),
      ∃ (Zg : Grid → ℕ → BilateralField d → ℝ) (Cb : Grid → ℝ) (Ggrid : Set (BilateralField d)),
        (∀ g, 0 ≤ Cb g) ∧
        (∀ g N, Measurable (Zg g N)) ∧
        (∀ g N β, 0 ≤ Zg g N β) ∧
        (∀ g N, ∀ q : ℝ, 0 < q → q ≤ p →
          MemLp (Zg g N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (Zg g N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cb g)) ∧
        (∀ g, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
          (chaosSampleLaw M).toMeasure {β | Mb < Zg g N β} ≤ ENNReal.ofReal rho) ∧
        MeasurableSet Ggrid ∧ (chaosSampleLaw M).toMeasure Ggridᶜ = 0 ∧
        ∀ β ∈ Ggrid, ∀ (g : Grid) (N k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
          ∀ hc : 0 < (3 : ℝ) ^ (-(k : ℤ)),
            (centeredCube (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                ((3 : ℝ) ^ (-(k : ℤ))) hc : Set (SpatialCoordinates d)) ⊆
              (centeredCube (z0 g) (R g) (hR g) : Set (SpatialCoordinates d)) →
            E.Lam (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ))) hc
                (cutoffPositiveCoefficient M H β N
                  (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) hc)
                (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ)))
                ((beta - 1 / 2) / 4) 2 +
              (E.lam (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                  ((3 : ℝ) ^ (-(k : ℤ))) hc
                  (cutoffPositiveCoefficient M H β N
                    (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) hc)
                  (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ)))
                  ((beta - 1 / 2) / 4) 2)⁻¹ ≤
              Zg g N β * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta)
  := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨δ0, hδ0, hgrid⟩ := (lem_extension d hd E Xc Sf).2 eta p heta hp beta hbeta
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm H hH hδ Grid _ z0 R hR origin
  set μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hμ
  haveI : IsProbabilityMeasure μ := inferInstance
  have hσ : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by
    obtain ⟨h1, h2⟩ := hbeta
    exact ⟨by linarith, by linarith⟩
  choose K Cb hKmem hKbound hKae using fun g =>
    hgrid M Rm H hH hδ (z0 g) (R g) (hR g) 1 (fun _ => origin g)
  choose Zg hZmeas hZnn hZdom hZmom using fun g =>
    aux_model_grid_constant_bank_modification μ (ENNReal.ofReal p) (K g) (Cb g)
      (hKmem g) (hKbound g)
  have hCb : ∀ g, 0 ≤ max (Cb g) 0 := fun g => le_max_right _ _
  have hZmom' : ∀ g N, ∀ q : ℝ, 0 < q → q ≤ p →
      MemLp (Zg g N) (ENNReal.ofReal q) μ ∧
        eLpNorm (Zg g N) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (max (Cb g) 0) := by
    intro g N q hq0 hqp
    have hqp' : ENNReal.ofReal q ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hqp
    refine ⟨(hZmom g N).1.mono_exponent hqp', ?_⟩
    exact ((eLpNorm_le_eLpNorm_of_exponent_le hqp').trans
      (hZmom g N).2).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have htight : ∀ g, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
      μ {β | Mb < Zg g N β} ≤ ENNReal.ofReal rho := fun g =>
    aux_model_triadic_cube_coercivity_tail μ (Zg g) (hZmeas g) (max (Cb g) 0) (hCb g)
      (fun N => by
        have := (hZmom' g N 1 one_pos hp).2
        rwa [ENNReal.ofReal_one] at this)
  -- the almost-sure good event, in the cell-local form
  have hdomAll : ∀ᵐ β ∂μ, ∀ g N, K g N β ≤ Zg g N β :=
    ae_all_iff.2 fun g => ae_all_iff.2 (hZdom g)
  have hrootAll := ae_all_iff.2 hKae
  have hgood : ∀ᵐ β ∂μ, ∀ (g : Grid) (N k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
      ∀ hc : 0 < (3 : ℝ) ^ (-(k : ℤ)),
        (centeredCube (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) hc : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z0 g) (R g) (hR g) : Set (SpatialCoordinates d)) →
        E.Lam (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ))) hc
            (cutoffPositiveCoefficient M H β N
              (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) hc)
            (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ)))
            ((beta - 1 / 2) / 4) 2 +
          (E.lam (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
              ((3 : ℝ) ^ (-(k : ℤ))) hc
              (cutoffPositiveCoefficient M H β N
                (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) hc)
              (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ)))
              ((beta - 1 / 2) / 4) 2)⁻¹ ≤
          Zg g N β * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta) := by
    filter_upwards [hdomAll, hrootAll] with β hdom hroot g N k nidx hkN hc hsub
    have hroot' := hroot g N k (0 : Fin 1) nidx hkN (SetLike.coe_subset_coe.1 hsub)
    have hloc := goodext_cutoff_ellipticity_locality E M H β N (z0 g) (R g) (hR g)
      (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ))) hc hsub
      ((beta - 1 / 2) / 4) hσ
    rw [← hloc.1, ← hloc.2]
    exact hroot'.trans (mul_le_mul_of_nonneg_right (hdom g N)
      (Real.rpow_nonneg hc.le _))
  -- a measurable full-measure event inside the good set
  obtain ⟨t, hts, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  refine ⟨Zg, fun g => max (Cb g) 0, tᶜ, hCb, hZmeas, hZnn, hZmom', htight, htm.compl, ?_, ?_⟩
  · rw [compl_compl]
    exact ht0
  · intro β hβ
    by_contra hcon
    exact hβ (hts hcon)

end Paper
