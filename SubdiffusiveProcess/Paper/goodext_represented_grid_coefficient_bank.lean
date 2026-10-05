module

public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.Paper.goodext_cutoff_ellipticity_locality

@[expose] public section

/-! This theorem transfers the one-root extension moment estimate to represented environments
and finite shifted grids. It establishes one scalar bank uniform over levels and grid centers; it
does not give estimates after the cutoff guard fails. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- One represented moment bank controls all shifted-grid local upper and inverse lower coefficients below each cutoff. -/
theorem goodext_represented_grid_coefficient_bank
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (X : in_extension d hd I) (Sob : SobolevFoundationalInput d hd)
    (beta eta : ℝ) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1) (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (J : ℕ) (origins : Fin J → SpatialCoordinates d) (N : ℕ → ℕ)
        (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (_hEnv : ∀ n, Measurable (env n))
        (_hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure),
      ∃ (bank : ℕ → Omega → ℝ) (bound : ℝ≥0),
        (∀ n, MemLp (bank n) 1 P) ∧
        (∀ n, eLpNorm (bank n) 1 P ≤ bound) ∧
        ∀ᵐ om ∂P, ∀ (n k : ℕ) (j : Fin J) (idx : Fin d → ℤ), k ≤ N n →
          let wc : SpatialCoordinates d := fun i => origins j i + (3 : ℝ) ^ (-(k : ℤ)) * idx i
          let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
          ∀ hc : 0 < rc,
          (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
            (centeredCube z r hr : Set (SpatialCoordinates d)) →
          I.Lam wc rc hc (cutoffPositiveCoefficient M H (env n om) (N n) wc hc)
            wc rc ((beta - 1 / 2) / 4) 2 +
            (I.lam wc rc hc (cutoffPositiveCoefficient M H (env n om) (N n) wc hc)
              wc rc ((beta - 1 / 2) / 4) 2)⁻¹ ≤ bank n om * rc ^ (-eta) := by
  classical
  obtain ⟨delta0, hdelta0, hExt⟩ :=
    (lem_extension d hd I X Sob).2 eta 1 heta le_rfl beta hb
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm H hIR hdelta z r hr J origins N Omega _ P _ env hEnv hLaw
  obtain ⟨K, C, hmem, hnorm, hbound⟩ := hExt M Rm H hIR hdelta z r hr J origins
  simp only [ENNReal.ofReal_one] at hmem hnorm
  let bank : ℕ → Omega → ℝ := fun n om => K (N n) (env n om)
  let bound : ℝ≥0 := C.toNNReal
  have hmp (n : ℕ) : MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure :=
    ⟨hEnv n, hLaw n⟩
  have hsigma : (beta - 1 / 2) / 4 ∈ Ioc (0 : ℝ) 1 :=
    aux_lem_extension_cell_moment_order hb
  refine ⟨bank, bound, ?_, ?_, ?_⟩
  · intro n
    exact (hmem (N n)).comp_measurePreserving (hmp n)
  · intro n
    change eLpNorm (K (N n) ∘ env n) 1 P ≤ C.toNNReal
    rw [eLpNorm_comp_measurePreserving (hmem (N n)).aestronglyMeasurable (hmp n)]
    exact hnorm (N n)
  · apply ae_all_iff.mpr
    intro n
    filter_upwards [ae_of_ae_map (hEnv n).aemeasurable
      (by rw [hLaw n]; exact hbound)] with om hom
    intro k j idx hk
    dsimp only
    intro hc hsub
    let wc : SpatialCoordinates d := fun i => origins j i + (3 : ℝ) ^ (-(k : ℤ)) * idx i
    let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
    have hparent : centeredCube wc rc hc ≤ centeredCube z r hr := by
      change (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d))
      exact hsub
    have hambient := hom (N n) k j idx hk hparent
    have hlocal := goodext_cutoff_ellipticity_locality I M H (env n om) (N n)
      z r hr wc rc hc hsub ((beta - 1 / 2) / 4) hsigma
    rw [hlocal.1, hlocal.2] at hambient
    simpa only [bank] using hambient

end SubdiffusiveProcess.Paper
