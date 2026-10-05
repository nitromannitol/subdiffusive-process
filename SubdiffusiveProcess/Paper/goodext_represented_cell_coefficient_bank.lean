module

public import SubdiffusiveProcess.Paper.lem_extension

@[expose] public section

/-! Coarse upper coefficients on fixed triadic cells have a represented moment
bank with the original ultraviolet cutoff condition retained. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Equal-law environments carry a countable bank controlling the actual local upper coefficients. -/
theorem goodext_represented_cell_coefficient_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (X : in_extension d hd I) (Sob : SobolevFoundationalInput d hd)
    (beta eta : ℝ) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1) (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (k : ℕ) (ι : Type) [Countable ι] (z : ι → SpatialCoordinates d)
        (N : ℕ → ℕ) (Omega : Type) [MeasurableSpace Omega]
        (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (_hEnv : ∀ n, Measurable (env n))
        (_hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure),
      ∃ (bank : ι → ℕ → Omega → ℝ) (bounds : ι → ℝ≥0),
        (∀ i n, MemLp (bank i n) 1 P) ∧
        (∀ i n, eLpNorm (bank i n) 1 P ≤ bounds i) ∧
        ∀ᵐ om ∂P, ∀ i n, k ≤ N n →
          I.Lam (z i) ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)
            (cutoffPositiveCoefficient M H (env n om) (N n) (z i) (by positivity))
            (z i) ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 ≤
              bank i n om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta) := by
  classical
  obtain ⟨delta0, hdelta0, hExt⟩ :=
    (lem_extension d hd I X Sob).2 eta 1 heta le_rfl beta hb
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm H hIR hdelta k ι _ z N Omega _ P _ env hEnv hLaw
  let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  have hr : 0 < r := by positivity
  have hcell (i : ι) := hExt M Rm H hIR hdelta (z i) r hr 1 (fun _ => z i)
  choose K C hmem hnorm hbound using hcell
  let bank : ι → ℕ → Omega → ℝ := fun i n om => K i (N n) (env n om)
  let bounds : ι → ℝ≥0 := fun i => (C i).toNNReal
  have hmp (n : ℕ) : MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure :=
    ⟨hEnv n, hLaw n⟩
  refine ⟨bank, bounds, ?_, ?_, ?_⟩
  · intro i n
    simpa only [bank, ENNReal.ofReal_one] using!
      (hmem i (N n)).comp_measurePreserving (hmp n)
  · intro i n
    change eLpNorm (K i (N n) ∘ env n) 1 P ≤ (C i).toNNReal
    rw [eLpNorm_comp_measurePreserving (hmem i (N n)).aestronglyMeasurable (hmp n)]
    simpa only [ENNReal.ofReal_one, ENNReal.ofReal, Real.toNNReal_one, ENNReal.coe_one] using! hnorm i (N n)
  · apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    filter_upwards [ae_of_ae_map (hEnv n).aemeasurable
      (by rw [hLaw n]; exact hbound i)] with om hom
    intro hk
    have hz : (fun j : Fin d => z i j + (3 : ℝ) ^ (-(k : ℤ)) * ((0 : ℤ) : ℝ)) = z i := by
      funext j
      simp only [Int.cast_zero, mul_zero, add_zero]
    have hq : centeredCube (fun j : Fin d => z i j +
        (3 : ℝ) ^ (-(k : ℤ)) * ((0 : ℤ) : ℝ)) ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
        centeredCube (z i) r hr := by
      rw [hz]
    have h := hom (N n) k (0 : Fin 1) (fun _ => (0 : ℤ)) hk hq
    simp only [hz] at h
    have hinv : 0 ≤ (I.lam (z i) r hr
        (cutoffPositiveCoefficient M H (env n om) (N n) (z i) hr)
        (z i) r ((beta - 1 / 2) / 4) 2)⁻¹ :=
      inv_nonneg.mpr (I.lam_pos _ _ _ _ _ _ _ _).le
    exact (le_add_of_nonneg_right hinv).trans h

end SubdiffusiveProcess.Paper
