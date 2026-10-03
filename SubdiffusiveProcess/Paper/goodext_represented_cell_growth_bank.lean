module

public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.prop_conc_form_cutoff_continuity
public import SubdiffusiveProcess.Sobolev.HarmonicSmoothGrowth

@[expose] public section

/-! The smooth-data cell-growth bank is transferred through equal-law environments.
The output retains its moments for a later joint subsequence extraction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- Actual zero-load growth on a countable cube catalogue has a represented moment bank. -/
theorem goodext_represented_cell_growth_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (ι : Type) [Countable ι] (z : ι → SpatialCoordinates d) (r : ι → ℝ)
        (hr : ∀ i, 0 < r i) (N : ℕ → ℕ)
        (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (hEnv : ∀ n, Measurable (env n))
        (hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure),
      ∃ (bank : ι → ℕ → Omega → ℝ) (bounds : ι → ℝ≥0),
        (∀ i n, MemLp (bank i n) 1 P) ∧
        (∀ i n, eLpNorm (bank i n) 1 P ≤ bounds i) ∧
        ∀ᵐ om ∂P, ∀ i n (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi → c2Norm (closedCube (z i) (r i) (hr i)) phi ≤ Cphi →
          ∀ b u : weakSobolevGraph (centeredCube (z i) (r i) (hr i)),
            ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] phi) →
            SolvesDirichlet (cutoffPositiveCoefficient M H (env n om) (N n) (z i) (hr i))
              (fun _ => 0) b u →
            ∃ V : SpatialCoordinates d → ℝ, Continuous V ∧
              ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] V) ∧
              IsHolderOn alpha (closure
                (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) V ∧
              cAlphaNorm alpha (closure
                (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) V ≤ bank i n om * Cphi := by
  classical
  obtain ⟨deltaSmall, hdeltaSmall, hsmall⟩ :=
    prop_growth d hd I Pin X W Cp Sob t alpha 1 (fun _ => 1)
      ht htd ha ha1 (fun _ => le_rfl)
  obtain ⟨deltaLarge, hdeltaLarge, hlarge⟩ :=
    prop_growth_large_root d hd I Pin X W Cp Sob t alpha 1 (fun _ => 1)
      ht htd ha ha1 (fun _ => le_rfl)
  refine ⟨min deltaSmall deltaLarge, lt_min hdeltaSmall hdeltaLarge, ?_⟩
  intro M Rm Sreg It H hIR hdelta ι _ z r hr N Omega _ P _ env hEnv hLaw
  have hcell (i : ι) := if hside : r i ≤ 1 then
      hsmall M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) (z i) (r i) (hr i) hside
    else hlarge M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _)) (z i) (r i) (hr i)
      (lt_of_not_ge hside)
  choose K C hmem hnorm _hge hgrowth using hcell
  let bank : ι → ℕ → Omega → ℝ := fun i n om => K i (N n) (env n om)
  let bounds : ι → ℝ≥0 := fun i => (C i 0).toNNReal
  have hmp (n : ℕ) : MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure :=
    ⟨hEnv n, hLaw n⟩
  refine ⟨bank, bounds, ?_, ?_, ?_⟩
  · intro i n
    simpa only [bank, ENNReal.ofReal_one] using!
      (hmem i 0 (N n)).comp_measurePreserving (hmp n)
  · intro i n
    change eLpNorm (K i (N n) ∘ env n) 1 P ≤ (C i 0).toNNReal
    rw [eLpNorm_comp_measurePreserving
      (hmem i 0 (N n)).aestronglyMeasurable (hmp n)]
    simpa only [ENNReal.ofReal_one, ENNReal.coe_toNNReal] using! hnorm i 0 (N n)
  · apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    filter_upwards [ae_of_ae_map (hEnv n).aemeasurable
      (by rw [hLaw n]; exact hgrowth i)] with om hom
    intro phi Cphi hphi hCphi b u hb hu
    obtain ⟨_, V, hVc, hVae, hVh, hVn⟩ := hom (N n) (fun _ => 0) 0 le_rfl
      aemeasurable_const (Filter.Eventually.of_forall fun _ => by norm_num)
      phi Cphi hphi hCphi b u hb hu
    refine ⟨V, hVc, hVae, ?_, ?_⟩
    · rw [aux_prop_conc_form_cutoff_continuity_closure_cube]
      exact hVh
    · rw [aux_prop_conc_form_cutoff_continuity_closure_cube]
      simpa only [bank, zero_add] using hVn

end Paper
