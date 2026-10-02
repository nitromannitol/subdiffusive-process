import SubdiffusiveProcess.Paper.prop_conc_countable_native_growth_with_moment
import SubdiffusiveProcess.Paper.lem_cutoffs
import SubdiffusiveProcess.Sobolev.NativeHarmonicMinimum
import SubdiffusiveProcess.Sobolev.NativeEnergyMeasureGrowth

/-! Actual native harmonic cell bounds along a common further subsequence.
The cell constants may depend on the cell; the distinguished bank keeps its uniform moment bound. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- All native harmonic functions with smooth cell data satisfy common energy, measure-growth and Holder bounds. -/
theorem prop_conc_native_cell_bounds_with_moment
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (ι : Type) [Countable ι] (z : ι → SpatialCoordinates d) (r : ι → ℝ)
        (hr : ∀ i, 0 < r i),
      ∀ (Bbank : ℕ → BilateralField d → ℝ) (Cbank : ℝ≥0),
        (∀ n, MemLp (Bbank n) 1 (chaosSampleLaw M).toMeasure) →
        (∀ n, eLpNorm (Bbank n) 1 (chaosSampleLaw M).toMeasure ≤ Cbank) →
      ∀ (Qbank : ℕ → BilateralField d → ℝ) (p : ℝ), 1 ≤ p →
      ∀ Qbound : ℝ≥0,
        (∀ n, MemLp (Qbank n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) →
        (∀ n, eLpNorm (Qbank n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ Qbound) →
      ∀ N : ℕ → ℕ,
      ∃ Kbank : BilateralField d → ℝ, Measurable Kbank ∧ (∀ om, 0 ≤ Kbank om) ∧
        eLpNorm Kbank (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (2 * ((Qbound : ℝ) + 1)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        (∀ n, |Qbank (N (seq n)) om| ≤ Kbank om) ∧
        (∃ B : ℝ, 0 ≤ B ∧ ∀ n, |Bbank (N (seq n)) om| ≤ B) ∧
      ∀ i : ι, r i ≤ 1 →
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
      ∀ beta : H1Function (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
        beta.toFun = phi →
      ∃ E Gr Ho : ℝ, 0 ≤ E ∧ 0 ≤ Gr ∧ 0 ≤ Ho ∧
      ∀ (n : ℕ) (v : H1Function (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
        IsWeaklyHarmonicOn (cutoffCoefficient M H om (N (seq n)))
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) v →
        HasZeroTraceDifferenceOn (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) v beta →
        ContinuousOn v.toFun (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) →
        energy (cutoffCoefficient M H om (N (seq n)))
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) v ≤ E ∧
        (∀ x ∈ closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
          ((volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (cutoffCoefficient M H om (N (seq n)) y *
              ∑ j : Fin d, (v.grad y j) ^ 2))) (Metric.ball x rad) ≤ ENNReal.ofReal (Gr * rad ^ t)) ∧
        (∀ x ∈ closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          ∀ y ∈ closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          |v.toFun x - v.toFun y| ≤ Ho * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) := by
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hdR, ht]
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_countable_native_growth_with_moment d hd I Pin X W Cp Sob
    t alpha ht htd ha ha1
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta ι _ z r hr Bbank Cbank hBmem hBnorm Qbank p hp Qbound hQmem hQnorm N
  obtain ⟨Kbank, hKm, hK0, hKn, hsamples⟩ :=
    hs M Rm Sreg It H hIR hdelta ι z r hr Bbank Cbank hBmem hBnorm
      Qbank p hp Qbound hQmem hQnorm N
  refine ⟨Kbank, hKm, hK0, hKn, ?_⟩
  filter_upwards [hsamples] with om hom
  obtain ⟨seq, hseq, hQbound, hbank, hcells⟩ := hom
  refine ⟨seq, hseq, hQbound, hbank, ?_⟩
  intro i hside phi hphi beta hbeta
  obtain ⟨K, hK, hbnd⟩ := hcells i
  let Cphi := c2Norm (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) phi
  have hC : 0 ≤ Cphi := aux_prop_growth_c2Norm_nonneg _ _
  have hE : 0 ≤ K * Cphi ^ 2 := mul_nonneg hK (sq_nonneg _)
  refine ⟨K * Cphi ^ 2, 2 ^ t * (K * Cphi ^ 2), K * Cphi,
    hE, mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE, mul_nonneg hK hC, ?_⟩
  intro n v hharm htrace hvcont
  let a := cutoffPositiveCoefficient M H om (N (seq n)) (z i) (hr i)
  have hc := (cutoffPositiveCoefficient_representative M H om (N (seq n)) (z i) (hr i)).2.2.2
  have hmin := native_harmonic_energy_eq_infimum a _ hc beta v htrace hharm
  obtain ⟨hholder, hnorm, hg⟩ := hbnd n phi hphi beta v
    (Filter.Eventually.of_forall fun x => congrFun hbeta x) htrace hmin.le hvcont
  refine ⟨?_, ?_, ?_⟩
  · apply native_energy_le_of_unit_growth (z i) (hr i) hside a _ hc v
    simpa only [Real.one_rpow, mul_one] using hg (z i) 1
      (Metric.mem_ball_self (half_pos (hr i))) one_pos le_rfl
  · intro x _ rad hrad hrad1
    exact native_energyMeasure_growth_of_localGradient (z i) (hr i) hside a _ hc v
      (K * Cphi ^ 2) t hE ht0 (fun y hy s hs hs1 => hg y s hy hs hs1) x rad hrad hrad1
  · rw [aux_prop_conc_form_cutoff_continuity_closure_cube]
    exact aux_lem_cutoffs_pair_bound_of_holder ha hholder hnorm

end
end Paper
