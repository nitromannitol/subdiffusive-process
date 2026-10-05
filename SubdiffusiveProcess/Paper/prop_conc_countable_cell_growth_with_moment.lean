module

public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.inputs_classical_countable_moment_subsequence

@[expose] public section

/-! Actual cutoff growth and a distinguished moment bank on a countable family of arbitrary cubes.
One samplewise further subsequence works for every cell and every source and
boundary datum. The distinguished bank retains its uniform moment bound; the cell bounds may depend on their indices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- One common subsequence preserves a moment majorant and bounds the actual growth and Holder constants on every cell. -/
theorem prop_conc_countable_cell_growth_with_moment
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
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
        ∀ i : ι, ∃ K : ℝ, 0 ≤ K ∧
        ∀ (n : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube (z i) (r i) (hr i))),
          ((b : SobolevData (centeredCube (z i) (r i) (hr i))).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om (N (seq n)) (z i) (hr i)) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube (z i) (r i) (hr i) →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om (N (seq n)) (z i) (hr i))
                (s := Metric.ball x rad ∩ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
                (Metric.isOpen_ball.measurableSet.inter
                  (centeredCube (z i) (r i) (hr i)).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube (z i) (r i) (hr i)))) ≤
              K * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube (z i) (r i) (hr i))).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) U ≤
              K * (Kf + Cphi)) := by
  classical
  obtain ⟨deltaSmall, hdeltaSmall, hsmall⟩ :=
    prop_growth d hd I Pin X W Cp Sob t alpha 1 (fun _ => 1)
      ht htd ha ha1 (fun _ => le_rfl)
  obtain ⟨deltaLarge, hdeltaLarge, hlarge⟩ :=
    prop_growth_large_root d hd I Pin X W Cp Sob t alpha 1 (fun _ => 1)
      ht htd ha ha1 (fun _ => le_rfl)
  refine ⟨min deltaSmall deltaLarge, lt_min hdeltaSmall hdeltaLarge, ?_⟩
  intro M Rm Sreg It H hIR hdelta ι _ z r hr Bbank Cbank hBmem hBnorm Qbank p hp Qbound hQmem hQnorm N
  have hcell (i : ι) := if h : r i ≤ 1 then
      hsmall M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) (z i) (r i) (hr i) h
    else hlarge M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _)) (z i) (r i) (hr i)
      (lt_of_not_ge h)
  choose K0 C0 hmem hnorm _hge hgrowth using hcell
  let bank : Option ι → ℕ → BilateralField d → ℝ := fun i n =>
    match i with
    | none => Bbank (N n)
    | some j => K0 j (N n)
  let bounds : Option ι → ℝ≥0 := fun i =>
    match i with
    | none => Cbank
    | some j => (C0 j 0).toNNReal
  obtain ⟨Kbank, hKm, hK0, hKn, hbank⟩ := inputs_classical_countable_moment_subsequence
    (chaosSampleLaw M).toMeasure bank bounds
    (fun i n => by
      cases i with
      | none => exact hBmem (N n)
      | some j => simpa only [bank, ENNReal.ofReal_one] using hmem j 0 (N n))
    (fun i n => by
      cases i with
      | none => exact hBnorm (N n)
      | some j => simpa only [bank, bounds, ENNReal.ofReal_one,
          ENNReal.coe_toNNReal, ENNReal.ofReal, Real.toNNReal_one, ENNReal.coe_one] using! hnorm j 0 (N n))
    (fun n => Qbank (N n)) p hp Qbound (fun n => hQmem (N n)) (fun n => hQnorm (N n))
  refine ⟨Kbank, hKm, hK0, hKn, ?_⟩
  filter_upwards [hbank, ae_all_iff.mpr hgrowth] with om hom hg
  obtain ⟨seq, hmono, hQbound, hbound⟩ := hom
  refine ⟨seq, hmono, hQbound, hbound none, ?_⟩
  intro i
  obtain ⟨K, hK, hKi⟩ := hbound (some i)
  refine ⟨K, hK, ?_⟩
  intro n F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
  have hKle : K0 i (N (seq n)) om ≤ K := (le_abs_self _).trans (hKi n)
  have hCphi0 : 0 ≤ Cphi :=
    (aux_prop_growth_c2Norm_nonneg (closedCube (z i) (r i) (hr i) :
      Set (SpatialCoordinates d)) phi).trans hCphi
  obtain ⟨henergy, U, hUcont, hUae, hUholder, hUnorm⟩ :=
    hg i (N (seq n)) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
  refine ⟨?_, U, hUcont, hUae, hUholder, hUnorm.trans ?_⟩
  · intro x rad hx hrad hrad1
    exact (henergy x rad hx hrad hrad1).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKle (sq_nonneg _)) (Real.rpow_nonneg hrad.le _))
  · exact mul_le_mul_of_nonneg_right hKle (add_nonneg hKf hCphi0)

end
end SubdiffusiveProcess.Paper
