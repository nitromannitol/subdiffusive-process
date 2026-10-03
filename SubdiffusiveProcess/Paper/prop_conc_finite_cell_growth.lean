module

public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Probability.FiniteGrowthSubsequence

@[expose] public section

/-! A common growth and continuity bound for finitely many actual cutoff cells.
The moment constant may depend on the model and cells; this does not assert
uniform concentration constants or boundedness of the original cutoff sequence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators

namespace Paper
noncomputable section

/-- Finitely many cells share one further cutoff subsequence with a moment-bounded growth constant. -/
theorem prop_conc_finite_cell_growth
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t alpha p : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hp : 1 ≤ p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (ι : Type) [Fintype ι] (z : ι → SpatialCoordinates d) (r : ι → ℝ)
        (hr : ∀ i, 0 < r i), (∀ i, r i ≤ 1) →
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ N : ℕ → ℕ,
      ∃ K : BilateralField d → ℝ,
        Measurable K ∧ (∀ om, 0 < K om) ∧
        eLpNorm K (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cbound ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∀ (i : ι) (n : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
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
              K om * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube (z i) (r i) (hr i))).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) U ≤
              K om * (Kf + Cphi)) := by
  classical
  obtain ⟨delta0, hdelta0, hsupplier⟩ :=
    prop_growth d hd I Pin X W Cp Sob t alpha 1 (fun _ => p) ht htd ha ha1 (fun _ => hp)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta ι _ z r hr hr1
  have hcell := fun i => hsupplier M Rm Sreg It H hIR hdelta (z i) (r i) (hr i) (hr1 i)
  choose K0 C0 hmem hnorm _hge hgrowth using hcell
  let f : ι → ℕ → BilateralField d → ℝ := fun i n =>
    (hmem i 0 n).aestronglyMeasurable.mk (K0 i n)
  let C : ι → ℝ≥0 := fun i => (C0 i 0).toNNReal
  let q : ℝ≥0 := ⟨p, by linarith only [hp]⟩
  have hq : 1 ≤ q := by exact_mod_cast hp
  have hqcoe : (q : ℝ≥0∞) = ENNReal.ofReal p := ENNReal.ofReal_coe_nnreal.symm
  have hf (i : ι) (n : ℕ) : Measurable (f i n) :=
    (hmem i 0 n).aestronglyMeasurable.measurable_mk
  have heq (i : ι) (n : ℕ) : K0 i n =ᵐ[(chaosSampleLaw M).toMeasure] f i n :=
    (hmem i 0 n).aestronglyMeasurable.ae_eq_mk
  have hb (i : ι) (n : ℕ) : eLpNorm (f i n) q (chaosSampleLaw M).toMeasure ≤ C i := by
    rw [← eLpNorm_congr_ae (heq i n), hqcoe]
    exact hnorm i 0 n
  refine ⟨((∑ i, C i : ℝ≥0) : ℝ) + 1, by positivity, ?_⟩
  intro N
  obtain ⟨K, hKm, hKpos, hKn, hseq⟩ := exists_common_bounded_subsequence_of_eLpNorm_bound
    (chaosSampleLaw M).toMeasure (fun i n => f i (N n)) q 1 C hq zero_lt_one
    (fun i n => hf i (N n)) (fun i n => hb i (N n))
  refine ⟨K, hKm, hKpos, ?_, ?_⟩
  · rw [hqcoe] at hKn
    exact hKn.trans_eq (ENNReal.ofReal_coe_nnreal.symm)
  · have heqAll : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ i n, K0 i n om = f i n om :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr (heq i)
    filter_upwards [hseq, heqAll, ae_all_iff.mpr hgrowth] with om hom he hg
    obtain ⟨seq, hmono, hbound⟩ := hom
    refine ⟨seq, hmono, ?_⟩
    intro i n F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsolve
    have hKi : K0 i (N (seq n)) om ≤ K om := by
      rw [he i (N (seq n))]
      exact (le_abs_self _).trans (hbound i n).le
    have hCphi0 : 0 ≤ Cphi :=
      (aux_prop_growth_c2Norm_nonneg (closedCube (z i) (r i) (hr i) :
        Set (SpatialCoordinates d)) phi).trans hCphi
    obtain ⟨henergy, U, hUcont, hUae, hUholder, hUnorm⟩ :=
      hg i (N (seq n)) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsolve
    refine ⟨?_, U, hUcont, hUae, hUholder, hUnorm.trans ?_⟩
    · intro x rad hx hrad hrad1
      exact (henergy x rad hx hrad hrad1).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKi (sq_nonneg _))
          (Real.rpow_nonneg hrad.le _))
    · exact mul_le_mul_of_nonneg_right hKi (add_nonneg hKf hCphi0)

end
end Paper
