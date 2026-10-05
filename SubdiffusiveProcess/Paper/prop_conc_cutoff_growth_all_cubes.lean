module

public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Probability.GrowthSubsequence

@[expose] public section

/-! Actual cutoff growth on arbitrary cubes, along bounded further subsequences.
This extends the cell supplier to large padded cubes; it makes no concentration claim. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- On the original pinned field law, all finite source/boundary growth and
Holder bounds hold along a further cutoff subsequence with one measurable
random bound. Its moment constant precedes the choice of subsequence. -/
theorem prop_conc_cutoff_growth_all_cubes
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t alpha p : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hp : 1 ≤ p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ N : ℕ → ℕ,
      ∃ K : BilateralField d → ℝ,
        Measurable K ∧ (∀ om, 0 < K om) ∧
        eLpNorm K (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cbound ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∀ (n : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om (N (seq n)) z hr) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om (N (seq n)) z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (Metric.isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K om * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K om * (Kf + Cphi)) := by
  obtain ⟨deltaSmall, hdeltaSmall, hsmall⟩ :=
    prop_growth d hd I Pin X W Cp Sob t alpha 1 (fun _ => p) ht htd ha ha1 (fun _ => hp)
  obtain ⟨deltaLarge, hdeltaLarge, hlarge⟩ :=
    prop_growth_large_root d hd I Pin X W Cp Sob t alpha 1 (fun _ => p)
      ht htd ha ha1 (fun _ => hp)
  refine ⟨min deltaSmall deltaLarge, lt_min hdeltaSmall hdeltaLarge, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr
  have hbase := if h : r ≤ 1 then
      hsmall M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) z r hr h
    else hlarge M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _)) z r hr (lt_of_not_ge h)
  obtain ⟨K0, C0, hmem, hnorm, _hge, hgrowth⟩ := hbase
  let C : ℝ≥0 := (C0 0).toNNReal
  let q : ℝ≥0 := ⟨p, by linarith only [hp]⟩
  have hq : 1 ≤ q := by exact_mod_cast hp
  have hqcoe : (q : ℝ≥0∞) = ENNReal.ofReal p := ENNReal.ofReal_coe_nnreal.symm
  refine ⟨(C : ℝ) + 1, by positivity, ?_⟩
  intro N
  let f : ℕ → BilateralField d → ℝ := fun n =>
    (hmem 0 (N n)).aestronglyMeasurable.mk (K0 (N n))
  have hf (n : ℕ) : Measurable (f n) :=
    (hmem 0 (N n)).aestronglyMeasurable.measurable_mk
  have heq (n : ℕ) : K0 (N n) =ᵐ[(chaosSampleLaw M).toMeasure] f n :=
    (hmem 0 (N n)).aestronglyMeasurable.ae_eq_mk
  have hb (n : ℕ) : eLpNorm (f n) q (chaosSampleLaw M).toMeasure ≤ C := by
    rw [← eLpNorm_congr_ae (heq n), hqcoe]
    exact hnorm 0 (N n)
  obtain ⟨K, hKm, hKpos, hKnorm, hseq⟩ := exists_bounded_subsequence_of_eLpNorm_bound
    (chaosSampleLaw M).toMeasure f q C 1 hq zero_lt_one hf hb
  refine ⟨K, hKm, hKpos, ?_, ?_⟩
  · rw [hqcoe] at hKnorm
    exact hKnorm.trans_eq (show ((C + 1 : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal ((C : ℝ) + 1) from ENNReal.ofReal_coe_nnreal.symm)
  · have heqAll : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ n, K0 (N n) om = f n om :=
      ae_all_iff.mpr heq
    filter_upwards [hseq, heqAll, hgrowth] with om hs heqOm hg
    obtain ⟨seq, hstrict, hbnd⟩ := hs
    refine ⟨seq, hstrict, ?_⟩
    intro n F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have hK0 : K0 (N (seq n)) om ≤ K om := by
      rw [heqOm]
      exact (le_abs_self _).trans (hbnd n).le
    obtain ⟨henergy, U, hUcont, hUae, hUholder, hUnorm⟩ :=
      hg (N (seq n)) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    constructor
    · intro x rad hx hrad hrad1
      exact (henergy x rad hx hrad hrad1).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK0 (sq_nonneg _))
          (Real.rpow_nonneg hrad.le t))
    · refine ⟨U, hUcont, hUae, hUholder, hUnorm.trans ?_⟩
      have hCphi0 := (aux_prop_growth_c2Norm_nonneg
        (closedCube z r hr : Set (SpatialCoordinates d)) phi).trans hCphi
      exact mul_le_mul_of_nonneg_right hK0 (add_nonneg hKf hCphi0)

end
end SubdiffusiveProcess.Paper

