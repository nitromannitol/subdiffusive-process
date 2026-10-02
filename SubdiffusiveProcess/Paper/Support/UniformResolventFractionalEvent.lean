import SubdiffusiveProcess.Paper.Support.UniformResolventFractionalLimit
import SubdiffusiveProcess.Paper.Support.UniformResolventMosco
import SubdiffusiveProcess.Paper.Support.UniformResolventHalfLift
import SubdiffusiveProcess.Probability.LiminfMomentEnvelope

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Section9
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- Original-space inverse convergence in probability and uniformly bounded
coercivity moments produce fractional lifting on one all-cube event. The proof
first selects an actual common inverse subsequence, then extracts bounded
coercivity levels samplewise. -/
theorem aux_mfd_prop_uniform_resolvent_fractional_event
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Sf : Lane4.SobolevFoundationalInput d hd)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (G : KilledInverseFamily d (BilateralField d))
    (hconv : ∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N omega => volumeResponseOperator (determiningResponseSpace d i)
        (Lane4.cutoffPositiveCoefficient M H omega N
          (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))) atTop (G i))
    (Kc : ℕ → ℕ → BilateralField d → ℝ) (Cb : ℕ → ℝ)
    (q : ℝ) (hq : 1 ≤ q) (hCb : ∀ i, 0 ≤ Cb i)
    (hmeas : ∀ i N, Measurable (Kc i N))
    (hn : ∀ i N omega, 0 ≤ Kc i N omega)
    (hmem : ∀ i N, MemLp (Kc i N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure)
    (hbound : ∀ i N, eLpNorm (Kc i N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cb i))
    (hcoer : ∀ i N, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ v : killedSobolevGraph (determiningCube d i),
        cubeFractionalSqNorm hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
          (rationalTriadicSide_pos d i) threeQuarterOrder v.val.1 ≤
        Kc i N omega * sobolevCoefficientForm
          (Lane4.cutoffPositiveCoefficient M H omega N
            (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) v.val v.val) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
      (∀ x y : DomainL2 (determiningCube d i),
        inner ℝ (G i omega x) y = inner ℝ x (G i omega y)) ∧
      (∀ x : DomainL2 (determiningCube d i), 0 ≤ inner ℝ x (G i omega x)) ∧
      ∃ Cbase : ℝ, 0 < Cbase ∧
        ∀ u : DomainL2 (determiningCube d i), (limitFormEnergy (G i omega) u).toENNReal ≠ ∞ →
          ∃ v : CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i)
              (rationalTriadicSide d i) (rationalTriadicSide_pos d i) threeQuarterOrder,
            v.val 0 = u ∧
            cubeFractionalL2Norm hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
                (rationalTriadicSide_pos d i) threeQuarterOrder v ^ 2 ≤
              Cbase * (limitFormEnergy (G i omega) u).toReal := by
  classical
  obtain ⟨phi, hphi, hnorm⟩ := aux_mfd_prop_uniform_resolvent_common_mosco_subsequence
    d M H G hconv id (fun _ _ h => h)
  have hfreq : ∀ i, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∃ b : ℕ, ∃ᶠ n in atTop, Kc i (phi n) omega ≤ b := by
    intro i
    obtain ⟨E, -, -, -, hf⟩ := SubdiffusiveProcess.Probability.exists_common_level_envelope
      (chaosSampleLaw M).toMeasure {q} (Finset.singleton_nonempty q)
      (fun p hp => by simpa only [Finset.mem_singleton.mp hp] using hq)
      (fun n => Kc i (phi n)) (fun n => Kc i (phi n))
      (fun n => hmeas i (phi n)) (fun n => hmeas i (phi n))
      (Eventually.of_forall fun omega n => ⟨hn i (phi n) omega, hn i (phi n) omega⟩)
      (fun p hp => by
        have hpq : p = q := Finset.mem_singleton.mp hp
        subst p
        exact ⟨⟨Cb i, fun n => ⟨ENNReal.toReal_le_of_le_ofReal (hCb i) (hbound i (phi n)),
          ENNReal.toReal_le_of_le_ofReal (hCb i) (hbound i (phi n))⟩⟩,
          fun n => ⟨hmem i (phi n), hmem i (phi n)⟩⟩)
    filter_upwards [hf] with omega hω
    obtain ⟨b, -, hb⟩ := hω
    exact ⟨b, hb.mono fun _ h => h.1⟩
  have hcAll : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i N,
      ∀ v : killedSobolevGraph (determiningCube d i),
        cubeFractionalSqNorm hd (rationalTriadicCenter d i) (rationalTriadicSide d i)
          (rationalTriadicSide_pos d i) threeQuarterOrder v.val.1 ≤
        Kc i N omega * sobolevCoefficientForm
          (Lane4.cutoffPositiveCoefficient M H omega N
            (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) v.val v.val :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr (hcoer i)
  filter_upwards [hnorm, ae_all_iff.mpr hfreq, hcAll] with omega hω hf hc i
  obtain ⟨b, hb⟩ := hf i
  obtain ⟨sigma, hsigma, hgood⟩ := Filter.extraction_of_frequently_atTop hb
  have hnormS := (hω i).1.comp hsigma.tendsto_atTop
  have hstrong : ∀ f : DomainL2 (determiningCube d i),
      Tendsto (fun n => (responseSolution (determiningResponseSpace d i)
        (Lane4.cutoffPositiveCoefficient M H omega (phi (sigma n))
          (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))
        ((sobolevVolumeLoad f).comp (determiningResponseSpace d i).space.subtypeL)).val.1)
        atTop (𝓝 (G i omega f)) := by
    intro f
    have hEval : Continuous (fun A : DomainL2 (determiningCube d i) →L[ℝ]
      DomainL2 (determiningCube d i) => A f) := continuous_id.clm_apply continuous_const
    simpa only [Function.comp_def, volumeResponseOperator_apply] using
      (hEval.tendsto (G i omega)).comp hnormS
  refine ⟨(hω i).2.1, (hω i).2.2.1, ?_⟩
  apply aux_mfd_prop_uniform_resolvent_fractional_limit hd Sf
    (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
    (centeredCube_killedPoincare (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))
    (fun n => Lane4.cutoffPositiveCoefficient M H omega (phi (sigma n))
      (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)) ((b : ℝ) + 1) (by positivity)
    (fun n v => (hc i (phi (sigma n)) v).trans (mul_le_mul_of_nonneg_right
      ((hgood n).trans (by linarith)) (sobolevCoefficientForm_nonneg _ _)))
    (G i omega) (hω i).2.1 (hω i).2.2.1 hstrong

end Paper
