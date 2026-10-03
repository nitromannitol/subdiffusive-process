module

public import SubdiffusiveProcess.Paper.neumann_ht_macro_campanato
public import SubdiffusiveProcess.Paper.neumann_ht_micro_campanato

@[expose] public section

/-! All-radii Campanato decay of the bounded-source Neumann solution for the top-block-removed coefficient
`A^{HT_j}_{N+j}` on the unit cube: the macro half (radii `≥ 3^{-(N+j)}`) and the micro half (radii
`≤ 3^{-(N+j)}`) glued at the wavelength with `K^{c} = K^{mic} + K^{mac}` (transplant of
`aux_cor_neumann_source_campanato`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

noncomputable section
namespace Paper

/-- All-radii Campanato decay: the macro and micro halves glued at `rad = 3^{-(N+j)}`. -/
theorem neumann_ht_campanato (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg),
        M.delta ≤ delta0 → ∀ j : ℕ, 0 < j →
        ∃ (Kc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
          (∀ N om, 0 ≤ Kc N om) ∧
          (∀ i N, MemLp (Kc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (Kc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cbound i)) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
              AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
              (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
                |F x| ≤ Kf) →
              (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
            ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
              SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
                (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) F v →
              ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
                ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
                    ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
                      (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                      (v : SobolevData (unitNeumannCube d)).1) ^ 2
                    ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
                  (Kc N om * Kf) ^ 2 * rad ^ (2 * alpha) *
                    volume.real (Metric.ball x rad ∩
                      (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  obtain ⟨delta1, hdelta1, hmac⟩ :=
    neumann_ht_macro_campanato d hd E _P _X _W D alpha k ps ha0 ha1 hps
  obtain ⟨delta2, hdelta2, hmic⟩ :=
    neumann_ht_micro_campanato d hd E _P _X _W D alpha k ps ha0 ha1 hps
  refine ⟨min delta1 delta2, lt_min hdelta1 hdelta2, ?_⟩
  intro M Rm Sreg It hdelta j hj
  obtain ⟨Kmac, Cmac, hKmac0, hKmacL, hKmacB, hmacE⟩ :=
    hmac M Rm Sreg It (hdelta.trans (min_le_left _ _)) j hj
  obtain ⟨Kmic, Cmic, hKmic0, hKmicL, hKmicB, hmicE⟩ :=
    hmic M Rm Sreg It (hdelta.trans (min_le_right _ _)) j hj
  refine ⟨fun N om => Kmic N om + Kmac N om, fun i => max (Cmic i) 0 + max (Cmac i) 0,
    fun N om => add_nonneg (hKmic0 N om) (hKmac0 N om), ?_, ?_, ?_⟩
  · intro i N
    exact (hKmicL i N).add (hKmacL i N)
  · intro i N
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (ps i) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hps i)
    calc eLpNorm (fun om => Kmic N om + Kmac N om) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure
        ≤ eLpNorm (Kmic N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure +
            eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure :=
          eLpNorm_add_le hp1
      _ ≤ ENNReal.ofReal (max (Cmic i) 0) + ENNReal.ofReal (max (Cmac i) 0) :=
          add_le_add ((hKmicB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
            ((hKmacB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      _ = ENNReal.ofReal (max (Cmic i) 0 + max (Cmac i) 0) :=
          (ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)).symm
  · filter_upwards [hmacE, hmicE] with om hom1 hom2
    intro N F Kf hKf hFm hFb hmean v hsol x hx rad hrad hrad1
    exact aux_cor_neumann_source_campanato_split _ (Kmic N om) (Kmac N om) Kf
      (rad ^ (2 * alpha)) _ ((3 : ℝ) ^ (-((N + j : ℕ) : ℤ))) rad (hKmic0 N om) (hKmac0 N om) hKf
      (Real.rpow_nonneg hrad.le _) measureReal_nonneg
      (fun h => hom2 N F Kf hKf hFm hFb hmean v hsol x hx rad hrad h hrad1)
      (fun h => hom1 N F Kf hKf hFm hFb hmean v hsol x hx rad h hrad1)

end Paper
