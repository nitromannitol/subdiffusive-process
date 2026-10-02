import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Sobolev.AffineResponses
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Lane4.Carriers

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_lem_neumann_error_volume_measurable_potential_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : Measurable H) (N : ℕ) (K : Compacts (SpatialCoordinates d))
    [MeasurableSpace C(K, ℝ)] [BorelSpace C(K, ℝ)] :
    Measurable (fun omega : BilateralField d =>
      (H omega).restrict (K : Set (SpatialCoordinates d)) +
        (∑ j ∈ Finset.range (N + 1),
          (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) -
        ContinuousMap.const K
          ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
        ContinuousMap.const K
          (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹)) := by
  have hH' : Measurable (fun omega : BilateralField d =>
      (H omega).restrict (K : Set (SpatialCoordinates d))) :=
    (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).measurable.comp hH
  have hsum : Measurable (fun omega : BilateralField d =>
      ∑ j ∈ Finset.range (N + 1),
        (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) := by
    refine Finset.measurable_sum _ ?_
    intro j hj
    exact (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).measurable.comp
      (measurable_pi_apply _)
  exact ((hH'.add hsum).sub measurable_const).add measurable_const

theorem aux_lem_neumann_error_volume_measurable_log_eq
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    continuousPositiveLog (cutoffCoefficientCM M H omega N z hr)
      (cutoffCoefficientCM_pos M H omega N z hr) =
      (H omega).restrict (closedCube z r hr : Set (SpatialCoordinates d)) +
        (∑ j ∈ Finset.range (N + 1),
          (omega (-(Int.ofNat j))).restrict (closedCube z r hr : Set (SpatialCoordinates d))) -
        ContinuousMap.const (closedCube z r hr)
          ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
        ContinuousMap.const (closedCube z r hr)
          (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹) := by
  ext x
  change Real.log (cutoffCoefficient M H omega N (x : SpatialCoordinates d)) = _
  simp only [cutoffCoefficient, cutoffPotential, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.sum_apply]
  rw [Real.log_mul]
  · rw [Real.log_inv, Real.log_exp]
    change
      -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
          ((H omega) (x : SpatialCoordinates d) +
            ∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) (x : SpatialCoordinates d) -
            (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
        (H omega) (x : SpatialCoordinates d) +
            ∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) (x : SpatialCoordinates d) -
          (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
        Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)
    ring
  · exact (inv_ne_zero (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)))
  · exact ne_of_gt (Real.exp_pos _)



theorem lem_neumann_error_volume_measurable :
  ∀ (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
    InfraredCharacterization M H →
  ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (fL2 : ℕ → BilateralField d → DomainL2 (unitNeumannCube d))
    (g : SpatialCoordinates d → ℝ),
    (∀ N om, ((fL2 N om : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] g)) →
  ∀ (N : ℕ),
    ∃ Lg : meanZeroSobolevGraph (unitNeumannCube d) →L[ℝ] ℝ,
      (∀ om, (sobolevVolumeLoad (fL2 N om)).comp
          (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL = Lg) ∧
      Measurable (fun om =>
        inverseResponse (meanZeroResponseSpace hP)
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          Lg)
    := by
  intro d _ _ M H hH hP fL2 g hfg N
  let Lg : meanZeroSobolevGraph (unitNeumannCube d) →L[ℝ] ℝ :=
    (sobolevVolumeLoad (fL2 N 0)).comp
      (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL
  refine ⟨Lg, ?_, ?_⟩
  · intro om
    have hae :
        (fL2 N om : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
          (fL2 N 0 : SpatialCoordinates d → ℝ) :=
      (hfg N om).trans (hfg N 0).symm
    have heq : fL2 N om = fL2 N 0 := Lp.ext hae
    dsimp [Lg]
    rw [heq]
  · let K : Compacts (SpatialCoordinates d) :=
      closedCube (d := d) (fun _ => (1 / 2 : ℝ)) 1 one_pos
    letI : Fact ((unitNeumannCube d : Set (SpatialCoordinates d)) ⊆ K) := ⟨by
      simpa [K, unitNeumannCube] using
        (centeredCube_subset_closedCube (d := d) (fun _ => (1 / 2 : ℝ)) one_pos)
    ⟩
    letI : MeasurableSpace C(K, ℝ) := borel _
    letI : BorelSpace C(K, ℝ) := ⟨rfl⟩
    letI : MeasurableSpace (Lp ℝ ∞
        (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)))) := borel _
    letI : BorelSpace (Lp ℝ ∞
        (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)))) := ⟨rfl⟩
    have hpot : Measurable (fun omega : BilateralField d =>
        (H omega).restrict (K : Set (SpatialCoordinates d)) +
          (∑ j ∈ Finset.range (N + 1),
            (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) -
          ContinuousMap.const K
            ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
          ContinuousMap.const K
            (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹)) :=
      aux_lem_neumann_error_volume_measurable_potential_measurable M H hH.1 N K
    have hload : Measurable (fun omega : BilateralField d =>
        compactPotentialToLp (Ω := unitNeumannCube d) K
          ((H omega).restrict (K : Set (SpatialCoordinates d)) +
            (∑ j ∈ Finset.range (N + 1),
              (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) -
            ContinuousMap.const K
              ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
            ContinuousMap.const K
              (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))) := by
      exact (compactPotentialToLp (Ω := unitNeumannCube d) K).continuous.measurable.comp hpot
    have hresp : Measurable (fun omega : BilateralField d =>
        inverseResponse (meanZeroResponseSpace hP)
          (expPotentialCoefficient (compactPotentialToLp (Ω := unitNeumannCube d) K
            ((H omega).restrict (K : Set (SpatialCoordinates d)) +
              (∑ j ∈ Finset.range (N + 1),
                (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) -
              ContinuousMap.const K
                ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
              ContinuousMap.const K
                (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹)))) Lg) :=
      (measurable_inverseResponse_potential (meanZeroResponseSpace hP) Lg).comp hload
    change Measurable (fun omega : BilateralField d =>
      inverseResponse (meanZeroResponseSpace hP)
        (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos) Lg)
    have hcoef : ∀ omega : BilateralField d,
        cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos =
          expPotentialCoefficient (compactPotentialToLp (Ω := unitNeumannCube d) K
            ((H omega).restrict (K : Set (SpatialCoordinates d)) +
              (∑ j ∈ Finset.range (N + 1),
                (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) -
              ContinuousMap.const K
                ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
              ContinuousMap.const K
                (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))) := by
      intro omega
      unfold cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient
      rw [aux_lem_neumann_error_volume_measurable_log_eq M H omega N
        (fun _ => (1 / 2 : ℝ)) one_pos]
      simp only [K, Real.log_one, ContinuousMap.const_zero, sub_zero]
      apply congrArg (fun q : Lp ℝ ∞
          (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) =>
        expPotentialCoefficient q)
      rfl
    simpa only [hcoef] using hresp

end Paper
