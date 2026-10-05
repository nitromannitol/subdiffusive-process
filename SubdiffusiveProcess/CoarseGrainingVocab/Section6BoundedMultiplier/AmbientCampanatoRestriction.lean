module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.AmbientParentCampanatoContract
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitGeometry

@[expose] public section

/-!
# Restricting the ambient theta-Campanato contract

The theta-ladder contract is stated for a Sobolev function whose carrier is
the moving top cube.  The bounded-multiplier consumer instead starts with one
function on a fixed parent cube.  This module performs the ordinary open-set
restriction and promotes the ambient bad event to any sigma-field containing
the ambient measurable space.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

abbrev ambientSampleSigma (d : ℕ) : MeasurableSpace (Sample d) :=
  inferInstance

abbrev ambientSampleMeasure {d : ℕ} (M : GMCModel d) :
    @Measure (Sample d) (ambientSampleSigma d) :=
  M.P.toMeasure

/-- the ambient Campanato estimate's ambient centered-Campanato event, transported to a chosen
sigma-field and to restrictions of one Sobolev function on a larger open
carrier. -/
theorem exists_ambientProductCampanatoContract_restrict
    (d : ℕ) [NeZero d] (step : ℕ)
    (Sigma : MeasurableSpace (Sample d))
    (hAmbient : ambientSampleSigma d ≤ Sigma) :
    ∃ Kbase Cgain Citer : ℝ,
      0 < Kbase ∧ 0 < Cgain ∧ 0 < Citer ∧
      ∀ C₁ C₂ Cabs : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 0 ≤ Cabs →
      ∀ k : ℕ, 6 ≤ k →
      (∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
        Real.exp
            (Citer * (k + 1) * (k + 2) +
              (Citer * (k + 2)) * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
          Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4)) →
      ∃ c Ctail : ℝ, 0 < c ∧ 0 < Ctail ∧ c ≤ 1 ∧
        ∃ j0 : ℕ, 0 < j0 ∧
          ∀ M : GMCModel d, M.delta ≤ c →
          64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) →
          ∀ L top : ℕ, ∀ z : Vec d,
            ∃ badTheta : Set (Sample d),
              @MeasurableSet (Sample d) Sigma badTheta ∧
              ambientSampleMeasure M badTheta ≤ ENNReal.ofReal
                (Ctail * Real.exp
                  (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
              ∀ omega ∉ badTheta, ∀ n : ℕ, n < top → j0 ≤ top - n →
              ∀ q : Vec d, OnTriadicGrid n q → q ∈ cube d top →
              let eta := Section6Stopping.holderStoppingEpsilon
                C₂ thetaLadderExponent
              ∀ _heta : eta ∈
                Set.Icc ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) 1,
              ∀ b epsilon : ℝ, 0 < b → 0 < epsilon → epsilon ≤ 1 / 2 →
              Kbase * eta + Cgain * Real.sqrt epsilon ≤ 1 →
              productIterationSlopeCoefficient d M.shellPrefix.dimension k
                  (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
                C₁⁻¹ * (1 - thetaLadderExponent) →
              ∀ theta : Vec d → ℝ,
              ContinuousOn theta
                (translatedCube d (top : ℤ) (z + q)) →
              (∀ x ∈ translatedCube d (top : ℤ) (z + q),
                |b⁻¹ * theta x - 1| ≤ epsilon) →
              let contraction := (3 : ℝ) ^ (-(1 / 4 : ℝ))
              contraction ∈ Set.Ioo (0 : ℝ) 1 →
              contraction ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
              oneStepContractionConst d *
                    Section6Schauder.schauderInteriorConst d *
                    ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) +
                  productOriginRecurrenceErrorConstant d
                    M.shellPrefix.dimension k *
                    (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
                contraction ^ k →
              ∀ (W : Set (Vec d)), IsOpen W →
              translatedCube d (top : ℤ) (z + q) ⊆ W →
              ∀ u : H1Function W,
              IsWeaklyHarmonicOn
                  (fun x ↦ aCutoff M L omega x * theta x) W u →
              normalizedL2On (translatedCube d (n : ℤ) (z + q))
                  (fun x ↦ u.toFun x - averageOn
                    (translatedCube d (n : ℤ) (z + q)) u.toFun) ≤
                Cabs * (3 : ℝ) ^
                    (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ))) *
                  normalizedL2On (translatedCube d (top : ℤ) (z + q))
                    (fun x ↦ u.toFun x - averageOn
                      (translatedCube d (top : ℤ) (z + q)) u.toFun) := by
  obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, hcontract⟩ :=
    exists_ambientProductCampanatoContract d step
  refine ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, ?_⟩
  intro C₁ C₂ Cabs hC₁ hC₂ hCabs k hk habs
  obtain ⟨c, Ctail, hc, hCtail, hcOne, j0, hj0, hevent⟩ :=
    hcontract C₁ C₂ Cabs hC₁ hC₂ hCabs k hk habs
  refine ⟨c, Ctail, hc, hCtail, hcOne, j0, hj0, ?_⟩
  intro M hdelta hsmall L top z
  obtain ⟨badTheta, hbadMeas, hbadTail, hpath⟩ :=
    hevent M hdelta hsmall L top z
  refine ⟨badTheta, hAmbient _ hbadMeas, hbadTail, ?_⟩
  intro omega homega n hntop hdepth q hqgrid hqmem
  dsimp only
  intro heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff theta
    htheta hnear hcontraction hcontractionPow hcontractionStep W hW htop u hu
  let uTop : H1Function (translatedCube d (top : ℤ) (z + q)) :=
    u.restrict (by
      rw [translatedCube_eq_metricBall]
      exact Metric.isOpen_ball) htop
  have huTop : IsWeaklyHarmonicOn
      (fun x ↦ aCutoff M L omega x * theta x)
      (translatedCube d (top : ℤ) (z + q)) uTop :=
    Section6BoundaryL2.isWeaklyHarmonicOn_restrict hW (by
      rw [translatedCube_eq_metricBall]
      exact Metric.isOpen_ball) htop hu
  have hout := hpath omega homega n hntop hdepth q hqgrid hqmem heta b epsilon
    hb hepsilon hepsilonHalf herrorOne hepsCoeff theta htheta hnear
    hcontraction hcontractionPow hcontractionStep uTop huTop
  simpa only [uTop, H1Function.restrict] using hout

/-- the ambient Campanato estimate's parent-uniform ambient Campanato event, transported to an
abstract sigma-field and to restrictions of one Sobolev function on a larger
open carrier.  The bad event is selected at `parent`, while the equation is
used only on the moving comparison cube at `top`. -/
theorem exists_ambientProductCampanatoContractOnParent_restrict
    (d : ℕ) [NeZero d] (step : ℕ)
    (Sigma : MeasurableSpace (Sample d))
    (hAmbient : ambientSampleSigma d ≤ Sigma) :
    ∃ Kbase Cgain Citer : ℝ,
      0 < Kbase ∧ 0 < Cgain ∧ 0 < Citer ∧
      ∀ C₁ C₂ Cabs : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 0 ≤ Cabs →
      ∀ k : ℕ, 6 ≤ k →
      (∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
        Real.exp
            (Citer * (k + 1) * (k + 2) +
              (Citer * (k + 2)) * (C₁⁻¹ * (1 - alpha)) * (gap + 1)) ≤
          Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4)) →
      ∃ c Ctail : ℝ, 0 < c ∧ 0 < Ctail ∧ c ≤ 1 ∧
        ∃ j0 : ℕ, 0 < j0 ∧
          ∀ M : GMCModel d, M.delta ≤ c →
          64 * M.delta ^ 2 ≤ (1 / 32 : ℝ) →
          ∀ L parent : ℕ, ∀ z : Vec d,
            ∃ badTheta : Set (Sample d),
              @MeasurableSet (Sample d) Sigma badTheta ∧
              ambientSampleMeasure M badTheta ≤ ENNReal.ofReal
                (Ctail * Real.exp
                  (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
              ∀ omega ∉ badTheta, ∀ n top : ℕ,
              n < top → top ≤ parent → j0 ≤ parent - n →
              ∀ q : Vec d, OnTriadicGrid n q → q ∈ cube d parent →
              let eta := Section6Stopping.holderStoppingEpsilon
                C₂ thetaLadderExponent
              ∀ _heta : eta ∈
                Set.Icc ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) 1,
              ∀ b epsilon : ℝ, 0 < b → 0 < epsilon → epsilon ≤ 1 / 2 →
              Kbase * eta + Cgain * Real.sqrt epsilon ≤ 1 →
              productIterationSlopeCoefficient d M.shellPrefix.dimension k
                  (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
                C₁⁻¹ * (1 - thetaLadderExponent) →
              ∀ theta : Vec d → ℝ,
              ContinuousOn theta
                (translatedCube d (top : ℤ) (z + q)) →
              (∀ x ∈ translatedCube d (top : ℤ) (z + q),
                |b⁻¹ * theta x - 1| ≤ epsilon) →
              let contraction := (3 : ℝ) ^ (-(1 / 4 : ℝ))
              contraction ∈ Set.Ioo (0 : ℝ) 1 →
              contraction ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
              oneStepContractionConst d *
                    Section6Schauder.schauderInteriorConst d *
                    ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) +
                  productOriginRecurrenceErrorConstant d
                    M.shellPrefix.dimension k *
                    (Kbase * eta + Cgain * Real.sqrt epsilon) ≤
                contraction ^ k →
              ∀ (W : Set (Vec d)), IsOpen W →
              translatedCube d (top : ℤ) (z + q) ⊆ W →
              ∀ u : H1Function W,
              IsWeaklyHarmonicOn
                  (fun x ↦ aCutoff M L omega x * theta x) W u →
              normalizedL2On (translatedCube d (n : ℤ) (z + q))
                  (fun x ↦ u.toFun x - averageOn
                    (translatedCube d (n : ℤ) (z + q)) u.toFun) ≤
                (Cabs * (3 : ℝ) ^
                    (((parent : ℝ) - (top : ℝ)) / 16)) *
                  (3 : ℝ) ^
                    (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ))) *
                  normalizedL2On (translatedCube d (top : ℤ) (z + q))
                    (fun x ↦ u.toFun x - averageOn
                      (translatedCube d (top : ℤ) (z + q)) u.toFun) := by
  obtain ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, hcontract⟩ :=
    exists_ambientProductCampanatoContractOnParent d step
  refine ⟨Kbase, Cgain, Citer, hKbase, hCgain, hCiter, ?_⟩
  intro C₁ C₂ Cabs hC₁ hC₂ hCabs k hk habs
  obtain ⟨c, Ctail, hc, hCtail, hcOne, j0, hj0, hevent⟩ :=
    hcontract C₁ C₂ Cabs hC₁ hC₂ hCabs k hk habs
  refine ⟨c, Ctail, hc, hCtail, hcOne, j0, hj0, ?_⟩
  intro M hdelta hsmall L parent z
  obtain ⟨badTheta, hbadMeas, hbadTail, hpath⟩ :=
    hevent M hdelta hsmall L parent z
  refine ⟨badTheta, hAmbient _ hbadMeas, hbadTail, ?_⟩
  intro omega homega n top hntop htopParent hdepth q hqgrid hqmem
  dsimp only
  intro heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff theta
    htheta hnear hcontraction hcontractionPow hcontractionStep W hW htopW u hu
  let uTop : H1Function (translatedCube d (top : ℤ) (z + q)) :=
    u.restrict (by
      rw [translatedCube_eq_metricBall]
      exact Metric.isOpen_ball) htopW
  have huTop : IsWeaklyHarmonicOn
      (fun x ↦ aCutoff M L omega x * theta x)
      (translatedCube d (top : ℤ) (z + q)) uTop :=
    Section6BoundaryL2.isWeaklyHarmonicOn_restrict hW (by
      rw [translatedCube_eq_metricBall]
      exact Metric.isOpen_ball) htopW hu
  have hout := hpath omega homega n top hntop htopParent hdepth q hqgrid hqmem
    heta b epsilon hb hepsilon hepsilonHalf herrorOne hepsCoeff theta htheta
    hnear hcontraction hcontractionPow hcontractionStep uTop huTop
  simpa only [uTop, H1Function.restrict] using hout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
