import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionSobolevUpper
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionLower
/-!
The actual parent and auxiliary Sobolev displays discharge both mean-exit caps in the torsion lower construction. Choose the cap constant before the interior margin, and choose contraction parameters before the inner volume fraction. The conclusion uses the intrinsic clock at every integer native scale.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Actual finite-family tests give the pointwise intrinsic-clock exit lower bound; no mean-exit upper premise remains. -/
theorem exists_goodCube_cutoff_sobolev_meanExit_lower_parameters
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (p A : ℝ) (hp : 2 < p) (hA : 1 ≤ A) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ theta : ℝ, 0 < theta → theta < 1 →
      ∃ k0 etaCap epsH : ℝ, 0 < k0 ∧ 0 < etaCap ∧ 0 < epsH ∧
      ∀ v0 : ℝ, 0 < v0 → ∃ epsL2 : ℝ, 0 < epsL2 ∧
      ∀ (M : GMCModel d) (J n : ℕ) (omega : PotentialSample d)
        (m : ℤ) (z : Vec d) (law : Kernel (Vec d) (Path d)),
        m ≤ (n : ℤ) →
        2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2 →
        LocalDiffusionData (aCutoff M n omega) (aCutoff M n omega) law →
      ∀ {ι : Type*} (t : ι → ℤ) (centre : ι → Vec d)
        (inner : ι → Set (Vec d)) (T : Set (Vec d)),
        let U := translateSet z (openCubeSet (originCube d m))
        let outer := fun i => translateSet (centre i) (openCubeSet (originCube d (t i)))
        let sigma : ℝ := if J ≤ n then ahom M n else 1
        (∀ i, t i ≤ (n : ℤ)) →
        (∀ i, ((3 : ℝ)^(t i))^2 ≤ etaCap / K * ((3 : ℝ)^m)^2) →
        IsOpen T → T ⊆ ⋃ i, inner i →
        (∀ i, MeasurableSet (inner i)) →
        (∀ i, inner i ⊆ outer i) →
        (∀ i, outer i ⊆ U) →
        (∀ i, inner i ⊆ translateSet z (scaledClosedCubeSet (originCube d m) theta)) →
        (∀ i, ENNReal.ofReal v0 * volume U ≤ volume (inner i)) →
        GoodCubeSobolevDisplay (aCutoff M n omega) p A
          (Section7Process.timeScale (ahom M)) (z, (3 : ℝ)^m) →
        (∀ i, GoodCubeSobolevDisplay (aCutoff M n omega) p A
          (Section7Process.timeScale (ahom M)) (centre i, (3 : ℝ)^(t i))) →
        GoodCubeTorsionComparisonTest (originCube d m)
          (fun x => aCutoff M n omega (x + z)) sigma epsL2 →
        (∀ i, ∀ h : Vec d → ℝ, WeakHarmonic (aCutoff M n omega) (outer i) h →
          oscillation (inner i) h ≤ ENNReal.ofReal epsH * oscillation (outer i) h) →
        ∀ x ∈ T, ENNReal.ofReal ((k0 / 2) *
          Section7Process.timeScale (ahom M) ((3 : ℝ)^m)) ≤ meanExit law U x := by
  obtain ⟨K, hK, hUpper⟩ :=
    exists_goodCube_cutoff_sobolev_meanExit_upper_constant p A hp hA
  refine ⟨K, hK, ?_⟩
  intro theta ht0 ht1
  obtain ⟨k0, etaCap, epsH, hk0, heta, hepsH, hLower⟩ :=
    exists_goodCube_torsion_meanExit_lower_parameters d hd theta K ht0 ht1 hK
  refine ⟨k0, etaCap, epsH, hk0, heta, hepsH, ?_⟩
  intro v0 hv0
  obtain ⟨epsL2, hepsL2, hLowerV⟩ := hLower v0 hv0
  refine ⟨epsL2, hepsL2, ?_⟩
  intro M J n omega m z law hmn hbudget hD ι t centre inner T
  dsimp only
  intro ht hside hTop hcover hmeas hnested houterU htheta hvol hSob hAuxSob htest hcontract
  set sigma : ℝ := if J ≤ n then ahom M n else 1 with hsigmadef
  have hclock := goodCube_native_clock_le_comparison_clock M J n m hmn hbudget
  have hsigma : 0 < sigma := by
    rw [hsigmadef]; exact hclock.1
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hparent : ∀ x ∈ translateSet z (openCubeSet (originCube d m)),
      meanExit law (translateSet z (openCubeSet (originCube d m))) x ≤
        ENNReal.ofReal (K * (cubeScaleFactor (originCube d m))^2 / sigma) := by
    intro x hx
    have h := hUpper d hd M J n omega m z law hmn hbudget hD hSob x hx
    rw [hsigmadef]
    simpa only [cubeScaleFactor_originCube] using h
  have haux : ∀ i, ∀ x ∈ translateSet (centre i) (openCubeSet (originCube d (t i))),
      meanExit law (translateSet (centre i) (openCubeSet (originCube d (t i)))) x ≤
        ENNReal.ofReal (etaCap * (cubeScaleFactor (originCube d m))^2 / sigma) := by
    intro i x hx
    have hcap := hUpper d hd M J n omega (t i) (centre i) law (ht i) hbudget hD
      (hAuxSob i) x hx
    rw [← hsigmadef] at hcap
    have hscaled : K * ((3 : ℝ)^(t i))^2 ≤ etaCap * ((3 : ℝ)^m)^2 := by
      calc K * ((3 : ℝ)^(t i))^2
          ≤ K * (etaCap / K * ((3 : ℝ)^m)^2) :=
            mul_le_mul_of_nonneg_left (hside i) hKpos.le
        _ = etaCap * ((3 : ℝ)^m)^2 := by
            field_simp [hKpos.ne']
    have hdiv : K * ((3 : ℝ)^(t i))^2 / sigma ≤ etaCap * ((3 : ℝ)^m)^2 / sigma :=
      div_le_div_of_nonneg_right hscaled hsigma.le
    refine hcap.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa only [cubeScaleFactor_originCube] using hdiv
  have hlow := hLowerV (aCutoff M n omega) law m z sigma
    (continuous_aCutoff M n omega) (aCutoff_pos M n omega) hD hsigma
    inner (fun i => translateSet (centre i) (openCubeSet (originCube d (t i)))) T
    hTop hcover hmeas hnested
    (fun i => ((isOpenBoundedConvexDomain_openCubeSet (originCube d (t i))).translateSet
      (centre i)).isOpen)
    houterU htheta hvol htest hparent haux hcontract
  intro x hx
  refine (ENNReal.ofReal_le_ofReal ?_).trans (hlow x hx)
  have hmul := mul_le_mul_of_nonneg_left hclock.2
    (show (0 : ℝ) ≤ k0 / 2 by positivity)
  calc (k0 / 2) * Section7Process.timeScale (ahom M) ((3 : ℝ)^m)
      ≤ (k0 / 2) * (2 * ((3 : ℝ)^m)^2 / sigma) := hmul
    _ = k0 * (cubeScaleFactor (originCube d m))^2 / sigma := by
        rw [cubeScaleFactor_originCube]; ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
