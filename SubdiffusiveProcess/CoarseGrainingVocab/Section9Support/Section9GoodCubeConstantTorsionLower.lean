import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionLowerTransport
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionLowerMargin
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionLowerEllipticity
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeInteriorTorsion
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionLowerAssembly
/-!

Choose the exit lower constant, outer mean cap and harmonic contraction tolerance before the inner volume fraction. Then choose the comparison tolerance, construct the physical positive profile and strict L2 margin, and obtain the pointwise exit lower bound from local contractions.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Uniform parameters close the physical exit lower bound from actual comparison and local contraction tests. -/
theorem exists_goodCube_torsion_meanExit_lower_parameters
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (theta K : ℝ) (htheta : 0 < theta) (htheta1 : theta < 1) (hK : 1 ≤ K) :
    ∃ k0 etaCap epsH : ℝ, 0 < k0 ∧ 0 < etaCap ∧ 0 < epsH ∧
      ∀ v0 : ℝ, 0 < v0 → ∃ epsL2 : ℝ, 0 < epsL2 ∧
      ∀ (a : Vec d → ℝ) (law : Kernel (Vec d) (Path d))
        (m : ℤ) (z : Vec d) (sigma : ℝ),
        Continuous a → (∀ x, 0 < a x) → LocalDiffusionData a a law → 0 < sigma →
      ∀ {ι : Type*} (inner outer : ι → Set (Vec d)) (T : Set (Vec d)),
        IsOpen T → T ⊆ ⋃ i, inner i →
        (∀ i, MeasurableSet (inner i)) →
        (∀ i, inner i ⊆ outer i) →
        (∀ i, IsOpen (outer i)) →
        (∀ i, outer i ⊆ translateSet z (openCubeSet (originCube d m))) →
        (∀ i, inner i ⊆ translateSet z (scaledClosedCubeSet (originCube d m) theta)) →
        (∀ i, ENNReal.ofReal v0 * volume (translateSet z (openCubeSet (originCube d m))) ≤
          volume (inner i)) →
        GoodCubeTorsionComparisonTest (originCube d m) (fun x => a (x + z)) sigma epsL2 →
        (∀ x ∈ translateSet z (openCubeSet (originCube d m)),
          meanExit law (translateSet z (openCubeSet (originCube d m))) x ≤
            ENNReal.ofReal (K * (cubeScaleFactor (originCube d m))^2 / sigma)) →
        (∀ i, ∀ x ∈ outer i, meanExit law (outer i) x ≤
          ENNReal.ofReal (etaCap * (cubeScaleFactor (originCube d m))^2 / sigma)) →
        (∀ i, ∀ h : Vec d → ℝ, WeakHarmonic a (outer i) h →
          oscillation (inner i) h ≤ ENNReal.ofReal epsH * oscillation (outer i) h) →
        ∀ x ∈ T, ENNReal.ofReal (k0 * (cubeScaleFactor (originCube d m))^2 / sigma) ≤
          meanExit law (translateSet z (openCubeSet (originCube d m))) x := by
  obtain ⟨cTheta, hcThetaPos, hprofile⟩ :=
    goodCube_constantTorsion_compactInterior_lower d htheta htheta1
  obtain ⟨c0, hc0pos, hc01, hc0le⟩ :
      ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ 1 ∧ c0 ≤ cTheta :=
    ⟨min cTheta 1, lt_min hcThetaPos zero_lt_one, min_le_right _ _, min_le_left _ _⟩
  have twopos : (0:ℝ) < 2 := by norm_num
  have fourpos : (0:ℝ) < 4 := by norm_num
  have eightpos : (0:ℝ) < 8 := by norm_num
  have sixteenpos : (0:ℝ) < 16 := by norm_num
  have hK1pos : (0:ℝ) < 8 * (K + 1) := by linarith
  refine ⟨c0 / 2, c0 / 16, c0 / (8 * (K + 1)),
    div_pos hc0pos twopos,
    div_pos hc0pos sixteenpos,
    div_pos hc0pos hK1pos, ?_⟩
  intro v0 hv0
  refine ⟨(c0 / 8) * Real.sqrt v0,
    mul_pos (div_pos hc0pos eightpos) (Real.sqrt_pos.mpr hv0), ?_⟩
  intro a law m z sigma hacont _hapos hD hsigma ι inner outer T hTop hcover hinner hnested
    houter houterU hinnerTheta hvolInner htest hmeanUcap hmeanOuterCap hcontract x hx
  have hUconv := (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).translateSet z
  have hU : IsOpen (translateSet z (openCubeSet (originCube d m))) := hUconv.isOpen
  have hUb : Bornology.IsBounded (translateSet z (openCubeSet (originCube d m))) :=
    hUconv.isBoundedDomain.isBounded
  have hUfin : volume (translateSet z (openCubeSet (originCube d m))) ≠ ∞ :=
    ne_of_lt hUconv.volume_lt_top
  have hUpos : 0 < (volume (translateSet z (openCubeSet (originCube d m)))).toReal := by
    rw [volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d m)
  have hsidepos : 0 < cubeScaleFactor (originCube d m) := by
    unfold cubeScaleFactor; positivity
  have hsidepowpos : 0 < (cubeScaleFactor (originCube d m))^2 := pow_pos hsidepos 2
  have htaunonneg : 0 ≤ (cubeScaleFactor (originCube d m))^2 / sigma :=
    div_nonneg hsidepowpos.le hsigma.le
  have htau : 0 < (cubeScaleFactor (originCube d m))^2 / sigma :=
    div_pos hsidepowpos hsigma
  have hcoeffU : CoefficientOn (translateSet z (openCubeSet (originCube d m))) a :=
    coefficientOn_mono subset_closure
      ((hD.1.2.1 (closure (translateSet z (openCubeSet (originCube d m))))
        hUb.isCompact_closure).1)
  obtain ⟨lam, Lam, hlam, hEll⟩ :=
    goodCube_scalar_ellipticity_of_continuous_coefficientOn hU hacont.continuousOn hcoeffU
  obtain ⟨w, hw⟩ := goodCube_exists_constantTorsion (originCube d m) hsigma
  have hwlower : ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d m)),
      x ∈ scaledClosedCubeSet (originCube d m) theta →
        c0 * (cubeScaleFactor (originCube d m))^2 / sigma ≤ w.toH1Function.toFun x := by
    filter_upwards [hprofile (originCube d m) sigma hsigma w hw] with x hxm
    intro hxin
    calc c0 * (cubeScaleFactor (originCube d m))^2 / sigma
        = c0 * ((cubeScaleFactor (originCube d m))^2 / sigma) := by ring
      _ ≤ cTheta * ((cubeScaleFactor (originCube d m))^2 / sigma) :=
        mul_le_mul_of_nonneg_right hc0le htaunonneg
      _ = cTheta * (cubeScaleFactor (originCube d m))^2 / sigma := by ring
      _ ≤ w.toH1Function.toFun x := hxm hxin
  obtain ⟨g, -, -, hglower, hgnorm⟩ :=
    goodCube_translated_constantTorsion_data (originCube d m) z a sigma
      ((c0 / 8) * Real.sqrt v0) theta
      (c0 * (cubeScaleFactor (originCube d m))^2 / sigma)
      htest w hw hwlower
  have hg : ∀ i, ∀ᵐ x ∂volume.restrict (inner i),
      c0 * (cubeScaleFactor (originCube d m))^2 / sigma ≤ g.toH1Function.toFun x := by
    intro i
    have h1 : ∀ᵐ x ∂volume.restrict (inner i),
        x ∈ translateSet z (scaledClosedCubeSet (originCube d m) theta) →
          c0 * (cubeScaleFactor (originCube d m))^2 / sigma ≤ g.toH1Function.toFun x :=
      ae_mono (Measure.restrict_mono ((hnested i).trans (houterU i)) le_rfl) hglower
    filter_upwards [ae_restrict_mem (hinner i), h1] with x hxmem hximp
    exact hximp (hinnerTheta i hxmem)
  have hcompare : ∀ u : H10Function (translateSet z (openCubeSet (originCube d m))),
      IsMassiveWeakSolutionOn a a 0 (translateSet z (openCubeSet (originCube d m)))
        u.toH1Function (fun _ => 1) →
      ∀ i, eLpNorm (fun x => u.toH1Function.toFun x - g.toH1Function.toFun x) 2
          (volume.restrict (translateSet z (openCubeSet (originCube d m)))) <
        ENNReal.ofReal ((c0 / 4) * (cubeScaleFactor (originCube d m))^2 / sigma) *
          volume (inner i) ^ (1 / 2 : ℝ) := by
    intro u hu i
    have hf : MemLp (fun x => u.toH1Function.toFun x - g.toH1Function.toFun x) 2
        (volume.restrict (translateSet z (openCubeSet (originCube d m)))) :=
      u.toH1Function.memL2.sub g.toH1Function.memL2
    have hmargin := goodCube_strict_local_l2_margin ((hnested i).trans (houterU i)) hUpos
      hUfin hv0 hc0pos htau (hvolInner i) hf
      ((hgnorm u hu).trans (le_of_eq (by ring)))
    have hconv : (c0 / 4) * ((cubeScaleFactor (originCube d m))^2 / sigma)
        = (c0 / 4) * (cubeScaleFactor (originCube d m))^2 / sigma := by ring
    rwa [hconv] at hmargin
  have hb : 0 < (c0 / 4) * (cubeScaleFactor (originCube d m))^2 / sigma :=
    div_pos (mul_pos (div_pos hc0pos fourpos) hsidepowpos) hsigma
  have hE : 0 ≤ K * (cubeScaleFactor (originCube d m))^2 / sigma :=
    div_nonneg (mul_nonneg (by linarith) hsidepowpos.le) hsigma.le
  have heta : 0 ≤ (c0 / 16) * (cubeScaleFactor (originCube d m))^2 / sigma :=
    div_nonneg (mul_nonneg (div_nonneg hc0pos.le sixteenpos.le) hsidepowpos.le) hsigma.le
  have heps : 0 ≤ c0 / (8 * (K + 1)) := div_nonneg hc0pos.le hK1pos.le
  have hk : 0 ≤ (c0 / 2) * (cubeScaleFactor (originCube d m))^2 / sigma :=
    div_nonneg (mul_nonneg (div_nonneg hc0pos.le twopos.le) hsidepowpos.le) hsigma.le
  have hbudget : (c0 / 2) * (cubeScaleFactor (originCube d m))^2 / sigma ≤
      c0 * (cubeScaleFactor (originCube d m))^2 / sigma -
        (c0 / 4) * (cubeScaleFactor (originCube d m))^2 / sigma -
        ((c0 / (8 * (K + 1))) *
            (K * (cubeScaleFactor (originCube d m))^2 / sigma +
              2 * ((c0 / 16) * (cubeScaleFactor (originCube d m))^2 / sigma)) +
          2 * ((c0 / 16) * (cubeScaleFactor (originCube d m))^2 / sigma)) := by
    have h := goodCube_torsion_lower_budget hc0pos hc01 hK htaunonneg
    convert h using 1 <;> ring
  exact goodCube_meanExit_lower_of_profile_and_local_contraction hd hD hU hUb hUconv
    hacont.continuousOn hlam hEll inner outer hTop hcover hinner hnested houter houterU
    g.toH1Function.toFun hb hE heta heps hk hbudget hmeanUcap hmeanOuterCap hcontract hg
    hcompare x hx

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
