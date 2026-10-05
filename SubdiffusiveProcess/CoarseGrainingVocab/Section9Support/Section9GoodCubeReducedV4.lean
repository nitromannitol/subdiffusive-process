module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeProviderV4
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReducedResidual
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePositiveMass

@[expose] public section

/-!
# Reduced good-cube obligations for one selected v4 template

This is the active residual for `weighted_good_cube_events` v4. It carries
`LocalDiffusionData` and exactly one selected geometry, bad event and set of
constants. The five remaining displays are Sobolev, two exit lower bounds,
and two mass bounds, together with the common layer-zero tail. Continuous
killed densities and both exit upper bounds are derived below. Positive
finite cutoff mass holds on every positive cube, so the raw event need not
contain the historical log-Lipschitz failure event `goodCubeBad`.

`GoodCubeReducedPackage` in the imported historical module is retained only
for its old conditional consumers. It is not an obligation of this interface.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (ahom ahom_pos)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The five analytic displays on the chosen reference template. -/
structure GoodCubeReducedDisplaysV4 (d : ℕ) (c A0 p0 eps1 : ℝ)
    (Pfam0 : Set (Cube d × Cube d)) (Qfam0 Afam0 : Set (Cube d))
    (bad : (M : GMCModel d) → (n : ℕ) →
      Set (nativeBox n 1 (0 : Lattice d) → ℝ)) : Prop where
  /-- The weighted Sobolev display at the intrinsic clock, at the fixed
  constant `A0`. -/
  sobolev : GoodCubeReferenceDataDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M n _ omega _ _ Qfam _ =>
      ∀ Q ∈ Qfam, GoodCubeSobolevDisplay (aCutoff M n omega) p0 A0
        (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) Q)
  /-- The parent mean-exit lower bound on the middle quarter. -/
  exit_lower : GoodCubeReferenceDataDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M n z _ law _ _ _ =>
      ∀ x ∈ middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n),
        ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)
            ((3 : ℝ) ^ n)) ≤
          meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x)
  /-- The **lower** half of the descendant exit estimate. -/
  descendant_lower : GoodCubeReferenceDataDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M _ _ _ law _ Qfam _ =>
      ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
        ∀ x ∈ cubeSet B',
          ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2) ≤
            meanExit law (cubeSet Bq) x)
  /-- The middle-quarter mass display. -/
  mass_quarter : GoodCubeReferenceDataDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M n z omega _ _ _ _ =>
      ENNReal.ofReal c *
          weightedMeasure (aCutoff M n omega)
            (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) ≤
        weightedMeasure (aCutoff M n omega)
          (middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n)))
  /-- The descendant mass display. -/
  mass_descendant : GoodCubeReferenceDataDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M n _ omega _ _ Qfam _ =>
      ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
        ENNReal.ofReal c * weightedMeasure (aCutoff M n omega) (cubeSet Bq) ≤
          weightedMeasure (aCutoff M n omega) (cubeSet B'))


/-- The v4 datum supplies the density on every family cube. -/
theorem hasContinuousKilledDensity_cubeSet_of_localDiffusionData {d : ℕ}
    {a : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (h : LocalDiffusionData a a law) (Q : Cube d) :
    HasContinuousKilledDensity a law (cubeSet Q) := by
  obtain ⟨_, hcont⟩ := h
  exact hcont (cubeSet Q) (isOpen_centeredAxisCube Q.1 Q.2)
    (isBounded_centeredAxisCube Q.1 Q.2)

/-- A single selected template, with all scalar calibration conditions explicit.
`CE` is supplied by the proved exit-upper transfer. The event and constants
are chosen together with this template; no other family is quantified over. -/
def GoodCubeSelectedReducedPackage (d : ℕ) (eta p0 CE : ℝ) : Prop :=
  ∃ (c C A0 eps1 : ℝ) (Cdep j1 j2 : ℕ) (r : ℤ),
    0 < c ∧ 0 < C ∧ 1 ≤ A0 ∧ A0 ≤ C ∧ CE * A0 ^ CE ≤ C ∧ 0 < eps1 ∧
    1 < (3 : ℝ) ^ r ∧ ((shellCoverShifts d r).card : ℝ) ≤ C ∧ 1 ≤ C ∧
    1 + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ) ∧
    c ≤ 1 / 3 ∧ c ≤ Real.sqrt layerTailConstant * eps1 ∧
    2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * c) ≤ eps1 ∧
    C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 ∧
    ∃ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
      (Qfam0 Afam0 : Set (Cube d))
      (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n 1 (0 : Lattice d) → ℝ)),
      (∀ (n : ℕ) (z : Lattice d),
        IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
          (goodCubeReferencePairs Pfam0 n z) (goodCubeReferenceFamily Qfam0 n z)
          (goodCubeReferenceFamily Afam0 n z)) ∧
      (∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))) ∧
      (∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
        M.P.toMeasure (coefficientLocalBadEvent M n 1 (bad M n) z) ≤ ENNReal.ofReal
          (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)))))) ∧
      GoodCubeReducedDisplaysV4 d c A0 p0 eps1 Pfam0 Qfam0 Afam0 bad

/-- The reduced v4 displays give the original analytic displays on this same
selected template. The continuous density is obtained from the datum. -/
theorem goodCubeAnalyticDisplays_v4_of_reduced {d : ℕ} (hd : 2 ≤ d)
    {p0 : ℝ} (hp0 : 2 < p0) :
    ∃ CE : ℝ, 0 < CE ∧
      ∀ (c C A0 eps1 : ℝ), 1 ≤ A0 → A0 ≤ C → CE * A0 ^ CE ≤ C →
      ∀ (j1 j2 : ℕ) (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
        (Qfam0 Afam0 : Set (Cube d))
        (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n 1 (0 : Lattice d) → ℝ)),
        (∀ (n : ℕ) (z : Lattice d),
          IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
            (goodCubeReferencePairs Pfam0 n z) (goodCubeReferenceFamily Qfam0 n z)
            (goodCubeReferenceFamily Afam0 n z)) →
        (∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))) →
        GoodCubeReducedDisplaysV4 d c A0 p0 eps1 Pfam0 Qfam0 Afam0 bad →
        GoodCubeReferenceDataDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
          (fun M n z omega law Pfam Qfam Afam =>
            LocalTorsionEstimates (aCutoff M n omega) law
                (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) p0 c C
                (goodCubeCentre n z, (3 : ℝ) ^ n) Qfam Afam ∧
              LocalHarmonicOscillation (aCutoff M n omega) 1 Pfam) := by
  obtain ⟨CE, hCE, hexit⟩ := exists_goodCube_exit_upper_constant hp0
  refine ⟨CE, hCE, ?_⟩
  intro c C A0 eps1 hA0 hA0C hCEC j1 j2 grid0 Pfam0 Qfam0 Afam0 bad hgeom _hin hdisp
    M hdelta n z omega hom law hdiff
  have hup : ∀ Q ∈ goodCubeReferenceFamily Qfam0 n z, ∀ x ∈ cubeSet Q,
      meanExit law (cubeSet Q) x ≤
        ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Q.2) := by
    intro Q hQ x hx
    have hQ2 := (hgeom n z).side_pos Q hQ
    have hclock := SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale_pos (ahom_pos M) hQ2
    obtain ⟨hm0, hmt⟩ := goodCube_weightedMeasure_aCutoff_ne_zero_ne_top M n omega Q hQ2
    refine (hexit d hd (aCutoff M n omega) law hdiff.1
      (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) A0 hA0 Q hQ2 hclock
      hm0 hmt (hdisp.sobolev M hdelta n z omega hom law hdiff Q hQ)
      (hasContinuousKilledDensity_cubeSet_of_localDiffusionData hdiff Q) x hx).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCEC hclock.le))
  refine goodCubeAnalyticPackage_of_supportInputs (aCutoff M n omega) law
    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) p0 c C 1
    (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferencePairs Pfam0 n z)
    (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z)
    (hdisp.exit_lower M hdelta n z omega hom law hdiff)
    (hup _ (hgeom n z).self_mem) ?_
    (hdisp.mass_quarter M hdelta n z omega hom law hdiff)
    (hdisp.mass_descendant M hdelta n z omega hom law hdiff)
    (mass_overlap_of_mass_descendant (hgeom n z) (weightedMeasure (aCutoff M n omega))
      (ENNReal.ofReal c) (hdisp.mass_descendant M hdelta n z omega hom law hdiff)) ?_
    (localHarmonicOscillation_one_of_isLocalCubeGeometry (hgeom n z) (aCutoff M n omega))
  · intro B' hB' Bq hBq hcomp
    exact ⟨hdisp.descendant_lower M hdelta n z omega hom law hdiff B' hB' Bq hBq hcomp,
      hup Bq hBq⟩
  · intro Q hQ f
    refine (hdisp.sobolev M hdelta n z omega hom law hdiff Q hQ f).trans ?_
    gcongr

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
