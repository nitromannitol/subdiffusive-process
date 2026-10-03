module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5Producer
public import SubdiffusiveProcess.Frozen.Assumptions.AAnchored

@[expose] public section




set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support



def GoodCubeAnchoredTransfer (d : ℕ) (c C p0 eps0 eps1 B : ℝ) (j1 j2 : ℕ)
    (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
    (Qfam0 Afam0 : Set (Cube d))
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ)) :
    Prop :=
  (∀ (n : ℕ) (z : Lattice d),
      IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
        (goodCubeReferencePairs Pfam0 n z) (goodCubeReferenceFamily Qfam0 n z)
        (goodCubeReferenceFamily Afam0 n z)) →
  ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d)
    (omega : AnchoredC11Sample d),
    (omega : PotentialSample d) ∈ goodCubeEvent
      (goodCubeEventField n B eps1 (coefficientLocalBadEvent M n B (bad M n))) z →
    (∀ law : Kernel (Vec d) (Path d),
      LocalDiffusionData (aCutoff M n omega.1) (aCutoff M n omega.1) law →
        LocalTorsionEstimates (aCutoff M n omega.1) law
            (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) p0 c C
            (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferenceFamily Qfam0 n z)
            (goodCubeReferenceFamily Afam0 n z) ∧
          LocalHarmonicOscillation (aCutoff M n omega.1) eps0
            (goodCubeReferencePairs Pfam0 n z)) →
    ∀ law : Kernel (Vec d) (Path d),
      LocalDiffusionData (aAnchored M omega) (aAnchored M omega) law →
        LocalTorsionEstimates (aAnchored M omega) law
            (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) p0 c C
            (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferenceFamily Qfam0 n z)
            (goodCubeReferenceFamily Afam0 n z) ∧
          LocalHarmonicOscillation (aAnchored M omega) eps0
            (goodCubeReferencePairs Pfam0 n z)

/-- The universally quantified form of the missing analytic input, as it is
consumed by the version-5 provider. -/
def GoodCubeAnchoredTransferAll (d : ℕ) : Prop :=
  ∀ (c C p0 eps0 eps1 : ℝ) (j1 j2 : ℕ) (grid0 : Finset (Vec d))
    (Pfam0 : Set (Cube d × Cube d)) (Qfam0 Afam0 : Set (Cube d))
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n 1 (0 : Lattice d) → ℝ)),
    0 < c → 0 < C → 2 < p0 → 0 < eps0 → 0 < eps1 →
    GoodCubeAnchoredTransfer d c C p0 eps0 eps1 1 j1 j2 grid0 Pfam0 Qfam0 Afam0 bad

theorem weighted_good_cube_events_v5_of_supportInputs
    (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (eta : ℝ) (_heta0 : 0 < eta) (_heta1 : eta < 1)
    (c C p0 eps0 eps1 B : ℝ) (Cdep j1 j2 : ℕ) (r : ℤ)
    (hc : 0 < c) (hC : 0 < C) (hp0 : 2 < p0) (heps0 : 0 < eps0)
    (heps0eta : eps0 ≤ eta / 2) (hB : 0 < B)
    (hBr : B < (3 : ℝ) ^ r)
    (hNC : ((shellCoverShifts d r).card : ℝ) ≤ C)
    (hBC : B ≤ C)
    (hCdep : B + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ))
    (hc3 : c ≤ 1 / 3)
    (hcK : c ≤ Real.sqrt layerTailConstant * eps1)
    (hcdelta : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * c) ≤ eps1)
    (hsmall : C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2)
    (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
    (Qfam0 Afam0 : Set (Cube d))
    (hgeom : ∀ (n : ℕ) (z : Lattice d),
      IsLocalCubeGeometry grid0 j1 j2
        (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferencePairs Pfam0 n z)
        (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z))
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ))
    (hE0tail : ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
      M.P.toMeasure (coefficientLocalBadEvent M n B (bad M n) z) ≤ ENNReal.ofReal
        (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2))))))
    (hexit_lower : GoodCubeReferenceDataDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n z _ law _ _ _ =>
        ∀ x ∈ middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n),
          ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) ((3 : ℝ) ^ n)) ≤
            meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x))
    (hexit_upper : GoodCubeReferenceDataDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n z _ law _ _ _ =>
        ∀ x ∈ cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n),
          meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x ≤
            ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) ((3 : ℝ) ^ n))))
    (hdescendant : GoodCubeReferenceDataDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M _ _ _ law _ Qfam _ =>
        ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
          (∀ x ∈ cubeSet B',
            ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2) ≤
              meanExit law (cubeSet Bq) x) ∧
          (∀ x ∈ cubeSet Bq,
            meanExit law (cubeSet Bq) x ≤
              ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2))))
    (hmass_quarter : GoodCubeReferenceDataDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n z omega _ _ _ _ =>
        ENNReal.ofReal c *
            weightedMeasure (aCutoff M n omega)
              (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) ≤
          weightedMeasure (aCutoff M n omega)
            (middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n))))
    (hmass_descendant : GoodCubeReferenceDataDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n _ omega _ _ Qfam _ =>
        ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
          ENNReal.ofReal c * weightedMeasure (aCutoff M n omega) (cubeSet Bq) ≤
            weightedMeasure (aCutoff M n omega) (cubeSet B')))
    (hsobolev : GoodCubeReferenceDataDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n _ omega _ _ Qfam _ =>
        ∀ Q ∈ Qfam, ∀ f : H10Function (cubeSet Q),
          lpSq (aCutoff M n omega) (cubeSet Q) p0 f.toH1Function.toFun ≤
            ENNReal.ofReal C *
              weightedMeasure (aCutoff M n omega) (cubeSet Q) ^ (-(1 - 2 / p0)) *
              ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Q.2 *
                energy (aCutoff M n omega) (cubeSet Q) f.toH1Function)))
    (hoscillation : GoodCubeReferenceDataDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n _ omega _ Pfam _ _ =>
        LocalHarmonicOscillation (aCutoff M n omega) eps0 Pfam))
    (htransfer : GoodCubeAnchoredTransfer d c C p0 eps0 eps1 B j1 j2 grid0 Pfam0
      Qfam0 Afam0 bad) :
    ∃ (c C eps0 p0 : ℝ) (Cdep j1 j2 : ℕ),
      0 < c ∧ 0 < C ∧ 0 < eps0 ∧ eps0 ≤ eta / 2 ∧ 2 < p0 ∧
      C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 ∧
      ∃ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
        (Qfam0 Afam0 : Set (Cube d)),
        let transportCube : ℕ → Lattice d → Cube d → Cube d := fun n z Q =>
          (goodCubeCentre n z + (3 : ℝ) ^ n • Q.1, (3 : ℝ) ^ n * Q.2)
        let Pfam : ℕ → Lattice d → Set (Cube d × Cube d) := fun n z =>
          (fun p => (transportCube n z p.1, transportCube n z p.2)) '' Pfam0
        let Qfam : ℕ → Lattice d → Set (Cube d) := fun n z =>
          transportCube n z '' Qfam0
        let Afam : ℕ → Lattice d → Set (Cube d) := fun n z =>
          transportCube n z '' Afam0
        (∀ (n : ℕ) (z : Lattice d),
          IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
            (Pfam n z) (Qfam n z) (Afam n z)) ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ c →
        ∀ n : ℕ,
        ∃ E : ℕ → Lattice d → Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
          (∀ z : Lattice d,
            MeasurableSet[restrictedCoefficientSigma
              (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
              (centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ n))] (E 0 z)) ∧
          (∀ j : ℕ, 1 ≤ j → ∀ z : Lattice d,
            MeasurableSet[shellLocalSigma (n + j)
              (centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ (n + j)))] (E j z)) ∧
          (∀ (j : ℕ) (z : Lattice d),
            M.P.toMeasure (E j z) ≤
              ENNReal.ofReal (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
                (3 : ℝ) ^ (3 * (j : ℝ) / 2))))) ∧
          IndependentEventScales M.P.toMeasure E ∧
          MultiscaleFiniteRangeIndependentEvents M.P.toMeasure (fun j => Cdep * 3 ^ j) E ∧
          TranslationInvariantEventLaw M.P.toMeasure E ∧
          (∀ z : Lattice d,
            ∀ omega ∈ goodCubeEvent E z,
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) law →
                LocalTorsionEstimates (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
                    eps0 (Pfam n z)) ∧
          (∀ z : Lattice d,
            ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d,
              (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ∈ goodCubeEvent E z →
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega)
                  (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega) law →
                LocalTorsionEstimates (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega)
                    eps0 (Pfam n z)) := by
  clear _hd _heta0 _heta1
  obtain ⟨E0, hE0meas, hE0sub, hE0prob, hE0cov⟩ := exists_layerZero_hull_family hB bad
  refine ⟨c, C, eps0, p0, Cdep, j1, j2, hc, hC, heps0, heps0eta, hp0, hsmall,
    grid0, Pfam0, Qfam0, Afam0, ?_⟩
  refine ⟨hgeom, ?_⟩
  intro M hdelta n
  have hcutoff : ∀ (z : Lattice d)
      (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
      omega ∈ goodCubeEvent (goodCubeEventField n B eps1 (E0 M n)) z →
      ∀ law : Kernel (Vec d) (Path d),
        LocalDiffusionData (aCutoff M n omega) (aCutoff M n omega) law →
        LocalTorsionEstimates (aCutoff M n omega) law
            (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) p0 c C
            (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferenceFamily Qfam0 n z)
            (goodCubeReferenceFamily Afam0 n z) ∧
          LocalHarmonicOscillation (aCutoff M n omega) eps0
            (goodCubeReferencePairs Pfam0 n z) := by
    intro z omega hom law hdiff
    have homraw := goodCubeEvent_mono_layerZero n B eps1
      (coefficientLocalBadEvent M n B (bad M n)) (E0 M n) (hE0sub M n) z hom
    exact goodCubeAnalyticPackage_of_supportInputs (aCutoff M n omega) law
      (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) p0 c C eps0
      (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferencePairs Pfam0 n z)
      (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z)
      (hexit_lower M hdelta n z omega homraw law hdiff)
      (hexit_upper M hdelta n z omega homraw law hdiff)
      (hdescendant M hdelta n z omega homraw law hdiff)
      (hmass_quarter M hdelta n z omega homraw law hdiff)
      (hmass_descendant M hdelta n z omega homraw law hdiff)
      (mass_overlap_of_mass_descendant (hgeom n z) (weightedMeasure (aCutoff M n omega))
        (ENNReal.ofReal c) (hmass_descendant M hdelta n z omega homraw law hdiff))
      (hsobolev M hdelta n z omega homraw law hdiff)
      (hoscillation M hdelta n z omega homraw law hdiff)
  refine ⟨goodCubeEventField n B eps1 (E0 M n), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- clause 7a, on the enlarged box
  · intro z
    have hbox : nativeBox n B z ⊆ centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ n) :=
      centeredAxisCube_mono (mul_le_mul_of_nonneg_right hBC (by positivity))
    exact SubdiffusiveProcess.CoarseGrainingVocab.restrictedCoefficientSigma_mono _ hbox _ (hE0meas M n z)
  -- clause 7b, on the enlarged box
  · intro j hj z
    have hbox : layerBox n j B z ⊆
        centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ (n + j)) :=
      centeredAxisCube_mono (mul_le_mul_of_nonneg_right hBC (by positivity))
    refine shellLocalSigma_mono (n + j) hbox _ ?_
    match j with
    | 0 => exact absurd hj (by omega)
    | (i + 1) => exact measurableSet_layerEvent hB.le n (i + 1) eps1 z
  -- clause 7c
  · intro j z
    have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
    match j with
    | 0 =>
        have h := (hE0prob M n z).le.trans (hE0tail M hdelta n z)
        have hrw : (3 : ℝ) ^ (3 * ((0 : ℕ) : ℝ) / 2) = 1 := by
          norm_num
        simpa only [goodCubeEventField, hrw, mul_one] using h
    | (i + 1) =>
        have hdlt : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) ≤ eps1 := by
          refine le_trans ?_ hcdelta
          have hpos : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
            Real.rpow_pos_of_pos (by positivity) _
          nlinarith
        have hlayer := measure_layerEvent_le_cover M n (i + 1) hB.le hBr hdlt z
        refine hlayer.trans (ENNReal.ofReal_le_ofReal ?_)
        have hexp : c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
            (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2) ≤
            layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) *
              (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _)
          exact tail_exponent_transfer layerTailConstant_pos hdpos hdelta hc3 hcK
        have hmono : Real.exp (-(layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) *
              (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2))) ≤
            Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
              (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2))) :=
          Real.exp_le_exp.mpr (by linarith)
        exact mul_le_mul hNC hmono (Real.exp_pos _).le hC.le
  -- clause 7d
  · exact (goodCubeEventField_clauses M n hB.le hCdep (E0 M n) (hE0meas M n)).2.1
  -- clause 7e
  · exact (goodCubeEventField_clauses M n hB.le hCdep (E0 M n) (hE0meas M n)).2.2
  -- clause 7f
  · exact translationInvariantEventLaw_goodCubeEventField M n hB.le (E0 M n)
      (fun z => measurableSet_of_restrictedCoefficientSigma (hE0meas M n z))
      (fun z a => hE0cov M n z a)
  -- Clause 7g on the selected original families, at the small exported tolerance.
  · exact fun z omega hom law hdiff => hcutoff z omega hom law hdiff
  -- The anchored coupled conclusion on the same events and transported families.
  · intro z omega hom law hdiff
    have homraw := goodCubeEvent_mono_layerZero n B eps1
      (coefficientLocalBadEvent M n B (bad M n)) (E0 M n) (hE0sub M n) z hom
    exact htransfer hgeom M hdelta n z omega homraw
      (fun law' hdiff' => hcutoff z omega.1 hom law' hdiff') law hdiff


/-- A chosen version-5 residual gives the exact frozen version-5 conclusion,
given the anchored transfer.  Everything except that transfer is proved. -/
theorem exists_goodCube_v5_reduced_assembly
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p0 : ℝ) (hp0 : 2 < p0)
    (htransfer : GoodCubeAnchoredTransferAll d) :
    ∃ CE : ℝ, 0 < CE ∧
      ∀ (eta eps0 : ℝ), 0 < eta → eta < 1 → 0 < eps0 → eps0 ≤ eta / 2 →
        GoodCubeSelectedReducedPackageV5 d eta p0 CE eps0 →
    ∃ (c C eps0 p0 : ℝ) (Cdep j1 j2 : ℕ),
      0 < c ∧ 0 < C ∧ 0 < eps0 ∧ eps0 ≤ eta / 2 ∧ 2 < p0 ∧
      C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 ∧
      ∃ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
        (Qfam0 Afam0 : Set (Cube d)),
        let transportCube : ℕ → Lattice d → Cube d → Cube d := fun n z Q =>
          (goodCubeCentre n z + (3 : ℝ) ^ n • Q.1, (3 : ℝ) ^ n * Q.2)
        let Pfam : ℕ → Lattice d → Set (Cube d × Cube d) := fun n z =>
          (fun p => (transportCube n z p.1, transportCube n z p.2)) '' Pfam0
        let Qfam : ℕ → Lattice d → Set (Cube d) := fun n z =>
          transportCube n z '' Qfam0
        let Afam : ℕ → Lattice d → Set (Cube d) := fun n z =>
          transportCube n z '' Afam0
        (∀ (n : ℕ) (z : Lattice d),
          IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
            (Pfam n z) (Qfam n z) (Afam n z)) ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ c →
        ∀ n : ℕ,
        ∃ E : ℕ → Lattice d → Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
          (∀ z : Lattice d,
            MeasurableSet[restrictedCoefficientSigma
              (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
              (centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ n))] (E 0 z)) ∧
          (∀ j : ℕ, 1 ≤ j → ∀ z : Lattice d,
            MeasurableSet[shellLocalSigma (n + j)
              (centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ (n + j)))] (E j z)) ∧
          (∀ (j : ℕ) (z : Lattice d),
            M.P.toMeasure (E j z) ≤
              ENNReal.ofReal (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
                (3 : ℝ) ^ (3 * (j : ℝ) / 2))))) ∧
          IndependentEventScales M.P.toMeasure E ∧
          MultiscaleFiniteRangeIndependentEvents M.P.toMeasure (fun j => Cdep * 3 ^ j) E ∧
          TranslationInvariantEventLaw M.P.toMeasure E ∧
          (∀ z : Lattice d,
            ∀ omega ∈ goodCubeEvent E z,
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) law →
                LocalTorsionEstimates (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
                    eps0 (Pfam n z)) ∧
          (∀ z : Lattice d,
            ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d,
              (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ∈ goodCubeEvent E z →
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega)
                  (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega) law →
                LocalTorsionEstimates (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega)
                    eps0 (Pfam n z)) := by
  obtain ⟨CE, hCE, hreduce⟩ := goodCubeAnalyticDisplays_v4_of_reduced hd hp0
  refine ⟨CE, hCE, ?_⟩
  intro eta eps0 heta0 heta1 heps0 heps0eta hpkg
  obtain ⟨c, C, A0, eps1, Cdep, j1, j2, r, hc, hC, hA0, hA0C, hCEC, heps1,
    hBr, hNC, hBC, hCdep, hc3, hcK, hcdelta, hsmall,
    grid0, Pfam0, Qfam0, Afam0, bad, hgeom, hin, htail, hdisp, hosc⟩ := hpkg
  have hcomplete := hreduce c C A0 eps1 hA0 hA0C hCEC j1 j2 grid0
    Pfam0 Qfam0 Afam0 bad hgeom hin hdisp
  exact weighted_good_cube_events_v5_of_supportInputs d hd eta heta0 heta1
    c C p0 eps0 eps1 1 Cdep j1 j2 r hc hC hp0 heps0 heps0eta one_pos hBr hNC hBC hCdep
    hc3 hcK hcdelta hsmall grid0 Pfam0 Qfam0 Afam0 hgeom bad htail
    (fun M hdelta n z omega hom law hdiff =>
      (hcomplete M hdelta n z omega hom law hdiff).1.exit_lower)
    (fun M hdelta n z omega hom law hdiff =>
      (hcomplete M hdelta n z omega hom law hdiff).1.exit_upper)
    (fun M hdelta n z omega hom law hdiff =>
      (hcomplete M hdelta n z omega hom law hdiff).1.descendant)
    (fun M hdelta n z omega hom law hdiff =>
      (hcomplete M hdelta n z omega hom law hdiff).1.mass_quarter)
    (fun M hdelta n z omega hom law hdiff =>
      (hcomplete M hdelta n z omega hom law hdiff).1.mass_descendant)
    (fun M hdelta n z omega hom law hdiff =>
      (hcomplete M hdelta n z omega hom law hdiff).1.sobolev)
    (fun M hdelta n z omega hom _law _hdiff =>
      hosc M hdelta n z omega (Set.mem_iInter.mp hom 0))
    (htransfer c C p0 eps0 eps1 j1 j2 grid0 Pfam0 Qfam0 Afam0 bad hc hC hp0 heps0 heps1)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
