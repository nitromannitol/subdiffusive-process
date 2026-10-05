module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCube7aClauses
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeMassGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeHarmonicMonotonicity

@[expose] public section

/-!
# Good-cube assembly for the proposed reference-family successor

Source: `mfd:in-deterministic` and `s.tightness`.
This internal conditional theorem uses the exact conclusion proposed for the
reference-family successor. It imports no draft anchor and does not install or approve v2.

The coefficient-local hull closes measurability and covariance. The overlap
mass display follows from descendant mass, and the literal exported harmonic
display holds with constant one. The seven remaining probability/analytic
inputs are explicit; they concern only the one reference family's images.
-/

set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The literal affine cube map in the proposed frozen block. -/
def goodCubeReferenceTransport {d : ℕ} (n : ℕ) (z : Lattice d) (Q : Cube d) : Cube d :=
  (goodCubeCentre n z + (3 : ℝ) ^ n • Q.1, (3 : ℝ) ^ n * Q.2)

/-- Transport only the prescribed original pairs. -/
def goodCubeReferencePairs {d : ℕ} (Pfam0 : Set (Cube d × Cube d))
    (n : ℕ) (z : Lattice d) : Set (Cube d × Cube d) :=
  (fun p => (goodCubeReferenceTransport n z p.1,
    goodCubeReferenceTransport n z p.2)) '' Pfam0

/-- Transport of an original cube family, not of the auxiliary testing family. -/
def goodCubeReferenceFamily {d : ℕ} (Qfam0 : Set (Cube d))
    (n : ℕ) (z : Lattice d) : Set (Cube d) :=
  goodCubeReferenceTransport n z '' Qfam0

/-- One analytic display for the selected reference template and the raw
coefficient-local bad predicate. No universal geometry-family quantifier occurs. -/
def GoodCubeReferenceDisplay (d : ℕ) (c eps1 B : ℝ)
    (Pfam0 : Set (Cube d × Cube d)) (Qfam0 Afam0 : Set (Cube d))
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ))
    (P : GMCModel d → ℕ → Lattice d → PotentialSample d →
      Kernel (Vec d) (Path d) → Set (Cube d × Cube d) → Set (Cube d) →
      Set (Cube d) → Prop) : Prop :=
  ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
    ∀ omega ∈ goodCubeEvent
      (goodCubeEventField n B eps1 (coefficientLocalBadEvent M n B (bad M n))) z,
    ∀ law : Kernel (Vec d) (Path d),
      LocalDiffusion (aCutoff M n omega) (aCutoff M n omega) law →
      P M n z omega law (goodCubeReferencePairs Pfam0 n z)
        (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z)

/-- Conditional assembly of the exact proposed v2 conclusion.

Remaining inputs, pinned to the source: `hE0tail`,
`hexit_lower`, `hexit_upper`,
`hdescendant`, `hmass_quarter` and `hmass_descendant`, and `hsobolev`.
The scalar constraints and reference geometry witness are displayed separately.
The strict interior oscillation needed for the lower exit proof remains inside
that obligation; choosing the exported `eps0 = 1` does not prove it.
-/
theorem weighted_good_cube_events_v2_of_supportInputs
    (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (eta : ℝ) (_heta0 : 0 < eta) (_heta1 : eta < 1)
    (c C p0 eps1 B : ℝ) (Cdep j1 j2 : ℕ) (r : ℤ)
    (hc : 0 < c) (hC : 0 < C) (hp0 : 2 < p0) (hB : 0 < B)
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
    (hexit_lower : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n z _ law _ _ _ =>
        ∀ x ∈ middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n),
          ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) ((3 : ℝ) ^ n)) ≤
            meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x))
    (hexit_upper : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n z _ law _ _ _ =>
        ∀ x ∈ cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n),
          meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x ≤
            ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) ((3 : ℝ) ^ n))))
    (hdescendant : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M _ _ _ law _ Qfam _ =>
        ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
          (∀ x ∈ cubeSet B',
            ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2) ≤
              meanExit law (cubeSet Bq) x) ∧
          (∀ x ∈ cubeSet Bq,
            meanExit law (cubeSet Bq) x ≤
              ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2))))
    (hmass_quarter : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n z omega _ _ _ _ =>
        ENNReal.ofReal c *
            weightedMeasure (aCutoff M n omega)
              (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) ≤
          weightedMeasure (aCutoff M n omega)
            (middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n))))
    (hmass_descendant : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n _ omega _ _ Qfam _ =>
        ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
          ENNReal.ofReal c * weightedMeasure (aCutoff M n omega) (cubeSet Bq) ≤
            weightedMeasure (aCutoff M n omega) (cubeSet B')))
    (hsobolev : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
      (fun M n _ omega _ _ Qfam _ =>
        ∀ Q ∈ Qfam, ∀ f : H10Function (cubeSet Q),
          lpSq (aCutoff M n omega) (cubeSet Q) p0 f.toH1Function.toFun ≤
            ENNReal.ofReal C *
              weightedMeasure (aCutoff M n omega) (cubeSet Q) ^ (-(1 - 2 / p0)) *
              ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Q.2 *
                energy (aCutoff M n omega) (cubeSet Q) f.toH1Function))) :
    ∃ (c C eps0 p0 : ℝ) (Cdep j1 j2 : ℕ),
      0 < c ∧ 0 < C ∧ 0 < eps0 ∧ 2 < p0 ∧
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
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ c →
        ∀ n : ℕ,
        ∃ E : ℕ → Lattice d → Set (_root_.SubdiffusiveProcess.Model.PotentialSample d),
          (∀ z : Lattice d,
            MeasurableSet[restrictedCoefficientSigma
              (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
                _root_.SubdiffusiveProcess.Model.aCutoff M n omega)
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
                LocalDiffusion (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
                  (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) law →
                LocalTorsionEstimates (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
                    eps0 (Pfam n z)) := by
  clear _hd _heta0 _heta1
  obtain ⟨E0, hE0meas, hE0sub, hE0prob, hE0cov⟩ := exists_layerZero_hull_family hB bad
  refine ⟨c, C, 1, p0, Cdep, j1, j2, hc, hC, by norm_num, hp0, hsmall,
    grid0, Pfam0, Qfam0, Afam0, ?_⟩
  refine ⟨hgeom, ?_⟩
  intro M hdelta n
  refine ⟨goodCubeEventField n B eps1 (E0 M n), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  -- Clause 7g on the selected original families.
  · intro z omega hom law hdiff
    have homraw := goodCubeEvent_mono_layerZero n B eps1
      (coefficientLocalBadEvent M n B (bad M n)) (E0 M n) (hE0sub M n) z hom
    exact goodCubeAnalyticPackage_of_supportInputs (aCutoff M n omega) law
      (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) p0 c C 1
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
      (localHarmonicOscillation_one_of_isLocalCubeGeometry (hgeom n z) (aCutoff M n omega))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
