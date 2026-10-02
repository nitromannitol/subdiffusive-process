import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceTemplate




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



structure GoodCubeAnalyticDisplays (d : ℕ) (c C p0 eps1 B : ℝ)
    (Pfam0 : Set (Cube d × Cube d)) (Qfam0 Afam0 : Set (Cube d))
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ)) :
    Prop where
  tail : ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
    M.P.toMeasure (coefficientLocalBadEvent M n B (bad M n) z) ≤ ENNReal.ofReal
      (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)))))
  exit_lower : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
    (fun M n z _ law _ _ _ =>
      ∀ x ∈ middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n),
        ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)
            ((3 : ℝ) ^ n)) ≤
          meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x)
  exit_upper : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
    (fun M n z _ law _ _ _ =>
      ∀ x ∈ cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n),
        meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x ≤
          ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)
            ((3 : ℝ) ^ n)))
  descendant : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
    (fun M _ _ _ law _ Qfam _ =>
      ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
        (∀ x ∈ cubeSet B',
          ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2) ≤
            meanExit law (cubeSet Bq) x) ∧
        (∀ x ∈ cubeSet Bq,
          meanExit law (cubeSet Bq) x ≤
            ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2)))
  mass_quarter : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
    (fun M n z omega _ _ _ _ =>
      ENNReal.ofReal c *
          weightedMeasure (aCutoff M n omega)
            (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) ≤
        weightedMeasure (aCutoff M n omega)
          (middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n)))
  mass_descendant : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
    (fun M n _ omega _ _ Qfam _ =>
      ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
        ENNReal.ofReal c * weightedMeasure (aCutoff M n omega) (cubeSet Bq) ≤
          weightedMeasure (aCutoff M n omega) (cubeSet B'))
  sobolev : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
    (fun M n _ omega _ _ Qfam _ =>
      ∀ Q ∈ Qfam, ∀ f : H10Function (cubeSet Q),
        lpSq (aCutoff M n omega) (cubeSet Q) p0 f.toH1Function.toFun ≤
          ENNReal.ofReal C *
            weightedMeasure (aCutoff M n omega) (cubeSet Q) ^ (-(1 - 2 / p0)) *
            ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Q.2 *
              energy (aCutoff M n omega) (cubeSet Q) f.toH1Function))



def GoodCubeAnalyticPackage (d : ℕ) : Prop :=
  ∃ (p0 B C0 : ℝ) (_hp0 : 2 < p0) (_hB : 0 < B) (_hC0 : 0 < C0)
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ)),
    ∀ (j1 j2 : ℕ), 2 ≤ j1 → 1 ≤ j2 →
      ∀ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
        (Qfam0 Afam0 : Set (Cube d)),
        IsLocalCubeGeometry grid0 j1 j2 ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))
            Pfam0 Qfam0 Afam0 →
        (∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))) →
        (∀ (n : ℕ) (z : Lattice d),
          IsLocalCubeGeometry grid0 j1 j2
            (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferencePairs Pfam0 n z)
            (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z)) →
        ∃ c0 : ℝ, 0 < c0 ∧
          ∀ c C eps1 : ℝ, 0 < c → c ≤ c0 → C0 ≤ C → 0 < eps1 →
            GoodCubeAnalyticDisplays d c C p0 eps1 B Pfam0 Qfam0 Afam0 bad

/-- **The frozen version 2 conclusion from the analytic package alone.**

Every numerical side condition, the cover depth, the dependence radius, the
smallness depth, the reference template and its `hgeom` witness are produced
here; only the seven analytic/probabilistic displays remain as input. -/
theorem weighted_good_cube_events_v2_of_analyticPackage
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hpkg : GoodCubeAnalyticPackage d) :
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
                LocalDiffusion (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) law →
                LocalTorsionEstimates (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
                    eps0 (Pfam n z)) := by
  obtain ⟨p0, B, C0, hp0, hB, hC0, bad, hpkg⟩ := hpkg
  -- cover depth and the layer-tail constant constraints, at `eps1 = 1`
  obtain ⟨r, c1, hc1, hBr, hc3, hcK, hcdelta⟩ :=
    exists_goodCubeConstants B 1 one_pos
  -- the analytic constant, enlarged to cover the box factor and the shell cover
  set C : ℝ := max (max C0 B) ((shellCoverShifts d r).card : ℝ) with hCdef
  have hC0C : C0 ≤ C := (le_max_left C0 B).trans (le_max_left _ _)
  have hC : 0 < C := lt_of_lt_of_le hC0 hC0C
  have hBC : B ≤ C := (le_max_right C0 B).trans (le_max_left _ _)
  have hNC : ((shellCoverShifts d r).card : ℝ) ≤ C := le_max_right _ _
  -- the dependence radius
  set Cdep : ℕ := ⌈B + Real.sqrt (d : ℝ)⌉₊ with hCdepdef
  have hCdep : B + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ) := Nat.le_ceil _
  -- the smallness depth, produced after `C` (finding P338-F1)
  obtain ⟨j1, hj1, hsmall⟩ := exists_smallness_depth C eta hC heta0
  -- the fixed reference template
  obtain ⟨grid0, Pfam0, Qfam0, Afam0, hgeom0, hinside, hgeom⟩ :=
    exists_goodCubeReferenceTemplate d hj1 (le_refl 1)
  -- the mass constant, produced after the template
  obtain ⟨c0, hc0, hdisp⟩ :=
    hpkg j1 1 hj1 (le_refl 1) grid0 Pfam0 Qfam0 Afam0 hgeom0 hinside hgeom
  set c : ℝ := min c1 c0 with hcdef
  have hc : 0 < c := lt_min hc1 hc0
  have hcc1 : c ≤ c1 := min_le_left _ _
  obtain ⟨htail, hxl, hxu, hdesc, hmq, hmd, hsob⟩ :=
    hdisp c C 1 hc (min_le_right _ _) hC0C one_pos
  exact weighted_good_cube_events_v2_of_supportInputs d hd eta heta0 heta1
    c C p0 1 B Cdep j1 1 r hc hC hp0 hB hBr hNC hBC hCdep
    (hcc1.trans hc3) (hcc1.trans hcK)
    (by
      have := mul_le_mul_of_nonneg_left hcc1
        (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 1 + Real.log 2) (2 : ℝ)⁻¹).le
      linarith)
    hsmall grid0 Pfam0 Qfam0 Afam0 hgeom bad htail hxl hxu hdesc hmq hmd hsob

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
