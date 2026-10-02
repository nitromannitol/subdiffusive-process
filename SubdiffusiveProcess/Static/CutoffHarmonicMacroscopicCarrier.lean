import SubdiffusiveProcess.Static.CutoffHarmonicCellCarrier

/-! # The macroscopic budget used by the microscopic cell-growth joining -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section
namespace SubdiffusiveProcess.Static

/-- A stronger macroscopic energy exponent, truncated at physical radius one.
The `1/4` exponent margin absorbs microscopic coefficient and derivative banks.
The same budget controls all smooth native harmonic extensions, faces and corners. -/
def CutoffHarmonicCellMacroscopicGrowth {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (z : Vec d) (omega : PotentialSample d) (G : ℝ) : Prop :=
  ∀ (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (B : ℝ), 0 ≤ B → HarmonicCutoffDatumSizeBound f B →
    ∀ u : H1Function (openCubeSet (originCube d 0)),
      IsWeaklyHarmonicOn
        (fun x => (ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ) ^ k • x))
        (openCubeSet (originCube d 0)) u →
      HasZeroTraceDifferenceOn (openCubeSet (originCube d 0)) u
        (cutoffHarmonicCellDatum f hf hc) →
      ∀ x ∈ openCubeSet (originCube d 0), ∀ r : ℝ, 0 < r → r ≤ 1 →
        ∫⁻ y in Metric.ball x r ∩ openCubeSet (originCube d 0),
          ENNReal.ofReal ((ahom M j)⁻¹ *
            aCutoff M j omega (z + (3 : ℝ) ^ k • y) * vecDot (u.grad y) (u.grad y)) ≤
          ENNReal.ofReal (G * B ^ 2 * (max r ((3 : ℝ) ^ k)⁻¹) ^ ((d : ℝ) - 1 / 4))

end SubdiffusiveProcess.Static
