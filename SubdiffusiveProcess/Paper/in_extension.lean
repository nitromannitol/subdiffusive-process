module

public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.in_J

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



structure in_extension (d : ℕ) (hd : 2 ≤ d) (E : in_J d) where
  C : ℝ
  C_pos : 0 < C
  bound : ∀ (z : SpatialCoordinates d) (m : ℕ) (hr : (0 : ℝ) < 3 ^ m)
      (a : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hr))
      (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
      -- the source datum `g ∈ H^s(𝕔_m; ℝ^d)` of `−∇·a∇v = ∇·g`
      (g : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hr)),
      cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
          (fun i => g i) ≠ ⊤ →
      -- the boundary datum `h ∈ H^{1+s}(𝕔_m)` and the solution `v ∈ H^1(𝕔_m)`
      ∀ (hDatum v : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr))
        (hhfin : cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
          (fun i => sobolevGradient (hDatum : SobolevData _) i) ≠ ⊤),
      -- `v` solves `−∇·a∇v = ∇·g` weakly
      (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr),
        sobolevCoefficientForm a (v : SobolevData _) (φ : SobolevData _) =
          -inner ℝ g
            (subspaceGradient
              (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr)) φ)) →
      -- `v = h` on `∂𝕔_m`
      ((v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) -
          (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr))) ∈
        killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr) →
      normalizedEnergyNorm a
          (centeredCube z ((3 : ℝ) ^ m) hr).isOpen.measurableSet
          (sobolevGradient (v : SobolevData _)) ≤
        C * s ^ (-3 : ℝ) *
            (E.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ (-(1 / 2) : ℝ) *
            (3 : ℝ) ^ (s * (m : ℝ)) *
            Real.sqrt (cubeFractionalVecSeminormSq hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
              (fun i => g i)) +
          C * s ^ (-(3 / 2) : ℝ) *
            (E.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ ((1 / 2) : ℝ) *
            (3 : ℝ) ^ (s * (m : ℝ)) *
            cubeFractionalL2Norm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
              ⟨fun i => sobolevGradient (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) i,
                lt_top_iff_ne_top.2 hhfin⟩

end SubdiffusiveProcess.Paper
