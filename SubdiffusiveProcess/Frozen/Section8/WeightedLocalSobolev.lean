module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Providers.Section8.WeightedLocalSobolev
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.Packet448SobolevChecks
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section

/-- The Sobolev inequality with its exponent choice exposed. -/

theorem SubdiffusiveProcess.Frozen.Section8.weighted_local_sobolev (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p0 C : ℝ, p0 = 2 + 1 / (2 * (4 * (d : ℝ) - 3)) ∧ 2 < p0 ∧ 0 < C ∧
      ∀ m : ℤ, ∀ b : Vec d → ℝ,
        let Q := originCube d m
        let U := openCubeSet Q
        CoefficientOn U b →
        ∀ hb : Homogenization.ExactCircIntegrable Q
            (fun x => b x / cubeAverage Q b - 1),
        ∀ coeff : Homogenization.Book.Ch02.TriadicCoeffFamily d,
        (∀ᵐ x ∂volume.restrict U,
          (coeff.coeffOn Q).toCoeffField x = scalarMatrix (b x)) →
        ∀ M : ℝ, 1 ≤ M →
        ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (m : ℝ))) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperNegativeBesovCircDiagonal Q (1 / 8)
            (4 * (d : ℝ)) (fun x => b x / cubeAverage Q b - 1) hb ≤
          ENNReal.ofReal M →
        ∀ f : H1Function U,
          ((∃ g : H10Function U, g.toH1Function = f) ∨
            (∫ x in U, f.toFun x * b x) = 0) →
          (ENNReal.ofReal ((cubeAverage Q b)⁻¹) *
            (volume U)⁻¹ * ∫⁻ x in U,
              ENNReal.ofReal (|f.toFun x| ^ p0 * b x)) ^ (2 / p0) ≤
            ENNReal.ofReal (C * (1 + M) ^ (2 / p0) * ((3 : ℝ) ^ m) ^ 2 *
              (Homogenization.Book.Ch02.lambdaSq Q (1 / 2) (.finite 1) coeff)⁻¹ *
              volumeAverage U (fun x => b x * vecDot (f.grad x) (f.grad x)))

:= SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.Packet448.weighted_local_sobolev_explicit d hd
